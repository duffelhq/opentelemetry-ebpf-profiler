// Copyright The OpenTelemetry Authors
// SPDX-License-Identifier: Apache-2.0

package beam // import "go.opentelemetry.io/ebpf-profiler/interpreter/beam"

// BEAM VM Unwinder support code

// The BEAM VM is an interpreter for Erlang, as well as several other languages
// that share the same bytecode, such as Elixir and Gleam.

import (
	"fmt"
	"regexp"
	"strconv"
	"strings"
	"unsafe"

	"github.com/elastic/go-freelru"
	"go.opentelemetry.io/ebpf-profiler/internal/log"
	"go.opentelemetry.io/ebpf-profiler/libpf/hash"
	"go.opentelemetry.io/ebpf-profiler/libpf/pfunsafe"
	npsr "go.opentelemetry.io/ebpf-profiler/nopanicslicereader"

	"go.opentelemetry.io/ebpf-profiler/interpreter"
	"go.opentelemetry.io/ebpf-profiler/libpf"
	"go.opentelemetry.io/ebpf-profiler/lpm"
	"go.opentelemetry.io/ebpf-profiler/process"
	"go.opentelemetry.io/ebpf-profiler/remotememory"
	"go.opentelemetry.io/ebpf-profiler/reporter"
	"go.opentelemetry.io/ebpf-profiler/support"
)

var (
	// regex for matching the process name
	beamRegex                      = regexp.MustCompile(`(^|\/)beam\.smp`)
	_         interpreter.Data     = &beamData{}
	_         interpreter.Instance = &beamInstance{}
)

type beamData struct {
	otpRelease          uint8
	ertsVersion         string
	theActiveCodeIndex  libpf.Address
	r                   libpf.Address
	beamNormalExit      libpf.Address
	ertsFrameLayout     uint64
	ertsAtomTable       uint64
	etpPtrMask          uint64
	etpHeaderSubtagMask uint64
	etpHeapBitsSubtag   uint64
	// Sizes and offsets BEAM internal structs we need to traverse
	vmStructs struct {
		// ranges
		// https://github.com/erlang/otp/blob/OTP-27.2.4/erts/emulator/beam/beam_ranges.c#L56-L61
		ranges struct {
			sizeOf uint8
		}

		// BeamCodeHeader
		// https://github.com/erlang/otp/blob/OTP-27.2.4/erts/emulator/beam/beam_code.h#L56-L125
		beamCodeHeader struct {
			sizeOf, numFunctions, lineTable, functions uint8
		}

		// ErtsCodeInfo
		// https://github.com/erlang/otp/blob/OTP-27.2.4/erts/emulator/beam/code_ix.h#L104-L123
		ertsCodeInfo struct {
			sizeOf, mfa uint8
		}

		// ErtsCodeMFA
		// https://github.com/erlang/otp/blob/OTP-27.2.4/erts/emulator/beam/code_ix.h#L87-L95
		ertsCodeMfa struct {
			sizeOf, module, function, arity uint8
		}

		// BeamCodeLineTab
		// https://github.com/erlang/otp/blob/OTP-27.2.4/erts/emulator/beam/beam_code.h#L130-L138
		beamCodeLineTab struct {
			sizeOf, fnamePtr, locSize, locTab, funcTab uint8
		}

		// IndexTable
		// https://github.com/erlang/otp/blob/OTP-27.2.4/erts/emulator/beam/index.h#L39-L47
		indexTable struct {
			segTable uint8
		}

		// Atom
		// https://github.com/erlang/otp/blob/OTP-27.2.4/erts/emulator/beam/atom.h#L48-L54
		// In OTP 28, we need to look it up as a binary:
		// https://github.com/erlang/otp/blob/OTP-28.0.2/erts/emulator/beam/atom.h#L50-L59
		atom struct {
			len, name uint8
			u         struct {
				bin uint8
			}
		}

		// ErlHeapBits
		// https://github.com/erlang/otp/blob/OTP-28.0.2/erts/emulator/beam/erl_bits.h#L149-L154
		erlHeapBits struct {
			data uint8
		}
	}
}

type beamMfa struct {
	module   uint32
	function uint32
	arity    uint32
}

type beamInstance struct {
	interpreter.InstanceStubs

	pid          libpf.PID
	data         *beamData
	rm           remotememory.RemoteMemory
	rangesPtr    libpf.Address
	atomTable    libpf.Address
	atomCache    *freelru.LRU[uint32, libpf.String]
	mfaNameCache *freelru.LRU[beamMfa, libpf.String]
	stringCache  *freelru.LRU[libpf.Address, libpf.String]

	// prefixes is indexed by the prefix added to ebpf maps (to be cleaned up) to its generation
	prefixes map[lpm.Prefix]uint32
	// mappingGeneration is the current generation (so old entries can be pruned)
	mappingGeneration uint32
}

func GetLoader(_ Config) interpreter.Loader {
	return loader
}

func loader(ebpf interpreter.EbpfHandler, info *interpreter.LoaderInfo) (interpreter.Data, error) {
	matches := beamRegex.FindStringSubmatch(info.FileName())
	if matches == nil {
		return nil, nil
	}

	ef, err := info.GetELF()
	if err != nil {
		return nil, err
	}

	// OTP 29 builds ERTS with hidden visibility. Read runtime globals from the
	// full symbol table, which we already need for beam_ranges.c's static r.
	symbols := map[libpf.SymbolName]libpf.Symbol{
		"r": {}, "the_active_code_index": {}, "erts_atom_table": {},
		"beam_normal_exit": {}, "erts_frame_layout": {},
		"etp_otp_release": {}, "etp_erts_version": {}, "etp_ptr_mask": {},
		"etp_header_subtag_mask": {}, "etp_heap_bits_subtag": {},
	}
	err = ef.VisitSymbols(func(sym libpf.Symbol) bool {
		if previous, wanted := symbols[sym.Name]; wanted && previous.Address == 0 && sym.Address != 0 {
			symbols[sym.Name] = sym
		}
		return true
	})
	if err != nil {
		return nil, fmt.Errorf("read BEAM symbol table: %w", err)
	}
	for name, sym := range symbols {
		if sym.Address != 0 {
			continue
		}
		// A partially stripped executable can retain r in .symtab but keep
		// its exported globals only in .dynsym.
		exported, err := ef.LookupSymbol(name)
		if err == nil {
			symbols[name] = *exported
		} else if name != "erts_frame_layout" {
			return nil, fmt.Errorf("missing BEAM symbol %q: %w", name, err)
		}
	}

	readData := func(name libpf.SymbolName, maxSize uint) ([]byte, error) {
		sym := symbols[name]
		data := make([]byte, min(sym.Size, uint64(maxSize)))
		_, err := ef.ReadAt(data, int64(sym.Address))
		return data, err
	}
	otpReleaseString, err := readData("etp_otp_release", 4)
	if err != nil {
		return nil, fmt.Errorf("read OTP release: %w", err)
	}
	otpRelease, err := strconv.ParseUint(strings.TrimSuffix(string(otpReleaseString), "\x00"), 10, 8)
	if err != nil {
		return nil, fmt.Errorf("invalid OTP release %q: %w", otpReleaseString, err)
	}
	ertsVersion, err := readData("etp_erts_version", 64)
	if err != nil {
		return nil, fmt.Errorf("read ERTS version: %w", err)
	}
	etpPtrMask, err := readData("etp_ptr_mask", 8)
	if err != nil {
		return nil, fmt.Errorf("read etp_ptr_mask: %w", err)
	}
	etpHeaderSubtagMask, err := readData("etp_header_subtag_mask", 8)
	if err != nil {
		return nil, fmt.Errorf("read etp_header_subtag_mask: %w", err)
	}
	etpHeapBitsSubtag, err := readData("etp_heap_bits_subtag", 8)
	if err != nil {
		return nil, fmt.Errorf("read etp_heap_bits_subtag: %w", err)
	}

	d := &beamData{
		otpRelease:          uint8(otpRelease),
		ertsVersion:         strings.TrimSuffix(string(ertsVersion), "\x00"),
		theActiveCodeIndex:  libpf.Address(symbols["the_active_code_index"].Address),
		r:                   libpf.Address(symbols["r"].Address),
		beamNormalExit:      libpf.Address(symbols["beam_normal_exit"].Address),
		ertsAtomTable:       uint64(symbols["erts_atom_table"].Address),
		ertsFrameLayout:     uint64(symbols["erts_frame_layout"].Address),
		etpPtrMask:          npsr.Uint64(etpPtrMask, 0),
		etpHeaderSubtagMask: npsr.Uint64(etpHeaderSubtagMask, 0),
		etpHeapBitsSubtag:   npsr.Uint64(etpHeapBitsSubtag, 0),
	}

	vms := &d.vmStructs

	// These values are the same on OTP releases 27.2.4 and 28.0.2.
	vms.ranges.sizeOf = 32
	vms.beamCodeHeader.numFunctions = 0
	vms.beamCodeHeader.lineTable = 72
	vms.ertsCodeInfo.sizeOf = 40
	vms.ertsCodeInfo.mfa = 16
	vms.ertsCodeMfa.sizeOf = 24
	vms.ertsCodeMfa.module = 0
	vms.ertsCodeMfa.function = 8
	vms.ertsCodeMfa.arity = 16
	vms.beamCodeLineTab.sizeOf = 32
	vms.beamCodeLineTab.fnamePtr = 0
	vms.beamCodeLineTab.locSize = 8
	vms.beamCodeLineTab.locTab = 16
	vms.beamCodeLineTab.funcTab = 24
	vms.indexTable.segTable = 120
	vms.atom.len = 24
	vms.erlHeapBits.data = 16

	switch d.otpRelease {
	case 27:
		vms.beamCodeHeader.sizeOf = 144
		vms.beamCodeHeader.functions = 136
		vms.atom.name = 32
	case 28, 29:
		vms.beamCodeHeader.sizeOf = 160
		vms.beamCodeHeader.functions = 152
		vms.atom.u.bin = 32
		if d.otpRelease == 29 {
			// OTP 29 made func_tab a flexible array at the end of BeamCodeLineTab.
			vms.beamCodeLineTab.sizeOf = 24
		}
	default:
		return d, fmt.Errorf("unsupported OTP version for BEAM interpreter: %d", d.otpRelease)
	}

	return d, nil
}

func (d *beamData) String() string {
	return fmt.Sprintf("BEAM OTP %d, ERTS %s", d.otpRelease, d.ertsVersion)
}

func hashMFA(key beamMfa) uint32 {
	mfhash := uint32(hash.Uint64(uint64(key.module)<<32 | uint64(key.function)))
	return uint32(hash.Uint64(uint64(mfhash)<<32 | uint64(key.arity)))
}

func (d *beamData) Attach(ebpf interpreter.EbpfHandler, pid libpf.PID, bias libpf.Address,
	rm remotememory.RemoteMemory) (interpreter.Instance, error) {
	log.Debugf("BEAM attaching, OTP %d, ERTS %s, bias: 0x%x", d.otpRelease, d.ertsVersion, bias)

	data := support.BEAMProcInfo{
		R:                     uint64(bias + d.r),
		The_active_code_index: uint64(bias + d.theActiveCodeIndex),
		Beam_normal_exit:      rm.Uint64(bias + d.beamNormalExit),
		Ranges_sizeof:         uint8(d.vmStructs.ranges.sizeOf),
	}

	// If this value is zero, it means that frame pointer support is not included in the runtime binary
	if d.ertsFrameLayout != 0 {
		ertsFrameLayout := rm.Uint64(bias + libpf.Address(d.ertsFrameLayout))
		// https://github.com/erlang/otp/blob/OTP-27.2.4/erts/emulator/beam/erl_vm.h#L68-L73
		data.Frame_pointers_enabled = ertsFrameLayout == 1
	}

	if err := ebpf.UpdateProcData(libpf.BEAM, pid, unsafe.Pointer(&data)); err != nil {
		return nil, err
	}

	atomCache, err := freelru.New[uint32, libpf.String](
		interpreter.LruFunctionCacheSize, hash.Uint32)
	if err != nil {
		return nil, err
	}

	mfaNameCache, err := freelru.New[beamMfa, libpf.String](
		interpreter.LruFunctionCacheSize, hashMFA)
	if err != nil {
		return nil, err
	}

	stringCache, err := freelru.New[libpf.Address, libpf.String](
		interpreter.LruFunctionCacheSize, libpf.Address.Hash32)
	if err != nil {
		return nil, err
	}

	return &beamInstance{
		pid:          pid,
		data:         d,
		rm:           rm,
		prefixes:     make(map[lpm.Prefix]uint32),
		rangesPtr:    bias + libpf.Address(d.r),
		atomTable:    bias + libpf.Address(d.ertsAtomTable),
		atomCache:    atomCache,
		mfaNameCache: mfaNameCache,
		stringCache:  stringCache,
	}, nil
}

func (d *beamData) Unload(_ interpreter.EbpfHandler) {
}

func (i *beamInstance) UsesAnonymousMappings() bool {
	return true
}

func (i *beamInstance) SynchronizeMappings(ebpf interpreter.EbpfHandler, _ reporter.ExecutableReporter, pr process.Process, mappings []process.RawMapping) error {
	pid := pr.PID()
	i.mappingGeneration++
	for idx := range mappings {
		m := &mappings[idx]
		if !m.IsExecutable() || !m.IsAnonymous() {
			continue
		}

		// Just assume all anonymous and executable mappings are BEAM for now
		log.Debugf("Enabling BEAM for %#x/%#x", m.Vaddr, m.Length)

		prefixes, err := lpm.CalculatePrefixList(m.Vaddr, m.Vaddr+m.Length)
		if err != nil {
			return fmt.Errorf("new anonymous mapping lpm failure %#x/%#x", m.Vaddr, m.Length)
		}

		for _, prefix := range prefixes {
			_, exists := i.prefixes[prefix]
			if !exists {
				err := ebpf.UpdatePidInterpreterMapping(pid, prefix, support.ProgUnwindBEAM, 0, 0)
				if err != nil {
					return err
				}
			}
			i.prefixes[prefix] = i.mappingGeneration
		}
	}

	// Remove prefixes not seen
	for prefix, generation := range i.prefixes {
		if generation == i.mappingGeneration {
			continue
		}
		log.Debugf("Delete BEAM prefix %#v", prefix)
		_ = ebpf.DeletePidInterpreterMapping(pid, prefix)
		delete(i.prefixes, prefix)
	}

	return nil
}

func (i *beamInstance) Detach(interpreter.EbpfHandler, libpf.PID) error {
	return nil
}

func (i *beamInstance) Symbolize(ef libpf.EbpfFrame, frames *libpf.Frames, _ libpf.FrameMapping) error {
	if !ef.Type().IsInterpType(libpf.BEAM) {
		return interpreter.ErrMismatchInterpreterType
	}
	pc := libpf.Address(ef.Data())
	codeHeader := libpf.Address(ef.Variable(0))

	functionIndex, mfa, err := i.findMFA(pc, codeHeader)
	if err != nil {
		return err
	}

	var mfaName libpf.String
	if value, ok := i.mfaNameCache.Get(mfa); ok {
		mfaName = value
	} else {
		moduleName, err := i.lookupAtom(mfa.module)
		if err != nil {
			return err
		}
		functionName, err := i.lookupAtom(mfa.function)
		if err != nil {
			return err
		}

		if strings.HasPrefix(moduleName.String(), "Elixir.") {
			// This is an Elixir module, so format the function using Elixir syntax (without the "Elixir." prefix)
			mfaName = libpf.Intern(fmt.Sprintf("%s.%s/%d", moduleName.String()[7:], functionName, mfa.arity))
		} else {
			// Assume it's Erlang and format it using Erlang syntax
			mfaName = libpf.Intern(fmt.Sprintf("%s:%s/%d", moduleName, functionName, mfa.arity))
		}

		i.mfaNameCache.Add(mfa, mfaName)
	}

	fileName, lineNumber, err := i.findFileLocation(codeHeader, functionIndex, pc)
	if err == nil {
		log.Debugf("BEAM Found function %s at %s:%d", mfaName, fileName, lineNumber)
		frames.Append(&libpf.Frame{
			Type:         libpf.BEAMFrame,
			FunctionName: mfaName,
			SourceFile:   fileName,
			SourceLine:   libpf.SourceLineno(lineNumber),
		})
	} else {
		log.Debugf("BEAM Found function %s", mfaName)
		frames.Append(&libpf.Frame{
			Type:         libpf.BEAMFrame,
			FunctionName: mfaName,
		})
	}

	return nil
}

func (i *beamInstance) findMFA(pc libpf.Address, codeHeader libpf.Address) (functionIndex uint64, mfa beamMfa, err error) {
	vms := i.data.vmStructs

	numFunctions := i.rm.Uint32(codeHeader + libpf.Address(vms.beamCodeHeader.numFunctions))
	functions := codeHeader + libpf.Address(vms.beamCodeHeader.functions)

	// This buffer is used to load the start and end pointers for the memory
	// ranges as we binary-search for the correct MFA entry in the codeHeader
	// based on whether the PC falls before, after, or within the mid range.
	// Based on the implementation here:
	// https://github.com/erlang/otp/blob/OTP-27.2.4/erts/etc/unix/etp-commands.in#L1343
	midBuffer := make([]byte, 16)

	ertsCodeInfo := libpf.Address(0)
	lowIdx := uint64(0)
	highIdx := uint64(numFunctions) - 1
	for lowIdx < highIdx {
		midIdx := lowIdx + (highIdx-lowIdx)/2
		err := i.rm.Read(functions+libpf.Address(midIdx*8), midBuffer)
		if err != nil {
			return 0, beamMfa{}, fmt.Errorf("BEAM unable to read codeHeader.functions[%d] for codeHeader 0x%x", midIdx, codeHeader)
		}
		midStart := npsr.Ptr(midBuffer, 0)
		midEnd := npsr.Ptr(midBuffer, 8)
		if pc < midStart {
			highIdx = midIdx
		} else if pc >= midEnd {
			lowIdx = midIdx + 1
		} else {
			ertsCodeInfo = midStart
			functionIndex = midIdx

			data := make([]byte, vms.ertsCodeMfa.sizeOf)
			err = i.rm.Read(ertsCodeInfo+libpf.Address(vms.ertsCodeInfo.mfa), data)
			if err != nil {
				return 0, beamMfa{}, fmt.Errorf("BEAM unable to look up MFA at for ertsCodeInfo 0x%x", ertsCodeInfo)
			}
			mfa.module = npsr.Uint32(data, uint(vms.ertsCodeMfa.module))
			mfa.function = npsr.Uint32(data, uint(vms.ertsCodeMfa.function))
			mfa.arity = npsr.Uint32(data, uint(vms.ertsCodeMfa.arity))

			return functionIndex, mfa, nil
		}
	}

	return 0, beamMfa{}, fmt.Errorf("BEAM unable to find the MFA for PC 0x%x in expected code range", pc)
}

func (i *beamInstance) findFileLocation(codeHeader libpf.Address, functionIndex uint64, pc libpf.Address) (fileName libpf.String, lineNumber uint64, err error) {
	vms := i.data.vmStructs

	lineTable := i.rm.Ptr(codeHeader + libpf.Address(vms.beamCodeHeader.lineTable))
	functionTable := lineTable + libpf.Address(vms.beamCodeLineTab.funcTab)

	lineRange := make([]byte, 16)
	err = i.rm.Read(functionTable+libpf.Address(8*functionIndex), lineRange)
	if err != nil {
		return libpf.NullString, 0, fmt.Errorf("BEAM failed to read function table info")
	}
	lineLow := npsr.Ptr(lineRange, 0)
	lineHigh := npsr.Ptr(lineRange, 8)

	// This buffer is used to load the start and end pointers for the memory
	// ranges as we binary-search for the correct line number from the start of
	// the MFA entry in the codeHeader based on whether the PC falls before,
	// after, or within the mid range.
	// Based on the implementation here:
	// https://github.com/erlang/otp/blob/OTP-27.2.4/erts/etc/unix/etp-commands.in#L1269
	lineMidBuffer := make([]byte, 16)
	// We need to align the lineMid values on 8-byte address boundaries
	bitmask := libpf.Address(^(uint64(0xf)))
	for lineHigh > lineLow {
		lineMid := lineLow + ((lineHigh-lineLow)/2)&bitmask
		err := i.rm.Read(lineMid, lineMidBuffer)
		if err != nil {
			return libpf.NullString, 0, fmt.Errorf("BEAM failed to read line table")
		}
		if pc < npsr.Ptr(lineMidBuffer, 0) {
			lineHigh = lineMid
		} else if pc < npsr.Ptr(lineMidBuffer, 8) {
			firstLine := i.rm.Ptr(functionTable)
			locIndex := uint32((lineMid - firstLine) / 8)
			lineTab := make([]byte, vms.beamCodeLineTab.sizeOf)
			err = i.rm.Read(lineTable, lineTab)
			if err != nil {
				return libpf.NullString, 0, fmt.Errorf("BEAM failed to read line table info")
			}
			locSize := npsr.Uint32(lineTab, uint(vms.beamCodeLineTab.locSize))
			locTab := npsr.Ptr(lineTab, uint(vms.beamCodeLineTab.locTab))
			locAddr := locTab + libpf.Address(locSize*locIndex)
			loc := uint64(0)
			if locSize == 2 {
				loc = uint64(i.rm.Uint16(locAddr))
			} else {
				loc = uint64(i.rm.Uint32(locAddr))
			}
			fnameIndex := loc >> 24
			fileNamePtr := i.rm.Ptr(lineTable) + libpf.Address(8*fnameIndex)
			fileName = i.readErlangString(i.rm.Ptr(fileNamePtr), 256)

			return fileName, loc & ((1 << 24) - 1), nil
		} else {
			lineLow = lineMid + 8
		}
	}

	return libpf.NullString, 0, fmt.Errorf("BEAM unable to find file and line number")
}

func (i *beamInstance) lookupAtom(index uint32) (libpf.String, error) {
	if value, ok := i.atomCache.Get(index); ok {
		return value, nil
	}

	vms := i.data.vmStructs

	segTable := i.rm.Ptr(i.atomTable + libpf.Address(vms.indexTable.segTable))
	segment := i.rm.Ptr(segTable + libpf.Address(8*(index>>16)))
	entry := i.rm.Ptr(segment + libpf.Address(8*((index>>6)&0x3FF)))

	len := i.rm.Uint16(entry + libpf.Address(vms.atom.len))

	name := make([]byte, len)
	switch i.data.otpRelease {
	case 27:
		err := i.rm.Read(i.rm.Ptr(entry+libpf.Address(vms.atom.name)), name)
		if err != nil {
			return libpf.NullString, fmt.Errorf("BEAM Unable to lookup atom with index %d: %v", index, err)
		}
	case 28, 29:
		// Implementation based on https://github.com/erlang/otp/blob/OTP-28.0.2/erts/etc/unix/etp-commands.in#L657-L674
		unboxed := i.rm.Ptr(entry+libpf.Address(vms.atom.u.bin)) & libpf.Address(i.data.etpPtrMask)

		subtag := i.rm.Uint64(unboxed) & uint64(i.data.etpHeaderSubtagMask)
		if subtag == uint64(i.data.etpHeapBitsSubtag) {
			err := i.rm.Read(unboxed+libpf.Address(vms.erlHeapBits.data), name)
			if err != nil {
				return libpf.NullString, fmt.Errorf("BEAM Unable to lookup atom with index %d (ErlHeapBits tag): %v", index, err)
			}
		} else {
			return libpf.NullString, fmt.Errorf("BEAM Unable to lookup atom with index %d: expected boxed value subtag 0x%x, found 0x%x", index, i.data.etpHeapBitsSubtag, subtag)
		}
	}

	nameString := libpf.Intern(pfunsafe.ToString(name))
	i.atomCache.Add(index, nameString)
	return nameString, nil
}

func (i *beamInstance) readErlangString(eterm libpf.Address, maxLength uint64) libpf.String {
	if value, ok := i.stringCache.Get(eterm); ok {
		return value
	}

	result := strings.Builder{}
	length := uint64(0)

	// TODO: Get this exported if possible in erl_etp.c
	// https://github.com/erlang/otp/blob/OTP-27.2.4/erts/etc/unix/etp-commands.in#L5326
	etp_nil := libpf.Address(0x3B)

	for eterm != etp_nil && length < maxLength {
		charAddr := eterm & libpf.Address(i.data.etpPtrMask)
		charValue := i.rm.Uint64(charAddr)
		char := uint8(charValue >> 4)
		result.WriteByte(char)
		length++
		nextAddr := libpf.Address((eterm & libpf.Address(i.data.etpPtrMask)) + 8)
		eterm = libpf.Address(i.rm.Uint64(nextAddr))
	}

	if length > maxLength {
		result.WriteString("...")
	}

	value := libpf.Intern(result.String())
	i.stringCache.Add(eterm, value)

	return value
}
