// Copyright The OpenTelemetry Authors
// SPDX-License-Identifier: Apache-2.0

package beam

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"testing"

	"github.com/stretchr/testify/require"

	"go.opentelemetry.io/ebpf-profiler/interpreter"
	"go.opentelemetry.io/ebpf-profiler/libpf/pfelf"
)

func TestLoaderSymbolVisibility(t *testing.T) {
	for _, release := range []int{27, 28, 29, 30} {
		t.Run(fmt.Sprint(release), func(t *testing.T) {
			dir := t.TempDir()
			source := fmt.Sprintf(`
static char r[96] __attribute__((used));
int the_active_code_index;
char erts_atom_table[128];
void *beam_normal_exit;
int erts_frame_layout;
const char etp_otp_release[] = "%d";
const char etp_erts_version[] = "test";
const unsigned long etp_ptr_mask = ~3UL;
const unsigned long etp_header_subtag_mask = 63;
const unsigned long etp_heap_bits_subtag = 36;
int main(void) { return 0; }
`, release)
			require.NoError(t, os.WriteFile(filepath.Join(dir, "runtime.c"), []byte(source), 0600))
			visibility := "-fvisibility=default"
			if release >= 29 {
				visibility = "-fvisibility=hidden"
			}
			cmd := exec.Command("cc", "-fPIE", "-pie", "-rdynamic", visibility, "runtime.c", "-o", "beam.smp")
			cmd.Dir = dir
			output, err := cmd.CombinedOutput()
			require.NoError(t, err, "%s", output)

			if release == 27 {
				// A partially stripped runtime can retain r in .symtab and
				// expose the other globals through .dynsym alone.
				cmd = exec.Command("strip", "--strip-all", "--keep-symbol=r", "beam.smp")
				cmd.Dir = dir
				output, err = cmd.CombinedOutput()
				require.NoError(t, err, "%s", output)
			}

			ref := pfelf.NewReferenceWithOpenFunc("beam.smp", nil, func() (*pfelf.File, error) {
				return pfelf.Open(filepath.Join(dir, "beam.smp"))
			})
			defer ref.Close()
			data, err := loader(nil, interpreter.NewLoaderInfo(0, ref))
			if release == 30 {
				require.ErrorContains(t, err, "unsupported OTP version")
				return
			}
			require.NoError(t, err)
			d := data.(*beamData)
			require.EqualValues(t, release, d.otpRelease)
			require.Equal(t, "test", d.ertsVersion)
			require.Equal(t, ^uint64(3), d.etpPtrMask)
			require.EqualValues(t, 63, d.etpHeaderSubtagMask)
			require.EqualValues(t, 36, d.etpHeapBitsSubtag)
			require.NotZero(t, d.ertsFrameLayout)
		})
	}
}
