#!/bin/bash
#
# End-to-end test for itrace.py's conditional-branch detection and its
# handling of .rodata: builds a couple of tiny C fixtures, traces them under
# real gdb, and checks the resulting errors, warnings and annotations.
# Complements test_itrace_arch.py, which only tests the pure classification
# logic against synthetic instruction strings and never touches gdb.
#
# Needs gdb (or gdb-multiarch) and gcc on $PATH.

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
ITRACE="${SCRIPT_DIR}/itrace.py"

if ! command -v gdb-multiarch >/dev/null 2>&1 && ! command -v gdb >/dev/null 2>&1; then
    echo "SKIP: neither gdb-multiarch nor gdb found on \$PATH"
    exit 0
fi

# Some environments hang trying an unreachable debuginfod server; opt out
# unless the caller already set a preference.
export DEBUGINFOD_URLS="${DEBUGINFOD_URLS:-}"

TMP=$(mktemp -d)
trap 'rm -rf "${TMP}"' EXIT

cat > "${TMP}/fixture.c" << 'EOF'
#include <stdint.h>

__attribute__((noinline))
uint64_t straightline_add(uint64_t a, uint64_t b) {
    return a + b;
}

__attribute__((noinline))
uint64_t never_called(uint64_t a) {
    return a * 2;
}

__attribute__((noinline))
uint64_t branchy_max(uint64_t a, uint64_t b) {
    if (a > b) {
        return a;
    }
    return b;
}

const uint64_t table[2] = { 0x1122334455667788ULL, 0xdeadbeefULL };

// the table is reached through a pointer, so that the compiler cannot fold
// the loads away and they stay in the trace
__attribute__((noinline))
uint64_t rodata_sum(uint64_t a, const uint64_t *t) {
    return a + t[0] + t[1];
}

int main(void) {
    volatile uint64_t r1 = straightline_add(3, 4);
    volatile uint64_t r2 = branchy_max(3, 4);
    volatile uint64_t r3 = rodata_sum(1, table);
    return (int)(r1 + r2 + r3);
}
EOF

if ! gcc -O0 -o "${TMP}/fixture" "${TMP}/fixture.c"; then
    echo "FAIL: could not build test fixture"
    exit 1
fi

num_ok=0
num_failed=0
failed=()

# report NAME OK_FLAG [log-file-to-dump-on-failure]
report() {
    local name="$1" ok="$2" logfile="${3:-}"
    if [[ "${ok}" == "1" ]]; then
        echo "  ${name} ... [OK]"
        num_ok=$((num_ok+1))
    else
        echo "  ${name} ... [FAIL]"
        num_failed=$((num_failed+1))
        failed+=("${name}")
        if [[ -n "${logfile}" && -f "${logfile}" ]]; then
            sed 's/^/    /' "${logfile}"
        fi
    fi
}

echo "straightline_add (no branches)"
python3 "${ITRACE}" "${TMP}/fixture" straightline_add "${TMP}/straight.trace" \
    >"${TMP}/straight.log" 2>&1
exit_code=$?
ok=1
[[ "${exit_code}" == "0" ]] || ok=0
grep -q "ERROR:\|WARNING:" "${TMP}/straight.log" && ok=0
grep -q "#ret" "${TMP}/straight.trace" 2>/dev/null || ok=0
report "exits 0, no error/warning, trace completes" "${ok}" "${TMP}/straight.log"

echo "branchy_max, default flags"
python3 "${ITRACE}" "${TMP}/fixture" branchy_max "${TMP}/branchy_default.trace" \
    >"${TMP}/branchy_default.log" 2>&1
exit_code=$?
ok=1
[[ "${exit_code}" == "1" ]] || ok=0
grep -q "ERROR: conditional branch" "${TMP}/branchy_default.log" || ok=0
grep -q "#ret" "${TMP}/branchy_default.trace" 2>/dev/null && ok=0
report "exits 1, errors on the conditional branch, trace does not complete" "${ok}" "${TMP}/branchy_default.log"

echo "branchy_max, --warn-conditional-branches"
python3 "${ITRACE}" "${TMP}/fixture" branchy_max "${TMP}/branchy_warn.trace" \
    --warn-conditional-branches >"${TMP}/branchy_warn.log" 2>&1
exit_code=$?
ok=1
[[ "${exit_code}" == "0" ]] || ok=0
grep -q "WARNING: conditional branch" "${TMP}/branchy_warn.log" || ok=0
grep -q "#ret" "${TMP}/branchy_warn.trace" 2>/dev/null || ok=0
report "exits 0, warns on the conditional branch, trace completes" "${ok}" "${TMP}/branchy_warn.log"

echo "rodata_sum, default flags"
python3 "${ITRACE}" "${TMP}/fixture" rodata_sum "${TMP}/rodata.trace" \
    >"${TMP}/rodata.log" 2>&1
exit_code=$?
ok=1
[[ "${exit_code}" == "0" ]] || ok=0
grep -q "WARNING: moving values read from .rodata" "${TMP}/rodata.log" || ok=0
grep -q "Segment = .rodata" "${TMP}/rodata.trace" 2>/dev/null || ok=0
# the values of both table entries are moved into the trace, along with the
# rule that translates such a move
grep -q "^#! rodata_mov64 " "${TMP}/rodata.trace" 2>/dev/null || ok=0
grep -q "rodata_mov64 0x1122334455667788," "${TMP}/rodata.trace" 2>/dev/null || ok=0
grep -q "rodata_mov64 0x00000000deadbeef," "${TMP}/rodata.trace" 2>/dev/null || ok=0
report "moves the .rodata values into the trace and warns about it" "${ok}" "${TMP}/rodata.log"

echo "rodata_sum, --no-rodata-values"
python3 "${ITRACE}" "${TMP}/fixture" rodata_sum "${TMP}/rodata_off.trace" \
    --no-rodata-values >"${TMP}/rodata_off.log" 2>&1
exit_code=$?
ok=1
[[ "${exit_code}" == "0" ]] || ok=0
grep -q "WARNING:" "${TMP}/rodata_off.log" && ok=0
grep -q "rodata_mov" "${TMP}/rodata_off.trace" 2>/dev/null && ok=0
grep -q "Segment = .rodata" "${TMP}/rodata_off.trace" 2>/dev/null || ok=0
report "leaves the .rodata values alone, still annotating the segment" "${ok}" "${TMP}/rodata_off.log"

echo "never_called (breakpoint never hit)"
python3 "${ITRACE}" "${TMP}/fixture" never_called "${TMP}/uncalled.trace" \
    >"${TMP}/uncalled.log" 2>&1
exit_code=$?
ok=1
[[ "${exit_code}" == "1" ]] || ok=0
grep -q "was never reached" "${TMP}/uncalled.log" || ok=0
report "exits 1 with a clear error instead of a gdb exception" "${ok}" "${TMP}/uncalled.log"

echo
echo "----- Summary -----"
echo "# of OK:     ${num_ok}"
echo "# of Fail:   ${num_failed}"
if [[ ${num_failed} -gt 0 ]]; then
    echo "----- Failed -----"
    for f in "${failed[@]}"; do
        echo "* ${f}"
    done
    exit 1
fi
