#!/usr/bin/env bash
# Spike 3: run test-suite programs on a probe runtime ($1, default the plain
# build) and on the unprobed verified runtime, and check for each one:
#   - both exit 0, with the same stdout once heap addresses are masked (ASLR),
#   - at least one probed collection, and the probe's summary line,
#   - no ThreadSanitizer report.
# Programs are the .byte files `make test` builds in ocaml-integration/tests.
set -u
HERE=$(pwd)
R=$(cd "$(dirname "${1:-_build/sweep/ocamlrun}")" && pwd)/$(basename "${1:-_build/sweep/ocamlrun}")
T=$HERE/../../generational/ocaml-integration/tests
V=$T/../ocaml-4.14-verified-gen/runtime/ocamlrun
O=$HERE/_build/sweep/runs/$(basename "$R")
mkdir -p "$O"
mask() { sed -E 's/[0-9a-f]{9,}/ADDR/g' "$1"; }
fail=0
# program  major-heap-words  args
while read -r p w a; do
  cd "$T"
  MIN_EXPANSION_WORDSIZE=$w "$V" $p.byte $a >"$O/$p.ref" 2>/dev/null; rv=$?
  MIN_EXPANSION_WORDSIZE=$w "$R" $p.byte $a >"$O/$p.out" 2>"$O/$p.err"; rr=$?
  cd "$HERE"
  n=$(grep -c '^sweep-probe #' "$O/$p.err")
  same=$( [ "$(mask "$O/$p.out")" = "$(mask "$O/$p.ref")" ] && echo same || echo DIFF)
  tsan=$(grep -c 'ThreadSanitizer' "$O/$p.err")
  summ=$(grep -c 'collections checked, all matched' "$O/$p.err")
  echo "$p: rc $rv/$rr, stdout $same, probed collections $n, tsan reports $tsan"
  if [ $rv -ne 0 ] || [ $rr -ne 0 ] || [ $same != same ] || [ $n -eq 0 ] || [ $summ -ne 1 ] || [ $tsan -ne 0 ]; then
    fail=1
  fi
done <<'EOF'
infix_closures 300000
no_scan 4000000
make_vect_barrier 4000000
fasta 300000 100000
count_change 2000000 100
EOF
[ $fail -eq 0 ] && echo "ok: all programs" || { echo FAIL; exit 1; }
