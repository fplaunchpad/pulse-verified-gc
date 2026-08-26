#!/bin/sh
# Build a complete OCaml 4.14 toolchain running on the verified GC.
#
# This is the local equivalent of the "Build the compiler on the verified GC"
# step in .github/workflows/testsuite.yml, and it is what makes everything
# afterwards reproducible: once `make world.opt` has run, the tree's own
# ocamlc/ocamlopt are themselves built and running on the verified collector, so
# testing anything is just "use these compilers". No wrapper scripts, no flag
# ordering to get right, no second copy of a runtime archive to go stale.
#
#   sh ci/build-verified-toolchain.sh            # build it
#   sh ci/build-verified-toolchain.sh --clean    # from scratch (slow)
#
# Roughly 15-40 minutes the first time. Afterwards it is incremental.
set -eu

ROOT=$(cd "$(dirname "$0")/.." && pwd)
TREE=$ROOT/generational/ocaml-integration/ocaml-4.14-verified-gen
LOG=$ROOT/build-verified-toolchain.log

[ "${1:-}" = "--clean" ] && CLEAN=yes || CLEAN=no

say() { printf '\n=== %s\n' "$1"; }

say "1/5  the snapshot must still carry its hand patches"
# make snapshot overwrites the extracted C with a plain cp, so a regeneration
# can silently drop them. Same guard CI runs first, and for the same reason.
make -C "$ROOT/generational" verify-snapshot-patches

say "2/5  OCaml trees present?"
if [ ! -d "$TREE" ]; then
  echo "cloning and patching (stock + verified) ..."
  make -C "$ROOT/generational/ocaml-integration" setup
else
  echo "$TREE already exists"
fi

say "3/5  the verified GC itself"
make -C "$ROOT/generational/ocaml-integration/verified_gc"

say "4/5  world.opt -- the whole toolchain, on the verified GC"
echo "logging to $LOG"
cd "$TREE"
[ "$CLEAN" = yes ] && make clean >/dev/null 2>&1 || true
set -o pipefail 2>/dev/null || true
if ! make world.opt 2>&1 | tee "$LOG"; then
  echo
  echo "world.opt FAILED. This is the interesting failure mode: a collector"
  echo "broken enough to matter cannot finish a bootstrap. What was being"
  echo "compiled, and what the runtime said:"
  echo
  grep -nE 'Segmentation|Fatal error|Aborted|out of memory|internal error' "$LOG" | tail -20 || true
  grep -E 'ocamlc|ocamlopt|ocamlrun' "$LOG" | tail -5 || true
  exit 1
fi

say "5/5  ocamltest (needed by the testsuite)"
make ocamltest 2>&1 | tee -a "$LOG" >/dev/null

cat <<EOF

Done. The toolchain in
  $TREE
is built on the verified GC. Use it directly:

  sh ci/run-verified.sh prog.ml        compile and run, bytecode and native
  sh ci/run-testsuite.sh               OCaml's own testsuite, both variants

EOF
