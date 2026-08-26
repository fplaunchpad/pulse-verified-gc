#!/bin/sh
# Build what you need to test against the verified GC.
#
#   sh ci/build-verified-toolchain.sh            runtimes only  (minutes)
#   sh ci/build-verified-toolchain.sh --full     + world.opt     (15-40 min)
#
# The default is enough for ci/run-verified.sh, because that swaps the *runtime*
# and compiles with the stock compiler:
#   - bytecode carries no collector; the collector is whichever ocamlrun runs it
#   - native links the collector out of the verified GC's libasmrun.a via -I
#
# --full additionally runs `make world.opt` + `make ocamltest`, which rebuilds
# the whole toolchain ON the verified collector. That is required only by
# ci/run-testsuite.sh, which exercises the compiler itself. It is also the
# strongest single check in the repository: a collector broken enough to matter
# cannot finish a bootstrap -- the infix bug surfaced exactly that way, with
# `make coldstart` dying on camlinternalFormat.ml.
#
# Rerun after any change to the F* source, the snapshot, or a hand patch.
set -eu

ROOT=$(cd "$(dirname "$0")/.." && pwd)
INT=$ROOT/generational/ocaml-integration
TREE=$INT/ocaml-4.14-verified-gen
LOG=$ROOT/build-verified-toolchain.log

FULL=no
[ "${1:-}" = "--full" ] && FULL=yes
[ "${1:-}" = "--help" ] && { awk 'NR>1 && /^#/ {sub(/^# ?/,""); print; next} NR>1 {exit}' "$0"; exit 0; }

say() { printf '\n=== %s\n' "$1"; }

say "the snapshot must still carry its hand patches"
# `make snapshot` overwrites the extracted C with a plain cp, so a regeneration
# can silently drop them. Same guard CI runs first, for the same reason.
make -C "$ROOT/generational" verify-snapshot-patches

say "OCaml trees (stock, installed + verified, patched)"
if [ ! -x "$INT/ocaml-4.14-unchanged/_install/bin/ocamlc" ] || [ ! -d "$TREE" ]; then
  make -C "$INT" setup
else
  echo "already present"
fi

say "the verified GC"
make -C "$INT/verified_gc"

say "the verified runtimes (bytecode ocamlrun + native libasmrun.a)"
make -C "$TREE/runtime" ocamlrun libasmrun.a

if [ "$FULL" = no ]; then
  cat <<EOF

Ready. Run your own code:

  sh ci/run-verified.sh prog.ml
  sh ci/run-verified.sh some/dir

For OCaml's own testsuite you also need the compiler rebuilt on the verified
collector -- rerun with --full, then use ci/run-testsuite.sh.
EOF
  exit 0
fi

say "world.opt -- the whole toolchain, on the verified GC"
echo "logging to $LOG"
cd "$TREE"
set -o pipefail 2>/dev/null || true
if ! make world.opt 2>&1 | tee "$LOG"; then
  echo
  echo "world.opt FAILED -- which is itself the interesting result. What was"
  echo "being compiled, and what the runtime said:"
  echo
  grep -nE 'Segmentation|Fatal error|Aborted|out of memory|internal error' "$LOG" | tail -20 || true
  grep -E 'ocamlc|ocamlopt|ocamlrun' "$LOG" | tail -5 || true
  exit 1
fi

say "ocamltest"
make ocamltest 2>&1 | tee -a "$LOG" >/dev/null

cat <<EOF

Ready, including the testsuite:

  sh ci/run-verified.sh prog.ml
  sh ci/run-testsuite.sh
EOF
