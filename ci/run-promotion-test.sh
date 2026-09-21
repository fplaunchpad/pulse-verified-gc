#!/bin/sh
# Run the promotion-path allocator test (issue #19) against the verified GC.
#
#   sh ci/run-promotion-test.sh [heap-words] [fill-fraction]
#
# Defaults to a 32 MB major heap at 60% fill, which is where the effect is
# large and fast. It reproduces at the 256 MB default too, just slower.
#
# Requires the verified tree's bytecode compiler, because the test calls
# caml_trigger_verified_gc -- a primitive that exists only in this runtime.
# Build it with: sh ci/build-verified-toolchain.sh --full
set -eu

ROOT=$(cd "$(dirname "$0")/.." && pwd)
TREE=$ROOT/generational/ocaml-integration/ocaml-4.14-verified-gen
SRC=$ROOT/ci/promotion-exactness/promotion_exactness.ml
WORDS=${1:-4194304}
FILL=${2:-0.60}
OUT=${TMPDIR:-/tmp}/promotion-exactness.$$

[ -x "$TREE/ocamlc.opt" ] || {
  echo "the tree's compilers are missing -- run: sh ci/build-verified-toolchain.sh --full" >&2
  exit 2; }

mkdir -p "$OUT"
cp "$SRC" "$OUT/t.ml"
( cd "$OUT" && "$TREE/ocamlc.opt" -use-runtime "$TREE/runtime/ocamlrun" \
    -nostdlib -I "$TREE/stdlib" -o t.byte t.ml >/dev/null )

set +e
( cd "$OUT" && MIN_EXPANSION_WORDSIZE="$WORDS" "$TREE/runtime/ocamlrun" ./t.byte "$WORDS" "$FILL" )
rc=$?
set -e
rm -rf "$OUT"

case $rc in
  0) echo "PASS: the allocator is size-exact on the promotion path." ;;
  1) echo "FAIL: promoted objects declare fields they do not own (issue #19)." ;;
  *) echo "harness problem, exit $rc" ;;
esac
exit $rc
