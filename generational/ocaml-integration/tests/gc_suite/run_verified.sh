#!/bin/sh
# Run the suite against the in-tree verified-GC toolchain instead of the system
# compilers. run_tests.sh defaults to `ocamlc`/`ocamlopt` from PATH, which is
# stock OCaml -- useful as a baseline, but it does not test this project.
#
# Prerequisite: both runtime flavours must be built AND propagated into stdlib/.
# `make coldstart` builds only the bytecode ones, and building in runtime/ is not
# enough on its own -- ocamlopt links stdlib/libasmrun.a, not runtime/libasmrun.a,
# so a fresh runtime/ library with a stale stdlib/ copy silently tests the old
# collector. The Makefile targets that do both are `runtime` and `runtimeopt`:
#
#   make -C ../../verified_gc
#   cd ../../ocaml-4.14-verified-gen && make runtime runtimeopt
#
# This script refuses to run if the two copies differ, because that mistake is
# invisible in the results: native tests link and pass against whatever old GC
# happens to be sitting in stdlib/.
#
# Usage: sh run_verified.sh [both|byte|native]
set -eu

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../ocaml-4.14-verified-gen" && pwd)
WRAP=$(mktemp -d)
trap 'rm -rf "$WRAP"' EXIT

for f in "$ROOT/ocamlc.opt" "$ROOT/ocamlopt.opt" "$ROOT/runtime/ocamlrun" \
         "$ROOT/runtime/libasmrun.a" "$ROOT/stdlib/libasmrun.a"; do
  [ -e "$f" ] || { echo "missing: $f" >&2; echo "see the header of this script" >&2; exit 1; }
done

# The check that matters: ocamlopt links the stdlib/ copy.
for lib in libasmrun.a libcamlrun.a; do
  if [ -e "$ROOT/stdlib/$lib" ] && \
     ! cmp -s "$ROOT/runtime/$lib" "$ROOT/stdlib/$lib"; then
    echo "stale: $ROOT/stdlib/$lib differs from runtime/$lib" >&2
    echo "native tests would link the stdlib/ copy -- an older collector." >&2
    echo "run: (cd $ROOT && make runtime runtimeopt)" >&2
    exit 1
  fi
done

# -use-runtime pins the bytecode executables to the verified ocamlrun rather
# than whatever the header would otherwise name.
cat > "$WRAP/ocamlc" <<INNER
#!/bin/sh
exec $ROOT/ocamlc.opt -nostdlib -I $ROOT/stdlib -use-runtime $ROOT/runtime/ocamlrun "\$@"
INNER
cat > "$WRAP/ocamlopt" <<INNER
#!/bin/sh
exec $ROOT/ocamlopt.opt -nostdlib -I $ROOT/stdlib "\$@"
INNER
chmod +x "$WRAP/ocamlc" "$WRAP/ocamlopt"

echo "verified GC toolchain: $ROOT"
cd "$HERE"
OCAMLC="$WRAP/ocamlc" OCAMLOPT="$WRAP/ocamlopt" sh run_tests.sh "${1:-both}"
