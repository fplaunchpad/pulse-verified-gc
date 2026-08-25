#!/bin/sh
# Run the suite against the in-tree verified-GC toolchain instead of the system
# compilers. run_tests.sh defaults to `ocamlc`/`ocamlopt` from PATH, which is
# stock OCaml -- useful as a baseline, but it does not test this project.
#
# Prerequisite: both runtime flavours must be built. `make coldstart` builds only
# the bytecode ones, so native needs `allopt` explicitly:
#
#   make -C ../../verified_gc
#   make -C ../../ocaml-4.14-verified-gen/runtime all allopt
#
# Usage: sh run_verified.sh [both|byte|native]
set -eu

HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../../ocaml-4.14-verified-gen" && pwd)
WRAP=$(mktemp -d)
trap 'rm -rf "$WRAP"' EXIT

for f in "$ROOT/ocamlc.opt" "$ROOT/ocamlopt.opt" "$ROOT/runtime/ocamlrun" \
         "$ROOT/runtime/libasmrun.a"; do
  [ -e "$f" ] || { echo "missing: $f" >&2; echo "see the header of this script" >&2; exit 1; }
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
