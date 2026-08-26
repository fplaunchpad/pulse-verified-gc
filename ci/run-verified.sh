#!/bin/sh
# Compile and run OCaml code on the verified GC, bytecode and native.
#
#   sh ci/run-verified.sh prog.ml               both variants
#   sh ci/run-verified.sh --byte prog.ml        one variant
#   sh ci/run-verified.sh --native prog.ml
#   sh ci/run-verified.sh tests/dir             every t*.ml there; if the
#                                               directory has expected_output.txt,
#                                               diff against it
#
# Requires ci/build-verified-toolchain.sh to have been run.
set -u

ROOT=$(cd "$(dirname "$0")/.." && pwd)
TREE=$ROOT/generational/ocaml-integration/ocaml-4.14-verified-gen

MODE=both; TARGET=
while [ $# -gt 0 ]; do
  case $1 in
    --byte|--bytecode) MODE=byte ;;
    --native)          MODE=native ;;
    -h|--help) awk 'NR>1 && /^#/ {sub(/^# ?/,""); print; next} NR>1 {exit}' "$0"; exit 0 ;;
    -*) echo "run-verified: unknown option $1" >&2; exit 2 ;;
    *)  TARGET=$1 ;;
  esac
  shift
done
[ -n "$TARGET" ] || { echo "run-verified: nothing to run (--help)" >&2; exit 2; }

for f in "$TREE/ocamlc.opt" "$TREE/ocamlopt.opt" "$TREE/runtime/ocamlrun"; do
  [ -x "$f" ] || { echo "run-verified: missing $f" >&2
                   echo "run: sh ci/build-verified-toolchain.sh" >&2; exit 1; }
done

# Two flags carry the whole thing and both fail silently if dropped:
#   -use-runtime  else the bytecode header names a stock /usr/local/bin/ocamlrun
#   -I runtime BEFORE -I stdlib  else native links stdlib's copy of
#                                libasmrun.a, which may predate your edit
BYTE="$TREE/ocamlc.opt   -nostdlib -I $TREE/stdlib -use-runtime $TREE/runtime/ocamlrun"
NAT="$TREE/ocamlopt.opt  -nostdlib -I $TREE/runtime -I $TREE/stdlib"

WORK=$(mktemp -d); trap 'rm -rf "$WORK"' EXIT
pass=0; fail=0

run_one() {
  src=$1; exp=$2
  base=$(basename "$src" .ml)
  cp "$src" "$WORK/$base.ml"
  for m in byte native; do
    [ "$MODE" = both ] || [ "$MODE" = "$m" ] || continue
    ( cd "$WORK" && if [ "$m" = byte ]
        then $BYTE -o "$base.byte" "$base.ml"
        else $NAT  -o "$base.exe"  "$base.ml"; fi ) 2>"$WORK/$base.$m.cerr"
    if [ $? -ne 0 ]; then
      printf '%-24s %-8s COMPILE FAIL\n' "$base" "$m"
      sed 's/^/    /' "$WORK/$base.$m.cerr" | head -5; fail=$((fail+1)); continue
    fi
    [ "$m" = byte ] && exe=$WORK/$base.byte || exe=$WORK/$base.exe
    "$exe" >"$WORK/$base.$m.out" 2>"$WORK/$base.$m.err"; rc=$?
    if [ $rc -ne 0 ]; then
      printf '%-24s %-8s FAIL (exit %d%s)\n' "$base" "$m" "$rc" \
        "$([ $rc -ge 128 ] && echo ", signal $((rc-128))")"
      sed 's/^/    /' "$WORK/$base.$m.err" | head -5; fail=$((fail+1)); continue
    fi
    if [ -n "$exp" ]; then
      if awk -v t="=== $base" '$0==t{f=1;next} /^=== /{f=0} f' "$exp" \
           | diff -q - "$WORK/$base.$m.out" >/dev/null 2>&1
      then printf '%-24s %-8s ok\n' "$base" "$m"; pass=$((pass+1))
      else printf '%-24s %-8s OUTPUT DIFFERS\n' "$base" "$m"
           printf '    expected: %s\n' "$(awk -v t="=== $base" '$0==t{f=1;next} /^=== /{f=0} f' "$exp" | tr '\n' ' ')"
           printf '    got:      %s\n' "$(tr '\n' ' ' <"$WORK/$base.$m.out")"
           fail=$((fail+1)); fi
    else
      printf '%-24s %-8s ok\n' "$base" "$m"; pass=$((pass+1))
      sed 's/^/    /' "$WORK/$base.$m.out"
    fi
  done
}

if [ -d "$TARGET" ]; then
  exp=""; [ -f "$TARGET/expected_output.txt" ] && exp=$(cd "$TARGET" && pwd)/expected_output.txt
  found=no
  for f in "$TARGET"/t*.ml; do [ -e "$f" ] || continue; found=yes; run_one "$f" "$exp"; done
  [ "$found" = yes ] || { echo "run-verified: no t*.ml in $TARGET" >&2; exit 2; }
  echo; echo "passed $pass, failed $fail"
else
  [ -f "$TARGET" ] || { echo "run-verified: no such file: $TARGET" >&2; exit 2; }
  run_one "$TARGET" ""
fi
[ "$fail" -eq 0 ]
