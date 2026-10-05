open Bigarray

external fill_halves : (int64, int64_elt, c_layout) Array1.t -> unit = "spike_fill_halves"
external thread_probe_fill : (int64, int64_elt, c_layout) Array1.t -> bool = "spike_thread_probe_fill"

let check a n =
  for i = 0 to n - 1 do
    let want = if i < n / 2 then 1L else 2L in
    if Array1.get a i <> want then (Printf.printf "FAIL at %d\n" i; exit 1)
  done

let () =
  let n = 1_000_001 in
  let a = Array1.create int64 c_layout n in
  Array1.fill a 0L;
  fill_halves a;
  check a n;
  Array1.fill a 0L;
  if not (thread_probe_fill a) then (print_endline "FAIL: one thread"; exit 1);
  check a n;
  let backend = match Sys.backend_type with
    | Native -> "native" | Bytecode -> "bytecode" | Other s -> s in
  Printf.printf "ok: OCaml %s %s, %d elements, two threads\n" Sys.ocaml_version backend n
