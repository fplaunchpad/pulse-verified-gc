(* t01_infix.ml
   Target: infix objects.
   Mutually recursive closures produce infix pointers. A field pointing at
   an infix object is what well_formed_heap currently forbids.
   This is the known native-compilation failure, reduced to a small case. *)

let make_pair n =
  let rec even k = if k = 0 then true else odd (k - 1)
  and odd k = if k = 0 then false else even (k - 1) in
  (* both closures escape into a tuple, so a field points at the infix *)
  (even, odd, n)

let () =
  let keep = Array.init 200 (fun i -> make_pair i) in
  (* allocate to force collections while the infix pointers are live *)
  for _ = 1 to 2000 do
    ignore (Array.make 50 0)
  done;
  let (e, o, _) = keep.(100) in
  Printf.printf "even 10 = %b, odd 10 = %b\n" (e 10) (o 10);
  Printf.printf "t01 ok\n"
