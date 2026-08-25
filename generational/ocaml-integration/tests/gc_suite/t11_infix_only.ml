(* t11_infix_only.ml
   Target: infix objects, reachable ONLY through an infix pointer.

   Added after t01_infix was found not to exercise this path. Two differences
   matter, and both are needed:

   1. Only the *second* function of the recursive group escapes. t01 keeps both
      `even` and `odd`, so the enclosing Closure_tag block stays reachable
      through its own start address and gets darkened correctly regardless.
   2. Enough allocation churn to force a major collection while those pointers
      are live. t01's workload triggers zero collections of either kind, so the
      collector never runs at all.

   Validated by A/B: with `resolve_object` in the generated C neutered to
   `return obj`, this test segfaults in bytecode. t01 passes either way. *)

let make_odd n =
  (* `n` is captured so the group must be heap-allocated: a recursive group with
     no free variables can be emitted as a static closure, which never involves
     the GC. *)
  let rec even k = if k = 0 then n >= 0 else odd (k - 1)
  and odd k = if k = 0 then n < 0 else even (k - 1) in
  odd

let () =
  let keep = Array.init 2000 (fun i -> make_odd i) in
  for _ = 1 to 120_000 do ignore (Array.make 200 0) done;
  let acc = ref 0 in
  Array.iteri (fun i f -> if f ((i mod 10) * 2 + 1) then incr acc) keep;
  Printf.printf "reachable-only-via-infix = %d\n" !acc;
  Printf.printf "t11 ok\n"
