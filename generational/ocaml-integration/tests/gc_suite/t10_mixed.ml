(* t10_mixed.ml
   Target: everything at once, over a long run.
   Individual tests isolate features. This one runs them together for
   long enough that many collections of both kinds occur. Failures here
   that do not appear in the isolated tests point at interactions. *)

type mut = { mutable a : int array; mutable s : string; mutable n : mut option }

let () =
  let rec even k = if k = 0 then true else odd (k - 1)
  and odd k = if k = 0 then false else even (k - 1) in

  let closures = Array.init 500 (fun _ -> (even, odd)) in
  let recs = Array.init 2000 (fun _ -> { a = [||]; s = ""; n = None }) in
  let big  = Array.init 50 (fun i -> Array.make 2000 i) in

  for round = 1 to 100 do
    for i = 0 to 1999 do
      recs.(i).a <- Array.make (1 + i mod 5) (round + i);
      recs.(i).s <- String.make (1 + i mod 20) 'a';
      if i > 0 then recs.(i).n <- Some recs.(i-1)
    done;
    for _ = 1 to 500 do ignore (Array.make 32 0) done
  done;

  let (e, _) = closures.(0) in
  let s1 = Array.fold_left (fun x r -> x + r.a.(0) + String.length r.s) 0 recs in
  let s2 = Array.fold_left (fun x b -> x + b.(0)) 0 big in
  Printf.printf "even 100 = %b s1=%d s2=%d\n" (e 100) s1 s2;
  Printf.printf "t10 ok\n"
