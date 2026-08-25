(* t04_promotion.ml
   Target: promotion during minor collection.
   Two phases. In the first every other object stays live, so each minor
   collection has survivors to copy. In the second all objects die, so
   each collection has none. *)

let () =
  (* phase one: half survive *)
  let keep = Array.make 5000 [||] in
  for i = 0 to 49999 do
    let a = Array.make 8 i in
    if i mod 10 = 0 && i / 10 < 5000 then keep.(i / 10) <- a
  done;
  let sum = Array.fold_left (fun acc a ->
    if Array.length a = 0 then acc else acc + a.(0)) 0 keep in

  (* phase two: none survive *)
  for i = 0 to 199999 do
    ignore (Array.make 8 i)
  done;

  Printf.printf "kept sum = %d\n" sum;
  Printf.printf "t04 ok\n"
