(* t03_large.ml
   Target: the minor/major allocation boundary.
   Objects larger than max_young_wosize go straight to the major heap.
   The interesting sizes are one word either side of the threshold. *)

let max_young = 256   (* OCaml's default Max_young_wosize *)

let () =
  let sizes = [ 1; 2; 3;
                max_young - 1; max_young; max_young + 1;
                max_young * 4; max_young * 64 ] in
  let keep = List.map (fun n -> Array.make n n) sizes in

  for _ = 1 to 2000 do ignore (Array.make 30 0) done;

  List.iter2 (fun n a ->
    if Array.length a <> n || a.(0) <> n then
      failwith (Printf.sprintf "size %d corrupted" n)) sizes keep;
  Printf.printf "t03 ok\n"
