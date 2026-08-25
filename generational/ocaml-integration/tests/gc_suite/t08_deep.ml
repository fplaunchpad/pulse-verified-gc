(* t08_deep.ml
   Target: mark's stack depth.
   A long chain and a deep tree both force many pending objects during
   marking. The bounded mark variant has a fixed stack, so this checks the
   overflow path. *)

type tree = Leaf | Node of tree * tree * int

let rec build d i = if d = 0 then Leaf else Node (build (d-1) (2*i), build (d-1) (2*i+1), i)
let rec total t = match t with Leaf -> 0 | Node (l, r, v) -> v + total l + total r

let rec chain n acc = if n = 0 then acc else chain (n-1) (n :: acc)

let () =
  let t = build 18 1 in                 (* about 260k nodes *)
  let c = chain 400000 [] in
  for _ = 1 to 2000 do ignore (Array.make 64 0) done;
  Printf.printf "tree=%d chain=%d\n" (total t) (List.length c);
  Printf.printf "t08 ok\n"
