(* t07_fragmentation.ml
   Target: free list search and coalescing.
   Allocate many major blocks, drop alternate ones, then ask for a block
   larger than any single hole. That forces adjacent free blocks to be
   merged before the request can be satisfied. *)

let () =
  let n = 4000 in
  let keep = Array.make n [||] in
  for i = 0 to n - 1 do
    keep.(i) <- Array.make 300 i        (* large enough for the major heap *)
  done;

  (* drop alternate blocks *)
  for i = 0 to n - 1 do
    if i mod 2 = 0 then keep.(i) <- [||]
  done;
  (* Force collections through allocation rather than Gc.compact, which the
     verified GC does not implement. Enough churn to trigger several major
     collections, so the dropped blocks are swept and coalesced. *)
  for _ = 1 to 20000 do
    ignore (Array.make 100 0)
  done;

  (* now request blocks bigger than any single hole *)
  let big = Array.init 20 (fun i -> Array.make 5000 i) in

  let s1 = Array.fold_left (fun a x -> a + Array.length x) 0 keep in
  let s2 = Array.fold_left (fun a x -> a + x.(0)) 0 big in
  Printf.printf "s1=%d s2=%d\n" s1 s2;
  Printf.printf "t07 ok\n"
