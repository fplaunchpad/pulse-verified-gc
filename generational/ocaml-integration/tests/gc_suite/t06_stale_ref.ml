(* t06_stale_ref.ml
   Target: ref table entries whose target dies before the collection.
   A major object is made to point at a fresh minor object, then that slot
   is overwritten before any minor collection runs. The ref table still
   holds the first entry. It now points at something unreachable.
   The specification cannot see this, since it rescans the major heap. *)

type box = { mutable v : int array }

let () =
  let boxes = Array.init 3000 (fun _ -> { v = [||] }) in
  for _ = 1 to 3000 do ignore (Array.make 64 0) done;   (* promote boxes *)

  for round = 1 to 40 do
    (* write a fresh minor object, then immediately overwrite it *)
    for i = 0 to 2999 do
      boxes.(i).v <- Array.make 2 (round * i);
      boxes.(i).v <- Array.make 2 (round * i + 1)
    done;
    (* now force a minor collection *)
    for _ = 1 to 400 do ignore (Array.make 32 0) done
  done;

  let s = Array.fold_left (fun a b -> a + b.v.(0)) 0 boxes in
  Printf.printf "sum=%d\n" s;
  Printf.printf "t06 ok\n"
