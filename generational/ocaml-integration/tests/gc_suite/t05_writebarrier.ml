(* t05_writebarrier.ml
   Target: the write barrier and the ref table.
   The C bridge relies on caml_ref_table, populated by caml_modify. The
   specification instead scans the whole major heap. So the code can miss
   a root that the proof would find.
   This drives stores through several distinct paths. *)

type mut = { mutable f : int array; mutable g : string; mutable h : mut option }

let major_array n = Array.make n [||]      (* large: allocated in major heap *)

let () =
  (* a major-heap array of major-heap records *)
  let big = major_array 4000 in
  let recs = Array.init 4000 (fun _ -> { f = [||]; g = ""; h = None }) in

  (* force everything above into the major heap *)
  for _ = 1 to 3000 do ignore (Array.make 64 0) done;

  (* path one: Array.set into a major array, value freshly minor-allocated *)
  for i = 0 to 3999 do
    big.(i) <- Array.make 3 i
  done;

  (* path two: mutable record field, int array *)
  for i = 0 to 3999 do
    recs.(i).f <- Array.make 2 i
  done;

  (* path three: mutable record field, string *)
  for i = 0 to 3999 do
    recs.(i).g <- string_of_int i
  done;

  (* path four: mutable field holding a record, forming major to minor links *)
  for i = 0 to 3998 do
    recs.(i).h <- Some { f = Array.make 1 i; g = ""; h = None }
  done;

  (* force minor collections while all those links are live *)
  for _ = 1 to 5000 do ignore (Array.make 16 0) done;

  let s1 = Array.fold_left (fun a x -> a + (if Array.length x = 0 then 0 else x.(0))) 0 big in
  let s2 = Array.fold_left (fun a r -> a + (if Array.length r.f = 0 then 0 else r.f.(0))) 0 recs in
  let s3 = Array.fold_left (fun a r -> a + String.length r.g) 0 recs in
  let s4 = Array.fold_left (fun a r ->
             a + (match r.h with None -> 0 | Some x -> x.f.(0))) 0 recs in
  Printf.printf "s1=%d s2=%d s3=%d s4=%d\n" s1 s2 s3 s4;
  Printf.printf "t05 ok\n"
