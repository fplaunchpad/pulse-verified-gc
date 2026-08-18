(* Targeted reproducer for the No_scan_tag scanning bug.

   A boxed Int64 is a Custom_tag block: header | &caml_int64_ops | payload.
   The payload word is raw data.  If the minor BFS scans it as a value field
   (no No_scan_tag guard), a payload that is 8-aligned and inside
   [8, minor_heap_size) is accepted as a nursery offset and enqueued as an
   "object".  Reading its header then lands on &caml_int64_ops, which decodes
   as tag 224 / wosize 4411, and the scanner over-scans ~35 KB.

   So: allocate many such Int64s, keep them live across minor collections so
   they get promoted and enqueued, and churn. *)

let minor_bytes = 2 * 1024 * 1024

let () =
  let live = Array.make 4096 0L in
  let junk = ref [] in
  let n = try int_of_string Sys.argv.(1) with _ -> 300_000 in
  for i = 1 to n do
    (* 8-aligned, in [8, minor_bytes) -- exactly the danger window *)
    let payload = Int64.of_int (8 + ((i * 8) mod (minor_bytes - 16))) in
    live.(i mod 4096) <- payload;
    (* keep a boxed copy reachable so the Custom block itself is promoted *)
    junk := ref payload :: !junk;
    if i mod 512 = 0 then junk := [];
    (* extra allocation to drive minor collections *)
    if i mod 64 = 0 then ignore (Array.make 8 i)
  done;
  (* touch the array so nothing is optimised away *)
  let s = Array.fold_left (fun a x -> Int64.add a x) 0L live in
  Printf.printf "ok checksum=%Ld\n" s
