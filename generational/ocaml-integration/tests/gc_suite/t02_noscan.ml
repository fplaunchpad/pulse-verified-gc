(* t02_noscan.ml
   Target: no-scan blocks.
   Strings, Bytes and float arrays carry a tag at or above no_scan_tag.
   Their contents are never traced. Raw bytes can look like pointers, so
   this checks the collector does not follow them. *)

let () =
  let strs  = Array.init 400 (fun i -> String.make (i mod 97 + 1) 'x') in
  let bytes = Array.init 400 (fun i -> Bytes.make (i mod 61 + 1) '\255') in
  let flts  = Array.init 400 (fun i -> Array.make (i mod 31 + 1) 1.5) in

  (* byte patterns that resemble heap addresses *)
  Array.iter (fun b ->
    if Bytes.length b >= 8 then Bytes.set_int64_le b 0 0x0000_7f00_0000_1008L) bytes;

  for _ = 1 to 3000 do ignore (Array.make 40 0) done;

  let n = Array.fold_left (fun a s -> a + String.length s) 0 strs in
  let m = Array.fold_left (fun a b -> a + Bytes.length b) 0 bytes in
  let f = Array.fold_left (fun a x -> a +. x.(0)) 0.0 flts in
  Printf.printf "strs=%d bytes=%d floats=%.1f\n" n m f;
  Printf.printf "t02 ok\n"
