(* Q2 probe: what C does the library's only CAS (Pulse.Lib.Primitives.cas_box,
   on a U32 box) extract to?  Single-threaded; no invariant. *)
module Spike.CasProbe
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Primitives
module U32 = FStar.UInt32
module B = Pulse.Lib.Box

fn try_claim (r: B.box U32.t) (id: U32.t) (#i: erased U32.t)
  requires r |-> i
  returns b: bool
  ensures cond b ((r |-> id) ** pure (reveal i == 0ul)) (r |-> i)
{
  cas_box r 0ul id
}
