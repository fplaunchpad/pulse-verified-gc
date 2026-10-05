(* Q1 probe: does Pulse.Lib.Par.par verify and extract to C?
   Two branches write disjoint boxes; no atomics involved. *)
module Spike.ParProbe
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Par
module U64 = FStar.UInt64
module B = Pulse.Lib.Box

fn write_one (r: B.box U64.t) (v: U64.t)
  requires exists* x. r |-> x
  ensures r |-> v
{
  B.(r := v)
}

fn left (a: B.box U64.t) (_: unit)
  requires a |-> 0UL
  ensures a |-> 1UL
{
  write_one a 1UL
}

fn right (b: B.box U64.t) (_: unit)
  requires b |-> 0UL
  ensures b |-> 2UL
{
  write_one b 2UL
}

divergent
fn run_par (a b: B.box U64.t)
  requires a |-> 0UL
  requires b |-> 0UL
  ensures a |-> 1UL
  ensures b |-> 2UL
{
  par #(a |-> 0UL) #(a |-> 1UL) #(b |-> 0UL) #(b |-> 2UL)
    (left a) (right b)
}
