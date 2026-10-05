(* Two threads each fill their own half of one array; the postcondition
   states the whole array afterwards.  The shape a parallel sweep needs:
   disjoint ranges of one array, no atomics, joined at the end. *)
module Spike.FillHalves
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsToRange
open Spike.ParEnv
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U64 = FStar.UInt64
module Seq = FStar.Seq

noextract
let len (lo hi: SZ.t) : nat =
  if SZ.v lo <= SZ.v hi then SZ.v hi - SZ.v lo else 0

let half_pre (e: half) : slprop =
  exists* s. pts_to_range e.arr (SZ.v e.lo) (SZ.v e.hi) s

let half_post (e: half) : slprop =
  pts_to_range e.arr (SZ.v e.lo) (SZ.v e.hi) (Seq.create (len e.lo e.hi) e.v)

instance is_send_half_pre (e: half) : is_send (half_pre e) =
  Tactics.Typeclasses.solve

instance is_send_half_post (e: half) : is_send (half_post e) =
  Tactics.Typeclasses.solve

fn fill_range (a: A.array U64.t) (lo hi: SZ.t) (v: U64.t)
  (#s0: erased (Seq.seq U64.t))
  requires pts_to_range a (SZ.v lo) (SZ.v hi) s0
  ensures pts_to_range a (SZ.v lo) (SZ.v hi) (Seq.create (len lo hi) v)
{
  pts_to_range_prop a;
  let mut i = lo;
  while (SZ.lt !i hi)
    invariant exists* vi s.
      pts_to i vi **
      pts_to_range a (SZ.v lo) (SZ.v hi) s **
      pure (SZ.v lo <= SZ.v vi /\ SZ.v vi <= SZ.v hi /\
            Seq.length s == SZ.v hi - SZ.v lo /\
            (forall (k: nat). k < SZ.v vi - SZ.v lo ==> Seq.index s k == v))
    decreases (Prims.op_Subtraction (SZ.v hi) (SZ.v !i))
  {
    let vi = !i;
    pts_to_range_upd a vi v;
    i := SZ.add vi 1sz;
  };
  with s. assert (pts_to_range a (SZ.v lo) (SZ.v hi) s);
  assert (pure (Seq.equal s (Seq.create (len lo hi) v)));
  rewrite (pts_to_range a (SZ.v lo) (SZ.v hi) s)
       as (pts_to_range a (SZ.v lo) (SZ.v hi) (Seq.create (len lo hi) v));
}

(* One branch: a top-level function of its environment. *)
fn fill_half (e: half)
  requires half_pre e
  ensures half_post e
{
  unfold half_pre e;
  fill_range e.arr e.lo e.hi e.v;
  fold half_post e;
}

noextract
let expected (n: nat) : Seq.seq U64.t =
  Seq.append (Seq.create (n / 2) 1UL) (Seq.create (n - n / 2) 2UL)

(* Entry point: the left half becomes 1, the right half 2, in parallel. *)
divergent
fn fill_halves (a: A.array U64.t) (n: SZ.t)
  (#s: erased (Seq.seq U64.t))
  requires A.pts_to a s ** pure (Seq.length s == SZ.v n)
  ensures A.pts_to a (expected (SZ.v n))
{
  A.pts_to_len a;
  let mid = SZ.div n 2sz;
  pts_to_range_intro a 1.0R s;
  pts_to_range_split a 0 (SZ.v mid) (SZ.v n);
  let el = { arr = a; lo = 0sz; hi = mid; v = 1UL };
  let er = { arr = a; lo = mid; hi = n; v = 2UL };
  with sl. assert (pts_to_range a 0 (SZ.v mid) sl);
  with sr. assert (pts_to_range a (SZ.v mid) (SZ.v n) sr);
  rewrite (pts_to_range a 0 (SZ.v mid) sl)
       as (pts_to_range el.arr (SZ.v el.lo) (SZ.v el.hi) sl);
  rewrite (pts_to_range a (SZ.v mid) (SZ.v n) sr)
       as (pts_to_range er.arr (SZ.v er.lo) (SZ.v er.hi) sr);
  fold (half_pre el);
  fold (half_pre er);
  par_env #half_pre #half_post #half_pre #half_post el er fill_half fill_half;
  unfold (half_post el);
  unfold (half_post er);
  rewrite (pts_to_range el.arr (SZ.v el.lo) (SZ.v el.hi) (Seq.create (len el.lo el.hi) el.v))
       as (pts_to_range a 0 (SZ.v mid) (Seq.create (SZ.v n / 2) 1UL));
  rewrite (pts_to_range er.arr (SZ.v er.lo) (SZ.v er.hi) (Seq.create (len er.lo er.hi) er.v))
       as (pts_to_range a (SZ.v mid) (SZ.v n) (Seq.create (SZ.v n - SZ.v n / 2) 2UL));
  pts_to_range_join a 0 (SZ.v mid) (SZ.v n);
  pts_to_range_elim a 1.0R (expected (SZ.v n));
}
