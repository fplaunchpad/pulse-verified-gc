(* Option A: parallel composition over top-level functions plus an explicit
   environment, so that no closure has to reach C.

   Same specification as Pulse.Lib.Par.par: two computations on separate
   resources, both finished on return.  The only differences are that each
   branch is a top-level function applied to an environment value, and that
   the pre/postconditions are indexed by that environment.

   TRUSTED: this is an assumed operation; its body is hand-written C in
   par_env.c (pthread_create + pthread_join). *)
module Spike.ParEnv
#lang-pulse
open Pulse.Lib.Pervasives
open Pulse.Lib.Send
module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module U64 = FStar.UInt64

(* The environment: one range of one array, and the value to write there.
   par_env is monomorphic in it, because F* does not extract polymorphic
   assumed operations ("polymorphic assumes are not supported"). *)
noeq
type half = {
  arr: A.array U64.t;
  lo: SZ.t;
  hi: SZ.t;
  v: U64.t;
}

assume val par_env
  (#preL #postL #preR #postR: half -> slprop)
  (ef eg: half)
  {| is_send (preL ef) |} {| is_send (postL ef) |}
  {| is_send (preR eg) |} {| is_send (postR eg) |}
  (f: (e: half -> stt unit (preL e) (fun _ -> postL e)))
  (g: (e: half -> stt unit (preR e) (fun _ -> postR e)))
  : stt_div unit (preL ef ** preR eg) (fun _ -> postL ef ** postR eg)
