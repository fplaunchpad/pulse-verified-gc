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

assume val par_env
  (#ea #eb: Type0)
  (#preL #postL: ea -> slprop)
  (#preR #postR: eb -> slprop)
  (ef: ea)
  (eg: eb)
  {| is_send (preL ef) |} {| is_send (postL ef) |}
  {| is_send (preR eg) |} {| is_send (postR eg) |}
  (f: (e: ea -> stt unit (preL e) (fun _ -> postL e)))
  (g: (e: eb -> stt unit (preR e) (fun _ -> postR e)))
  : stt_div unit (preL ef ** preR eg) (fun _ -> postL ef ** postR eg)
