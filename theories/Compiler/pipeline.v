Require Export L1g.toplevel L2k.toplevel L4.toplevel L6.toplevel L7.toplevel.
Require Import compcert.lib.Maps.
Require Import ZArith.
Require Import Common.Common Common.compM Common.Pipeline_utils.
Require Import String.
Require Import maps_util.
Require Import Glue.glue.
Require Import Glue.ffi.
Require Import ExtLib.Structures.Monad.

Import Monads.
Import MonadNotation.

(** * CertiCoq's Compilation Pipeline *)
Definition CertiCoq_pipeline (p : global_context * term) :=
  o <- get_options ;;
  p <- compile_L1g p ;;
  p <- compile_L2k p ;;
  p <- compile_L2k_eta p ;;
  p <- compile_L4 p ;;
  p <- (if direct o then compile_L6_ANF p else compile_L6_CPS p) ;; 
  compile_L6 p.

(** * The main CertiCoq pipeline, with MetaCoq's erasure and C-code generation *)
Definition pipeline (p : Template.Ast.program) :=
  p <- erase_PCUIC p ;; 
  p <- CertiCoq_pipeline p ;;
  compile_Clight p.

(** * After-erasure pipeline -- could be useful for using CertiCoq with custom erasure functions *)
Definition lbox_pipeline (p : global_context * term) :=
  p <- CertiCoq_pipeline p ;;
  compile_Clight p.


Definition default_opts : Options :=
  {| direct := false;
     c_args := 5;
     fv_args := 5;
     show_anf := false;
     o_level := 0;
     time := false;
     debug := false;
     dev := 0;
     Pipeline_utils.prefix := "" |}.

Definition make_opts (cps : bool)
           (args : nat) (* number of C args *)
           (all_args : nat) (* do not add more fvs as args the number of original args and fvs exceeds all_args *)
           (o_level : nat) (time : bool) (debug : bool) (dev : nat) (prefix : string) : Options :=
  {| direct := negb cps;
     c_args := args;
     fv_args := args;
     show_anf := false;
     o_level := o_level;
     time := time;
     debug := debug;
     dev := dev;
     Pipeline_utils.prefix := prefix |}.

Definition printProg :=
  fun prog file =>
    L6_to_Clight.print_Clight_dest_names (snd prog) (cps.M.elements (fst prog)) file.

Definition compile (opts : Options) (p : Template.Ast.program) :=
  run_pipeline _ _ opts p pipeline.

(** * For compiling to λ_ANF and printing out the code *)
Definition show_IR (opts : Options) (p : Template.Ast.program) : (error string * string) :=
  let ir_term p := 
      p <- erase_PCUIC p ;; CertiCoq_pipeline p
  in 
  let (perr, log) := run_pipeline _ _ opts p ir_term in
  match perr with
  | Ret p =>
    let '(pr, cenv, _, _, nenv, fenv, _,  e) := p in
    (Ret (cps_show.show_exp nenv cenv false e), log)
  | Err s => (Err s, log)
  end.

Definition compile_lbox (opts : Options) (p : global_context * term) :=
  run_pipeline _ _ opts p lbox_pipeline.

(** * Glue Code *)

Definition make_glue (opts : Options) (p : Template.Ast.program)
  : error (cps_util.name_env * Clight.program * Clight.program * list string)  :=
  match generate_glue opts p with
  | Ret (nenv, Some hdr, Some prg, logs) =>
      Ret (nenv, hdr, prg, logs)
  | Ret (nenv, _, _, logs) =>
      Err "No Clight program generated"
  | Err s => Err s
  end.

Definition make_ffi (opts : Options) (p : Template.Ast.program)
  : error (cps_util.name_env * Clight.program * Clight.program * list string)  :=
  match generate_ffi opts p with
  | Ret (nenv, Some hdr, Some prg, logs) =>
      Ret (nenv, hdr, prg, logs)
  | Ret (nenv, _, _, logs) =>
      Err "No Clight program generated"
  | Err s => Err s
  end.
