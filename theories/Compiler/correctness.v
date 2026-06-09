From Wasm Require Import binary_format_printer.

Require Export LambdaANF.toplevel Codegen.toplevel CodegenWasm.toplevel.
Require Import compcert.lib.Maps.
From Stdlib Require Import ZArith.
Require Import Common.Common Common.compM Common.Pipeline_utils.
From Stdlib Require Import List.
Require Import maps_util.
Require Import Glue.glue.
Require Import ExtLib.Structures.Monad.
Require Import MetaRocq.Common.BasicAst.
From MetaRocq.Erasure Require Import EAst Erasure.
From MetaRocq.ErasurePlugin Require Import Erasure.
From MetaRocq.Utils Require Import MRString.

From CertiRocq Require Import pipeline.

Import Monads.
Import MonadNotation.
Import ListNotations.

Print CertiRocq_pipeline.
Print get_options.
Print compile_LambdaBoxEAst.
Print erase_program.
Print compile_LambdaANF_ANF.
Definition pipeline (o : Options) next_id p :=
  let p' := erase_program (erasure_config o) (inductives_mapping o) p in
  compile_LambdaANF_ANF next_id [] p'.
Print compM.
Theorem correctness o next_id p : 
  pipeline o next_id p = comp.
