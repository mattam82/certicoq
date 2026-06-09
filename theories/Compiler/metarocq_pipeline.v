Require Import Common.Common Common.compM Common.Pipeline_utils.
From Stdlib Require Import List.
Require Import maps_util.
Require Import MetaRocq.Common.BasicAst.
From MetaRocq.Erasure Require Import EAst Erasure.
From MetaRocq.ErasurePlugin Require Import Erasure.
From MetaRocq.Utils Require Import MRString.

Import Monads.
Import MonadNotation.
Import ListNotations.

From MetaRocq.Erasure Require Import EProgram.
From MetaRocq.Common Require Import Transform.
From MetaRocq.ErasurePlugin Require Import ETransform.
Import Transform.

Import EWellformed.
From MetaRocq.Erasure Require Import EImplementBox.

Definition certirocq_post_metarocq_init_flags :=
  (EConstructorsAsBlocks.switch_cstr_as_blocks
    (EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags))).

Definition disable_lazy_force_term_flags (et : ETermFlags) :=
  {| has_tBox := has_tBox
    ; has_tRel := has_tRel
    ; has_tVar := has_tVar
    ; has_tEvar := has_tEvar
    ; has_tLambda := true
    ; has_tLetIn := has_tLetIn
    ; has_tApp := true
    ; has_tConst := has_tConst
    ; has_tConstruct := has_tConstruct
    ; has_tCase := has_tCase
    ; has_tProj := has_tProj
    ; has_tFix := has_tFix
    ; has_tCoFix := has_tCoFix
    ; has_tPrim := has_tPrim
    ; has_tLazy_Force := has_tLazy_Force
  |}.

Definition switch_off_lazy_force (efl : EEnvFlags) :=
  {|  has_axioms := efl.(has_axioms) ; has_cstr_params := efl.(has_cstr_params) ; term_switches := disable_lazy_force_term_flags efl.(term_switches) ; cstr_as_blocks := efl.(cstr_as_blocks) |}.

Definition certirocq_pose_metarocq_final_flags :=
  EImplementBox.switch_off_box 
    (switch_off_lazy_force
      (ETransform.efl_coind_to_ind certirocq_post_metarocq_init_flags)).

Program Definition implement_box_transformation (efl := (switch_off_lazy_force
      (ETransform.efl_coind_to_ind certirocq_post_metarocq_init_flags))) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram block_wcbv_flags) (eval_eprogram block_wcbv_flags) :=
  {| name := "implementing box";
    transform p _ := EImplementBox.implement_box_program p ;
    pre p := wf_eprogram efl p ;
    post p := wf_eprogram (switch_off_box efl) p ;
    obseq p hp p' v v' := v' = implement_box v |}.
Next Obligation.
  intros. cbn in *. split.
  - eapply implement_box_env_wf_glob; eauto. apply p.
  - eapply transform_wellformed'. all: try reflexivity. all: apply p.
Qed.
Next Obligation.
  intros pr v wf pre.
  destruct pr. destruct wf, pre; cbn in * |-.
  eexists. split; [ | eauto].
  econstructor.
  eapply implement_box_eval; cbn; eauto.
  all: reflexivity.
Qed.

Program Definition implement_lazy_force_transformation (efl : EEnvFlags) (has_app : has_tApp = true) (has_lam : has_tLambda = true) (has_tbox : has_tBox = true) :
  Transform.t _ _ EAst.term EAst.term _ _ (eval_eprogram block_wcbv_flags) (eval_eprogram block_wcbv_flags) :=
  {| name := "implementing lazy and force using lambdas ";
    transform p _ := (* todo *) p ;
    pre p := wf_eprogram efl p ;
    post p := wf_eprogram (switch_off_lazy_force efl) p ;
    obseq p hp p' v v' := v' = (* todo *) v |}.
Next Obligation. Admitted.
Next Obligation. Admitted.


(** The CertiRocq MetaRocq pipeline is composed of the verified typed or untyped MetaRocq pipelines plus:

    - CoFixpoints to fixpoints (unverified, only relevant if the source term contains cofixpoints)
    - Transformation of constants to values (verified, simplifies the ANF proof)
    - Transformation of lazy/force to lambda abstractions and applications (verified)
    - Unboxing of single argument constructors (verified)
    - Implementation of "box" as a fixpoint expression (verified)
    
    *)
Program Definition certirocq_post_metarocq_pipeline : Transform.t global_context global_context term term term term
  (eval_eprogram final_wcbv_flags)
  (eval_eprogram final_wcbv_flags) :=
  let efl := EConstructorsAsBlocks.switch_cstr_as_blocks
  (EInlineProjections.disable_projections_env_flag (ERemoveParams.switch_no_params EWellformed.all_env_flags)) in
  let efl' := efl_coind_to_ind efl in
  (* Rebuild the efficient lookup table *)
  rebuild_wf_env_transform (efl := efl) false false ▷
  (* Coinductives & cofixpoints are translated to inductive types and thunked fixpoints *)
  coinductive_to_inductive_transformation efl
      (has_app := eq_refl) (has_box := eq_refl) (has_rel := eq_refl) (has_pars := eq_refl) (has_cstrblocks := eq_refl) ▷
  consts_to_values_transformation efl' final_wcbv_flags eq_refl eq_refl eq_refl ▷
  (* Lazy-to-lambda *)
  implement_lazy_force_transformation _ eq_refl eq_refl eq_refl ▷
  rebuild_wf_env_transform (efl := efl') false false ▷
  unbox_transformation efl' final_wcbv_flags (has_app := _) (has_cofix := _) (has_prop_case := eq_refl) (has_letin := eq_refl) (has_cstrparams := eq_refl) (has_cstr_block := eq_refl) ▷
  implement_box_transformation.
Import TemplateProgram.

Program Definition run_erase_program {guard : PCUICWfEnvImpl.abstract_guard_impl} (econf : erasure_configuration)
  (p : Transform.program inductives_mapping template_program) : pre pre_erasure_pipeline_mapping p -> Transform.program global_context EAst.term :=
 if econf.(enable_typed_erasure) as _ return pre pre_erasure_pipeline_mapping p -> Transform.program global_context EAst.term then
    run (typed_erasure_pipeline econf ▷ certirocq_post_metarocq_pipeline) p
  else
   run (erasure_pipeline_mapping econf ▷ certirocq_post_metarocq_pipeline) p.
Next Obligation.
Proof.
  destruct econf as [[[] ? ? ?] ? ? [] ? ?]; cbn in *; intuition eauto.
Qed.
Next Obligation.
Proof.
  destruct econf as [[[] ? ? ?] ? ? [] ? []]; cbn in *; intuition eauto.
Qed.