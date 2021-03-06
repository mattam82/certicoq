Require Import Coq.NArith.BinNat Coq.Relations.Relations Coq.MSets.MSets Coq.MSets.MSetRBT
        Coq.Lists.List Coq.omega.Omega Coq.Sets.Ensembles Coq.micromega.Lia.

Require Import L6.cps L6.eval L6.Ensembles_util L6.List_util L6.tactics L6.set_util
        L6.logical_relations L6.logical_relations_cc L6.algebra L6.inline_letapp.
Require Import micromega.Lia.

Import ListNotations.

Open Scope alg_scope. 


Section Bounds.
  

  (* ***** Fuel ***** *)
  
  Global Program Instance fuel_res_pre : @resource fin nat :=
    { zero := 0;
      one_i fin := 1;
      plus x y  := x + y; }.
  Solve Obligations with (simpl; lia).


  Global Program Instance fuel_res_ordered : @ordered fin nat fuel_res_pre :=
    { lt := Peano.lt }.
  Solve Obligations with (intro; intros; simpl; lia).
  Solve Obligations with (simpl; lia).
  Next Obligation.
    destruct (lt_dec x y); auto. right. eexists (x - y). lia.
  Qed.
  
  Global Program Instance fuel_res_ones : @resource_ones fin nat fuel_res_pre. 

  Global Program Instance fuel_res_hom : @nat_hom fin nat fuel_res_pre :=
    { to_nat y := y }.

  Global Program Instance fuel_res_exp : @exp_resource nat :=
    { HRes := fuel_res_pre }.
  
  Global Instance fuel_res : @fuel_resource nat.
  Proof.
    econstructor.
    eapply fuel_res_ordered.
    eapply fuel_res_ones.
    eapply fuel_res_hom.
  Defined.


  (* ***** Trace ***** *)

  
  Global Program Instance trace_res_pre : @resource fin (nat * nat) :=
    { zero := (0, 0);
      one_i fin :=
        match fin with
        | Four => (0, 1)
        | Six => (0, 1)
        | _ => (1, 0)
        end;
      plus x y := (fst x + fst y, snd x + snd y) }.
  Solve Obligations with (simpl; lia).
  Solve Obligations with (split; congruence).
  Next Obligation. simpl. f_equal; lia. Qed.
  Next Obligation. simpl. f_equal; lia. Qed.
  Next Obligation. simpl. f_equal; lia. Qed.  

  Global Program Instance trace_res_exp : @exp_resource (nat * nat) :=
    { HRes := trace_res_pre }.
  
  Global Instance trace_res : @trace_resource (nat * nat).
  Proof.
    econstructor. eapply trace_res_exp.
  Defined.

  Ltac unfold_all :=
    try unfold zero in *;
    try unfold one_ctx in *;
    try unfold one in *;
    try unfold one_i in *;
    try unfold HRes in *;
    try unfold HRexp_f in *; try unfold fuel_res in *; try unfold fuel_res_exp in *; try unfold fuel_res_pre in *;
    try unfold HRexp_t in *; try unfold trace_res in *; try unfold trace_res_exp in *; try unfold trace_res_pre in *.


  Section Inline_bound. 

    (* bound for inlining *)
    Definition inline_bound (L G : nat) : PostT := 
      fun '(e1, rho1, c1, (t1, tapp1)) '(e2, rho2, c2, (t2, tapp2)) =>
        c1 <= c2 + 2 * G * tapp1 + 2 * L /\
        tapp1 <= tapp2 + 2 * G * tapp2 + L /\
        t2 + tapp2 = c2. 

    Context (cenv : ctor_env).

    Instance inline_bound_compat L G (Hi : L <= G) :
      Post_properties cenv (inline_bound L G) (inline_bound L G) (inline_bound G G). 
    Proof.
      constructor; (try (intro; intros; intro; intros; destruct cout1; destruct cout2;
                         unfold inline_bound in *; unfold_all; simpl; split; [| split ]; lia)).
      - intro; intros. intro; intros. destruct cout1; destruct cout2. destruct cout1'; destruct cout2'.
        unfold inline_bound in *; unfold_all; simpl. destructAll. split. lia. split; lia.

      - intro; intros. intro; intros. 
        unfold inline_bound in *; unfold_all; simpl.
        assert (c = 0). eapply Nat.lt_1_r. eassumption. subst. lia.
      - intro; intros. unfold post_base'. 
        unfold inline_bound in *; unfold_all; simpl. lia.
      - intro; intros; unfold inline_bound in *.
        destruct x as [[[? ?] ?] [? ?]]; destruct y as [[[? ?] ?] [? ?]]. split; [| split ]; lia.
    Qed. 
    
    Lemma inline_bound_post_Eapp_l i G v t l rho1 x rho2 :
      post_Eapp_l (inline_bound i G) (inline_bound (S i) G) v t l rho1 x rho2.
    Proof.
      intro; intros. unfold inline_bound in *. unfold_all. simpl in *.
      destruct cout1; destruct cout2. simpl in *. destructAll. 
      split; [| split ]; try lia.
    Qed.

    Lemma inline_bound_remove_steps_letapp_OOT i j G : 
      remove_steps_letapp_OOT cenv (inline_bound j G) (inline_bound (S (i + j)) G).
    Proof.
      intro; intros. unfold inline_bound in *. unfold_all. simpl in *.
      destruct cout1; destruct cout2. simpl in *.
      split; [| split ]; lia.
    Qed.

    Lemma inline_bound_remove_steps_letapp i j G : 
      remove_steps_letapp cenv (inline_bound i G) (inline_bound j G) (inline_bound (S (i + j)) G).
    Proof.
      intro; intros. unfold inline_bound in *. unfold_all; simpl in *.
      destruct cout1; destruct cout2. destruct cout1'; destruct cout2'. simpl in *. lia. 
    Qed.    


    (* This allows us to prove divergence preservation *)  
    Lemma inline_bound_post_upper_bound L G :
      post_upper_bound (inline_bound L G).
    Proof.
      intro; intros. unfold inline_bound in *. unfold_all.
      eexists (fun x => (1 + 2 * G + 2 * G * 2 * G) * x + 2 * L * 2 * G + 2 * L).
      intros. 
      destruct cout1 as [t1 tapp1]; destruct cout2 as [t2 tapp2].

      destruct H. destruct H0.
      assert (Hleq : tapp1 <= cin2 + 2 * G * cin2 + L) by lia. clear H0 H1.
      
      assert (Hleq' : (1 + 2 * G + 2 * G * 2 * G) * cin1 + 2 * L * 2 * G + 2 * L <=
                      (1 + 2 * G + 2 * G * 2 * G) * cin2 + 2 * L * 2 * G + 2 * L).
      { eapply le_trans. eassumption. eapply le_trans.
        eapply plus_le_compat_r. eapply plus_le_compat_l. eapply mult_le_compat_l. eassumption.
        lia. } 
      
      assert (Hleq'' : cin1 <= cin2).
      { eapply Nat.add_le_mono_r in Hleq'. eapply Nat.add_le_mono_r in Hleq'.
        eapply NPeano.Nat.mul_le_mono_pos_l in Hleq'. eassumption. lia. }

      eexists (cin2 - cin1). simpl. lia.
    Qed.

    (* bound for inlining, toplevel *)
    Definition inline_bound_top (G : nat) : @PostT nat (nat * nat) := 
      fun '(e1, rho1, c1, (t1, tapp1)) '(e2, rho2, c2, (t2, tapp2)) =>
        let A := 1 + 2 * G + 2 * G * 2 * G in
        c1 <= A * c2 + A.

    Lemma inline_bound_top_impl (G : nat) :
      inclusion _ (inline_bound G G) (inline_bound_top G).
    Proof.
      intros [[[? ?] ?] [? ?]] [[[? ?] ?] [? ?]]. unfold inline_bound, inline_bound_top in *. unfold_all.
      intros. destructAll.
      eapply le_trans. eassumption.
      eapply le_trans. eapply plus_le_compat_r. eapply plus_le_compat_l. eapply mult_le_compat_l. eassumption.
      lia.
    Qed.

  
  End Inline_bound.


  Require Import L6.closure_conversion_correct ctx.
  
  Section SimpleBound.

    Context (cenv : ctor_env).
    
    (* Simple bound for transformations that don't decrease steps *)
    Definition simple_bound (L : nat) : @PostT nat (nat * nat) :=
      fun '(e1, rho1, c1, (t1, tapp1)) '(e2, rho2, c2, (t2, tapp2)) =>
        c1 <= c2 + L.


    Instance simple_bound_compat k :
      Post_properties cenv (simple_bound 0) (simple_bound k) (simple_bound 0). 
    Proof.
      constructor; (try (intro; intros; intro; intros; destruct cout1; destruct cout2;
                         unfold simple_bound  in *; unfold_all; simpl; lia)).
      - intro; intros. intro; intros. destruct cout1; destruct cout2. destruct cout1'; destruct cout2'.
        unfold simple_bound in *; unfold_all; simpl. destructAll. lia.
      - intro; intros. intro; intros. 
        unfold simple_bound in *; unfold_all; simpl. lia.
      - intro; intros. unfold post_base'. 
        unfold simple_bound in *; unfold_all; simpl. lia.
      - intro; intros; unfold simple_bound in *.
        destruct x as [[[? ?] ?] [? ?]]; destruct y as [[[? ?] ?] [? ?]]. lia.
    Qed. 
    

    (* CC bound properties *)

    Lemma Hpost_locals_r :
      forall (n : nat) (rho1 rho2  rho2' : env)(e1 : exp) (e2 : exp)
             (cin1 : nat) (cout1 : nat * nat)
             (cin2 : nat) (cout2 : nat * nat) (C : exp_ctx),
        ctx_to_rho C rho2 rho2' ->
        simple_bound (n + to_nat (one_ctx C)) (e1, rho1, cin1, cout1)
                     (e2, rho2', cin2, cout2) ->
        simple_bound n (e1, rho1, cin1, cout1)
                     (C |[ e2 ]|, rho2, cin2 <+> (one_ctx C), cout2 <+> (one_ctx C)).
    Proof.
      intros. destruct cout1; destruct cout2. unfold simple_bound in *. unfold_all. simpl in *.
      lia.
    Qed.
    
      
    Lemma Hpost_locals_l :
      forall (n : nat) (rho1 rho2  rho2' : env)(e1 : exp) (e2 : exp)
             (cin1 : nat) (cout1 : nat * nat)
             (cin2 : nat) (cout2 : nat * nat) (C : exp_ctx),
        ctx_to_rho C rho2 rho2' ->
        simple_bound n (e1, rho1, cin1, cout1)
                     (C |[ e2 ]|, rho2, cin2 <+> (one_ctx C), cout2 <+> (one_ctx C)) ->
        simple_bound (n + to_nat (one_ctx C)) (e1, rho1, cin1, cout1)
                     (e2, rho2', cin2, cout2).
    Proof.
      intros. destruct cout1; destruct cout2. unfold simple_bound in *. unfold_all. simpl in *.
      lia.
    Qed.
    
    Lemma Hpost_locals_l0 :
      forall (n : nat) (rho1 rho2  rho2' : env)(e1 : exp) (e2 : exp)
             (cin1 : nat) (cout1 : nat * nat)
             (cin2 : nat) (cout2 : nat * nat) (C : exp_ctx),
        ctx_to_rho C rho2 rho2' ->
        simple_bound n (e1, rho1, cin1, cout1)
                     (C |[ e2 ]|, rho2, cin2, cout2) ->
        simple_bound (n + to_nat (one_ctx C)) (e1, rho1, cin1, cout1)
                     (e2, rho2', cin2, cout2).
    Proof.
      intros. destruct cout1; destruct cout2. unfold simple_bound in *. unfold_all. simpl in *.
      lia.
    Qed.

    Lemma HOOT : forall j, post_OOT (simple_bound j).
    Proof.
      intros. intro; intros. intro; intros.
      unfold simple_bound in *. unfold_all. simpl in *.
      omega.
    Qed.

    Lemma Hbase : forall j, post_base (simple_bound j).
    Proof.
      intros. intro; intros. unfold post_base'.
      unfold simple_bound in *. unfold_all. simpl in *.
      omega.
    Qed.

    Context (clo_tag : ctor_tag).

    Lemma HPost_letapp_cc :
      forall f x t xs e1 rho1 n k, 
        k <= 4 + 4 * length xs  ->
        post_letapp_compat_cc' cenv clo_tag f x t xs e1 rho1 (simple_bound n) (simple_bound (n + k)) (simple_bound 0).
    Proof.
      intro; intros. intro; intros. destruct cout1; destruct cout2. destruct cout1'; destruct cout2'.
      unfold simple_bound in *; unfold_all; simpl. destructAll. lia.
    Qed.
    
    
    Lemma HPost_letapp_OOT_cc :
      forall f x t xs e1 rho1 n k, 
        k <= 4 + 4 * length xs ->
        post_letapp_compat_cc_OOT' clo_tag f x t xs e1 rho1 (simple_bound (n + k)) (simple_bound 0).
    Proof.
      intro; intros. intro; intros. destruct cout1; destruct cout2.
      unfold simple_bound in *; unfold_all; simpl. destructAll. lia.
    Qed.
    

    Lemma HPost_app :
      forall k v t l rho1,
        k <= 4 + 4 * length l -> post_app_compat_cc' clo_tag v t l rho1 (simple_bound k) (simple_bound 0).
    Proof.
      intro; intros. intro; intros. destruct cout1; destruct cout2.
      unfold simple_bound in *; unfold_all; simpl. destructAll. lia.
    Qed.


    (* This allows us to prove divergence preservation *)  
    Lemma simple_bound_post_upper_bound L :
      post_upper_bound (simple_bound L).
    Proof.
      intro; intros. unfold simple_bound in *. unfold_all.
      eexists (fun x => x +  L).
      intros. 
      destruct cout1 as [t1 tapp1]; destruct cout2 as [t2 tapp2].
      eapply Nat.add_le_mono_r in H.

      eexists (cin2 - cin1). simpl. lia.
    Qed.

  End SimpleBound.

  Section HoistingBound.

    Context (cenv : ctor_env). 

    Definition hoisting_bound (L G : nat) : @PostT nat (nat * nat) := 
      fun '(e1, rho1, c1, (t1, tapp1)) '(e2, rho2, c2, (t2, tapp2)) =>
        c1 <= c2 + G * c2 + L.
    
    Instance hoisting_bound_compat L G (Hi : L <= G) :
      Post_properties cenv (hoisting_bound L G) (hoisting_bound L G) (hoisting_bound G G).
    Proof.
      constructor; (try (intro; intros; intro; intros; destruct cout1; destruct cout2;
                         unfold hoisting_bound in *; unfold_all; simpl; lia)).
      - intro; intros. intro; intros. destruct cout1; destruct cout2. destruct cout1'; destruct cout2'.
        unfold hoisting_bound in *; unfold_all; simpl. destructAll. lia.
      - intro; intros. intro; intros. 
        unfold hoisting_bound in *; unfold_all; simpl. lia. 
      - intro; intros. unfold post_base'. 
        unfold hoisting_bound in *; unfold_all; simpl. lia.
      - intro; intros; unfold hoisting_bound in *.
        destruct x as [[[? ?] ?] [? ?]]; destruct y as [[[? ?] ?] [? ?]]. lia.
    Qed. 

    Lemma hoisting_bound_mon n m G :
      n <= m -> inclusion _ (hoisting_bound n G) (hoisting_bound m G).
    Proof.
      intros Hleq.
      intro; intros; unfold hoisting_bound in *.
      destruct x as [[[? ?] ?] [? ?]]; destruct y as [[[? ?] ?] [? ?]]. lia.
    Qed. 

    
    Lemma hoisting_bound_post_Efun_l n G :
      post_Efun_l (hoisting_bound n G) (hoisting_bound (S n) G).
    Proof.
      intro; intros. unfold hoisting_bound in *. unfold_all. simpl in *.
      destruct cout1; destruct cout2. lia.
    Qed.

    Definition hoisting_bound_top G := hoisting_bound (G + 1) G. 

    Lemma hoisting_bound_post_Efun_r n G :
      n <= G -> 
      post_Efun_r (hoisting_bound n G) (hoisting_bound_top G).
    Proof.
      intros Hleq. 
      intro; intros. unfold hoisting_bound, hoisting_bound_top in *. unfold_all. simpl in *.      
      destruct cout1; destruct cout2. lia.
    Qed.

    Lemma hoisting_boound_top_incl n G :
      n <= G -> inclusion _ (hoisting_bound n G) (hoisting_bound_top G).
    Proof.
      intros Hleq.
      intro; intros. unfold hoisting_bound_top, hoisting_bound in *.
      destruct x as [[[? ?] ?] [? ?]]; destruct y as [[[? ?] ?] [? ?]]. lia.
    Qed.

    Lemma hoisting_bound_post_upper_bound G :
      post_upper_bound (hoisting_bound_top G).
    Proof.
      intro; intros. unfold hoisting_bound_top, hoisting_bound in *. unfold_all.
      eexists (fun x => (1 + G) * x + (G + 1)).
      intros. 
      destruct cout1 as [t1 tapp1]; destruct cout2 as [t2 tapp2].
      eapply Nat.add_le_mono_r in H.

      replace (cin2 + G * cin2) with ((1 + G) * cin2) in H by lia.
      eapply NPeano.Nat.mul_le_mono_pos_l in H. 
      eexists (cin2 - cin1). simpl. lia.
      lia. 
    Qed.

  End HoistingBound.
    
End Bounds.
  
