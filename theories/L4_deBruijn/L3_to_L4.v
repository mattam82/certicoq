(** Naive conversion to a deBruijn-only expression language for a core
    calculus including mutually recursive functions, data constructors,
    and pattern matching.
 *)

Require Import Coq.Arith.Arith Coq.NArith.BinNat Coq.Strings.String
        Coq.Lists.List Coq.omega.Omega Coq.Program.Program Coq.micromega.Psatz.
Require Export Common.Common.  (* shared namespace *)
Open Scope N_scope.
Opaque N.add.
Opaque N.sub.
Require Import L2k.compile.
Module L3t := L2k.compile.
Require Import L4.expression.

(** Tactics *)
Ltac forward H :=
  match type of H with
  | ?T -> _ => let H' := fresh in cut T;[intros H'; specialize (H H') | ]
  end.

Definition dcon_of_con (i : inductive) (n : nat) := (i, N.of_nat n).

(** Definition environment *)
Definition env := list (kername * exp).

Fixpoint cst_offset (e : env) (s : kername) : N :=
  match e with
  | [] => 0%N
  | (c, e) :: tl => if eq_kername s c then 0 else 1 + cst_offset tl s
  end.

(** Inductive environment, kept to record arities of constructors.
    No more parameters by this stage. *)
Definition ienv := list (kername * itypPack).

Definition map_terms (f : L3t.Term -> exp) :=
  fix map_terms (l : L3t.Terms) : exps :=
  match l with
  | L3t.tnil => enil
  | L3t.tcons t ts => econs (f t) (map_terms ts)
  end.

Definition map_exps (f : exp -> exp) :=
  fix map_exps (l : exps) : exps :=
  match l with
  | enil => enil
  | econs t ts => econs (f t) (map_exps ts)
  end.

Section TermTranslation.
  Variable e : env.
    
  Fixpoint strip_lam (k : nat) (e : exp) : list name * exp :=
    match k, e with
    | 0%nat, _ => ([], e)
    | S n, Lam_e na e => let '(names, e) := strip_lam n e in
                       (na :: names, e)
    | S n, _ => ([],e)
    end.

  Section fixes.
    Variable trans : N -> L3t.Term -> exp.
    Definition trans_args (k : N) (t : L3t.Terms) : exps :=
      map_terms (trans k) t.
    Fixpoint trans_brs ind k n l :=
      match l with
      | L3t.bnil => brnil_e
      | L3t.bcons nargs t ts =>
        let '(names, t') := strip_lam nargs (trans k t) in
        brcons_e (ind,n) (N.of_nat nargs, names) t'
                 (trans_brs ind k (n + 1)%N ts)
      end.
    Fixpoint trans_fixes k l :=
      match l with
      | L3t.dnil => eflnil
      | L3t.dcons na t _ l' =>
        eflcons na (trans k t) (trans_fixes k l')
      end.

  End fixes.
  
  Fixpoint trans (k : N) (t : L3t.Term) : exp :=
    match t with
    | L3t.TWrong _ => Prf_e
    | L3t.TProof => Prf_e
    | L3t.TRel n => Var_e (N.of_nat n)
    | L3t.TLambda n t => Lam_e n (trans (1+k) t)
    | L3t.TLetIn n t u => Let_e n (trans k t) (trans (1+k) u)
    | L3t.TApp t u => App_e (trans k t) (trans k u)
    | L3t.TConst s => (* Transform to let-binding *)
      Var_e (cst_offset e s + k)
    | L3t.TConstruct ind c args =>
      let args' := trans_args trans k args in
      Con_e (dcon_of_con ind c) args'
    | L3t.TCase ind t brs =>
      let brs' := trans_brs trans ind k 0%N brs in
      Match_e (trans k t) 0 brs'
    | L3t.TFix d n =>
      let len := L3t.dlength d in
      let defs' := trans_fixes trans (N.of_nat len + k) d in
      Fix_e defs' (N.of_nat n)
    | L3t.TProj proj t => Prf_e     (****  FIX  ****)
    end.

End TermTranslation.

Definition translate (e : env) t :=
  trans e 0 t.

Definition translate_entry x acc :=
  match x with
  | (s, ecTrm t) =>
    let t' := translate acc t in
    (s, t') :: acc
  | (s, ecTyp _ _) => acc
  end.

Definition translate_entry_aux x acc : option (string * exp) :=
  match x with
  | (s, ecTrm t) =>
    let t' := translate acc t in
    Some (s, t')
  | (s, ecTyp _ _) => None
  end.

Definition translate_env_aux (e : environ L2k.compile.Term) (k : env) : env :=
  fold_right translate_entry k e.

Definition translate_env (e : environ L2k.compile.Term) : env :=
  translate_env_aux e [].

Definition inductive_entry_aux {A} (x : kername * envClass A) acc : ienv :=
  match x with
  | (s, ecTrm t) => acc
  | (s, ecTyp pars pack) =>
    (* pars is always 0 in the output of L2k_noCstrParams *)
    (s, pack) :: acc
  end.

Definition inductive_env (e : environ L2k.compile.Term) : ienv :=
  fold_right inductive_entry_aux [] e.

Definition mkLets (e : env) (t : exp) :=
  fold_left (fun acc (x : _ * exp) => Let_e (string_of_kername (fst x)) (snd x) acc) e t.

Require Import L3_to_L3_eta.

Definition translate_program
           (e: environ L2k.compile.Term) (t: L3t.Term) : exp :=
  let e' := translate_env e in
  mkLets e' (translate e' t).
