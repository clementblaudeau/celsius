(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL & Inria 2020-2022 *)
(* ------------------------------------------------------------------------ *)

(** This file defines the notion of stackability between stores. When we evaluate expressions, it
might have the effect of creating new objects. If we are in the middle of the creation of a new
object, the newly added objects might point to the current [this], which might be not fully
initialized. So those newly created objects might not be hot. However, they have to be fully
initialized, and thus, warm. Stackability states exactly this: two stores [σ] and [σ'] are stackable
if the new objects in [σ'] are warm. *)

From Celsius Require Export Wellformedness.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc) (L: LocSet) (el: list Expr).

(* ------------------------------------------------------------------------ *)
(** ** Definition  *)
Definition stackability σ σ' :=
  forall l, l < (dom σ') -> ((σ' ⊨ l : warm) \/ (l < (dom σ))).
Global Instance notation_stackability_store : notation_stackability Store :=
  { stackability_ := stackability }.

Local Hint Unfold notation_stackability_store: notations.
Local Hint Unfold stackability : stk.

(* ------------------------------------------------------------------------ *)
(** ** Basic results *)
(** Reflexivity: *)

Lemma stk_refl:
  forall σ, σ ≪ σ.
Proof.
  auto with stk notations.
Qed.
Global Hint Resolve stk_refl: stk.

(** The transitivity relation requires additional conditions between [σ2] and [σ3]: *)
Lemma stk_trans: forall σ1 σ2 σ3,
    σ1 ≪ σ2 -> σ2 ≪ σ3 ->
    σ2 ⪯ σ3 ->
    σ1 ≪ σ3.
Proof.
  intros. intros l H__l.
  specialize (H l);
    specialize (H0 l);
    specialize (H1 l).
  intuition auto.
  inverts H.
  lets [ω' [ ]]: H1 H2.
  left; repeat eexists; eauto with rch lia.
Qed.
Global Hint Resolve stk_trans: stk.

(** Assignments *)

Lemma stk_assign : forall σ l C ω f v,
    getObj σ l = Some (C, ω) ->
    σ ≪ [l ↦ (C, [f ↦ v]ω)]σ.
Proof.
  autounfold with stk notations; steps.
  updates; eauto.
Qed.
Local Hint Resolve stk_assign: stk.

Lemma stk_assign_new:
  forall σ σ' l x v,
    assign_new l x v σ = Some σ' ->
    σ ≪ σ'.
Proof.
  unfold assign_new.
  autounfold with stk notations;
    steps; updates; eauto.
Qed.
Local Hint Resolve stk_assign_new: stk.


(* ------------------------------------------------------------------------ *)
(** ** Stackability theorem *)
(** Stackability is not maintained throughout the initialization of a new object, as the field of
the current object are being initialized. We can however show that the number of initialized fields
grows during initialization, reaching warm at the end (thanks to the mandatory field initializers)
*)

Lemma initP_warm :
  forall C I x ρ σ σ',
        initP C I x ρ σ σ' ->
        (σ ⊨ I : (C, cool x)) ->
        (σ' ⊨ I : (C, warm)).
Proof with (updates; cross_rewrites; eauto 3 with stk pM lia ).
  intros.
  induction H.
  - inverts H0; inverts H1; inverts H2...
    split; [eapply sm_warm | eexists ]...
  - lets H__pM: pM_theorem_expr H2.
    lets H__pM2: pM_theorem_init H4.
    inverts H0. inverts H5. inverts H6... rename x0 into ω.
    lets [?ω [ ]]: H__pM H7...
    rewrite /assign_new H0 in H3.
    lets: getObj_dom H0.
    destruct IHinitP. {
    destruct_if_eqb ; inverts H3; split;
      try eapply sm_cool; try eexists ... all: updates... }
    inverts H8. inverts H9...
    destruct_if_eqb ; inverts H3; split;
      try eapply sm_warm; try eexists ...
Qed.


Theorem stk_theorem :
  (forall e σ ρ ψ v σ',
      ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> σ ≪ σ') /\
    (forall el σ ρ ψ vl σ',
        ⟦el⟧ (σ, ρ, ψ) --> (vl, σ') -> σ ≪ σ') /\
    (forall C I x ρ σ σ',
        initP C I x ρ σ σ' -> σ ≪ σ').

Proof with (updates; cross_rewrites; eauto 3 with stk pM lia ).

  apply evalP_multi_ind;
    unfold assign; simpl; intros;
    eval_dom; ss_trans...

  - (* e = m.(el) *)
    eapply stk_trans...
    eauto with pM.

  - (* e = new C(args) *)
    lets: pM_theorem_list H__args.
    lets: pM_theorem_init H__init.
    ct_lookup C.
    lets [ ]: initP_warm H__init. { split; [eapply sm_cool | eexists]... }
    inverts H3; inverts H4...
    eapply stk_trans with σ1...
    intros l Hl.
    specialize (IH__init l Hl)...
    destruct_eq (l = dom σ1); steps...
    left. eapply sm_warm...

  - (* e = e1.x <- e2; e' *)
    lets: pM_theorem_expr H__e1.
    lets: pM_theorem_expr H__e2.
    lets: pM_theorem_expr H__e'.
    destruct (getObj σ2 v1) as [[?C ω]|] eqn:?; updates;
      eapply stk_trans...
    eapply stk_trans with σ2 ...
    eapply stk_trans with ([v1 ↦ (C, [x ↦ v2] (ω))] (σ2)) ...

  - (* init_cons *)
    lets: stk_assign_new H__assign.
    lets H__pM: pM_theorem_expr H__e.
    lets H__pM2: pM_theorem_init H__init.
    eapply stk_trans with σ2 ...
Qed.

Corollary stk_theorem_expr :
  forall e σ ρ ψ v σ',
    ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> σ ≪ σ'.
Proof.
  apply stk_theorem.
Qed.
Global Hint Resolve stk_theorem_expr: stk.

Corollary stk_theorem_list :
    forall el σ ρ ψ vl σ',
      ⟦el⟧ (σ, ρ, ψ) --> (vl, σ') -> σ ≪ σ'.
Proof.
  apply stk_theorem.
Qed.
Global Hint Resolve stk_theorem_list: stk.
