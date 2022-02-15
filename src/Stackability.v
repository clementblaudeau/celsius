(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the notion of stackability between stores. When we evaluate expressions, it might have the effect of creating new objects. If we are in the middle of the creation of a new object, the newly added objects might point to the current [this], which might be not fully initialized. So those newly created objects might not be hot. However, they have to be fully initialized, and thus, warm. Stackability states exactly this: two stores [σ] and [σ'] are stackable if the new objects in [σ'] are warm. To prove this, we use the evaluator results of Eval.v, whith a custom proof the initialization case *)

From Celsius Require Export PartialMonotonicity Reachability Wellformedness.
Require Import ssreflect ssrbool Psatz List.
Import ListNotations.
Open Scope nat_scope.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc) (L: LocSet).
Global Hint Resolve eM_warm_monotone: stk.


(** ** Definitions and notations *)
Definition stackability σ σ' :=
  forall l, l < (dom σ') -> ((σ' ⊨ l : warm) \/ (l < (dom σ))).
Global Instance notation_stackability_store : notation_stackability Store :=
  { stackability_ := stackability }.

Local Hint Unfold notation_stackability_store: notations.
Local Hint Unfold stackability : stk.

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
  steps. unfold stackability_, notation_stackability_store, stackability in *.
  steps.
  specialize (H l);
    specialize (H0 l);
    specialize (H1 l);
    steps.
  left. unfold reachable_warm in *.
  steps.
  specialize (H1 C ω H3) as [ω' [ ]].
  exists C ω'.
  repeat eexists; eauto with lia.
Qed.
Global Hint Resolve stk_trans: stk.

(** Assignment *)
Lemma stk_assign : forall σ l C ω ω',
    getObj σ l = Some (C, ω) ->
    length ω <= length ω' ->
    σ ≪ [l ↦ (C, ω')]σ.
Proof.
  autounfold with stk notations; steps.
  updates; eauto.
Qed.
Global Hint Resolve stk_assign: stk.


(** ** Main stackability theorem *)
(** Here we show the main result. We proceed by induction, enriching the goal with partial monotonicity and compatibility.Stackability is not maintained throughout the initialization of a new object, as its fields are being initialized. For the proof, we use a custom predicate [Pin] : the stores grows and the number of initialized fields grows too. Doing this, when we reach the end of initialization, we get a store with all initialized fields for the new object  *)

Theorem stk_theorem :
  forall e σ σ' ρ ψ v,
    ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> σ ≪ σ'.
Proof with (updates; eauto 3 with stk pM updates lia ).
  intros.
  induction H using evalP_ind2 with
    (Pl := fun _ σ _ _ _ σ' _ => σ ≪ σ')
    (Pin := fun C fls I _ σ σ' _   =>
              forall ω, getObj σ I = Some (C, ω) ->
                σ ≪ σ' /\ (exists ω', getObj σ' I = Some (C, ω') /\ (length fls + length ω = length ω')));
    unfold assign, assign_new in * ; eval_dom;
    try solve [steps; eauto with stk pM]...
  - rewrite getObj_last in IHevalP0.
    move /(_ [] eq_refl): IHevalP0. steps ...
    eapply stk_trans with σ1; try eapply pM_trans with (σ1 ++ [(C, [])])...
    move => l Hl.
    move /(_ l Hl): H1 => H1. steps ...
    destruct_eq (l = dom σ1); steps; [left |] ...
    repeat eexists ...
  - steps ; pM_trans ...
    eapply stk_trans with ([v1 ↦ (c, [x ↦ v2] (e))] (σ2)) ...
    eapply stk_trans with σ2 ...
    eapply stk_trans with σ2 ...
  - intros.
    repeat destruct_match => //.
    invert_constructor_equalities; subst...
    lets [?ω [ ]]: eM_theorem H H2.
    rewrite getObj_update_same in IHevalP0 ...
    cross_rewrites.
    move /(_ _ eq_refl): IHevalP0. steps ...
    eapply stk_trans with ([I ↦ (C, ω0 ++ [v])] (σ1)) ...
    eapply stk_trans with σ1 ...
Qed.
Global Hint Resolve stk_theorem: stk.
