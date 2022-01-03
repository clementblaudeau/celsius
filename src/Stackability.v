(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the notion of stackability between stores. When we evaluate expressions, it might have the effect of creating new objects. If we are in the middle of the creation of a new object, the newly added objects might point to the current [this], which might be not fully initialized. So those newly created objects might not be hot. However, they have to be fully initialized, and thus, warm. Stackability states exactly this: two stores [σ] and [σ'] are stackable if the new objects in [σ'] are warm. To prove this, we use the evaluator results of Eval.v, whith a custom proof the initialization case *)

From Celsius Require Export PartialMonotonicity.
Require Import ssreflect ssrbool Psatz List.
Import ListNotations.
Open Scope nat_scope.

Global Hint Resolve pM_warm_monotone: stk.

(** ** Definitions and notations *)
Definition stackability (σ σ' : Store) :=
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
    σ2 ⪯ σ3 -> σ2 ⪨ σ3 ->
    σ1 ≪ σ3.
Proof.
  steps. unfold stackability_, notation_stackability_store, stackability in *.
  steps.
  specialize (H l);
    specialize (H0 l);
    specialize (H1 l);
    specialize (H2 l);
    steps.
  left. unfold reachable_warm in *.
  steps.
  specialize (H2 C ω H4) as [ω' H2].
  exists C ω'.
  repeat eexists; eauto.
  autounfold with notations in H1.
  unfold initialized_fields in H1.
  specialize (H1 fields). steps.
Qed.
Global Hint Resolve stk_trans: stk.

(** Assignment *)
Lemma stk_assign : forall σ l C ω ω',
    getObj σ l = Some (C, ω) ->
    length ω <= length ω' ->
    σ ≪ [l ↦ (C, ω')]σ.
Proof.
  autounfold with stk notations; steps.
  rewrite_anywhere update_one3; steps.
Qed.
Global Hint Resolve stk_assign: stk.


(** ** Main stackability theorem *)
(** Here we show the main result. We proceed by induction, enriching the goal with partial monotonicity and compatibility.Stackability is not maintained throughout the initialization of a new object, as its fields are being initialized. For the proof, we use a custom predicate [Pin] : the stores grows and the number of initialized fields grows too. Doing this, when we reach the end of initialization, we get a store with all initialized fields for the new object  *)

Theorem stk_theorem :
  forall e σ σ' ρ ψ v,
    ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> σ ≪ σ'.
Proof with (eauto with stk pM cmpt updates lia ).
  intros.
  apply proj1 with (B := (σ ⪨ σ' /\ σ ⪯ σ')).
  induction H using evalP_ind2 with
    (Pl := fun _ σ _ _ _ σ' _ => σ ≪ σ' /\ σ ⪨ σ' /\ σ ⪯ σ')
    (Pin := fun fls I _ σ σ' _  => forall C ρ,
                getObj σ I = Some (C, ρ) ->
                (σ ≪ σ' /\ σ ⪨ σ' /\ σ ⪯ σ' /\
                   (exists ρ', getObj σ' I = Some (C, ρ') /\ (length fls + length ρ <= length ρ'))));
    unfold assign, assign_new in * ; try solve [steps; eauto with stk pM cmpt]...
  - rewrite getObj_last in IHevalP0.
    move /(_ C [] eq_refl): IHevalP0. steps ...
    eapply stk_trans with σ1 ...
    unfold stackability in H1 |- * => l Hl.
    move /(_ l Hl): H1 => H1. steps.
    destruct_eq (l = dom σ1); steps; [left |].
    + unfold reachable_warm ; repeat eexists ...
    + rewrite app_length in H5. steps. lia.
  - steps ; pM_trans ...
    eapply stk_trans with ([v1 ↦ (c, [x ↦ v2] (e))] (σ2)) ...
    eapply stk_trans with σ2 ...
  - intros.
    repeat destruct_match => //.
    invert_constructor_equalities; subst.
    destruct IHevalP as [? [ ]].
    rewrite getObj_update1 in IHevalP0 ...
    move /(_ c _ eq_refl): IHevalP0. steps ...
    + eapply stk_trans with ([I ↦ (c, e0 ++ [v])] (σ1)) ...
      eapply stk_trans with σ1 ...
    + exists ρ'; split.
      ++ assert (C = c); steps.
         eapply H2 in H0; steps.
      ++ rewrite length_plus_1 in H9 .
         assert (length ρ0 <= length e0); try lia.
         move /(_ I (repeat (field T e) (length ρ0))): H3 => H3.
         autounfold with notations pM in H3. unfold initialized_fields in H3.
         steps.
         rewrite repeat_length in H3. lia.
Qed.
Global Hint Resolve stk_theorem: stk.
