(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the notion of stackability between stores. When we evaluate expressions, it
might have the effect of creating new objects. If we are in the middle of the creation of a new
object, the newly added objects might point to the current [this], which might be not fully
initialized. So those newly created objects might not be hot. However, they have to be fully
initialized, and thus, warm. Stackability states exactly this: two stores [σ] and [σ'] are stackable
if the new objects in [σ'] are warm. To prove this, we use the evaluator results of Eval.v, whith a
custom proof the initialization case *)

From Celsius Require Export Wellformedness.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc) (L: LocSet) (el: list Expr).

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

(** Assignment *)
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
  autounfold with stk notations; steps.
  updates; eauto.
Qed.
Local Hint Resolve stk_assign_new: stk.


(** ** Main stackability theorem *)
(** Here we show the main result. We proceed by induction, enriching the goal with partial
monotonicity and compatibility.Stackability is not maintained throughout the initialization of a new
object, as its fields are being initialized. For the proof, we use a custom predicate [Pin] : the
stores grows and the number of initialized fields grows too. Doing this, when we reach the end of
initialization, we get a store with all initialized fields for the new object *)

Theorem stk_theorem :
  (forall e σ ρ ψ v σ',
      ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> σ ≪ σ') /\
    (forall el σ ρ ψ vl σ',
        ⟦el⟧ (σ, ρ, ψ) --> (vl, σ') -> σ ≪ σ') /\
    (forall C I x ρ σ σ',
        initP C I x ρ σ σ' ->
          forall ω Args Flds Mtds,
            getObj σ I = Some (C, ω) ->
            dom ω >= x ->
            ct C = class Args Flds Mtds ->
            σ ≪ σ' /\
            exists ω', getObj σ' I = Some (C, ω') /\
                    dom ω' >= dom Flds).

Proof with (updates; cross_rewrites; eauto 4 with rch stk pM lia ).

  apply evalP_multi_ind;
    unfold assign; simpl; intros;
    eval_dom; ss_trans...

  - (* e = m.(el) *)
    eapply stk_trans...

  - (* e = new C(args) *)
    lets: pM_theorem_list H__args.
    lets: pM_theorem_init H__init.
    eapply stk_trans with σ1...
    rewrite getObj_last in IH__init; edestruct IH__init as [H3 [ω' [ ]]]...
    move => l Hl.
    specialize (H3 l Hl)...
    destruct_eq (l = dom σ1); steps; [left |] ...

  - (* e = e1.x <- e2; e' *)
    lets: pM_theorem_expr H__e1.
    lets: pM_theorem_expr H__e2.
    lets: pM_theorem_expr H__e'.
    destruct (getObj σ2 v1) as [[?C ω]|] eqn:?; updates;
      eapply stk_trans...
    eapply stk_trans with ([v1 ↦ (C, [x ↦ v2] (ω))] (σ2)) ...

  - (* fld = e::flds *)
    lets H__pM: pM_theorem_expr H__e.
    lets H__pM2: pM_theorem_init H__init.
    lets [?ω [ ]]: H__pM H...
    lets: stk_assign_new H__assign.
    lets: pM_assign_new H__assign.
    unfold assign_new in H__assign. rewrite H1 in H__assign.
    destruct (Nat.eqb x (dom ω0)) eqn:Heq; inverts H__assign.
    + rewrite getObj_update_same in IH__init; eauto with updates ...
      apply PeanoNat.Nat.eqb_eq in Heq; subst.
      specialize (IH__init (ω0++[v]) Args0 Flds0 Mtds0) as [H__stk [?ω [ ]]]...
      split; [| exists ω1; split]...
    + apply PeanoNat.Nat.eqb_neq in Heq; subst.
      specialize (IH__init ω0 Args0 Flds0 Mtds0) as [H__stk [?ω [ ]]]...
      split...
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
