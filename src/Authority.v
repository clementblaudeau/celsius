From Celsius Require Export Semantics.
Require Import ssreflect ssrbool List Psatz Coq.Program.Tactics.
Import ListNotations.
Open Scope nat_scope.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc).



(** ** Exact monotonicity  *)
Definition authority σ σ' :=
  forall l C ω, getObj σ l = Some(C, ω) -> exists ω', getObj σ' l = Some(C, ω') /\ dom ω = dom ω'.
Notation "s ⊵ s'" := (authority s s') (at level 60).
Local Hint Unfold authority: aty.

(** ** Basic results on partial monotonicity*)
(** The relation is trivially reflexive and transitive *)
Lemma aty_refl: forall σ,
    σ ⊵ σ.
Proof. eauto with aty. Qed.
Global Hint Resolve aty_refl: aty.

Lemma aty_trans : forall σ1 σ2 σ3,
    σ1 ⊵ σ2 ->
    σ2 ⊵ σ3 ->
    σ1 ⊵ σ3.
Proof.
  unfold authority; intros.
  specialize (H l C ω); steps.
  specialize (H0 l C ω'); steps; eauto with aty lia.
Qed.
Global Hint Resolve aty_trans: aty.

Ltac aty_trans :=
  repeat match goal with
         | H:_ |- ?σ ⊵ ?σ => apply aty_refl
         | H: ?σ1 ⊵ ?σ2 |- ?σ1 ⊵ ?σ3 => apply aty_trans with σ2 ; [ assumption | ]
         | H: ?σ2 ⊵ ?σ3 |- ?σ1 ⊵ ?σ3 => apply aty_trans with σ2 ; [ | assumption ]
         end.
Global Hint Extern 1 => aty_trans: aty.


(** We have a result on the store sizes *)
Lemma aty_domains:
  forall σ σ',
    σ ⊵ σ' -> dom σ <= dom σ'.
Proof.
  autounfold; unfold authority; intros.
  destruct σ eqn:Σ; simpl; [lia |].
  destruct o as [C ω].
  specialize (H (dom s)).
  destruct (getObj ((C, ω)::s) (dom s)) eqn: H__e.
  - destruct o as [D ω'].
    apply H in H__e; steps.
    apply getObj_dom in H1; auto.
  - unfold getObj in H__e.
    apply nth_error_None in H__e.
    simpl in H__e; lia.
Qed.
Global Hint Resolve aty_domains: aty.

(** ** Main Monotonicity result *)
(** We start with two technical results on partial monotonicity for assignment (update) and fresh location *)
Lemma aty_assignment :
  forall σ l C ω ω',
    getObj σ l = Some (C, ω) ->
    length ω = length ω' ->
    σ ⊵ [l ↦ (C, ω')]σ.
Proof.
  autounfold with aty notations.
  intros.
  lets: getObj_dom H.
  destruct_eq (l = l0); subst;
    updates; eauto.
Qed.
Global Hint Resolve aty_assignment: aty.

Lemma aty_freshness :
  forall σ c ρ,
    σ ⊵ (σ ++ [(c, ρ)]).
Proof.
  autounfold with notations aty.
  intros.
  lets: getObj_dom H.
  exists ω; steps;
    try rewrite getObj_last2;
    eauto with updates.
Qed.
Global Hint Resolve aty_freshness: aty.

(** Then we have the main result *)
Theorem aty_theorem:
  (forall e σ ρ ψ v σ',
      ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> σ ⊵ σ') /\
    (forall el σ ρ ψ vl σ',
        ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') -> σ ⊵ σ') /\
    (forall C flds ψ ρ σ σ',
        initP C flds ψ ρ σ σ' ->
        forall ω,
          getObj σ ψ = Some(C, ω) ->
          σ ⊵ [ψ ↦ (C, ω)]σ').

Proof with (updates; eauto 3 with aty updates lia).
  eapply evalP_multi_ind;
    unfold assign, assign_new; intros;
    repeat destruct_match; eval_dom;
    flatten; aty_trans; try discriminate ...

  - (* e_new *)
    intros l D ω H__get; steps.
    rewrite getObj_last in IH__init.
    specialize (IH__init [] eq_refl l D ω).
    rewrite getObj_last2 in IH__init...
    rewrite getObj_update_diff in IH__init...
    lets: getObj_dom H__get...

  - (* init_cons *)
    intros l D ω0 H__get; steps.
    lets: getObj_dom H.
    apply IH__e in H; steps.
    destruct_eq (I = l); subst; updates; cross_rewrites...
    rewrite getObj_update_same in IH__flds...
    specialize (IH__flds _ eq_refl l D ω0) as [ ]...

Qed.

Corollary aty_theorem_expr:
  forall e σ ρ ψ v σ',
      ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> σ ⊵ σ'.
Proof.
  apply aty_theorem.
Qed.
Global Hint Resolve aty_theorem: aty.

Corollary aty_theorem_list:
  forall el σ ρ ψ vl σ',
      ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') -> σ ⊵ σ'.
Proof.
  apply aty_theorem.
Qed.
Global Hint Resolve aty_theorem_list: aty.

(** Exact monotonic stores keep objects warm *)
From Celsius Require Import Reachability.
Lemma aty_warm_monotone:
  forall σ σ' l,
    σ ⊵ σ' ->
    σ  ⊨ l : warm ->
    σ' ⊨ l : warm.
Proof.
  intros. cbn in *.
  unfold reachable_warm in *.
  steps.
  lets [?ω' [ ] ] : H H1.
  repeat eexists; eauto.
  congruence.
Qed.
