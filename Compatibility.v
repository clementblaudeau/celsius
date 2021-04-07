(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the compatibility relation between stores.
 Two stores are compatible when they have the same objects stored at the same locations. The local environment associated with the object can be different, but the object type must be the same. It's a technical result that is proven using the general evaluation maintained property of Eval.v *)

From Celsius Require Export Trees Eval Reachability Tactics.
Require Import ssreflect ssrbool List.
Import ListNotations.
Open Scope nat_scope.

(** ** Definition of compatibility *)
Definition compatible (σ σ': Store) : Prop := forall l C ω,
    getObj σ l  = Some (C, ω) ->
    (exists ω', getObj σ' l = Some (C, ω')).
Notation "σ ⊆ σ'" := (compatible σ σ') (at level 80).

(** ** Basic properties *)
(** We show that the relation is reflexive, transitive, and goes through assignment and adding of a fresh location *)

Lemma compatibility_reflexivity :
  forall σ, σ ⊆ σ.
Proof.
  unfold compatible. eauto. Qed.
Hint Resolve compatibility_reflexivity : cmpt.

Lemma compatibility_transitivity :
  forall s1 s2 s3, s1 ⊆ s2 -> s2 ⊆ s3 -> s1 ⊆ s3.
Proof.
  unfold compatible; intros.
  move /(_ l C ω H1):H  => [ω' H].
  move /(_ l C ω' H):H0 => [ω'' H0].
  eauto.
Qed.
Hint Resolve compatibility_transitivity : cmpt.

Lemma compatibility_assignment :
  forall σ σ' l C ω ω',
    getObj σ l = Some (C, ω) ->
    σ' = [l ↦ (C, ω')]σ ->
    σ ⊆ σ'.
Proof.
  unfold compatible; intros.
  destruct_eq (l = l0);
    repeat rewrite_any; try invert_constructor_equalities; subst;
      [rewrite getObj_update1 | rewrite getObj_update2];
      eauto using getObj_dom.
Qed.
Hint Resolve compatibility_assignment: cmpt.

Lemma compatibility_freshness :
  forall σ c ρ,
    σ ⊆ σ ++ [(c, ρ)].
Proof.
  unfold compatible.
  induction σ; destruct l; simpl ; eauto => //.
Qed.
Hint Resolve compatibility_freshness: cmpt.

(** ** Main compatibility theorem *)
(** Using the theorem shown in Eval.v, as the compatibility relation verifies enough properties, it is maintained by the evaluator *)

Theorem compatibility_theorem:
  forall n e σ σ' ρ v v',
      ⟦e⟧(σ, ρ, v)(n) = (Success v' σ') -> σ ⊆ σ'.
Proof.
  apply (EvalMaintainedProp compatible);
    try (intros; apply FreshnessInitMaintained);
    unfoldProps;
    eauto with cmpt.
Qed.
Hint Resolve compatibility_theorem: cmpt.
