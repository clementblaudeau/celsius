From Celsius Require Export Trees Eval Reachability Tactics.
Require Import ssreflect ssrbool.

Require Import List.
Import ListNotations.
Open Scope nat_scope.

Module Compatibility.
  Import Eval.Evaluator.
  Create HintDb cmpt.

  (* Definitions and notations : *)
  Definition compatible (σ σ': Store) : Prop := forall l C ω,
      getObj σ l  = Some (C, ω) ->
      (exists ω', getObj σ' l = Some (C, ω')).
  Notation "σ ⊆ σ'" := (compatible σ σ') (at level 80).

  Lemma compatibility_reflexivity : forall σ, σ ⊆ σ.
  Proof.
    unfold compatible. eauto. Qed.
  Hint Resolve compatibility_reflexivity : cmpt.

  Lemma compatibility_transitivity : forall s1 s2 s3, s1 ⊆ s2 -> s2 ⊆ s3 -> s1 ⊆ s3.
  Proof.
    unfold compatible. intros.
    move /(_ l C ω H1):H => [ω' H].
    move /(_ l C ω' H):H0 => [ω'' H0].
    eauto.
  Qed.
  Hint Resolve compatibility_transitivity : cmpt.

  Lemma compatibility_assignment : forall (σ σ': Store) (l: Loc) (C: ClN) (ω ω': Env),
      getObj σ l = Some (C, ω) ->
      σ' = [l ↦ (C, ω')]σ ->
      σ ⊆ σ'.
  Proof.
    intros.
    unfold compatible. intros.
    move: (PeanoNat.Nat.eq_dec l l0) => [H4 | H4].
    + rewrite H4 H1 in H.
      invert_constructor_equalities.
      rewrite H0 H4.
      rewrite getObj_update1.
      apply (getObj_dom _ _ _ H1).
      exists ω' => //.
    + rewrite H0.
      rewrite getObj_update2.
      apply (getObj_dom _ _ _ H).
      eauto.
      exists ω0 => //.
  Qed.
  Hint Resolve compatibility_assignment: cmpt.

  Lemma compatibility_freshness : forall (σ: Store) (c: ClN) (ρ: Env),
      σ ⊆ σ ++ [(c, ρ)].
  Proof.
    unfold compatible.
    induction σ; destruct l; simpl ; eauto => //.
  Qed.
  Hint Resolve compatibility_freshness: cmpt.


  Theorem Compatibility_theorem: forall (n : nat), forall (e: Expr) (σ σ': Store) (ρ: Env) (v v': Value),
      ⟦e⟧(σ, ρ, v)(n) = (Success v' σ') -> σ ⊆ σ'.
  Proof.
    apply (eval_prop compatible); unfold Reflexive, Transitive, Assignment, Freshness; eauto with cmpt.
  Qed.

  End Compatibility.
