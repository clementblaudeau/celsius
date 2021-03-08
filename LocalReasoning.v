From Celsius Require Export Trees.
From Celsius Require Export Eval.
From Celsius Require Export PartialMonotonicity.
From Celsius Require Export Reachability.
From Celsius Require Export Compatibility.
From Celsius Require Export Scopability.
From Celsius Require Export Stackability.
From Celsius Require Export Wellformedness.
Require Import ssreflect ssrbool.
Require Import Psatz.

Require Import Sets.Ensembles.
Require Import List.
Import ListNotations.
Open Scope nat_scope.


Module LocalReasoning.
  Import Eval.Evaluator.
  Import Reachability.Reachability.
  Import Scopability.Scopability.
  Import Compatibility.Compatibility.
  Import PartialMonotonicity.PartialMonotonicity.
  Import Stackability.Stackability.
  Import Wellformedness.Wellformedness.

  Lemma local_reasoning:
    forall σ σ' L L',
      L ⪽ σ ->
      L' ⪽ σ' ->
      (σ, L) ⋖ (σ', L') ->
      σ ≪ σ' ->
      σ ⊆ σ' ->
      σ ⪯ σ' ->
      (σ ⊫ L : hot) ->
      σ' ⊫ L' : hot.
  Proof.
    intros σ σ' L L' H H0 H1 H2 H3 H4 H5.
    intros l0 Hl0. unfold reachable_hot. intros l1 Hl1.
    move : (partialMonotonicity_domains _ _ H4) => H_dom.
    destruct (PeanoNat.Nat.lt_ge_cases l1 (dom σ)).
    + (* l ∈ (dom σ) *)
      assert (reachability_set σ L l1). {
        apply H1; simpl => //.
        exists l0 => //.
      }
      move : H7 => [l2 [Hl2_dom Hl2_rch]].
      move : (H5 l2 Hl2_dom l1 Hl2_rch).
      eapply partialMonotonicity_warm_monotone; eauto.
    +
      unfold stackability in H2.
      move /(_ l1):H2 => H2.
      pose proof (proj2 (reachability_dom _ _ _ Hl1)). intuition.
  Qed.


  Theorem Local_reasoning:
    forall e σ σ' ρ ψ l k,
      ⟦e⟧(σ, ρ, ψ)(k) = (Success l σ') ->
      wf σ -> (codom ρ ∪ {ψ}) ⪽ σ ->
      (σ ⊫ ((codom ρ) ∪ {ψ}) : hot) ->
      σ' ⊨ l : hot.
  Proof.
    intros.
    assert (σ' ⊫ (Singleton Loc l) : hot). {
      eapply local_reasoning;
        eauto using stackability_theorem, compatibility_theorem, partialMonotonicity_theorem.

      pose proof (wellformedness_conserved _ _ _ _ _ _ _ H H0 H1) as [A1 A2].
      unfold storeSubset; intros. induction H3 => //.
      pose proof (scopability_theorem _ _ _ _ _ _ _ H) as [A2 A3] => //.
    }
      by apply (H3 l).
  Qed.

  Print DependGraph Local_reasoning.


  End LocalReasoning.
