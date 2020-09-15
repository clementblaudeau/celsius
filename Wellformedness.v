From Celsius Require Export Trees.
From Celsius Require Export Eval.
From Celsius Require Export PartialMonotonicity.
From Celsius Require Export Reachability.
From Celsius Require Export Compatibility.
Require Import ssreflect ssrbool.

Require Import List.
Import ListNotations.
Open Scope nat_scope.
Require Import Sets.Ensembles.

(*
  Notation "σ ⊨ l1 ⇝ l2" := (σ + l1 + l2) (at level 80, l1 at level 80, l2 at level 80).
  Notation "σ1 ⇝ σ2 ⋖ L" := (σ1 * σ2 * L) (at level 81, σ2 at level 81).
  Eval compute in (2 ⊨ 2 ⇝ 3) + (1 ⇝ 2 ⋖ 3).
  Check (1 ⊨ 2 ⇝ 3).
  Check (2 ⇝ 3 ⋖ 4).
 *)

Module Wellformedness.
  Import Eval.Evaluator.

  Definition wf σ := forall l C ω, getObj σ l = Some(C,ω) -> forall f l, getVal ω f = Some l -> l < dom σ.

  Definition storeSubset (σ: Store) L := (forall l, (l ∈ L) -> l < (dom σ)).
  Notation "L ⪽ σ" := (storeSubset σ L) (at level 80).
  Definition codom (ρ: Env) : (LocSet):=
    fun (l: Loc) => (List.In l ρ).

  Notation " a ∪ { b } " := (Union Loc a (Singleton Loc b)) (at level 80).
  Lemma storeSubset_singleton : forall a b σ, a ∪ {b} ⪽ σ -> b < dom σ.
  Proof.
    intros. apply (H b).
    eauto using Union_intror, In_singleton.
  Qed.


  Theorem wellformedness_conserved :
    forall k e σ σ' ρ ψ l, ⟦e⟧(σ, ρ, ψ)(k) = (Success l σ') -> wf σ -> (codom ρ) ∪ {ψ} ⪽ σ -> (wf σ' /\ l < dom σ').
    apply (strong_induction (fun k => forall e σ σ' ρ ψ l, ⟦e⟧(σ, ρ, ψ)(k) = (Success l σ') -> wf σ -> (codom ρ) ∪ {ψ} ⪽ σ ->  (wf σ' /\ l < dom σ'))). intros.
    assert (ψ < dom σ /\ forall l', List.In l' ρ -> l' < dom σ). {
      unfold storeSubset in *.
      split; steps; eauto using Union_introl, Union_intror, In_singleton. }
    destruct_and.
    destruct n => //.
    move : (PeanoNat.Nat.lt_succ_diag_r n) => Hn.
    destruct e ; simpl in H0 ;
      repeat discriminate || subst || invert_constructor_equalities || destruct_match ||
             match goal with
             | H1 : ⟦ _ ⟧ ( _, _, _)( _ ) = Success _ _ |- _ =>
               pose proof (H n Hn _ _ _ _ _ _ H1); clear H1 end; eauto.
    + intuition auto. eauto using nth_error_In.
    + intuition auto. unfold wf in H5. eapply H5; eauto.
    +
    destruct l1 => //. destruct l0, n => //. simpl in *. invert_constructor_equalities; subst.  apply H5 => //.
    intros l' Hl'. induction Hl' => //. induction H0. admit.
    simpl in *.
    admit.
  Admitted.


End Wellformedness.
