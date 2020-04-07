From Celsius Require Export Trees.
Require Import ssreflect ssrbool.

Require Import List.
Import ListNotations.
Open Scope nat_scope.


Definition dom {X: Type} (x: list X) : nat :=
  (length x).

Definition initializedFields (σ: Store) (l: Loc) (f: list Field) : Prop :=
  match (getObj σ l) with
    | Some (C, ω) => ((length ω) <= (length f))
    | _ => False
  end.

Notation "σ ⊨ l : f" := (initializedFields σ l f) (at level 80, l at level 0).

Definition partialMonotonicity (σ σ': Store) :=
  forall l f, l <= (dom σ) -> (σ ⊨ l : f) -> (σ' ⊨ l : f).

Notation "σ ⪯ σ'" := (partialMonotonicity σ σ') (at level 80).

Lemma partialMonotonicity_reflexivity : forall (σ : Store), σ ⪯ σ.
  Proof. unfold partialMonotonicity. intros. assumption.
  Qed.
  
Lemma partialMonotonicity_domains : forall (σ σ': Store), σ ⪯ σ' -> (dom σ) <= (dom σ').
  Proof.
    Admitted.
    

Lemma partialMonotonicity_transitivity : forall (σ1 σ2 σ3 : Store), ((σ1 ⪯ σ2) /\ (σ2 ⪯ σ3)) -> (σ1 ⪯ σ3).
  Proof.
    move => σ1 σ2 σ3 h1.
    destruct h1 as [h1  h2].
    move : (partialMonotonicity_domains σ1 σ2) => h3.
    move : (h3 h1) => h4.
    unfold partialMonotonicity.
    intros.
    unfold partialMonotonicity in h2, h1.
    apply h2.
    apply (PeanoNat.Nat.le_trans l (dom σ1) ) => //.
    apply h1 => //.
Qed.    


