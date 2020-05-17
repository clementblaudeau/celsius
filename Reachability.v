From Celsius Require Export Trees.
From Celsius Require Export Eval.
Require Import ssreflect ssrbool.

Require Import List.
Import ListNotations.
Open Scope nat_scope.
Open Scope list_scope.
Require Import Sets.Ensembles.

Module Reachability.
  Import Eval.Evaluator.

  (* Reserved Notation "σ ⊨ l1 ⇝ l2" (at level 80). *)
  Inductive reachability : Store -> Loc -> Loc ->Prop :=
  |rch_heap  : forall l σ,  l < (dom σ) -> (reachability σ l l)
  |rch_trans : forall l0 l1 l2 C ω σ, (reachability σ l0 l1) -> (getObj σ l1 = Some (C, ω)) -> (exists f, (getVal ω f = Some l2)) -> (l2 < dom σ) -> (reachability σ l0 l2).
  Notation "σ ⊨ l1 ⇝ l2" := (reachability σ l1 l2) (at level 80, l1 at level 80, l2 at level 80).

  (* To be moved to Trees.v at some point *)
  Definition LocSet := (Ensemble Loc).
  Notation "l ∈ L" := (In Loc L l) (at level 80).
  Notation "L ⊆ L'" := (Included Loc L L') (at level 80).
  Notation "L ∪ L'" := (Union Loc L L') (at level 80).
  Notation "{ l }" := (Singleton Loc l).


  Definition reachability_set σ (L: LocSet) l := exists l', (l' ∈ L) /\ (σ ⊨ l' ⇝ l).
  Notation "σ ⊫ L ⇝ l" := (reachability_set σ L l) (at level 80, l at level 99, L at level 99).


  Definition reachable_cold (σ: Store) (l: Loc) := (l < dom σ).
  Notation "σ ⊨ l : 'cold'" := (reachable_cold σ l) (at level 80, l at level 80).
   Notation "σ ⊫ L : 'cold'" := (forall l, (l ∈ L) -> reachable_cold σ l) (at level 80, L at level 99).

  Definition reachable_warm (σ: Store) (l: Loc) := (exists C ω args fields methods , (getObj σ l) = Some (C, ω) /\ ((ct C) = Some (class args fields methods)) /\ (length fields <= length ω)).
  Notation "σ ⊨ l : 'warm'" := (reachable_warm σ l) (at level 80, l at level 80).
  Notation "σ ⊫ L : 'warm'" := (forall l, (l ∈ L) -> reachable_warm σ l) (at level 80, L at level 99).

  Definition reachable_hot  (σ: Store) (l: Loc) :=(forall (l': Loc), (σ ⊨ l ⇝ l') -> (σ ⊨ l' : cold)).
  Notation "σ ⊨ l : 'hot'"  := (reachable_hot σ l) (at level 80, l at level 80).
  Notation "σ ⊫ L : 'hot'" := (forall l, (l ∈ L) -> reachable_hot σ l) (at level 80, L at level 99).

  Lemma reachability_trans: (forall σ l1 l2 l3, (σ ⊨ l1 ⇝ l2) -> (σ ⊨ l2 ⇝ l3) -> (σ ⊨ l1 ⇝ l3)).
  Proof.
    intros σ l1 l2 l3 H1 H2.
    induction H2 => //.
    apply (rch_trans l1 l2 l3 C ω σ (IHreachability H1) H H0 H3).
  Qed.
  Lemma reachability_hot: forall (σ: Store) (l l': Loc), σ ⊨ l: hot -> σ ⊨ l ⇝ l' -> σ ⊨ l': hot.
  Proof.
    intros σ l l' H1 H2 l'' H3.
    apply (H1 l'' ((reachability_trans _ _ _ _) H2 H3)).
  Qed.


End Reachability.
