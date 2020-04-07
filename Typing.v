From Celsius Require Export Trees.
Require Import List.
Import ListNotations.
Open Scope nat_scope.


(* Mode lattice *)
Definition mode_leq (m1 m2 : mode) :=
  match (m1, m2) with
    | (hot, _ ) => true
    | (warm, hot) => true
    | (warm, warm) => true
    | ( _ , cold) => true
    | ( _ , _ ) => false end.
Notation "m1 ⊑ m2" := (mode_leq m1 m2) (at level 100).

Definition mode_max (m1 m2 : mode) : mode :=
  match (m1 ⊑ m2) with
    | true => m2
    | false => m1
  end.

Definition mode_min (m1 m2 : mode) : mode :=
  mode_max m2 m1.

Notation "m1 ⊓ m2" := (mode_min m1 m2) (at level 100).
Notation "m1 ⊔ m2" := (mode_max m1 m2) (at level 100).

(* Subtyping *)
Inductive subType : Tpe -> Tpe -> Prop :=
  | s_refl (T : Tpe) : subType T T
  | s_trans (T1 T2 T3 : Tpe) (H1: subType T1 T2) (H2: subType T2 T3) : subType T1 T3
  | s_mode (C: ClN) (μ1 μ2 : mode) (H : (μ1 ⊑ μ2) = true) : subType (C, μ1) (C, μ2).

Notation "T1 '<:' T2" := (subType T1 T2) (at level 100, right associativity).

Example test1 : (0, @hot) <: (0, @warm).
Proof.
  assert ((hot ⊑ warm) = true) as H. {
    reflexivity. }
  Unset Printing Notations.
  apply s_mode.
  assumption.
Qed.

(* Typing *)
