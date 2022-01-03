(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** Store typing *)

From Celsius Require Export Typing.
Require Import Coq.ssr.ssreflect Coq.ssr.ssrbool Coq.Lists.List Coq.micromega.Psatz Ensembles.
(* Import ListNotations. *)
(* Open Scope nat_scope. *)


(** * Main definitions *)
(** ** Store_typing *)
(** Here is the link between the abstract environment of types and the store used in execution *)
Definition store_typing (Σ: StoreTyping) (σ: Store) :=
  forall l, l < dom Σ -> (exists C ω μ, getObj σ l = Some (C,ω) /\ getType Σ l = Some (C, μ)).

Notation "Σ ⊨ σ" := (store_typing Σ σ) (at level 60, σ at level 98).

(** ** Monotonicity *)
Definition monotonicity Σ1 Σ2 :=
  forall l, l < dom Σ1 -> (exists T1 T2, getType Σ1 l = Some T1 /\ getType Σ2 l = Some T2 /\ T1 <: T2).
Notation "Σ1 ≼ Σ2" := (monotonicity Σ1 Σ2) (at level 60).

Lemma monotonicity_dom :
  forall Σ1 Σ2, Σ1 ≼ Σ2 -> dom Σ1 <= dom Σ2.
Proof.
  intros.
  edestruct PeanoNat.Nat.le_gt_cases; eauto.
  destruct (dom Σ1) eqn:E; steps; try lia.
  specialize (H n).
  destruct H; try lia; steps.
  pose proof (nth_error_None Σ2 n).
  unfold getType in *.
  eapply_anywhere le_S_n.
  rewrite_any. exfalso. steps.
Qed.

Global Hint Resolve monotonicity_dom: typ.

(** ** Authority *)
Definition authority Σ1 Σ2 :=
  forall l, l < dom Σ1 -> (exists T, getType Σ1 l = Some T /\ getType Σ2 l = Some T).
Notation "Σ1 ▷ Σ2" := (monotonicity Σ1 Σ2) (at level 60).

(** ** Value typing (with variants) *)

Inductive value_typing : StoreTyping -> Loc -> Tpe -> Prop :=
| vt_sub : forall Σ l (T1 T2: Tpe),
    getType Σ l = Some T1 ->
    (T1 <: T2) -> value_typing Σ l T2.
Global Instance notation_value_typing_Tpe : notation_dash_colon StoreTyping Loc Tpe :=
  { dash_colon_ := value_typing }.
Global Hint Unfold notation_value_typing_Tpe: notations.

Definition value_typing_mode Σ l μ :=
  exists C, Σ ⊨ l : (C, μ).
Global Instance notation_value_typing_Mode : notation_dash_colon StoreTyping Loc Mode :=
  { dash_colon_ := value_typing_mode }.
Global Hint Unfold notation_value_typing_Mode: notations.

Definition value_typing_cln Σ l C :=
  exists μ, Σ ⊨ l : (C, μ).
Global Instance notation_value_typing_ClN : notation_dash_colon StoreTyping Loc ClN :=
  { dash_colon_ := value_typing_cln }.
Global Hint Unfold notation_value_typing_ClN: notations.

Definition value_typing_locset Σ L (μ:Mode) :=
  forall (l: Loc), (In Loc L l) -> Σ ⊨ l : μ.
Global Instance notation_value_typing_LocSet : notation_dash_colon StoreTyping LocSet Mode :=
  { dash_colon_ := value_typing_locset }.
Global Hint Unfold notation_value_typing_LocSet: notations.

(** ** Stackability *)
Definition stackability (Σ1 Σ2: StoreTyping) :=
  forall l, l < dom Σ2 -> (Σ2 ⊨ l : warm) \/ (l < dom Σ1).
Global Instance notation_stackability_StoreTyping : notation_stackability StoreTyping :=
  { stackability_ := stackability }.
From Celsius Require Import Stackability.
