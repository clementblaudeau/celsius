(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the notion of partial monotonicity between stores. The idea behind partial monotonicity is simple: objects that are being initialized (not warm already) can only get "warmer": the number of initialized fields can only increase. Between two stores [σ] and [σ'], it means that all objects in [σ] have more initialized fields in [σ']; it does not states anything about new objects that [σ'] can have. *)

From Celsius Require Export Compatibility Reachability.
Require Import ssreflect ssrbool List Psatz Coq.Program.Tactics.
Import ListNotations.
Open Scope nat_scope.

(** ** Definitions and notations *)
Definition initialized_fields σ l (f: list Field) : Prop :=
  match (getObj σ l) with
  | Some (C, ω) => ((length f) <= (length ω))
  | _ => False
  end.

Global Instance notation_initialized_fields : notation_dash_colon Store Loc (list Field) :=
  { dash_colon_ := initialized_fields }.
Global Hint Unfold notation_initialized_fields: notations.

Definition partial_monotonicity σ σ' :=
  forall l f, (σ ⊨ l : f) -> (σ' ⊨ l : f).

Notation "s ⪯ s'" := (partial_monotonicity s s') (at level 60).

Local Hint Unfold partial_monotonicity: pM.
Local Hint Unfold initialized_fields: pM.
Implicit Type σ: Store.

(** ** Basic results *)
(** The relation is trivially reflexive *)
Lemma pM_refl: forall σ,
    σ ⪯ σ.
Proof.
  auto with pM.
Qed.
Global Hint Resolve pM_refl: pM.

(** The relation is trivially transitive *)
Lemma pM_trans : forall σ1 σ2 σ3,
    σ1 ⪯ σ2 ->
    σ2 ⪯ σ3 ->
    σ1 ⪯ σ3.
Proof.
  autounfold with notations. eauto with pM.
Qed.
Global Hint Resolve pM_trans: pM.

Ltac pM_trans :=
  repeat match goal with
         | H:_ |- ?σ ⪯ ?σ => apply pM_refl
         | H: ?σ1 ⪯ ?σ2 |- ?σ1 ⪯ ?σ3 => apply pM_trans with σ2 ; [ assumption | ]
         | H: ?σ2 ⪯ ?σ3 |- ?σ1 ⪯ ?σ3 => apply pM_trans with σ2 ; [ | assumption ]
         end.
Global Hint Extern 1 => pM_trans: pM.


(** Initialized fields are within the domain *)
Lemma initialized_fields_dom :
  forall σ l f,
    (σ ⊨ l : f) -> (l < (dom σ)).
Proof.
  autounfold with notations.
  unfold initialized_fields, getObj.
  induction σ; destruct l as [| l']; steps; try lia.
  eapply Le.le_n_S, IHσ; rewrite_any; eauto.
Qed.
Global Hint Resolve initialized_fields_dom: pM.

(** Technical result: an object always have 0 or more fields initialized *)
Lemma initialized_fields_exists :
  forall σ C ω,
  exists f, ((C,ω)::σ) ⊨ (dom σ) : f.
Proof.
  autounfold with notations pM core.
  unfold initialized_fields.
  intros. exists ([]: list Field).
  induction σ; intros ; simpl ; try lia.
  destruct σ, a; steps; lia.
Qed.
Global Hint Resolve initialized_fields_exists: pM.

(** We have a result on the store sizes *)
Lemma pM_domains:
  forall σ σ',
    σ ⪯ σ' -> dom σ <= dom σ'.
Proof.
  autounfold; unfold partial_monotonicity; intros.
  destruct σ eqn:Σ; simpl; [lia |].
  destruct o.
  move : (initialized_fields_exists s c e) => [f Hf].
  eauto using Lt.lt_le_S with pM.
Qed.
Global Hint Resolve pM_domains: pM.


(** ** Main Monotonicity result *)
(** We start with two technical results on partial monotonicity for assignment (update) and fresh location *)
Lemma pM_assignment :
  forall σ l C (ω ω': Env),
    getObj σ l = Some (C, ω) ->
    length ω <= length ω' ->
    σ ⪯ [l ↦ (C, ω')]σ.
Proof.
  autounfold with pM notations.
  intros.
  destruct_eq (l = l0); subst;
    repeat rewrite_any;
    rewrite getObj_update1 || rewrite getObj_update2;
    eauto using getObj_dom.
Qed.
Global Hint Resolve pM_assignment: pM.

Lemma pM_freshness :
  forall σ c ρ,
    σ ⪯ (σ ++ [(c, ρ)]).
Proof.
  autounfold with notations pM. unfold getObj.
  steps;
    rewrite nth_error_app1 in matched; steps;
    apply nth_error_Some; steps.
Qed.
Global Hint Resolve pM_freshness: pM.

(** Then we have the main result *)
Theorem pM_theorem:
  forall e σ σ' ρ ψ v,
      ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> σ ⪯ σ'.
Proof with (eauto with pM updates lia).
  intros.
  induction H using evalP_ind2 with
    (Pl := fun _ σ _ _ _ σ' _ => σ ⪯ σ')
    (Pin := fun _ _ _ σ σ' _ => σ ⪯ σ');
    unfold assign, assign_new in *;
    repeat destruct_match;
    flatten; pM_trans ...
Qed.
Global Hint Resolve pM_theorem: pM.

Theorem pM_theorem_list:
  forall el σ σ' ρ ψ vl,
      ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') -> σ ⪯ σ'.
Proof with (eauto with pM updates lia).
  intros.
  induction H ...
Qed.
Global Hint Resolve pM_theorem_list: pM.

Theorem pM_theorem_init:
  forall fls ψ ρ σ σ',
      initP fls ψ ρ σ σ' -> σ ⪯ σ'.
Proof with (eauto with pM updates lia).
  intros.
  induction H;
    unfold assign, assign_new in *; ground ...
  eapply pM_theorem in H ...
Qed.
Global Hint Resolve pM_theorem_init: pM.

(** ** Other conservation results *)
(** As a consequence, we have monotonicity on the sizes of stores *)
Lemma evalP_dom:
   forall e σ ρ ψ v σ',
      ⟦e⟧p (σ, ρ, ψ) --> (v, σ') -> dom σ <= dom σ'.
Proof.
  eauto with pM.
Qed.
Global Hint Resolve evalP_dom: pM.

Lemma evalListP_dom:
   forall el σ ρ ψ vl σ',
      ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') -> dom σ <= dom σ'.
Proof.
  eauto with pM.
Qed.
Global Hint Resolve evalListP_dom: pM.

Lemma initP_dom:
  forall fls ψ ρ σ σ',
      initP fls ψ ρ σ σ' -> dom σ <= dom σ'.
Proof.
  eauto with pM.
Qed.
Global Hint Resolve initP_dom: pM.

Ltac eval_dom :=
  repeat match goal with
  | H: ⟦ ?e ⟧p (?σ, ?ρ, ?ψ) --> (?v, ?σ') |- _ =>
    let fresh := fresh "H_dom" in
    add_hypothesis fresh (evalP_dom e σ ρ ψ v σ' H)
  | H: ⟦_ ?el _⟧p (?σ, ?ρ, ?ψ) --> (?vl, ?σ') |- _ =>
    let fresh := fresh "H_dom" in
    add_hypothesis fresh (evalListP_dom el σ ρ ψ vl σ' H)
  | H: initP ?fls ?ψ ?ρ ?σ ?σ' |- _ =>
    let fresh := fresh "H_dom" in
    add_hypothesis fresh (initP_dom fls ψ ρ σ σ' H)
  end.


(** If we combine partial monotonicity with compatibility (objects do no change type), we can prove that warm objects stay warm *)
Lemma pM_warm_monotone:
  forall σ σ' (l: Loc),
    σ ⪯ σ' ->
    σ ⪨ σ' ->
    σ  ⊨ l : warm ->
    σ' ⊨ l : warm.
Proof.
  autounfold with pM core notations. unfold reachable_warm.
  steps.
  specialize (H l fields).
  repeat rewrite_any.
  eapply H0 in H2; steps.
  repeat eexists; eauto.
Qed.
