(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the notion of partial monotonicity between stores. The idea behind partial monotonicity is simple: objects that are being initialized (not warm already) can only get "warmer": the number of initialized fields can only increase. Between two stores [σ] and [σ'], it means that all objects in [σ] have more initialized fields in [σ']; it does not states anything about new objects that [σ'] can have. *)

From Celsius Require Export Trees Eval Reachability Tactics Compatibility strongInduction.
Require Import ssreflect ssrbool List Psatz Coq.Program.Tactics.
Import ListNotations.
Open Scope nat_scope.

(** ** Definitions and notations *)
Definition initializedFields σ l (f: list Field) : Prop :=
  match (getObj σ l) with
  | Some (C, ω) => ((length f) <= (length ω))
  | _ => False
  end.
Notation "σ ⊨ l : f" := (initializedFields σ l f) (at level 80, l at level 80, f at level 80).

Definition partialMonotonicity (σ σ': Store) :=
  forall l f, (σ ⊨ l : f) -> (σ' ⊨ l : f).
Notation "σ ⪯ σ'" := (partialMonotonicity σ σ') (at level 80).

(** ** Basic results *)
(** The relation is trivially reflexive *)
Lemma partialMonotonicity_reflexivity :
  forall σ, σ ⪯ σ.
Proof.
  unfold partialMonotonicity => //.
Qed.
Global Hint Resolve partialMonotonicity_reflexivity: pM.

(** The relation is trivially transitive *)
Lemma partialMonotonicity_transitivity : forall (σ1 σ2 σ3 : Store), (σ1 ⪯ σ2) -> (σ2 ⪯ σ3) -> (σ1 ⪯ σ3).
Proof.
  unfold partialMonotonicity; auto.
Qed.
Global Hint Resolve partialMonotonicity_transitivity: pM.

(** Initialized fields are within the domain *)
Lemma initializedFields_dom :
  forall σ l f,
    (σ ⊨ l : f) -> (l < (dom σ)).
Proof.
  unfold initializedFields, getObj.
  induction σ; destruct l as [| l']; steps; try lia.
  eapply Le.le_n_S, IHσ; rewrite_any; eauto.
Qed.
Global Hint Resolve initializedFields_dom: pM.

(** Technical result: an object always have 0 or more fields initialized *)
Lemma initializedFields_exists :
  forall σ c e,
  exists f, ((c,e)::σ) ⊨ (dom σ) : f.
Proof.
  unfold initializedFields.
  intros. exists [].
  induction σ; intros ; simpl ; try lia.
  - destruct σ, a; steps; lia.
Qed.
Global Hint Resolve initializedFields_exists: pM.

(** We have a result on the store sizes *)
Lemma partialMonotonicity_domains:
  forall σ σ',
    σ ⪯ σ' -> dom σ <= dom σ'.
Proof.
  unfold partialMonotonicity; intros.
  destruct σ eqn:Σ; simpl; [lia |].
  destruct o.
  case : (initializedFields_exists s c e) => f Hf.
  eauto using Lt.lt_le_S with pM.
Qed.
Global Hint Resolve partialMonotonicity_domains: pM.


(** ** Main Monotonicity result *)
(** We start with two technical results on partial monotonicity for assignment (update) and fresh location *)
Lemma partialMonotonicity_assignment :
  forall σ σ' l C ω ω',
    getObj σ l = Some (C, ω) ->
    length ω <= length ω' ->
    σ' = [l ↦ (C, ω')]σ ->
    σ ⪯ σ'.
Proof.
  unfold partialMonotonicity, initializedFields.
  intros.
  destruct_eq (l = l0); subst;
    repeat rewrite_any;
    rewrite getObj_update1 || rewrite getObj_update2;
    eauto using getObj_dom.
Qed.
Global Hint Resolve partialMonotonicity_assignment: pM.

Lemma partialMonotonicity_freshness :
  forall σ c ρ,
    σ ⪯ σ ++ [(c, ρ)].
Proof.
  unfold partialMonotonicity, initializedFields.
  induction σ ; destruct l => //.
  apply IHσ => //.
Qed.
Global Hint Resolve partialMonotonicity_freshness: pM.

(** Then we have the main result *)
Theorem partialMonotonicity_theorem:
  forall n, forall e σ σ' ρ v v',
      ⟦e⟧(σ, ρ, v)(n) = Success v' σ' ->
      σ ⪯ σ'.
Proof.
  apply (EvalMaintainedProp partialMonotonicity);
    try (intros; apply FreshnessInitMaintained);
    unfoldProps;
    eauto with pM.
Qed.
Global Hint Resolve partialMonotonicity_theorem: pM.

(** ** Other conservation results *)
(** As a consequence, we have monotonicity on the sizes of stores *)
Theorem partialMonotonicity_theorem_dom:
  forall n, forall e σ σ' ρ v v',
      ⟦e⟧(σ, ρ, v)(n) = Success v' σ' ->
      dom σ <= dom σ'.
Proof.
  eauto with pM.
Qed.
Global Hint Resolve partialMonotonicity_theorem_dom: pM.

Ltac eval_dom :=
  match goal with
  | H: ⟦?e⟧(?σ, ?ρ, ?v)(?n) = Success ?v' ?σ' |- _ =>
    let fresh := fresh "H_dom" in
    add_hypothesis fresh (partialMonotonicity_theorem_dom n e σ σ' ρ v v' H)
  end.


(** Similarly, we have a result for evaluation of lists *)
Theorem partialMonotonicity_theorem_list_dom:
  forall n el σ σ' ρ ψ ρ',
    ⟦_ el _⟧(σ, ρ, ψ)(n) = (Success_l ρ' σ') ->
    dom σ <= dom σ'.
Proof.
  intros.
  eapply (EvalListMaintained (fun σ σ' => dom σ <= dom σ') (S n));
    unfoldProps ; eauto with pM lia.
Qed.
Global Hint Resolve partialMonotonicity_theorem_list_dom: pM.

(** If we combine partial monotonicity with compatibility (objects do no change type), we can prove that warm objects stay warm *)
Lemma partialMonotonicity_warm_monotone:
  forall σ σ' l,
    σ ⪯ σ' ->
    σ ⊆ σ' ->
    (σ ⊨ l : warm) ->
    (σ' ⊨ l : warm).
Proof.
  unfold partialMonotonicity, initializedFields, reachable_warm; steps.
  specialize (H l fields).
  repeat rewrite_any.
  eapply H0 in H2; steps.
  repeat eexists; eauto.
Qed.
