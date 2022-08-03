(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL & Inria 2020-2022 *)
(* ------------------------------------------------------------------------ *)
(* This files describes the semantic authority that our calculus enjoys. It is not used for
soundness *)

From Celsius Require Export Semantics.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc).

(* ------------------------------------------------------------------------ *)
(** ** Definition *)

Definition authority σ σ' :=
  forall l C ω, getObj σ l = Some(C, ω) -> exists ω', getObj σ' l = Some(C, ω') /\ dom ω >= dom ω'.
Global Instance notation_authority_store : notation_authority Store :=
  { authority_ := authority }.
Local Hint Unfold notation_authority_store: notations.
Local Hint Unfold authority : aty.

(* ------------------------------------------------------------------------ *)
(** ** Basic results *)
(** The relation is trivially reflexive and transitive *)

Lemma aty_refl: forall σ,
    σ ▷ σ.
Proof.
  intros ? ? ; eauto with aty.
Qed.
Global Hint Resolve aty_refl: aty.

Lemma aty_trans : forall σ1 σ2 σ3,
    σ1 ▷ σ2 ->
    σ2 ▷ σ3 ->
    σ1 ▷ σ3.
Proof.
  intros. intros ?; intros.
  specialize (H l C ω); steps.
  specialize (H0 l C ω'); steps; eauto with aty lia.
Qed.
Global Hint Resolve aty_trans: aty.

Ltac aty_trans :=
  repeat match goal with
         | H:_ |- ?σ ▷ ?σ => apply aty_refl
         | H: ?σ1 ▷ ?σ2 |- ?σ1 ▷ ?σ3 => apply aty_trans with σ2 ; [ assumption | ]
         | H: ?σ2 ▷ ?σ3 |- ?σ1 ▷ ?σ3 => apply aty_trans with σ2 ; [ | assumption ]
         end.
Global Hint Extern 1 => aty_trans: aty.

(** We have a result on the store sizes *)
Lemma aty_domains:
  forall σ σ',
    σ ▷ σ' -> dom σ <= dom σ'.
Proof.
  intros.
  destruct σ eqn:Σ; simpl; [lia |].
  destruct o as [C ω].
  specialize (H (dom s)).
  destruct (getObj ((C, ω)::s) (dom s)) eqn: H__e.
  - destruct o as [D ω'].
    apply H in H__e; steps.
    apply getObj_dom in H1; auto.
  - unfold getObj in H__e.
    apply nth_error_None in H__e.
    simpl in H__e; lia.
Qed.
Global Hint Resolve aty_domains: aty.

(* ------------------------------------------------------------------------ *)
(** ** Authority theorem *)
(** We start with two technical results on authority for assignment (update) and fresh
location *)

Lemma aty_assignment :
  forall σ l C ω ω',
    getObj σ l = Some (C, ω) ->
    length ω >= length ω' ->
    σ ▷ [l ↦ (C, ω')]σ.
Proof.
  intros. introv ?.
  lets: getObj_dom H.
  destruct_eq (l = l0); subst;
    updates; eauto with lia.
Qed.
Global Hint Resolve aty_assignment: aty.

Lemma aty_freshness :
  forall σ c ρ,
    σ ▷ (σ ++ [(c, ρ)]).
Proof.
  intros. introv ?.
  lets: getObj_dom H.
  exists ω; steps;
    try rewrite getObj_last2;
    eauto with updates.
Qed.
Global Hint Resolve aty_freshness: aty.

(** Then we have the main result *)
Theorem aty_theorem:
  (forall e σ ρ ψ v σ',
      ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> σ ▷ σ') /\
    (forall el σ ρ ψ vl σ',
        ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') -> σ ▷ σ') /\
    (forall C ψ x ρ σ σ',
        initP C ψ x ρ σ σ' ->
        [ψ ↦ (C,[])]σ ▷ [ψ ↦ (C, [])]σ').

Proof with (updates; cross_rewrites; eauto 3 with aty updates lia).
  eapply evalP_multi_ind;
    unfold assign; intros;
    repeat destruct_match; eval_dom;
    flatten; aty_trans; try discriminate ...

  - (* e_new *)
    intros l D ?ω H__get; steps.
    specialize (IH__init l D ω).
    lets: getObj_dom H__get...
    repeat rewrite getObj_update_diff in IH__init...
    rewrite getObj_last2 in IH__init...

  - (* init_cons *)
    lets: assign_new_dom H__assign.
    intros l ?D ?ω H__obj...
    destruct (getObj σ I) as [[?D ?ω]|] eqn:H2.
    + lets: IH__e I H2; steps.
      rewrite /assign_new H4 in H__assign...
      destruct_if_eqb; inverts H__assign;
        destruct_eq (I = l); subst...
    + destruct_eq (I = l); subst...
      destruct (getObj σ1 I) as [[?D ?ω]|] eqn:H4;
        rewrite /assign_new H4 in H__assign;
        try destruct_if_eqb; inverts H__assign...
Qed.

Corollary aty_theorem_expr:
  forall e σ ρ ψ v σ',
      ⟦e⟧ (σ, ρ, ψ) --> (v, σ') -> σ ▷ σ'.
Proof.
  apply aty_theorem.
Qed.
Global Hint Resolve aty_theorem: aty.

Corollary aty_theorem_list:
  forall el σ ρ ψ vl σ',
      ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') -> σ ▷ σ'.
Proof.
  apply aty_theorem.
Qed.
Global Hint Resolve aty_theorem_list: aty.
