(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines the notion of wellformedness for scopes. The set of reachable locations must all be valid locations of the store - that is, locations that are inside of the store. The main result is to show that if we start from a wellformed store that contains the local environment ρ and the [this] pointer, then we end up with a wellformed store that contains the location of the result *)

From Celsius Require Export Reachability Semantics PartialMonotonicity.
Require Import ssreflect ssrbool Psatz List Sets.Ensembles Coq.Program.Tactics Coq.Sets.Finite_sets_facts.
Import ListNotations.
Open Scope nat_scope.

(** ** Definitions and notations *)
(** A wellformed store only contains pointers to locations that are within itself *)
Definition wf σ :=
  forall l C ω,
    getObj σ l = Some(C, ω) ->
    (forall Args Flds Mtds,
        ct C = class Args Flds Mtds ->
        dom ω <= dom Flds) /\
      (forall f l',
          getVal ω f = Some l' ->
          l' < dom σ).

Lemma wf_proj1 : forall σ l C ω f v,
    wf σ ->
    getObj σ l = Some (C, ω) ->
    getVal ω f = Some v ->
    v < dom σ.
Proof.
  intros.
  eapply H; eauto.
Qed.
Global Hint Resolve wf_proj1: wf.

Lemma wf_proj2 : forall σ l C ω Args Flds Mtds,
    wf σ ->
    getObj σ l = Some (C, ω) ->
    ct C = class Args Flds Mtds ->
    dom ω <= dom Flds.
Proof.
  intros.
  eapply H; eauto.
Qed.
Global Hint Resolve wf_proj2: wf.


(** In preparation for initialization theorems, we have technical results about adding a location *)
Lemma wf_add : forall s C ρ Args Flds Mtds,
    wf s ->
    codom ρ ⪽ s ->
    ct C = class Args Flds Mtds ->
    dom ρ <= dom Flds ->
    wf (s ++ [(C,ρ)]).
Proof with (eauto with wf lia).
  steps.
  unfold wf; simpl; intros.
  rewrite app_length; simpl.
  destruct_eq (l = length s);
    [subst; try rewrite_anywhere getObj_last | try rewrite_anywhere getObj_last2].
  + steps.
    specialize (H0 l') as [ ] ...
    eapply getVal_codom...
  + split; intros...
    lets [ _ ? ]: H H3 ...
    lets : H5 H4 ...
  + apply getObj_dom in H3.
    rewrite_anywhere  app_length; simpl in *.
    assert (l < length s) by lia ; eauto.
Qed.
Global Hint Resolve wf_add: wf.

Lemma wf_add_empty : forall s C,
    wf s ->
    wf (s ++ [(C,[])]).
Proof.
  intros.
  destruct (ct C) eqn:H__ct.
  eapply wf_add; eauto using ss_codom_empty with cbn lia.
Qed.
Global Hint Resolve wf_add_empty: wf.


(** ** Evaluation-maintained results *)
(** First a technical result on assignment *)
Lemma wf_assign:
  forall σ ω l v f C,
    (getObj σ l) = Some (C, ω) ->
    v < dom σ ->
    wf σ ->
    wf [l ↦ (C, [f ↦ v]ω)]σ .
Proof.
  unfold wf; intros; updates.
  lets [ ]: H1 H.
  destruct_eq (l = l0); subst; updates.
  - split; intros; eauto.
    destruct_eq (f = f0); subst; updates; eauto.
  - lets [ ]: H1 H2.
    split; intros; eauto.
Qed.
Global Hint Resolve wf_assign: wf.

Lemma wf_assign_new:
  forall σ C I v ω (flds: list Field) Args Flds Mtds,
    ct C = class Args Flds Mtds ->
    dom ω + S (dom flds) = dom Flds ->
    wf σ ->
    getObj σ I = Some (C, ω) ->
    v < dom σ ->
    wf [I ↦ (C, ω ++ [v])] (σ).
Proof with (updates; cross_rewrites; eauto with wf lia).
  intros.
  unfold wf; intros; updates.
  destruct_eq (I = l); subst; split; intros; cross_rewrites; updates...
  eapply getVal_add in H5; steps...
  eapply H1...
Qed.

Ltac wf_assign_new :=
  match goal with
  | H: ct ?C = class ?Args ?Flds ?Mtds,
      H1: dom ?ω' = dom ?ω |- wf [?I ↦ (?C, ?ω ++ [?v])] (?σ) =>
      eapply wf_assign_new with (Args := Args) (Flds := Flds) (Mtds := Mtds);
      try rewrite -H1;
      eauto with wf
  | H: ct ?C = class ?Args ?Flds ?Mtds |- wf [?I ↦ (?C, ?ω ++ [?v])] (?σ) =>
      eapply wf_assign_new with (Args := Args) (Flds := Flds) (Mtds := Mtds); eauto with wf
  end.
Global Hint Extern 1 => wf_assign_new: wf.

(** Then we have the main result *)
Theorem wf_theorem :
 forall e σ ρ ψ v σ',
    ⟦e⟧ (σ, ρ, ψ) --> (v, σ') ->
    wf σ ->
    (codom ρ) ∪ {ψ} ⪽ σ ->
    (wf σ' /\ v < dom σ').
Proof with (updates; cross_rewrites; eauto with wf lia).
  intros.
  move: H0 H1.
  induction H using evalP_ind2 with
    (Pl := fun _ σ ρ ψ vl σ' _ => (codom ρ ∪ {ψ}) ⪽ σ -> wf σ -> (wf σ' /\ codom vl ⪽ σ'))
    (Pin := fun C flds ψ ρ σ σ' _ =>
              forall (H__codom : codom ρ ∪ {ψ} ⪽ σ) (H__wf: wf σ) ω Args Flds Mtds
                (H__ct : ct C = class Args Flds Mtds) (H__obj: getObj σ ψ = Some(C, ω)),
                dom ω + dom flds = dom Flds ->
                 (exists ω', getObj σ' ψ = Some (C, ω') /\ dom ω' = dom Flds) /\ wf σ');
    unfold assign, assign_new in * ; intros; eval_dom ...
  - (* e_var *)
    split; eauto with ss.
  -  (* e_fld *)
    destruct IHevalP...
  - (* e_mtd *)
    destruct IHevalP1 ...
    destruct IHevalP2 ...
  - (* e_new *)
    destruct IHevalP ...
    lets ((ω' & ? & ?) & ?) : IHevalP0 ([]: Env) H__ct...
    ss...
    eapply ss_trans with σ1...
  - (* e_assgn *)
    destruct IHevalP1 ...
    destruct IHevalP2 ...
    repeat destruct_match; subst;
      destruct IHevalP3...
    apply ss_trans with σ...
    apply ss_trans with σ...
  - (* el_cons *)
    destruct IHevalP ...
    destruct IHevalP0; steps ...
    apply ss_add...
  - (* init_nil *)
    simpl in *.
    split; [eexists; split |] ...
  - (* init_cons *)
    destruct IHevalP ...
    lets [?ω [ ] ]: eM_theorem H H__obj.
    rewrite H5 in H__assign... inverts H__assign...
    simpl in H0.
    edestruct IHevalP0; repeat ss; eauto with updates...
    eapply ss_trans with σ...
Qed.

Corollary wf_theorem_list :
  forall (el: list Expr) σ ρ ψ vl σ',
    ⟦ el ⟧ (σ, ρ, ψ) --> (vl, σ') ->
    (codom ρ ∪ {ψ}) ⪽ σ ->
    wf σ ->
    wf σ' /\ (codom vl ⪽ σ').
Proof with (eauto with wf lia).
  intros. move: H0 H1.
  induction H; steps;
    eval_dom ...
  + eapply wf_theorem in H; steps .
    apply IHevalListP ...
  + eapply wf_theorem in H; steps.
    destruct IHevalListP...
    eapply ss_add...
Qed.
Global Hint Resolve wf_theorem_list: wf.

Corollary wf_theorem_init :
  forall C flds ψ ρ σ σ' Args Flds Mtds ω,
    initP C flds ψ ρ σ σ' ->
    codom ρ ∪ {ψ} ⪽ σ ->
    wf σ ->
    ct C = class Args Flds Mtds ->
    getObj σ ψ = Some(C, ω) ->
    dom ω + dom flds = dom Flds ->
    (exists ω', getObj σ' ψ = Some (C, ω') /\ dom ω' = dom Flds) /\ wf σ'.
Proof with (updates; eauto with wf lia).
  intros. move: H0 H1 H2 H3 H4. gen ω.
  induction H; intros; eval_dom ...
  - steps ...
  - simpl in *.
    lets [ ] : wf_theorem H; eauto.
    lets [?ω [ ] ]: eM_theorem H H5.
    unfold assign_new in *.
    rewrite H11 in H0... inverts H0...
    edestruct IHinitP; repeat ss; eauto with updates...
    eapply ss_trans with σ...
Qed.
Global Hint Resolve wf_theorem_list: wf.


(* A simple corollary on the conservation of wellformedness *)
Corollary wf_conserved :
  forall e σ ρ ψ v σ',
    ⟦e⟧p(σ, ρ, ψ) --> (v, σ') ->
    wf σ ->
    (codom ρ) ∪ {ψ} ⪽ σ ->
    wf σ'.
Proof.
  eapply wf_theorem.
Qed.
Global Hint Resolve wf_conserved: wf.

(** Another consequence: the returned value is within the returned store: *)
Corollary correct_value :
  forall e σ ρ ψ v σ',
    ⟦e⟧p (σ, ρ, ψ) --> (v, σ') ->
    wf σ ->
    (codom ρ) ∪ {ψ} ⪽ σ ->
    v < dom σ'.
Proof.
  eapply wf_theorem.
Qed.
Global Hint Resolve correct_value: wf.


(** A useful tactic: *)
Ltac eval_wf :=
  repeat
    match goal with
    | H: codom ?ρ ∪ {?ψ} ⪽ ?σ1, H2: dom ?σ1 <= dom ?σ2 |- _ =>
        let name := fresh "H__codom" in
        add_hypothesis name (ss_trans _ σ1 σ2 H2 H)
    | H:⟦ ?e ⟧p (?σ, ?ρ, ?ψ) --> (?v, ?σ'),
        H1:wf ?σ,
          H2 : codom ?ρ ∪ {?ψ} ⪽ ?σ
      |- _ =>
        match goal with
        | H':wf σ' |- _ => fail 1
        | _ =>
            let H_val := fresh "H_val" in
            let H_wf := fresh "H_wf" in
            pose proof (wf_theorem e σ ρ ψ v σ' H H1 H2) as [H_wf H_val]
        end
    | H:⟦_ ?el _⟧p (?σ, ?ρ, ?ψ) --> (?vl, ?σ'),
        H1:wf ?σ,
          H2 : codom ?ρ ∪ {?ψ} ⪽ ?σ
      |- _ =>
        match goal with
        | H':wf σ' |- _ => fail 1
        | _ =>
            let H_val := fresh "H_val" in
            let H_wf := fresh "H_wf" in
            pose proof (wf_theorem_list el σ ρ ψ vl σ' H H2 H1) as [H_wf H_vals]
        end
    end.

(** Partially monotonic wellformed stores keep objects warm *)
Lemma pM_wf_warm_monotone:
  forall σ σ' (l: Loc),
    σ ⪯ σ' ->
    wf σ' ->
    σ  ⊨ l : warm ->
    σ' ⊨ l : warm.
Proof.
  autounfold with pM core notations. unfold reachable_warm.
  steps.
  lets [?ω' [ ] ] : H H2.
  lets [ ? _ ]: H0 H3.
  lets : H6 H1.
  repeat eexists; eauto with lia.
Qed.
