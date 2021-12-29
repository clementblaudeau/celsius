(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines the notion of wellformedness for scopes. The set of reachable locations must all be valid locations of the store - that is, locations that are inside of the store. The main result is to show that if we start from a wellformed store that contains the local environment ρ and the [this] pointer, then we end up with a wellformed store that contains the location of the result *)

From Celsius Require Export PartialMonotonicity Reachability Compatibility.
Require Import ssreflect ssrbool Psatz List Sets.Ensembles Coq.Program.Tactics.
Import ListNotations.
Open Scope nat_scope.

Global Hint Resolve Union_intror: wf.
Global Hint Resolve Union_introl: wf.
Global Hint Resolve In_singleton: wf.

(** ** Definitions and notations *)
(** A wellformed store only contains pointers to locations that are within itself *)
Definition wf σ :=
  forall l C ω,
    getObj σ l = Some(C,ω) ->
    forall f l,
      getVal ω f = Some l ->
      l < dom σ. (**r [l ∈ dom σ] *)

(** A set of locations is contained in a store: [L ⪽ σ] *)
Definition storeSubset (σ: Store) L :=
  forall l, l ∈ L ->
       l < dom σ.

(** The codomain of an environment is the set of locations it contains *)
Definition codom (ρ: Env) : (LocSet) :=
  fun l => (List.In l ρ).

Notation "L ⪽ σ" := (storeSubset σ L) (at level 80).
Notation " a ∪ { b } " := (Union Loc a (Singleton Loc b)) (at level 80).

(** ** Basic results *)

Lemma storeSubset_trans :
  forall a s s',
    dom s <= dom s' ->
    a ⪽ s ->
    a ⪽ s'.
Proof.
  unfold storeSubset; steps.
  eapply H0 in H1 ; lia.
Qed.

Lemma storeSubset_union :
  forall a b s,
    a ⪽ s ->
    b ⪽ s ->
    (a∪b) ⪽ s.
Proof.
  unfold storeSubset; intros.
  induction H1; eauto.
Qed.

Lemma storeSubset_union_l :
  forall a b s,
    (a∪b) ⪽ s -> a ⪽ s.
Proof.
  unfold storeSubset; eauto with wf.
Qed.

Lemma storeSubset_union_r :
  forall a b s,
    (a∪b) ⪽ s -> b ⪽ s.
Proof.
  unfold storeSubset; eauto with wf.
Qed.

Lemma storeSubset_add :
  forall v a s,
    codom (v :: a) ⪽ s <-> v < dom s /\ codom a ⪽ s.
Proof.
  unfold codom, List.In, In, storeSubset in *; split.
  + steps; eapply_any; steps; right => //.
  + steps; move: H0 => [Hl|Hl]; steps.
Qed.

Lemma storeSubset_singleton :
  forall a b σ,
    a ∪ {b} ⪽ σ -> b < dom σ.
Proof.
  intros.
  eapply_any; eauto with wf.
Qed.

Lemma storeSubset_singleton2 :
  forall a σ,
    (Singleton Loc a) ⪽ σ -> a < dom σ.
Proof.
  unfold storeSubset; steps.
  induction (H a) ; steps.
Qed.

Lemma storeSubset_singleton3 :
  forall a σ,
    a < dom σ -> (Singleton Loc a) ⪽ σ.
Proof.
  unfold storeSubset; steps;
    induction H0 ; steps.
Qed.

Lemma storeSubset_codom_empty : forall s, codom [] ⪽ s.
Proof.
  unfold storeSubset; steps.
Qed.

Lemma codom_empty_union: forall a, (codom [] ∪ a) = a.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included;
    repeat steps || destruct H;
    eauto with wf.
Qed.

Lemma codom_cons:
  forall a ρ, codom (a::ρ) = ({a} ∪ (codom ρ)).
Proof.
  intros; apply Extensionality_Ensembles.
  unfold Same_set; steps; intros l; steps; try inversion H; steps;
    try inSingleton;
    eauto using Union_introl, Union_intror.
Qed.


Lemma storeSubset_update:
  forall L l o σ,
    L ⪽ [l ↦ o] (σ) -> L ⪽ σ.
Proof.
  unfold storeSubset; steps; update_dom; eauto.
Qed.
Global Hint Resolve storeSubset_update: wf.


(** In preparation for initialization theorems, we have technical results about adding a location *)
Lemma wf_add : forall s c ρ, wf s -> codom ρ ⪽ s -> wf (s ++ [(c,ρ)]).
Proof.
  unfold wf; intros.
  rewrite app_length; simpl.
  destruct_eq (l = length s);
    [subst; rewrite_anywhere getObj_last | rewrite_anywhere getObj_last2]; eauto.
  + invert_constructor_equalities; subst.
    apply PeanoNat.Nat.lt_trans with (length s); [| lia].
    eapply H0, nth_error_In, H2.
  + apply PeanoNat.Nat.lt_trans with (length s); [| lia]; eauto.
  + apply getObj_dom in H1.
    rewrite_anywhere  app_length; simpl in *.
    assert (l < length s) by lia ; eauto.
Qed.

Lemma wf_add_empty : forall s c, wf s -> wf (s ++ [(c,[])]).
Proof.
  eauto using wf_add, storeSubset_codom_empty.
Qed.

Lemma getVal_codom : forall x l ρ,
    getVal ρ x = Some l -> l ∈ codom ρ.
Proof.
  intros.
  eapply nth_error_In in H. auto.
Qed.


(** We add all hints *)
Global Hint Resolve storeSubset_trans: wf.
Global Hint Resolve storeSubset_union: wf.
Global Hint Resolve storeSubset_union_l: wf.
Global Hint Resolve storeSubset_add: wf.
Global Hint Resolve storeSubset_union_r: wf.
Global Hint Resolve storeSubset_singleton: wf.
Global Hint Resolve storeSubset_singleton2: wf.
Global Hint Resolve storeSubset_singleton3: wf.
Global Hint Resolve storeSubset_codom_empty: wf.
Global Hint Resolve wf_add: wf.
Global Hint Resolve wf_add_empty: wf.
Global Hint Resolve nth_error_In: wf.
Global Hint Resolve storeSubset_update: wf.
Global Hint Resolve getVal_codom: wf.
Global Hint Rewrite codom_cons: wf.

(** ** Evaluation-maintained results *)
(** We want to show that the evaluator maintains the wellformedness of stores. As it is not only about stores but also the location of [this] and the result, we cannot use the results proved in Eval.v. We reprove it from scratch, starting with some technical results. *)

(** First a technical result on assignment *)
Lemma wf_assign:
  forall σ ω l v f C,
    (getObj σ l) = Some (C, ω) ->
    v < dom σ ->
    wf σ ->
    wf [l ↦ (C, [f ↦ v]ω)]σ .
Proof.
  unfold wf; steps.
  rewrite update_dom.
  getObj_update; steps; eauto.
  getVal_update; steps; eauto.
Qed.
Global Hint Resolve wf_assign: wf.

Global Hint Unfold storeSubset: wf.

(** Then we have the main result *)
Theorem wf_theorem :
  forall e σ ρ ψ v σ',
    ⟦e⟧p (σ, ρ, ψ) --> (v, σ') ->
    wf σ ->
    (codom ρ) ∪ {ψ} ⪽ σ ->
    (wf σ' /\ v < dom σ').
Proof with (eauto with wf lia).
  intros. move: H0 H1.
  induction H using evalP_ind2 with
    (Pl := fun _ σ ρ ψ vl σ' _ => (codom ρ ∪ {ψ}) ⪽ σ -> wf σ -> (wf σ' /\ codom vl ⪽ σ'))
    (Pin := fun _ ψ ρ σ σ' _   => (codom ρ ∪ {ψ}) ⪽ σ -> wf σ -> wf σ');
    unfold assign, assign_new in * ; intros; eval_dom ...
  - (* e_fld *)
    steps. eapply_any ...
  - (* e_mtd *)
    destruct IHevalP3, IHevalP2; steps ...
  - (* e_new *)
    destruct IHevalP ...
    rewrite dom_app in H2.
    steps ...
    eapply IHevalP0 ...
    eapply storeSubset_union;
      [ eapply storeSubset_trans with σ1 |
        eapply storeSubset_singleton3] ; try rewrite dom_app ...
  - (* e_assgn *)
    destruct IHevalP1 ...
    destruct IHevalP2 ...
    repeat destruct_match; subst;
      destruct IHevalP3 ...
    eapply storeSubset_trans with σ ...
    rewrite update_dom ...
  - (* el_cons *)
    destruct IHevalP ...
    destruct IHevalP0 ...
    steps. apply storeSubset_add...
  - (* init_cons *)
    destruct IHevalP ...
    destruct (getObj σ1 I) eqn:H__obj; steps ;
      repeat rewrite_anywhere update_dom ...
    eapply IHevalP0 ...
    + eapply storeSubset_trans with σ ...
      rewrite update_dom ...
    + intros l; intros.
      getObj_update; steps; try rewrite update_dom; try lia.
      * eapply getVal_add in H7; steps ...
        eapply H4 ...
      * eapply H4 ...
Qed.

Theorem wf_theorem_list :
  forall el σ ρ ψ vl σ',
    ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') ->
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
    eapply storeSubset_add; steps ...
    apply IHevalListP ...
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
  repeat match goal with
  | H: ⟦ ?e ⟧p (?σ, ?ρ, ?ψ ) -->( ?v, ?σ'),
      H1:wf ?σ
    |- _ => match goal with
          | H':wf σ' |- _ => fail 1
          | _ =>
              let H_val := fresh "H_val" in
              let H_wf := fresh "H_wf" in
              pose proof (wf_theorem e σ ρ ψ v σ' H) as [H_wf H_val]; eauto with wf
          end
  | H: ⟦_ ?el _⟧p (?σ, ?ρ, ?ψ ) --> (?vl, ?σ'),
      H1:wf ?σ
    |- _ => match goal with
          | H':wf σ' |- _ => fail 1
          | _ =>
              let H_val := fresh "H_val" in
              let H_wf := fresh "H_wf" in
              let H_codom := fresh "H_codom" in
              pose proof (wf_theorem_list el σ ρ ψ vl σ' H)
                as [H_wf H_vals];
              eauto with wf pM
          end
  end.
