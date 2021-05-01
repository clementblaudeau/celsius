(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines the notion of wellformedness for scopes. The set of reachable locations must all be valid locations of the store - that is, locations that are inside of the store. The main result is to show that if we start from a wellformed store that contains the local environment ρ and the [this] pointer, then we end up with a wellformed store that contains the location of the result *)

From Celsius Require Export Trees Eval PartialMonotonicity Reachability Compatibility.
Require Import ssreflect ssrbool Psatz List Sets.Ensembles Coq.Program.Tactics.
Import ListNotations.
Open Scope nat_scope.

Hint Resolve Union_intror: wf.
Hint Resolve Union_introl: wf.
Hint Resolve In_singleton: wf.

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

Lemma storeSubset_update:
  forall L l o σ,
    L ⪽ [l ↦ o] (σ) -> L ⪽ σ.
Proof.
  unfold storeSubset; steps; update_dom; eauto.
Qed.
Hint Resolve storeSubset_update: wf.


(** In preparation for initialization theorems, we have technical results about adding a location *)
Lemma wf_add : forall s c ρ, wf s -> codom ρ ⪽ s -> wf (s ++ [(c,ρ)]).
Proof.
  unfold wf, dom; intros.
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

(** We add all hints *)
Hint Resolve storeSubset_trans: wf.
Hint Resolve storeSubset_union: wf.
Hint Resolve storeSubset_union_l: wf.
Hint Resolve storeSubset_add: wf.
Hint Resolve storeSubset_union_r: wf.
Hint Resolve storeSubset_singleton: wf.
Hint Resolve storeSubset_singleton2: wf.
Hint Resolve storeSubset_singleton3: wf.
Hint Resolve storeSubset_codom_empty: wf.
Hint Resolve wf_add: wf.
Hint Resolve wf_add_empty: wf.
Hint Resolve nth_error_In: wf.
Hint Resolve storeSubset_update: wf.

(** ** Evaluation-maintained results *)
(** We want to show that the evaluator maintains the wellformedness of stores. As it is not only about stores but also the location of [this] and the result, we cannot use the results proved in Eval.v. We reprove it from scratch, starting with some technical results. *)

(** First a technical result on assignment *)
Lemma wf_assign:
  forall σ σ' ω ω' l v f C,
    (getObj σ l) = Some (C, ω) ->
    σ' = [l ↦ (C, ω')]σ ->
    ω' = [f ↦ v]ω ->
    v < dom σ ->
    wf σ -> wf σ'.
Proof.
  unfold wf; steps.
  rewrite update_dom.
  getObj_update; steps; eauto.
  getVal_update; steps; eauto.
Qed.
Hint Resolve wf_assign: wf.

(** Then we show the induction case for evaluating a list of expressions *)
Lemma wellformedness_theorem_list_aux :
  forall n,
    (forall k : nat,
        k < n ->
        forall e σ σ' ρ ψ l,
          ⟦ e ⟧ (σ, ρ, ψ )( k) = Success l σ' ->
          wf σ ->
          (codom ρ ∪ {ψ}) ⪽ σ ->
          wf σ' /\ l < dom σ') ->
    forall k, k < n ->
    forall ρ ψ el s s' vl1 vl2,
      fold_left (eval_list_aux ρ ψ k) el (Success_l vl1 s) = Success_l vl2 s' ->
      wf s ->
      codom vl1 ⪽ s ->
      (codom ρ ∪ {ψ}) ⪽ s ->
      wf s' /\ (codom vl2 ⪽ s') /\ (dom s <= dom s').
Proof.
  intros n H_strong k Hn.
  induction el; simpl; intros; try solve [steps].
  destruct k => //; try solve [rewrite foldLeft_constant in H => //].
  simpl in *; destruct_eval.
  move: (H3); intros.
  eapply H_strong in H4 ; eauto with wf; try lia.
  eapply partialMonotonicity_theorem_dom in H3.
  eapply IHel in H;
    steps; try lia;
       try eapply storeSubset_add;
      eauto with wf pM.
Qed.

(** Then for the initialization case *)
Lemma wellformedness_theorem_init_aux:
  forall n,
    (forall k : nat,
        k < n ->
        forall e σ σ' ρ ψ l,
          ⟦ e ⟧ (σ, ρ, ψ )( k) = Success l σ' ->
          wf σ ->
          (codom ρ ∪ {ψ}) ⪽ σ ->
          wf σ' /\ l < dom σ') ->
    forall k, k < n ->
         forall fields l1 l σ1 σ2,
           l < dom σ1 ->
           fold_left (init_field l1 l k) fields (Some σ1) = Some σ2 ->
           (codom l1 ∪ {l}) ⪽ σ1 ->
           wf σ1 ->
           wf σ2 /\ (dom σ1 <= dom σ2).
Proof.
  intros n Hstrong k Hn.
  induction fields; simpl; intros; try solve [steps].
  destruct k; simpl in H0; try solve [rewrite_anywhere foldLeft_constant  => //].
  destruct a.
  destruct_eval.
  unfold assign_new in *.
  destruct_match; try solve [rewrite_anywhere foldLeft_constant  => //].
  destruct o.
  eval_dom.
  eapply Hstrong in H3; eauto with wf; [destruct_and | lia].
  apply IHfields in H0; clear IHfields;
    unfold storeSubset; steps; update_dom;
      eauto with wf lia updates.
  + destruct_eq (l = l0); subst; eauto with updates lia.
    induction H6; try inSingleton; steps.
    eapply storeSubset_union_l in H1.
    eapply PeanoNat.Nat.le_trans with (dom σ1);
      eauto with wf lia.
    eapply H1 => //.
  + intros l'; intros. update_dom.
    unfold wf in H3.
    getObj_update; steps; eauto with wf lia.
    eapply_anywhere getVal_add; steps; try lia; eauto.
Qed.

(** Then we have the main result *)
Theorem wellformedness_theorem :
  forall n e σ σ' ρ ψ l,
    ⟦e⟧(σ, ρ, ψ)(n) = (Success l σ') ->
    wf σ ->
    (codom ρ) ∪ {ψ} ⪽ σ ->
    (wf σ' /\ l < dom σ').
Proof.
  apply (strong_induction (fun k => forall e σ σ' ρ ψ l, ⟦e⟧(σ, ρ, ψ)(k) = (Success l σ') -> wf σ -> (codom ρ) ∪ {ψ} ⪽ σ ->  (wf σ' /\ l < dom σ'))).
  intros n H_strongInd; intros.
  assert (ψ < dom σ /\ forall l', List.In l' ρ -> l' < dom σ)
    by (unfold storeSubset in *;  steps; eauto with wf).
  destruct_and.
  destruct n => //.
  move : (PeanoNat.Nat.lt_succ_diag_r n) => Hn.
  destruct e; intros; simpl in *;
    unfold wf in *;
      try solve [steps; eauto with wf pM lia];
      try solve [steps; eapply H_strongInd in matched; steps; eauto with wf pM lia];
      repeat (destruct_match; try discriminate) || eval_dom.

  + destruct n => //.
    eapply H_strongInd in matched; eauto; destruct_and.
    eapply wellformedness_theorem_list_aux in matched6;
      eauto with wf pM lia; try destruct_and.
    eapply H_strongInd in H; try eapply_any; eauto with wf; destruct_and.
    eapply storeSubset_union; [| eapply storeSubset_singleton3];
      eauto with wf lia.
  + destruct n => //; simpl in *; repeat (destruct_match; try discriminate).
    eapply wellformedness_theorem_list_aux in matched;
      eauto with wf pM lia; destruct_and.
    invert_constructor_equalities; subst.
    eapply wellformedness_theorem_init_aux in matched0;
      try rewrite dom_app; try rewrite_anywhere dom_app;
        eauto with wf lia; try destructs.
    eapply storeSubset_union; [| eapply storeSubset_singleton3;  rewrite dom_app];
      eauto with wf lia.
    intros l Hl; rewrite dom_app.
    eapply H6 in Hl; eauto with lia.
  + eapply H_strongInd in matched; eauto; destruct_and.
    eapply H_strongInd in matched0; eauto with wf;  destruct_and.
    unfold assign in *.
    repeat (destruct_match; try discriminate); eauto with wf lia.
    update_dom.
    eapply H_strongInd in H ; eauto with wf; try destruct_and.
    ++ intros.
       update_dom.
       getObj_update; steps; eauto.
       getVal_update; steps; eauto.
    ++ eapply storeSubset_trans with σ; eauto with wf lia.
       update_dom; lia.
Qed.

(* A simple corollary on the conservation of wellformedness *)
Corollary wellformedness_conserved :
  forall n e σ σ' ρ ψ l,
    ⟦e⟧(σ, ρ, ψ)(n) = (Success l σ') ->
    wf σ ->
    (codom ρ) ∪ {ψ} ⪽ σ ->
    wf σ'.
Proof.
  eapply wellformedness_theorem.
Qed.
Hint Resolve wellformedness_conserved: wf.

(** Another consequence: the returned value is within the returned store: *)
Corollary correct_value :
  forall k e σ σ' ρ ψ l,
    ⟦e⟧(σ, ρ, ψ)(k) = (Success l σ') ->
    wf σ ->
    (codom ρ) ∪ {ψ} ⪽ σ ->
    l < dom σ'.
Proof.
  eapply wellformedness_theorem.
Qed.
Hint Resolve correct_value: wf.

(** We extend it to list evalutions *)
Theorem wellformedness_list_conserved :
  forall n ρ ψ el s s' vl1 vl2,
    fold_left (eval_list_aux ρ ψ n) el (Success_l vl1 s) = Success_l vl2 s' ->
    wf s ->
    codom vl1 ⪽ s ->
    (codom ρ ∪ {ψ}) ⪽ s ->
    wf s' /\ (codom vl2 ⪽ s') /\ (dom s <= dom s').
Proof.
  intros n; eapply wellformedness_theorem_list_aux with (S n); eauto with wf.
Qed.
Hint Resolve wellformedness_list_conserved: wf.

(** A useful tactic: *)
Ltac eval_wf :=
  match goal with
  | H:(⟦ ?e ⟧ (?σ, ?ρ, ?v )( ?n)) = Success ?v' ?σ', H1:wf ?σ
    |- _ => match goal with
          | H':wf σ' |- _ => fail 1
          | _ =>
            let H_val := fresh "H_val" in
            let H_wf := fresh "H_wf" in
            pose proof (wellformedness_theorem n e σ σ' _ _ _ H) as [H_wf H_val]; eauto with wf
          end
  | H:(⟦_ ?el _⟧ (?σ, ?ρ, ?v )( ?n)) = Success_l ?v_l ?σ', H1:wf ?σ
    |- _ => match goal with
          | H':wf σ' |- _ => fail 1
          | _ =>
            let H_val := fresh "H_val" in
            let H_wf := fresh "H_wf" in
            let H_codom := fresh "H_codom" in
            pose proof (wellformedness_list_conserved _ _ _  el σ σ' _ _ H)
              as [H_wf [H_codom H_val]];
            eauto with wf pM
          end
  end.
