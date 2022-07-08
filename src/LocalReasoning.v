(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(* ------------------------------------------------------------------------ *)
(* This file defines the main result of local reasoning, built upon partial monotonicity,
 stackability and scopability. In a wellformed, fully initialized context, a newly created object
 can only access hot (transitively fully initialized) locations. *)

From Celsius Require Export Scopability Stackability MetaTheory.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc) (L: LocSet) (Σ: StoreTyping).

(* ------------------------------------------------------------------------ *)
(** ** Local Reasoning theorem *)
(** We start with a lemma : *)

Lemma hot_preservation:
  forall σ σ' L L',
    (* Side conditions *)
    L ⪽ σ ->
    L' ⪽ σ' ->
    wf σ' ->

    (* Scopability, stackability, monotonicity *)
    (σ, L) ⋖ (σ', L') ->
    σ ≪ σ' ->
    σ ⪯ σ' ->

    (* Preservation of hot locations *)
    σ  ⊨ L  : hot ->
    σ' ⊨ L' : hot.

Proof with (eauto with rch).
  intros. intros l' H__l'.
  apply sm_hot => l H__rch.
  assert (dom σ <= dom σ') by eauto with pM.
  assert (l < dom σ \/ l >= dom σ) as [|] by lia.

  + (* l ∈ (dom σ) : the object was already in the store *)
    eapply pM_wf_warm_monotone...
    assert (σ ⊨ L ⇝ l).
    * eapply H2...
      eexists...
    * rch_set.
      lets: H5 H__ln.
      inverts H9...
      apply H10...

  + (* l ∉ (dom σ) *)
    destruct (H3 l); eauto with lia rch.
Qed.

(* Then the main theorem : *)
Theorem local_reasoning:
  forall e σ ρ ψ v σ',
    ⟦e⟧(σ, ρ, ψ) --> (v, σ') ->
    wf σ ->
    (codom ρ ∪ {ψ}) ⪽ σ ->
    σ  ⊨ ((codom ρ) ∪ {ψ}) : hot ->
    σ' ⊨ v : hot.
Proof.
  intros.
  assert (σ' ⊨ (Singleton Loc v) : hot).
  + eapply hot_preservation;
      eauto using stk_theorem with pM stk wf lia.
    eapply scp_theorem_expr; eauto with pM wf lia; steps.
  + eapply H3; eauto using In_singleton.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Local Reasoning for typing *)
(* We show here that we can upgrade the whole transitive closure to hot while preserving typing
properties (monotonicity, authority, stackability) *)

(* This axiom could be removed, as Reachability is decidable *)
Axiom classicT : forall (P : Prop), {P} + {~ P}.

Theorem Local_reasoning_for_typing: forall Σ1 Σ2 σ1 σ2 L1 L2,
    L1 ⪽ σ1 -> L2 ⪽ σ2 ->
    (σ1, L1) ⋖ (σ2, L2) ->
    (Σ1 ≪ Σ2) ->
    (Σ1 ▷ Σ2) ->
    (Σ1 ≼ Σ2) ->
    (Σ1 ⊨ σ1) -> (Σ2 ⊨ σ2) ->
    (Σ1 ⊨ L1 : hot) ->
    wf σ1 -> wf σ2 ->
    exists Σ', (Σ2 ≪ Σ') /\
            (Σ2 ≼ Σ') /\
            (Σ2 ▷ Σ') /\
            (Σ' ⊨ σ2) /\
            (Σ' ⊨ L2 : hot).
Proof with (meta; eauto 3 with typ lia).


  Ltac getType_combine :=
    lazymatch goal with
    | H1: getType ?Σ ?l = Some ?T, H__st: ?Σ ⊨ ?σ
      |- context [getType (map ?f (combine (seq 0 (dom _)) ?Σ)) ?l ] =>
        try rewrite (proj1 H__st) ;
        rewrite /getType nth_error_map;
        rewrite (nth_error_nth' _  (0,(Entry,cold)));
        [rewrite combine_length seq_length PeanoNat.Nat.min_id ; auto |];
        rewrite ?combine_nth ?seq_nth ?seq_length; eauto with updates; simpl;
        rewrite (nth_error_nth _ _ _ H1)
    end.

  intros.
  remember ((fun l' '(C,μ) => if (classicT (σ2 ⊨ L2 ⇝ l'))
                           then (C, hot)
                           else (C, μ)):Loc -> Tpe -> Tpe) as f.
  remember (map (fun '(l, T) => f l T) (combine (seq 0 (dom Σ2)) Σ2)) as Σ2'.
  exists Σ2'.
  assert ( Σ2 ≪ Σ2' /\
             Σ2 ≼ Σ2' /\
             (Σ2 ≪ Σ2' -> Σ2 ▷ Σ2') /\
             (Σ2 ≪ Σ2' -> Σ2 ≼ Σ2' -> Σ2' ⊨ σ2) /\ Σ2' ⊨ L2 : hot);
    [| steps; eauto with typ].
  splits; subst.

  - (* ≪ *)
    intros l H__l.
    rewrite map_length combine_length seq_length Nat.min_id in H__l...

  - (* ≼ *)
    intros l H__l.
    lets [[C μ] ?]: getType_Some H__l.
    exists (C, μ). exists (if is_left (classicT (σ2 ⊨ L2 ⇝ l)) then (C, hot) else (C, μ)); splits; [| | steps]...
    getType_combine; steps...

  - (* ▷ *)
    intros H__stk l H__l Ω H__getType.
    getType_combine;
      destruct (classicT (σ2 ⊨ L2 ⇝ l)); steps.
    lets[|]: H2 l... inverts H14.
    apply H1 in d...
    lets: hot_transitivity_set d...
    lets (?T & ?T & ? & ? & ?): H4 l...
    congruence.

  - (* ⊨ *)
    intros H__stk H__mn.
    split; rewrite map_length combine_length seq_length Nat.min_id...
    intros l H__l.
    lets (C & ω & μ & ? & ? & ?): (proj2 H6) l...
    exists C, ω, (if is_left (classicT (σ2 ⊨ L2 ⇝ l)) then hot else μ); splits...
    getType_combine; steps.
    destruct (classicT (σ2 ⊨ L2 ⇝ l)); steps...
    destruct (ct C) as [Args Flds Mtds] eqn:?.
    eapply ot_hot...
    intros.
    lets: getObj_dom H10.
    lets [|]: H2 l...
    + inverts H15.
      * inverts H12...
        lets (v & D & μ & ? & ? & ?): H19 H13.
        exists v, D, μ; splits... exists (D, hot)...
        getType_combine.
        destruct (classicT (σ2 ⊨ L2 ⇝ v)); steps...
        exfalso; apply n. rch_set.
        exists l0; split; eauto with rch...
      * inverts H12...
        lets (v & D & μ & ? & ? & ?): H19 H13.
        exists v, D, μ; splits... exists (D, hot)...
        getType_combine.
        destruct (classicT (σ2 ⊨ L2 ⇝ v)); steps...
    + lets: H1 d... clear d.
      lets: hot_transitivity_set H16...
      lets [?T1 [?T2 (? & ? & ?)]]: H4 l...
      lets (?C & ?ω & ?μ & ? & ? & ?): (proj2 H6) l...
      inverts H21.
      lets (v & D & μ & ? & ? & ?): H24 f...
      exists v, D, μ; splits... exists (D, hot)...
      getType_combine.
      destruct (classicT (σ2 ⊨ L2 ⇝ v)); steps...

  - (* ⊨ L' : hot *)
    intros l H__l.
    lets []: getType_Some Σ2 l...
    exists C. exists (C, hot)...
    getType_combine.
    destruct (classicT (σ2 ⊨ L2 ⇝ l)); steps...
    exfalso. apply n. exists l; split; eauto with rch.

Qed.
