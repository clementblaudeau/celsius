(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines and proves the soundess of the type system. *)

From Celsius Require Export LocalReasoning Eval.
Require Import ssreflect ssrbool Psatz Sets.Ensembles List Coq.Sets.Finite_sets_facts Coq.Program.Tactics.
Import ListNotations Arith.
Open Scope nat_scope.

Lemma e_this2:
  forall Γ U T,
    (Γ, U) ⊢ this : T -> U <: T.
Proof.
  intros. remember this as e.
  induction H; steps; meta; eauto with typ.
Qed.

Local Hint Constructors evalP: typ.
Local Hint Constructors T_Expr: typ.

Lemma typ_mtd: forall Γ T__this e m args T,
    ((Γ, T__this) ⊢ (mtd e m args) : T) ->
    exists C D e__m argTs paramTs μ__m μ0 μ__r,
      ((Γ, T__this) ⊢ e : (C, μ0)) /\
        methodInfo C m = Some (μ__m, paramTs, (D, μ__r),  e__m) /\
        μ0 ⊑ μ__m /\
        ((Γ, T__this) ⊩ args : argTs) /\
        S_Typs argTs paramTs /\
        ((D, hot) <: T) /\
        ((D, μ__r) <: T \/ P_hots argTs /\ μ0 = hot).
Proof with (meta; eauto with typ wf lia).
  introv H.
  remember (mtd e m args) as E.
  induction H; steps...
  - repeat eexists...
  - repeat eexists; steps...
  - repeat eexists...
    clear IHT_Expr H1 H H0 H2.
    induction argsT ; eauto using S_Typs with typ...
  - repeat eexists...
Qed.

Parameter typable_classes: T_Classes.

Ltac move_top t :=
  try match goal with
  | H1:t, H2:t, H3:t, H4:t, H5:t, H6:t, H7:t, H8:t, H9:t |- _ =>
     move H1 at top;
     move H2 at top;
     move H3 at top;
     move H4 at top;
     move H5 at top;
     move H6 at top;
     move H7 at top;
     move H8 at top;
     move H9 at top
  | H1:t, H2:t, H3:t, H4:t, H5:t, H6:t, H7:t, H8:t |- _ =>
     move H1 at top;
     move H2 at top;
     move H3 at top;
     move H4 at top;
     move H5 at top;
     move H6 at top;
     move H7 at top;
     move H8 at top
  | H1:t, H2:t, H3:t, H4:t, H5:t, H6:t, H7:t |- _ =>
     move H1 at top;
     move H2 at top;
     move H3 at top;
     move H4 at top;
     move H5 at top;
     move H6 at top;
     move H7 at top
  | H1:t, H2:t, H3:t, H4:t, H5:t, H6:t |- _ =>
     move H1 at top;
     move H2 at top;
     move H3 at top;
     move H4 at top;
     move H5 at top;
     move H6 at top
  | H1:t, H2:t, H3:t, H4:t, H5:t |- _ =>
     move H1 at top;
     move H2 at top;
     move H3 at top;
     move H4 at top;
     move H5 at top
  | H1:t, H2:t, H3:t, H4:t |- _ =>
     move H1 at top;
     move H2 at top;
     move H3 at top;
     move H4 at top
  | H1:t, H2:t, H3:t |- _ =>
     move H1 at top;
     move H2 at top;
     move H3 at top
  | H1:t, H2:t |- _ =>
     move H1 at top;
     move H2 at top
  | H1:t |- _ =>
     move H1 at top
  end.
Ltac meta_clean :=
  move_top StoreTyping;
  move_top EnvTyping;
  move_top Env;
  move_top Store;
  move_top (list Loc);
  move_top Loc;
  move_top (list Tpe);
  move_top Mode; move_top ClN; move_top Expr.

Ltac modus :=
  repeat match goal with
         | H: ?A -> ?B, H': ?A |- _ => specialize (H H')
         end.

Ltac eval_wf2 :=
  repeat
    match goal with
    | H: codom ?ρ ∪ {?ψ} ⪽ ?σ1, H2: dom ?σ1 <= dom ?σ2 |- _ =>
        let name := fresh "H__codom" in
        add_hypothesis name (storeSubset_trans _ σ1 σ2 H2 H)
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

Definition expr_soundness n e ρ σ ψ r Γ Σ U T :=
    ((Γ, U) ⊢ e : T) ->
    (Γ, Σ) ⊨ ρ ->
    Σ ⊨ σ ->
    (Σ ⊨ ψ : U) ->
    wf σ ->
    (codom ρ ∪ {ψ} ⪽ σ) ->
    ⟦e⟧(σ, ρ, ψ)(n) = r ->
    r <> Timeout ->
    exists Σ' v σ',
      r = Success v σ' /\
        Σ ≼ Σ' /\ Σ ≪ Σ' /\ Σ ▷ Σ' /\ (Σ' ⊨ σ') /\ wf σ' /\
        Σ' ⊨ v : T.

Definition expr_list_soundness n el ρ σ ψ r Γ Σ U Tl :=
    ((Γ, U) ⊩ el : Tl) ->
    (Γ, Σ) ⊨ ρ ->
    Σ ⊨ σ ->
    (Σ ⊨ ψ : U) ->
    wf σ ->
    (codom ρ ∪ {ψ} ⪽ σ) ->
    ⟦_ el _⟧(σ, ρ, ψ)(n) = r ->
    r <> Timeout_l ->
    exists Σ' vl σ',
      r = Success_l vl σ' /\
        Σ ≼ Σ' /\ Σ ≪ Σ' /\ Σ ▷ Σ' /\ (Σ' ⊨ σ') /\ wf σ' /\
        (Tl, Σ') ⊨ vl.


Theorem soundness:
  forall n,
    (forall e ρ σ ψ r Γ Σ U T,
        expr_soundness n e ρ σ ψ r Γ Σ U T) /\
    (forall el ρ σ ψ r Γ Σ U Tl,
      expr_list_soundness n el ρ σ ψ r Γ Σ U Tl).
Proof with (
    meta;
    meta_clean;
    eauto 4 with typ wf lia;
    try match goal with
        | |- ?Σ ⊨ ?l : ?T => try solve [eapply vt_sub; eauto with typ]
        end
  ).
  induction n as [n IHn] using lt_wf_ind. destruct n;
    intros; unfold expr_soundness, expr_list_soundness; split; intros;
    [steps | steps | destruct e | destruct el]; subst;
    simpl in *...
  - (* e = var x *)
    eapply env_regularity in H as (?l & ?H__get & ?)...
    rewrite H__get in H6 |- * ...
    exists Σ, l, σ; steps...
  - (* e = this *)
    eapply e_this2 in H.
    exists Σ, ψ, σ; steps...
  - (* e = fld *)
    admit.
  - (* e = mtd e m l *)
    rename l into args.
    specialize (IHn n ltac:(lia)) as [IH__expr IH__list]...

    (* Induction on the typing judgment *)
    eapply typ_mtd in H as
        (?C & ?C & ?e__m & ?Args & ?Flds & ?μ__m & ?μ' & ?μ__r &
           HT__e0 & H__mtdinfo & ? & HT__args & HS__args & H__sub & H__hots) ...

    (* Destruct evaluation of e0 *)
    destruct_eval H__eval0 v σ';
      lets (Σ0 & v0 & σ0 & H__r & H__mn0 & H__stk0 & H__aty0 & H__st0 & H__wf0 & H__v0) :
      IH__expr HT__e0 H0 H1 H3 H__eval0; try inverts H__r ...
    eapply eval_implies_evalp in H__eval0.
    lets H__pM0: pM_theorem H__eval0.
    lets (?C & ?ω & ?μ & H__obj & ? & ?): H__st0 H11...
    rewrite H__obj in H6 |- *.

    (* Destruct method fetch*)
    unfold methodInfo in H__mtdinfo.
    destruct (ct C1) as [Args1 Flds1 Mtds1] eqn:H__ct1.
    destruct (Mtds1 m) as [[?μ__r Ts retT ?] |] eqn:H__Mtds1; [| steps] . inverts H__mtdinfo...

    (* Extract typing for method body from Ξ (well-typed) *)
    pose proof (typable_classes C1) as HT__em.
    rewrite H__ct1 in HT__em.
    destruct HT__em as [_ HT__em].
    specialize (HT__em m _ _ _ _ H__Mtds1).

    (* Destruct argument evaluation *)
    lets H__env0: env_typing_monotonicity H__mn0 H0.
    eval_dom. eval_wf2...
    lets (?T & ?T & ? & ? & ?): H__mn0 ψ H2...
    destruct_eval H__eval1 vl σ';
      lets (Σ1 & args_val & σ1 & H__r & H__mn1 & H__stk1 & H__aty1 & H__st1 & H__wf1 & H__v1) :
      IH__list HT__args H__env0 H__st0 H__wf0 H__eval1; try inverts H__r ...
    eapply eval_list_implies_evalp in H__eval1. eval_dom; eval_wf2.

    (* Destruct evaluation of method body *)
    lets (?T & ?T & ? & ? & ?): H__mn1 ψ H5...
    lets (?T & ?T & ? & ? & ?): H__mn1 v0 H11...
    assert (HT__em': (Args, (C1, μ__m)) ⊢ e__m : (C, μ__r)) by admit.
    destruct (⟦ e__m ⟧ (σ1, args_val, v0 )( n)) as [ | | σ' v' ] eqn:H__eval2; try congruence;
    lets (Σ2 & v2 & σ2 & H__r & H__mn2 & H__stk2 & H__aty2 & H__st2 & H__wf2 & H__v2) :
      IH__expr HT__em' H__v1 H__st1 H__wf1 H__eval2; try inverts H__r ... admit. admit.
    eapply eval_implies_evalp in H__eval2.

    (* Result *)
    destruct H__hots as [? | [ H__hots ?] ]...
    + exists Σ2, v2, σ2; repeat split...
    + (* Local reasoning *)
      subst...
      destruct (local_reasoning2 Σ1 Σ2 σ1 σ2 (codom args_val ∪ { v0 }) {v2} ) as
        (Σ3 & ? & ? & ? & ? & H__v2)...
      * admit.
      * admit.
      * intros ? [l H__l | ? ]; rch_set.
        admit.
        admit.
      * intros l Hl; rch_set.




    destruct H__hots as [H__hots | H__hots]...

    steps...
    exists (C, μ6)...
    eapply s_typ_mode.
    eapply s_mode_trans; eauto.
    eapply s_mode_trans; eauto.



    destruct_eval.
    meta.
    meta_clean.
    eauto with typ wf lia.
    try match goal with
    | |- ?Σ ⊨ ?l : ?T => try solve [eapply vt_sub; eauto with typ]
    end.
    + steps.
    + clear H8.
      destruct (getObj s v) as [[?C ?ω] |]. admit.
      destruct (ct C3) as [?Args ?Flds ?Mtds] eqn:H__ct3.
      destruct (Mtds m) as [[_ _ _ e1] |]. eqn:H__mtd.

      steps.
      eapply H8.
      eapply IHn in H5...
      congruence. admit. admit.  ; try congruence.



    exosts
    rewrite_any.
    repeat destruct_match; try congruence.
    admit.
    destruct



(** by induction on evaluation *)
Theorem semantic_soundness:
    forall e ρ σ ψ l σ',
      ⟦e⟧p(σ, ρ, ψ) --> (l, σ') ->
      wf σ ->
      (codom ρ ∪ {ψ} ⪽ σ) ->
      forall Γ U T Σ,
        ((Γ, U) ⊢ e : T) ->
        (Γ, Σ) ⊨ ρ ->
        Σ ⊨ σ ->
        (Σ ⊨ ψ : U) ->
        exists Σ',
          Σ ≼ Σ' /\ Σ ≪ Σ' /\ Σ ▷ Σ' /\ (Σ' ⊨ σ') /\ wf σ' /\
            Σ' ⊨ l : T.
Proof with (meta; meta_clean; eauto with typ wf lia; try solve [eapply vt_sub; eauto with typ]).

  introv H.
  induction H using evalP_ind2 with
    (Pl := fun el σ ρ ψ vl σ' _ =>
               wf σ ->
               (codom ρ ∪ {ψ} ⪽ σ) ->
             forall Γ U Tl Σ,
               ((Γ, U) ⊩ el : Tl) ->
               (Γ, Σ) ⊨ ρ ->
               Σ ⊨ σ ->
               (Σ ⊨ ψ : U) ->
               exists Σ',
                 Σ ≼ Σ' /\ Σ ≪ Σ' /\ Σ ▷ Σ' /\ (Σ' ⊨ σ') /\ wf σ' /\ ((Tl, Σ') ⊨ vl))
    (Pin := fun C fls I _ σ σ' _   => False );
    intros; eval_dom; eval_wf2; modus...
  - (* e_var *)
    pose proof (env_regularity Γ Σ ρ x (C0,μ0) (C, μ) H2) as [?l [ ]]...
    exists Σ; steps...
  - (* e_this *)
    admit.
  - (* e_fld *)
    admit.
    (* + (* t_sub *) *)
    (* + (* t_selhot *) *)
    (* + (* t_selwarm *) *)
    (* + (* t_selcool *) *)
  - (* e_mtd *)
    clear H1 H2 H7 H8 H9 H__codom H__codom0 H__codom1 H_wf H_wf0 H H__el H0.
    rename H10 into H__getType, H6 into H__inDom, H4 into H__eT, H5 into H__sT.
    eapply typ_mtd in H3 as
        (?C & ?C & ?e__m & ?Args & ?Flds & ?μ__m & ?μ' & ?μ__r &
           HT__e0 & H__mtdinfo & ? & HT__args & HS__args & [? | (H__hot & ?) ] )...
    + (* t_block *)
      lets (Σ0 & H__mn0 & H__stk0 & H__aty0 & H__st0 & _ & ?) : IHevalP1 HT__e0 H__eT... clear IHevalP1.
      lets H__eT0 : env_typing_monotonicity H__mn0 H__eT ...
      lets (?U1 & ?U2 & ? & ? & ?): H__mn0 H__inDom...
      lets (Σ__args & H__mnargs & H__stkargs & H__atyargs & H__stargs & _ & H__eTargs) : IHevalP2 HT__args H__eT0...
      assert (C2 = C). {
        match goal with
        | H1: getObj ?σ ?v = Some (?C, ?μ),
          H2: ?Σ ⊨ ?σ,
            H3: in_dom ?Σ ?v |- _ =>
          lets (?C & ?ω & ?μ & ? & ? & ?) : H2 v H3 ; meta
      end... } subst.
      unfold methodInfo in *.
      pose proof (typable_classes C) as H__C. steps...
      specialize (H8 _ _ _ _ _ matched0) ...
      lets: H17 H23; steps...
      lets [Σ__m ?]: IHevalP3 H34; steps ... clear IHevalP3.
      exists Σ__m; steps...

      * lets: H27 H23; steps...
      *
    + (* t_block_call *)

    remember (mtd e0 m el) as e.
    induction H1; steps ...
    + (* t_sub *)

      admit.
    + (* t_block *)
      admit.
    + (* t_block_call *)
      admit.
    lets [Σ' ?] : IHevalP1 H11 H2; steps... clear IHT_Expr.
    lets : env_typing_monotonicity H15 H3; clear H0.
    lets [?U1 [?U2 [? [? ?]]]]: H15 H5...
    specialize (IHT_Expr0 Σ' ρ ψ (C1, μ6) σ1 vl2 σ2 H20 H_wf) as [Σ'' [ ]]; steps...

    pose proof (typable_classes C).
    admit.
  - (* t_call_hot *)
    admit.
  - (* tl_nil *)
    exists ([]: list Loc), σ, Σ; steps...
  - (* tl_cons *)
    admit.
Admitted.

Theorem syntactic_soundness: forall Γ U e T,
    ((Γ, U) ⊢ e : T) ->
    forall ρ σ ψ l σ' Σ,
      ⟦e⟧p(σ, ρ, ψ) --> (l, σ') ->
      wf σ ->
      (codom ρ ∪ {ψ} ⪽ σ) ->
      (Γ, Σ) ⊨ ρ ->
      Σ ⊨ σ ->
      (Σ ⊨ ψ : U) ->
      exists Σ',
        Σ ≼ Σ' /\ Σ ≪ Σ' /\ Σ ▷ Σ' /\ (Σ' ⊨ σ') /\ wf σ' /\
          Σ' ⊨ l : T.
Proof with (meta; eauto with typ wf lia; try solve [eexists; eauto with typ]).

  introv H.
  induction H using typing_ind with
    (Pl := fun Γ T el Ul _ => forall Σ ρ ψ (U:Tpe) σ vl σ',
               ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') ->
               wf σ ->
               (codom ρ ∪ {ψ} ⪽ σ) ->
               (Γ, Σ) ⊨ ρ ->
               Σ ⊨ σ ->
               (Σ ⊨ ψ : U) ->
               exists Σ',
                   Σ ≼ Σ' /\ Σ ≪ Σ' /\ Σ ▷ Σ' /\ (Σ' ⊨ σ') /\ wf σ' /\
                   (forall l, List.In l vl -> Σ' ⊨ l : T));
    intros ...
  - (* t_sub *)
    lets  [Σ' ?] : IHT_Expr H0 H1; steps... clear IHT_Expr.
    exists Σ'; steps...
  - (* t_var *)
    pose proof (env_regularity Γ Σ ρ x (C0,μ1) (C, μ) H2) as [?l [ ]]...
    inverts H.
    exists Σ; steps...
  - (* t_this *)
    inverts H.
    exists Σ; steps...
  - (* t_selhot *)
    inverts H0.
    lets [Σ' ?] : IHT_Expr H10 H3; steps... clear IHT_Expr.
    lets [?C [?ω [?μ ?]]]: H12 H15; steps...
    lets [?v [ ]]: hot_selection l1 H13 H12 H19 H__field...
    exists Σ'; steps...
  - (* t_selwarm *)
    inverts H0.
    lets [Σ' ?] : IHT_Expr H10 H3; steps... clear IHT_Expr.
    lets [?C [?ω [?μ ?]]]: H12 H15; steps...
    lets [?v [ ]]: warm_selection l1 H12 H19 H__field...
    exists Σ'; steps...
  - (* t_selcool *)
    inverts H0.
    lets [Σ' ?] : IHT_Expr H10 H3; steps... clear IHT_Expr.
    lets [?C [?ω [?μ ?]]]: H12 H15; steps...
    lets [?v [ ]]: cool_selection l1 Ω H12 H19 H__field...
    exists Σ'; steps...
  - (* t_new *)
    admit.
  - (* t_new_hot *)
    admit.
  - (* t_block *)
    admit.
  - (* t_call *)
    inverts H0. eval_dom; eval_wf.
    lets [Σ' ?] : IHT_Expr H11 H2; steps... clear IHT_Expr.
    lets : env_typing_monotonicity H15 H3; clear H0.
    lets [?U1 [?U2 [? [? ?]]]]: H15 H5...
    specialize (IHT_Expr0 Σ' ρ ψ (C1, μ6) σ1 vl2 σ2 H20 H_wf) as [Σ'' [ ]]; steps...

    pose proof (typable_classes C).
    admit.
  - (* t_call_hot *)
    admit.
  - (* tl_nil *)
    exists ([]: list Loc), σ, Σ; steps...
  - (* tl_cons *)
    admit.
Admitted.

Parameter typable_classes : T_Classes.

Theorem expression_soundness: forall e Γ Σ σ U T ρ ψ,
    ((Γ, U) ⊢ e : T) ->
    (Γ, Σ) ⊨ ρ ->
    Σ ⊨ σ ->
    (Σ ⊨ ψ : U) ->
    wf σ ->
    exists l σ' Σ',
      ⟦e⟧(σ, ρ, ψ) --> (l, σ') /\
        Σ ≼ Σ' /\ Σ ≪ Σ' /\ Σ ▷ Σ' /\ (Σ' ⊨ σ') /\ wf σ' /\
        Σ' ⊨ l : T.
Proof with (meta; eauto with typ; try solve [eexists; eauto with typ]).
  intros. gen Σ ρ ψ σ.
  induction H using typing_ind with
    (Pl := fun Γ T el Ul _ => forall Σ ρ ψ U σ,
               (Γ, Σ) ⊨ ρ ->
               Σ ⊨ σ ->
               (Σ ⊨ ψ : U) ->
               wf σ ->
               exists vl σ' Σ',
                 ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ') /\
                   Σ ≼ Σ' /\ Σ ≪ Σ' /\ Σ ▷ Σ' /\ (Σ' ⊨ σ') /\ wf σ' /\
                   (forall l, List.In l vl -> Σ' ⊨ l : T));
    intros ...
  - (* t_sub *)
    lets  [l [σ' [Σ' ?]]] : IHT_Expr H0 ψ H1; steps... clear IHT_Expr.
    exists l, σ', Σ'; steps...
  - (* t_var *)
    pose proof (env_regularity Γ Σ ρ x (C0,μ1) (C, μ) H0) as [?l [ ]]...
    exists l, σ, Σ; steps...
    apply e_var...
  - (* t_this *)
    exists ψ, σ, Σ; steps...
  - (* t_selhot *)
    lets [l [σ' [Σ' ?]]] : IHT_Expr H0 ψ H1; steps... clear IHT_Expr.
    lets [?C [?ω [?μ ?]]]: H10 H13; steps...
    lets [?v [ ]]: hot_selection l H11 H10 H15 H__field...
    exists v σ' Σ'; steps...
    eapply e_fld...
  - (* t_selwarm *)
    lets [l [σ' [Σ' ?]]] : IHT_Expr H0 ψ H1; steps... clear IHT_Expr.
    lets [?C [?ω [?μ ?]]]: H10 H13; steps...
    lets [?v [ ]]: warm_selection l H10 H15 H__field...
    exists v σ' Σ'; steps...
    eapply e_fld...
  - (* t_selcool *)
    lets [l [σ' [Σ' ?]]] : IHT_Expr H0 ψ H1; steps... clear IHT_Expr.
    lets [?C [?ω [?μ ?]]]: H10 H13; steps...
    lets [?v [ ]]: cool_selection l Ω H10 H15 H__field...
    exists v σ' Σ'; steps...
    eapply e_fld...
  - (* t_new *)
    admit.
  - (* t_new_hot *)
    admit.
  - (* t_block *)
    admit.
  - (* t_call *)
    lets [l [σ' [Σ' ?]]] : IHT_Expr H0 ψ H1; steps... clear IHT_Expr.
    lets [U1 [U2 [? [ ]]]]: H5 ψ H2 ...
    clear H1 H3 H6 H2 H14.
    lets : env_typing_monotonicity H5 H0; clear H0.
    lets [?C [?ω [?μ ?]]]: H10 H13; steps...
    specialize (IHT_Expr0 Σ' ρ ψ C1 σ' H1 H10) as [vl [σ'' [Σ'' [ ]]]]; steps... exists μ4 ...
    pose proof (typable_classes C).
    admit.
  - (* t_call_hot *)
    admit.
  - (* tl_nil *)
    exists ([]: list Loc), σ, Σ; steps...
  - (* tl_cons *)
    admit.
Admitted.
