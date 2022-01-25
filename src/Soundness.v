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
    lets (?C & ?ω & ?μ & H__obj & ? & ?): (proj2 H__st0) v0 ...
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

    (* Destruct evaluation of arguments *)
    lets H__env0: env_typing_monotonicity H__mn0 H0.
    eval_dom. eval_wf2...
    lets (?T & ?T & ? & ? & ?): H__mn0 ψ ...
    destruct_eval H__eval1 vl σ';
      lets (Σ1 & args_val & σ1 & H__r & H__mn1 & H__stk1 & H__aty1 & H__st1 & H__wf1 & H__v1) :
      IH__list HT__args H__env0 H__st0 H__wf0 H__eval1; try inverts H__r ...
    eapply eval_list_implies_evalp in H__eval1. eval_dom; eval_wf2.

    (* Destruct evaluation of method body *)
    lets (?T & ?T & ? & ? & ?): H__mn1 ψ...
    lets (?T & ?T & ? & ? & ?): H__mn1 v0...
    assert (HT__em': (Args, (C1, μ__m)) ⊢ e__m : (C, μ__r)) by admit.
    destruct (⟦ e__m ⟧ (σ1, args_val, v0 )( n)) as [ | | σ' v' ] eqn:H__eval2; try congruence;
    lets (Σ2 & v2 & σ2 & H__r & H__mn2 & H__stk2 & H__aty2 & H__st2 & H__wf2 & H__v2) :
      IH__expr HT__em' H__v1 H__st1 H__wf1 H__eval2; try inverts H__r ... admit. admit.
    eapply eval_implies_evalp in H__eval2. clear H6.

    (* Result *)
    destruct H__hots as [? | [ H__hots ?] ]...
    + exists Σ2, v2, σ2; splits...
    + (* Local reasoning *)
      subst...
      destruct (local_reasoning2 Σ1 Σ2 σ1 σ2 (codom args_val ∪ { v0 }) {v2} ) as
        (Σ3 & ? & ? & ? & ? & H__v2)...
      * admit.
      * admit.
      * admit.
      * lets: H__v2 v2 In_singleton...
        lets (? & ? & ? & ? & ?): H6 v2...
        exists Σ3, v2, σ2; splits...

  - (* e = new C l *)
    admit.

  - (* e = e1.f = e2; e3 *)
    admit.

  - (* el = nil *)
    inverts H.
    exists Σ, ([]: list Loc), σ; splits...
    apply et_nil.

  - (* el = e::el *)
    specialize (IHn n ltac:(lia)) as [IH__expr IH__list]...
    inverts H ...

    (* Destruct evaluation of head *)
    destruct_eval H__eval v' σ';
      lets (Σ0 & v & σ0 & H__r & H__mn0 & H__stk0 & H__aty0 & H__st0 & H__wf0 & H__v0) :
      IH__expr H14 H0 H1 H3 H__eval; try inverts H__r ...
    eapply eval_implies_evalp in H__eval. eval_dom.

    (* Destruct evaluation of tail *)
    lets (?T & ?T & ? & ? & ?): H__mn0 ψ...
    lets H__env0: env_typing_monotonicity H__mn0 H0.
    destruct (⟦_ el _⟧ (σ0, ρ, ψ )( n)) as [ | | σ' vl' ] eqn:H__eval1; try congruence;
    lets (Σ1 & vl & σ1 & H__r & H__mn1 & H__stk1 & H__aty1 & H__st1 & H__wf1 & H__v1):
      IH__list H12 H__env0 H__st0 H__wf0 H__eval1; try inverts H__r ...
    exists Σ1, (v::vl), σ1; splits...

    (* Result *)
    lets (?T & ?T & ? & ? & ?): H__mn1 v ...
    apply et_cons...

Admitted.
