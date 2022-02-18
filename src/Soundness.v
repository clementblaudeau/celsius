(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines and proves the soundess of the type system. *)

From Celsius Require Export LocalReasoning Eval.
Require Import ssreflect ssrbool Psatz Sets.Ensembles List Coq.Sets.Finite_sets_facts Coq.Program.Tactics.
Import ListNotations Arith.
Open Scope nat_scope.


Local Hint Constructors evalP: typ.
Local Hint Constructors T_Expr: typ.

Parameter typable_classes: T_Classes.

(** ** Weakening *)


Lemma S_Typs_weakening:
  forall Γ Γ',
    S_Typs Γ' Γ ->
    forall x T__x, typeLookup Γ x = Some T__x -> exists T__x', typeLookup Γ' x = Some T__x' /\ T__x' <: T__x.
Proof with (meta; eauto with typ).
  intros. gen x T__x.
  induction H; steps.
  - destruct x; steps.
  - destruct x; steps...
Qed.
Global Hint Resolve S_Typs_weakening: typ.


Theorem weakening: forall Γ Γ' U e T,
    (forall x T__x, typeLookup Γ x = Some T__x -> exists T__x', typeLookup Γ' x = Some T__x' /\ T__x' <: T__x) ->
    ((Γ, U) ⊢ e : T) ->
    ((Γ', U) ⊢ e : T).
Proof with (meta; eauto using T_Exprs with typ lia).
  intros. gen Γ'.
  induction H0 using typing_ind with
    (Pl := fun Γ0 T0 el Ul _ =>
             forall Γ',
               (forall x T__x, typeLookup Γ0 x = Some T__x -> exists T__x', typeLookup Γ' x = Some T__x' /\ T__x' <: T__x) ->
               ((Γ0, T0) ⊩ el : Ul) ->
               ((Γ', T0) ⊩ el : Ul));
    intros ...
  eapply H in H__lkp as [T__x' [ ]]...
Qed.

Lemma P_Hots_env:
  forall Args l args_val Σ1,
    P_hots Args ->
    (Args, Σ1) ⊨ args_val ->
    l ∈ codom args_val ->
    Σ1 ⊨ l : hot.
Proof with (meta; eauto with typ).
  induction Args; intros; steps;
    inverts H0; inverts H1; simpl in * ...
  - inverts H.
    unfold P_hot in H6; steps ...
    exists C. eapply vt_sub ...
  - inverts H ...
Qed.
Global Hint Resolve P_Hots_env: typ.


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

(* Expr soundness trans lemma *)

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

Definition init_soundness n C flds I ρ σ Γ Σ r :=
  forall Args Flds Mtds ω DoneFlds,
    (Γ, Σ) ⊨ ρ ->
    Σ ⊨ σ ->

    wf σ ->
    (codom ρ ∪ {I} ⪽ σ) ->

    ct C = class Args Flds Mtds ->
    getObj σ I = Some (C, ω) ->
    dom ω + dom flds = dom Flds ->
    DoneFlds ++ flds = Flds ->
    getType Σ I = Some (C, cool (dom ω)) ->

    init C flds I ρ σ n = r ->
    r <> Timeout_i ->

    exists Σ' σ' ω',
      r = Success_i σ' /\
        Σ ≼ Σ' /\ Σ ≪ Σ' /\ ([I↦(C,cool (dom Flds))]Σ ▷ Σ') /\ (Σ' ⊨ σ') /\ wf σ' /\
        getObj σ' I = Some (C, ω') /\
        dom ω' = dom Flds /\
        getType Σ' I = Some (C, cool (dom Flds)) /\
        ( forall L σ0,
            (* Hypothesis *)
            ((σ0, L) ⋖ (σ, (codom ρ) ∪ {I})) ->
            (σ0 ⇝ σ ⋖ L) ->
            dom σ0 <= dom σ ->
            (* Conclusions *)
            ((σ0, L) ⋖ (σ', (codom ρ) ∪ {I})) /\
              (σ0 ⇝ σ' ⋖ L)).


Theorem soundness:
  forall n,
    (forall e ρ σ ψ r Γ Σ U T,
        expr_soundness n e ρ σ ψ r Γ Σ U T) /\
    (forall el ρ σ ψ r Γ Σ U Tl,
      expr_list_soundness n el ρ σ ψ r Γ Σ U Tl) /\
    (forall C flds I ρ σ Γ Σ r,
       init_soundness n C flds I ρ σ Γ Σ r).
Proof with (
    meta;
    meta_clean;
    eauto 4 with typ wf lia;
    try match goal with
        | |- ?Σ ⊨ ?l : ?T => try solve [eapply vt_sub; eauto with typ]
        end
  ).
  induction n as [n IHn] using lt_wf_ind. destruct n;
    intros; unfold expr_soundness, expr_list_soundness, init_soundness; splits; intros;
    [steps | steps | steps | destruct e | destruct el | destruct flds ]; subst;
    simpl in *;
    try specialize (IHn n ltac:(lia)) as [IH__expr [IH__list IH__init]]...

  - (* e = var x *)
    eapply env_regularity in H as (?l & ?H__get & ?)...
    rewrite H__get in H6 |- * ...
    exists Σ, l, σ; steps...

  - (* e = this *)
    eapply t_this_inv in H.
    exists Σ, ψ, σ; steps...

  - (*  e = fld e f *)
    rename v into f.
    (* Induction on the typing judgment *)
    eapply t_fld_inv in H as
        (D & μ__e & μ__f & HT__e & H__fieldType & H__mode) ...
    destruct (ct D) as [Args Flds Mtds] eqn:H__ct.

    (* Destruct evaluation of e *)
    destruct_eval H__eval v' σ';
      lets (Σ0 & v0 & σ0 & H__r & H__mn0 & H__stk0 & H__aty0 & H__st0 & H__wf0 & H__v0) :
      IH__expr HT__e H0 H1 H3 H__eval; try inverts H__r; try congruence ...
    eapply eval_implies_evalp in H__eval.
    lets (?C & ?ω & ?μ & H__obj & ? & H__ot): (proj2 H__st0) v0 ...
    rewrite H__obj in H6 |- *.

    (* Case analysis *)
    destruct H__mode as [ ? |[ [? ?] | [Ω [? [? ?]]]]]; subst...
    + (* hot *)
      inverts H__ot...
      lets [v1 [ ]]: H13 H__fieldType... rewrite_any.
      exists Σ0, v1, σ0; splits ...
    + (* warm *)
      inversion H11; subst;
        inverts H__ot;
        lets [v1 [ ]]: H15 H__fieldType...
      all: rewrite_any.
      all: exists Σ0, v1, σ0; splits ...
    + (* cool Ω *)
      inversion H11; subst;
        inverts H__ot.
      * (* cool Ω *)
        destruct (getVal ω f) as [v1 |] eqn:H__getVal; [|apply nth_error_None in H__getVal] ...
        lets: H16 H__getVal H__fieldType...
        exists Σ0, v1, σ0; splits ...
      * (* hot *)
        lets [v1 [ ]]: H16 H__fieldType... rewrite_any.
        exists Σ0, v1, σ0; splits ...
      * (* warm *)
        lets [v1 [ ]]: H16 H__fieldType... rewrite_any.
        exists Σ0, v1, σ0; splits ...
      * (* cool Ω1 + Ω2 *)
        destruct (getVal ω f) as [v1 |] eqn:H__getVal; [|apply nth_error_None in H__getVal] ...
        lets: H16 H__getVal H__fieldType...
        exists Σ0, v1, σ0; splits ...

  - (* e = mtd e m l *)
    rename l into args.
    (* Induction on the typing judgment *)
    eapply t_mtd_inv in H as
        (?C & ?C & ?e__m & ?Args & ?Flds & ?μ__m & ?μ' & ?μ__r &
           HT__e0 & H__mtdinfo & ? & HT__args & HS__args & H__sub & H__hots) ...

    (* Destruct evaluation of e0 *)
    destruct_eval H__eval0 v σ';
      lets (Σ0 & v0 & σ0 & H__r & H__mn0 & H__stk0 & H__aty0 & H__st0 & H__wf0 & H__v0) :
      IH__expr HT__e0 H0 H1 H3 H__eval0; try inverts H__r; try congruence ...
    eapply eval_implies_evalp in H__eval0.
    lets H__pM0: pM_theorem H__eval0.
    lets (?C & ?ω & ?μ & H__obj & ? & ?): (proj2 H__st0) v0 ...
    rewrite H__obj in H6 |- *.

    (* Destruct method fetch*)
    unfold methodInfo in H__mtdinfo.
    destruct (ct C1) as [Args1 Flds1 Mtds1] eqn:H__ct1.
    destruct (Mtds1 m) as [[?μ__r Ts retT ?] |] eqn:H__Mtds1; [| steps] . inverts H__mtdinfo...

    (* Destruct evaluation of arguments *)
    lets H__env0: env_typing_monotonicity H__mn0 H0.
    eval_dom. eval_wf...
    lets (?T & ?T & ? & ? & ?): H__mn0 ψ ...
    destruct_eval H__eval1 vl σ';
      lets (Σ1 & args_val & σ1 & H__r & H__mn1 & H__stk1 & H__aty1 & H__st1 & H__wf1 & H__v1) :
      IH__list HT__args H__env0 H__st0 H__wf0 H__eval1; try inverts H__r; try congruence ...
    eapply eval_list_implies_evalp in H__eval1. eval_dom; eval_wf.

    (* Extract typing for method body from Ξ (well-typed) *)
    pose proof (typable_classes C1) as HT__em.
    rewrite H__ct1 in HT__em.
    destruct HT__em as [_ HT__em].
    specialize (HT__em m _ _ _ _ H__Mtds1).

    (* Destruct evaluation of method body *)
    lets (?T & ?T & ? & ? & ?): H__mn1 ψ...
    lets (?T & ?T & ? & ? & ?): H__mn1 v0...
    assert (HT__em': (Args, (C1, μ__m)) ⊢ e__m : (C, μ__r)) by (eapply weakening with (Γ := Flds); eauto with typ).
    assert (codom args_val ∪ {v0} ⪽ σ1). { ss... eapply wf_theorem_list... }
    destruct (⟦ e__m ⟧ (σ1, args_val, v0 )( n)) as [ | | σ' v' ] eqn:H__eval2; try congruence;
    lets (Σ2 & v2 & σ2 & H__r & H__mn2 & H__stk2 & H__aty2 & H__st2 & H__wf2 & H__v2) :
      IH__expr HT__em' H__v1 H__st1 H__wf1 H__eval2; try inverts H__r; try congruence ...
    eapply eval_implies_evalp in H__eval2. clear H6.

    (* Result *)
    eval_dom; eval_wf.
    destruct H__hots as [? | [ H__hots ?] ]...
    + exists Σ2, v2, σ2; splits...
    + (* Local reasoning *)
      subst...
      destruct (local_reasoning2 Σ1 Σ2 σ1 σ2 (codom args_val ∪ { v0 }) {v2} ) as
        (Σ3 & ? & ? & ? & ? & H__v2)...
      * apply scp_theorem with (e:=e__m); eauto with wf lia.
      * intros l' [l H__l | l H__l]; rch_set; [| exists C1]...
      * lets: H__v2 v2 In_singleton...
        lets (? & ? & ? & ? & ?): H12 v2...
        exists Σ3, v2, σ2; splits...

  - (* e = new C l *)
    rename l into args.

    (* Induction on the typing judgment *)
    eapply t_new_inv in H as
        (Args & Flds & Mtds & argsTs & ?μ & ? & H__ct & HT__args & HS__args & H__mode) ...

    (* Destruct evaluation of arguments *)
    destruct_eval H__eval1 vl σ';
      lets (Σ1 & args_val & σ1 & H__r & H__mn1 & H__stk1 & H__aty1 & H__st1 & H__wf1 & H__argsval) :
      IH__list HT__args H0 H1 H3 H__eval1; try inverts H__r; try congruence ...
    inverts H... rename c into C.
    rewrite H__ct in H6 |- *.
    eapply eval_list_implies_evalp in H__eval1...

    (* Destruct result of initialization *)
    remember (Σ1 ++ [(C, cool 0)]) as Σ2.
    remember (σ1 ++ [(C, [])]) as σ2...
    assert ((codom args_val ∪ {dom σ1}) ⪽ σ2). {
      subst; ss; updates... apply ss_trans with σ1; updates...
      eapply wf_theorem_list... }
    assert (H__mn2:  Σ1 ≼ Σ2). {
        subst. intros l0 H__l0.
        lets [T ?]: getType_Some H__l0. exists T, T; splits...
        rewrite getType_last2... }
    lets H__env2: env_typing_monotonicity H__mn2 H__argsval.
    assert (H__st2: Σ2 ⊨ σ2). { (* could be a lemma *)
      subst. split; updates...
      intros l H__l.
      destruct_eq (l = dom σ1); subst; updates.
      - rewrite (proj1 H__st1) getType_last.
        exists C ([]:Env) (cool 0); splits...
        apply ot_cool; simpl => //.
        intros [ ] ? ? ? Hf; inverts Hf.
      - rewrite getObj_last2...
        rewrite getType_last2...
        lets (?C & ?ω & ?μ & ? & ? & ?): (proj2 H__st1) l...
        repeat eexists... }
    lets H__wf2: wf_add_empty C H__wf1. rewrite -Heqσ2 in H__wf2.
    lets: getObj_last σ1 C ([]: Env).
    destruct (init C Flds dom σ1 args_val (σ1 ++ [(C, [])]) n) as [ | | σ3] eqn:Heq;
      rewrite Heq in H6 |- *; try congruence;
    specialize (IH__init C Flds (dom σ1) args_val σ2 argsTs Σ2);
      lets (Σ4 & σ4 & ω4 & H__r & H__mn4 & H__stk4 & H__aty4 & H__st4 & H__wf4 & H__obj4 & H__dom4 & H__getType4 & H__scp4):
      IH__init ([]: list Field) H__env2 H__st2 H__ct; subst; simpl...
    all: try solve [intros; discriminate].
    all: try solve [rewrite (proj1 H__st1) getType_last; simpl; reflexivity].
    inverts H__r.

    (* Promotion *)
    remember ([dom σ1 ↦ (C, warm)] (Σ4)) as Σ5.
    assert (H__stk5: Σ4 ≪ Σ5). {
      subst.
      intros l H__l. updates... }
    assert (H__mn5: Σ4 ≼ Σ5). {
      intros l H__l. subst.
      lets (? & ?): getType_Some Σ4 l... exists (C1, μ).
      destruct_eq (dom σ1 = l); subst; updates...
      exists (C, warm)... }
    assert (H__aty4': Σ1 ▷ Σ4). {
      intros l ? ? H__getType.
      lets: getType_dom H__getType.
      assert (l <> dom Σ1) by lia.
      apply H__aty4...
      rewrite getType_update_diff...
      rewrite getType_last2... }
    pose proof (promotion Σ1 Σ4 C (dom σ1) σ4 Args Flds Mtds) as H__promotion...
    lets (H__aty5 & H__mn5' & H__st5): H__promotion H__ct Σ5... clear H__promotion.

    (* Case analysis : warm or hot *)
    destruct H__mode as [H__warm | H__hots].
    + (* warm *)
      exists Σ5, (dom σ1), σ4; splits...
      * eapply stk_st_trans with Σ1...
        intros l H__l; subst; updates.
        destruct_eq (dom σ1 = l); subst; updates.
        -- left; exists C, (C, warm); updates...
        -- lets [ ]: H__stk4 H__l; updates...
           inverts H11. inverts H12. left. exists C1, (C1, μ); updates...
      * exists (C, warm); subst; updates...

    + (* hot *)
      eapply init_implies_initP in Heq. eval_dom. updates...
      destruct (local_reasoning2 Σ1 Σ5 σ1 σ4 (codom args_val) {dom σ1} ) as
        (Σ6 & ? & ? & ? & ? & H__vnew)...
      * eapply wf_theorem_list...
      * lets (? & ? & ? & ? & ?): scp_theorem_init Heq (codom args_val ∪ {dom σ1}) (σ1++[(C,[])]);
          eauto with scp... unfold scoping_preservation; steps.
        intros ? ? l H__l H__rch. ss.
        assert ((σ1 ++ [(C, [])]) ⊨ codom args_val ∪ {dom σ1} ⇝ l). {
          apply H12; updates... eapply ss_trans with (σ1++[(C,[])]); updates...
          rch_set. exists (dom σ1); split; eauto with ss. }
        eapply rch_add_empty_set in H17 as [|]...
        inversion H17 as (l' & ? & H__rch').
        lets: reachability_dom2 H__rch'.
        inverts H18; rch_set...
        exists l'; splits; eauto with ss.
      * intros l H__l.
        lets [|] : H__stk4 l;  updates...
        ++ left.
           lets (?T & ?T & ? & ? & ?): H__mn5 l...
           eexists. eexists...
        ++ assert (l = dom σ1 \/ l < dom σ1) as [|] by lia...
           subst. left. eexists. eexists; updates...
      * intros l H__l.
        eapply P_Hots_env...
      * exists Σ6, (dom σ1), σ4; splits...
        -- apply stk_st_trans with Σ1...
           apply stk_st_trans with Σ5... subst.
           intros l H__l...
           lets [|] : H__stk4 l...
           ++ left. lets (?T & ?T & ? & ? & ?): H__mn5 l...
              eexists...
           ++ updates.
              assert (l = dom σ1 \/ l < dom σ1) as [|] by lia...
              subst. left.
              exists C, (C, warm); updates...
        -- exists (C, hot)...
           lets: H__vnew (dom σ1) In_singleton... inverts H16. inverts H17. meta.
           assert (x = C); subst...
           lets (? & ? & ? & ? & ? & ?): (proj2 H15) (dom σ1)...
  - (* e = e1.f = e2; e3 *)
    rename v into f.

    (* Induction on typing derivation *)
    eapply t_asgn_inv in H as
        (D & ? & ? & HT__e1 & HT__e2 & ? & HT__e3) ...
    eapply t_fld_inv in HT__e1 as
        (?D & μ__e & μ__f & HT__e1 & H__fieldType & H__mode) ...

    (* Destruct evaluation of e1 *)
    destruct_eval H__eval1 v' σ';
      lets (Σ1 & v1 & σ1 & H__r & H__mn1 & H__stk1 & H__aty1 & H__st1 & H__wf1 & H__v1) :
      IH__expr HT__e1 H0 H1 H3 H__eval1; try inverts H__r; try congruence ...
    eapply eval_implies_evalp in H__eval1.
    lets (?C & ?ω & ?μ & H__obj & ? & H__ot): (proj2 H__st1) v1 ...

    (* Destruct evaluation of e2 *)
    lets (?T & ?T & ? & ? & ?): H__mn1 ψ ...
    lets H__env1: env_typing_monotonicity H__mn1 H0.
    eval_dom. eval_wf...
    destruct_eval H__eval2 v' σ';
      lets (Σ2 & v2 & σ2 & H__r & H__mn2 & H__stk2 & H__aty2 & H__st2 & H__wf2 & H__v2) :
      IH__expr HT__e2 H__env1 H__st1 H__wf1 H__eval2; try inverts H__r; try congruence ...
    eapply eval_implies_evalp in H__eval2. eval_dom; eval_wf.
    lets (?T & ?T & ? & ? & ?): H__mn2 ψ ...

    (* Destruct assignment *)
    unfold assign in *.
    destruct (getObj σ2 v1) as [[?C ?ω] |] eqn:H__getObj.

    + (* Useful assignment *)
      remember ([v1 ↦ (C1, [f ↦ v2] (ω0))] (σ2)) as σ2'. rewrite -Heqσ2' in H6.
      assert (H__st2': Σ2 ⊨ σ2'). {
        subst. rename v1 into l, v2 into v.
        lets [?ω [H__obj2 _]]: pM_theorem H__eval2 H__obj.
        lets [v0 [H__v0 ?]]: cool_selection D0 l H__st2 H__obj2... {
          lets (?T & ?T & ? & ? & ?): H__mn2 l...
          steps...
          apply vt_sub with (C1, μ5)...
          apply s_typ_mode...
          eapply s_mode_trans...
          eapply s_mode_trans...
          apply s_mode_cool...
        }
        meta.
        eapply storeTyping_assgn with (μ0 := μ5) ...
      }
      assert (H__wf2': wf σ2') by (subst; eapply wf_assign; eauto).
      assert (H__codom' : (codom ρ ∪ {ψ}) ⪽ σ2'). by (subst; ss).
      destruct (⟦ e3 ⟧ (σ2', ρ, ψ )( n)) as [ | | σ' v' ] eqn:H__eval3; try congruence;
        lets (Σ3 & v3 & σ3 & H__r & H__mn3 & H__stk3 & H__aty3 & H__st3 & H__wf3 & H__v3) :
        IH__expr HT__e3 H__st2' H__eval3; try inverts H__r; try congruence ...
      (* eapply eval_implies_evalp in H__eval3. eval_dom; eval_wf.*)
      subst.
      exists Σ3, v3, σ3; subst; splits...

    + (* Useless assignment *)
      destruct (⟦ e3 ⟧ (σ2, ρ, ψ )( n)) as [ | | σ' v' ] eqn:H__eval3; try congruence;
        lets (Σ3 & v3 & σ3 & H__r & H__mn3 & H__stk3 & H__aty3 & H__st3 & H__wf3 & H__v3) :
        IH__expr HT__e3 H__st2 H__wf2 H__eval3; try inverts H__r; try congruence ...
      eapply eval_implies_evalp in H__eval3. eval_dom; eval_wf.
      exists Σ3, v3, σ3; splits...

  - (* el = nil *)
    inverts H.
    exists Σ, ([]: list Loc), σ; splits...
    apply et_nil.

  - (* el = e::el *)
    inverts H ...

    (* Destruct evaluation of head *)
    destruct_eval H__eval v' σ';
      lets (Σ0 & v & σ0 & H__r & H__mn0 & H__stk0 & H__aty0 & H__st0 & H__wf0 & H__v0) :
      IH__expr H14 H0 H1 H3 H__eval; try inverts H__r; try congruence ...
    eapply eval_implies_evalp in H__eval. eval_dom.

    (* Destruct evaluation of tail *)
    lets (?T & ?T & ? & ? & ?): H__mn0 ψ...
    lets H__env0: env_typing_monotonicity H__mn0 H0.
    destruct (⟦_ el _⟧ (σ0, ρ, ψ )( n)) as [ | | σ' vl' ] eqn:H__eval1; try congruence;
    lets (Σ1 & vl & σ1 & H__r & H__mn1 & H__stk1 & H__aty1 & H__st1 & H__wf1 & H__v1):
      IH__list H12 H__env0 H__st0 H__wf0 H__eval1; try inverts H__r; try congruence ...

    (* Result *)
    exists Σ1, (v::vl), σ1; splits...
    lets (?T & ?T & ? & ? & ?): H__mn1 v ...
    apply et_cons...

  - (* init [] *)
    updates. simpl in *. repeat rewrite Nat.add_0_r in H5 |- *.
    exists Σ, σ, ω. splits...
    + intros l ?C Ω H__getType.
      destruct_eq (I = l); subst; updates...
      rewrite getType_update_same in H__getType... steps.
    + splits... congruence.

  - (* init_cons *)
    destruct f as [μ__f e].

    (* Extract typing from the well-typed classes *)
    pose proof (typable_classes C) as HT__C. rewrite H3 in HT__C.
    destruct HT__C as [HT__Field _].
    eapply T_Fields_In in HT__Field. unfold T_Field in HT__Field.
    eapply weakening with (Γ' := Γ) in HT__Field; [| intros [ ] Tx Hf; inverts Hf].
    rename HT__Field into HT__e.
    updates.
    assert (H__doms: dom DoneFlds = dom ω). {
      eapply plus_reg_l.
      rewrite Nat.add_comm.
      rewrite <- H5... } rewrite H__doms in HT__e |- *.

  (* Destruct evaluation of e *)
    destruct_eval H__eval v' σ';
      lets (Σ0 & v0 & σ0 & H__r & H__mn0 & H__stk0 & H__aty0 & H__st0 & H__wf0 & H__v0) :
       IH__expr HT__e H0 H1 H2 H__eval; try inverts H__r; try congruence ...
    eapply eval_implies_evalp in H__eval.
    lets H__eM: eM_theorem H__eval. lets [ω' [ ]]: H__eM H4.
    lets: monotonicity_dom H__mn0.
    lets (? & ? & ? & ? & ?): H__mn0 I...
    lets (?C & ?ω & ?μ & ? & ? & ?): (proj2 H__st0) I...
    eval_dom; eval_wf.

    (* Use field initialization lemma *)
    unfold assign_new in *.
    rewrite H7 in H9 |- *.
    lets H__env0: env_typing_monotonicity H__mn0 H.
    clear IH__expr IH__list.
    lets: H__aty0 I H15.
    assert (H__field: fieldType C (dom ω) = Some (C0, μ)). {
      unfold fieldType. rewrite H3.
      rewrite nth_error_app2... rewrite H__doms -minus_diag_reverse.
      simpl => //.
    }
    rewrite H12 in H10, H__field.
    remember ([I ↦ (C, cool (S dom ω'))] (Σ0)) as Σ1.
    remember ([I ↦ (C, ω' ++ [v0])] (σ0)) as σ1.
    lets (H__st1 & H__mn1 & H__stk1): field_initialization v0 H__st0 H10 H__field Σ1;
      unfold assign_new; auto; [|steps|]...

    (* Use induction hypothesis *)
    lets: env_typing_monotonicity H__mn1 H__env0.
    assert ( wf [I ↦ (C, ω' ++ [v0])] (σ0)). {
      eapply wf_assign_new with (flds := flds)... updates... }
    specialize (IH__init
                  C flds I ρ
                  σ1
                  Γ Σ1
                  (init C flds I ρ σ1 n)
                  Args (DoneFlds++(field (C0,μ) e)::flds) Mtds
                  (ω'++[v0])
                  (DoneFlds ++ [field (C0, μ) e])).
    subst; modus.
    destruct IH__init
      as (Σ2 & σ2 & ω2 & H__r & H__mn2 & H__stk2 & H__aty2 & H__st2 & H__wf2 & H__obj2 & H__dom2 & H__getType2 & H__scp2)...
    + rewrite getObj_update_same...
    + updates...
    + rewrite app_assoc_reverse. simpl => //.
    + rewrite getType_update_same; updates...
      rewrite Nat.add_1_r...
    + (* Result *)
      updates.
      rewrite H__doms in H__aty2, H__getType2.
      lets H__initP: H__r.
      eapply init_implies_initP in H__initP.
      lets H__scpInit: scp_theorem_init H__initP.
      lets [ ]: scp_theorem H__eval...
      exists Σ2, σ2, ω2; splits...
      * intros l ?C Ω H__getType.
        destruct_eq (I = l); subst; updates.
        -- rewrite getType_update_same in H__getType... steps.
        -- eapply H__aty0 in H__getType.
           eapply H__aty2. updates...
      * splits...
        intros.
        eapply H__scp2...
        -- eapply scp_add_env; eauto with lia wf; updates.
           ++ apply H23.
           ++ eapply scp_trans; eauto with scp.
           ++ eapply scp_trans; eauto with scp.
        -- eapply scp_pr_trans; eauto.
           eapply scp_pr_trans; eauto.
           unfold scoping_preservation; intros; eauto with scp.
Qed.

Corollary Soundness :
  forall n e ρ σ ψ r Γ Σ U T,
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
        Σ ≼ Σ' /\
        Σ ≪ Σ' /\
        Σ ▷ Σ' /\
        (Σ' ⊨ σ') /\
        Σ' ⊨ v : T.
Proof with (eauto with typ).
  intros.
  lets [(Σ'& v& σ'& ?) _]: soundness n... steps.
  exists Σ', v, σ'; splits...
Qed.
