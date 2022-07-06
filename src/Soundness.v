(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines and proves the soundess of the type system. *)

From Celsius Require Export LocalReasoning Eval.
Implicit Type (ρ: Env).

Local Hint Constructors evalP: typ.
Local Hint Constructors expr_typing: typ.
Local Hint Constructors expr_list_typing: typ.

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
Proof with (meta; eauto using expr_typing with typ lia).
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
    Σ1 ⊨ args_val : Args ->
    l ∈ codom args_val ->
    Σ1 ⊨ l : hot.
Proof with (meta; eauto with typ).
  induction Args; intros; steps;
    inverts H0; inverts H1; simpl in * ...
  - inverts H.
    unfold P_hot in H6; steps ...
    exists c. eapply vt_sub ...
  - inverts H ...
Qed.
Global Hint Resolve P_Hots_env: typ.

Definition expr_soundness n e ρ σ ψ r Γ Σ U T :=
    ((Γ, U) ⊢ e : T) ->
    Σ ⊨ ρ : Γ ->
    Σ ⊨ σ ->
    (Σ ⊨ ψ : U) ->
    wf σ ->
    (codom ρ ∪ {ψ} ⪽ σ) ->
    ⟦e⟧(σ, ρ, ψ, n) = r ->
    r <> Timeout ->
    exists Σ' v σ',
      r = Success v σ' /\
        Σ ≼ Σ' /\ Σ ≪ Σ' /\ Σ ▷ Σ' /\ (Σ' ⊨ σ') /\ wf σ' /\
        Σ' ⊨ v : T.

(* Expr soundness trans lemma *)

Definition expr_list_soundness n el ρ σ ψ r Γ Σ U Tl :=
    ((Γ, U) ⊩ el : Tl) ->
    Σ ⊨ ρ : Γ ->
    Σ ⊨ σ ->
    (Σ ⊨ ψ : U) ->
    wf σ ->
    (codom ρ ∪ {ψ} ⪽ σ) ->
    ⟦_ el _⟧(σ, ρ, ψ, n) = r ->
    r <> Timeout_l ->
    exists Σ' vl σ',
      r = Success_l vl σ' /\
        Σ ≼ Σ' /\ Σ ≪ Σ' /\ Σ ▷ Σ' /\ (Σ' ⊨ σ') /\ wf σ' /\
        Σ' ⊨ vl : Tl.

Definition init_soundness n C flds I x ρ σ Γ Σ r :=
  forall Args Flds Mtds DoneFlds,
    Σ ⊨ ρ : Γ ->
    Σ ⊨ σ ->

    wf σ ->
    (codom ρ ∪ {I} ⪽ σ) ->

    ct C = class Args Flds Mtds ->
    Flds = DoneFlds ++ flds ->
    length DoneFlds = x ->
    getType Σ I = Some (C, cool x) ->

    init C flds I x ρ σ n = r ->
    r <> Timeout_i ->

    exists Σ' σ',
      r = Success_i σ' /\
        Σ ≼ Σ' /\ Σ ≪ Σ' /\ ([I↦(C,cool (dom Flds))]Σ ▷ Σ') /\ (Σ' ⊨ σ') /\ wf σ' /\
        getType Σ' I = Some (C, cool (dom Flds)).

Lemma soundness_fld:
  forall n,
    (forall e ρ σ ψ r Γ Σ U T,
        expr_soundness n e ρ σ ψ r Γ Σ U T) /\
    (forall el ρ σ ψ r Γ Σ U Tl,
      expr_list_soundness n el ρ σ ψ r Γ Σ U Tl) /\
    (forall C flds I x ρ σ Γ Σ r,
        init_soundness n C flds I x ρ σ Γ Σ r) ->
    (forall e f ρ σ ψ r Γ Σ U T,
        expr_soundness (S n) (e_fld e f) ρ σ ψ r Γ Σ U T).
Proof with (meta; meta_clean; eauto 2 with typ;
            try match goal with
                | |- ?Σ ⊨ ?l : ?T => try solve [eapply vt_sub; eauto with typ]
                end).
  intros n [IH__expr [IH__list IH__init]];
    unfold expr_soundness, expr_list_soundness, init_soundness; intros.
  simpl in *...

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
  rewrite H__obj in H5 |- *.

  (* Case analysis *)
  destruct H__mode as [ ? | [Ω [? [? ?]]]]; subst...
  + (* hot *)
    inverts H__ot...
    lets [v1 [ ]]: H13 H__fieldType... rewrite_any.
    exists Σ0, v1, σ0; splits ...
  + (* cool Ω *)
    inversion H12; subst;
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
Qed.

Lemma soundness_mtd:
  forall n,
    (forall e ρ σ ψ r Γ Σ U T,
        expr_soundness n e ρ σ ψ r Γ Σ U T) /\
      (forall el ρ σ ψ r Γ Σ U Tl,
          expr_list_soundness n el ρ σ ψ r Γ Σ U Tl) /\
      (forall C flds I x ρ σ Γ Σ r,
          init_soundness n C flds I x ρ σ Γ Σ r) ->
    (forall e m args ρ σ ψ r Γ Σ U T,
        expr_soundness (S n) (e_mtd e m args) ρ σ ψ r Γ Σ U T).
Proof with (meta; meta_clean; eauto 2 with typ;
            try match goal with
                | |- ?Σ ⊨ ?l : ?T => try solve [eapply vt_sub; eauto 4 with typ]
                end).
  intros n [IH__expr [IH__list IH__init]];
    unfold expr_soundness, expr_list_soundness, init_soundness; intros.
  simpl in *...

  (* Induction on the typing judgment *)
  eapply t_mtd_inv in H as
      (?C & ?C & ?e__m & ?Args & ?Flds & ?μ__m & ?μ' & ?μ__r &
         HT__e0 & H__mtdinfo & ? & HT__args & HS__args & H__sub & H__hots) ...

  (* Destruct evaluation of e0 *)
  destruct_eval H__eval0 v σ';
    lets (Σ0 & v0 & σ0 & H__r & H__mn0 & H__stk0 & H__aty0 & H__st0 & H__wf0 & H__v0) :
    IH__expr HT__e0 H0 H1 H3 H__eval0; try inverts H__r; try congruence ...
  eapply eval_implies_evalp in H__eval0.
  lets H__pM0: pM_theorem_expr H__eval0.
  lets (?C & ?ω & ?μ & H__obj & ? & ?): (proj2 H__st0) v0 ...
  rewrite H__obj in H5 |- *.

  (* Destruct method fetch*)
  unfold methodInfo in H__mtdinfo.
  destruct (ct C) as [Args1 Flds1 Mtds1] eqn:H__ct1.
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
  pose proof (typable_classes C) as HT__em.
  rewrite H__ct1 in HT__em.
  destruct HT__em as [_ HT__em].
  specialize (HT__em m _ _ _ _ H__Mtds1).

  (* Destruct evaluation of method body *)
  lets (?T & ?T & ? & ? & ?): H__mn1 ψ...
  lets (?T & ?T & ? & ? & ?): H__mn1 v0...
  assert (HT__em': (Args, (C, μ__m)) ⊢ e__m : (C0, μ__r)) by (eapply weakening with (Γ := Flds); eauto with typ).
  assert (codom args_val ∪ {v0} ⪽ σ1). { ss... eapply wf_theorem_list... }
  destruct (⟦ e__m ⟧ (σ1, args_val, v0 ,  n)) as [ | | σ' v' ] eqn:H__eval2; try congruence;
    lets (Σ2 & v2 & σ2 & H__r & H__mn2 & H__stk2 & H__aty2 & H__st2 & H__wf2 & H__v2) :
    IH__expr HT__em' H__v1 H__st1 H__wf1 H__eval2; try inverts H__r; try congruence ...
  eapply eval_implies_evalp in H__eval2. subst.

  (* Result *)
  eval_dom; eval_wf.
  destruct H__hots as [? | [ H__hots ?] ]...

  - exists Σ2, v2, σ2; splits...
    all: eauto with typ.

  - (* Local reasoning *)
    subst; meta.
    destruct (Local_reasoning_for_typing Σ1 Σ2 σ1 σ2 (codom args_val ∪ { v0 }) {v2} ) as
      (Σ3 & ? & ? & ? & ? & H__v2); ss => //.
    + apply scp_theorem_expr with (e:=e__m); eauto with wf lia.
    + intros l' [l H__l | l H__l]; rch_set; [| exists C]...
    + lets: H__v2 v2 In_singleton. clear H__v2...
      lets (?T & ?T & ? &?&?): H13 v2...
      exists Σ3, v2, σ2; splits ; auto; [ | | | eexists ]; eauto with typ.
Qed.

Lemma soundness_new:
  forall n,
    (forall e ρ σ ψ r Γ Σ U T,
        expr_soundness n e ρ σ ψ r Γ Σ U T) /\
      (forall el ρ σ ψ r Γ Σ U Tl,
          expr_list_soundness n el ρ σ ψ r Γ Σ U Tl) /\
      (forall C flds I x ρ σ Γ Σ r,
          init_soundness n C flds I x ρ σ Γ Σ r) ->
    (forall C args ρ σ ψ r Γ Σ U T,
        expr_soundness (S n) (e_new C args) ρ σ ψ r Γ Σ U T).
Proof with (meta; meta_clean; eauto 2 with typ;
            try match goal with
                | |- ?Σ ⊨ ?l : ?T => try solve [eapply vt_sub; eauto with typ]
                end).
  intros n [IH__expr [IH__list IH__init]];
    unfold expr_soundness, expr_list_soundness, init_soundness; intros.
  simpl in *...

  (* Induction on the typing judgment *)
  eapply t_new_inv in H as
      (Args & Flds & Mtds & argsTs & ?μ & ? & H__ct & HT__args & HS__args & H__mode) ...

  (* Destruct evaluation of arguments *)
  destruct_eval H__eval1 vl σ';
    lets (Σ1 & args_val & σ1 & H__r & H__mn1 & H__stk1 & H__aty1 & H__st1 & H__wf1 & H__argsval) :
    IH__list HT__args H0 H1 H3 H__eval1; try inverts H__r; try congruence ...
  inverts H...
  rewrite H__ct in H5 |- *.
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
  destruct (init C Flds dom σ1 0 args_val (σ1 ++ [(C, [])]) n) as [ | | σ3] eqn:Heq;
    rewrite Heq in H5 |- *; try congruence;
    specialize (IH__init C Flds (dom σ1) 0 args_val σ2 argsTs Σ2);
  lets (Σ4 & σ4 & H__r & H__mn4 & H__stk4 & H__aty4 & H__st4 & H__wf4 & H__getType4):
     IH__init ([]: list Field) H__st2 H__wf2 H__ct ; subst; simpl in *...
  all: try solve [intros; discriminate].
  all: try solve [rewrite (proj1 H__st1) getType_last; simpl; reflexivity].
  inverts H__r.
  eapply init_implies_initP with (DoneFlds := []) in Heq...

  (* Promotion *)
  remember ([dom σ1 ↦ (C, warm)] (Σ4)) as Σ5.
  assert (H__aty4': Σ1 ▷ Σ4). {
    intros l ? ? H__getType.
    lets: getType_dom H__getType.
    assert (l <> dom Σ1) by lia.
    apply H__aty4...
    rewrite getType_update_diff...
    rewrite getType_last2... }
  assert (H__stk5: Σ1 ≪ [dom σ1 ↦ (C, warm)] (Σ4)). {
    intros l H__l. updates...
    assert (l < dom σ1 \/ l = dom σ1 \/ dom σ1 <> l) as [ |[|] ] by lia; subst...
    + left. exists C, (C, warm); updates...
    + destruct (H__stk4 l); updates...
      left; exists C0, (C0, μ0); updates...
  }
  lets (H__aty5 & H__mn5' & H__stk5' & H__st5) : promotion Σ1 Σ4 (dom σ1) σ4 HeqΣ5...

  (* Case analysis : warm or hot *)
  destruct H__mode as [H__warm | H__hots].
  + (* warm *)
    exists Σ5, (dom σ1), σ4; splits...
    exists (C, warm); subst; updates...

  + (* hot *)
    eval_dom. updates...
    destruct (Local_reasoning_for_typing Σ1 Σ5 σ1 σ4 (codom args_val) {dom σ1} ) as
      (Σ6 & ? & ? & ? & ? & H__vnew)...
    * eapply wf_theorem_list...
    * lets: scp_theorem_init Heq; eauto with scp...
      apply scp_trans with σ4 (codom args_val ∪ {dom σ1}); ss... {
        eapply ss_trans with (σ1++[(C,[])]); updates...
      }
      ++ apply scp_trans with (σ1 ++ [(C, [])]) (codom args_val ∪ {dom σ1}); updates...
         intros ? ? l ? H__rch.
         apply rch_add_empty_set in H__rch as [ [x [ [ ] H__rch]] |]; rch_set...
         eexists...
         apply rch_dom2 in H__rch...
      ++ apply scp_refl2; intros ? [ ]. apply Union_intror, In_singleton.
    * intros l H__l.
      eapply P_Hots_env...
    * exists Σ6, (dom σ1), σ4; splits;
        eauto 3 with typ.
      exists (C, hot)...
      lets (? & ? & ? & ? & ?): H13 (dom σ1); subst...
      rewrite getType_update_same in H16... inverts H16...
      lets: H__vnew (dom σ1) In_singleton... inverts H16... inverts H18...
Qed.

Lemma soundness_asgn:
  forall n,
    (forall e ρ σ ψ r Γ Σ U T,
        expr_soundness n e ρ σ ψ r Γ Σ U T) /\
      (forall el ρ σ ψ r Γ Σ U Tl,
          expr_list_soundness n el ρ σ ψ r Γ Σ U Tl) /\
      (forall C flds I x ρ σ Γ Σ r,
          init_soundness n C flds I x ρ σ Γ Σ r) ->
    (forall e1 f e2 e' ρ σ ψ r Γ Σ U T,
        expr_soundness (S n) (e_asgn e1 f e2 e') ρ σ ψ r Γ Σ U T).
Proof with (meta; meta_clean; eauto 2 with typ;
            try match goal with
                | |- ?Σ ⊨ ?l : ?T => try solve [eapply vt_sub; eauto with typ]
                end).
  intros n [IH__expr [IH__list IH__init]];
    unfold expr_soundness, expr_list_soundness, init_soundness; intros.
  simpl in *...
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
    remember ([v1 ↦ (C, [f ↦ v2] (ω0))] (σ2)) as σ2'. rewrite -Heqσ2' in H6.
    assert (H__st2': Σ2 ⊨ σ2'). {
      subst. rename v1 into l, v2 into v.
      lets [?ω [H__obj2 _]]: pM_theorem_expr H__eval2 H__obj.
      lets [v0 [H__v0 ?]]: cool_selection D0 l H__st2 H__obj2... {
        lets (?T & ?T & ? & ? & ?): H__mn2 l...
        steps...
        apply vt_sub with (C, μ5)...
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
    destruct (⟦ e' ⟧ (σ2', ρ, ψ ,  n)) as [ | | σ' v' ] eqn:H__eval3; try congruence;
      lets (Σ3 & v3 & σ3 & H__r & H__mn3 & H__stk3 & H__aty3 & H__st3 & H__wf3 & H__v3) :
      IH__expr HT__e3 H__st2' H__eval3; try inverts H__r; try congruence ...
    (* eapply eval_implies_evalp in H__eval3. eval_dom; eval_wf.*)
    subst.
    exists Σ3, v3, σ3; subst; splits...
    all: eauto with typ.

  + (* Useless assignment *)
    destruct (⟦ e' ⟧ (σ2, ρ, ψ ,  n)) as [ | | σ' v' ] eqn:H__eval3; try congruence;
      lets (Σ3 & v3 & σ3 & H__r & H__mn3 & H__stk3 & H__aty3 & H__st3 & H__wf3 & H__v3) :
      IH__expr HT__e3 H__st2 H__wf2 H__eval3; try inverts H__r; try congruence ...
    eapply eval_implies_evalp in H__eval3. eval_dom; eval_wf.
    exists Σ3, v3, σ3; splits...
    all: eauto with typ.
Qed.

Lemma soundness_init_cons:
  forall n,
    (forall e ρ σ ψ r Γ Σ U T,
        expr_soundness n e ρ σ ψ r Γ Σ U T) /\
      (forall el ρ σ ψ r Γ Σ U Tl,
          expr_list_soundness n el ρ σ ψ r Γ Σ U Tl) /\
      (forall C flds I x ρ σ Γ Σ r,
          init_soundness n C flds I x ρ σ Γ Σ r) ->
    (forall f flds C I x ρ σ Γ Σ r,
        init_soundness (S n) C (f::flds) I x ρ σ Γ Σ r).
Proof with (meta; meta_clean; eauto 2 with typ;
            try match goal with
                | |- ?Σ ⊨ ?l : ?T => try solve [eapply vt_sub; eauto with typ]
                end).
  intros n [IH__expr [IH__list IH__init]];
    unfold expr_soundness, expr_list_soundness, init_soundness; intros.
  simpl in *...
  destruct f as [μ__f e]. subst.

  (* Extract typing from the well-typed classes *)
  pose proof (typable_classes C) as HT__C. rewrite H3 in HT__C.
  destruct HT__C as [HT__Field _].
  eapply T_Fields_In in HT__Field.
  unfold T_Field in HT__Field.
  eapply weakening with (Γ' := Γ) in HT__Field; [| intros [ ] Tx Hf; inverts Hf].
  rename HT__Field into HT__e.
  (* assert (H__doms: dom DoneFlds = dom ω) by (updates; meta; lia). *)
  (* rewrite H__doms in HT__e |- *. *)

  (* Destruct evaluation of e *)
  destruct_eval H__eval v' σ';
    lets (Σ0 & v0 & σ0 & H__r & H__mn0 & H__stk0 & H__aty0 & H__st0 & H__wf0 & H__v0) :
    IH__expr HT__e H0 H1 H2 H__eval; try inverts H__r; try congruence ...
  eapply eval_implies_evalp in H__eval.
  (* lets H__eM: aty_theorem_expr H__eval. lets [ω' [ ]]: H__eM H4. *)
  lets: monotonicity_dom H__mn0.
  lets (? & ? & ? & ? & ?): H__mn0 I...
  lets (?C & ?ω & ?μ & ? & ? & ?): (proj2 H__st0) I...
  eval_dom; eval_wf.

  destruct (assign_new I dom DoneFlds v0 σ0) as [σ1 |] eqn:H__assign;
    [| unfold assign_new in H__assign; steps].

  (* Use field initialization lemma *)
  lets H__env0: env_typing_monotonicity H__mn0 H.
  clear IH__expr IH__list.
  lets: H__aty0 I H10.
  assert (H__field: fieldType C (dom DoneFlds) = Some (C1, μ0)). {
    unfold fieldType. rewrite H3.
    rewrite nth_error_app2... subst.
    rewrite -minus_diag_reverse...
  }
  cross_rewrites.
  remember ([I ↦ (C, cool (S (dom DoneFlds)))] (Σ0)) as Σ1.
  lets (H__st1 & H__mn1 & H__stk1): field_initialization I (dom DoneFlds) H__st0 H__field Σ1... { inverts H15... }

  (* Use induction hypothesis *)
  lets: env_typing_monotonicity H__mn1 H__env0.
  lets: wf_assign_new H__assign...
  specialize (IH__init
                C flds I (S dom DoneFlds) ρ
                σ1
                Γ Σ1
                (init C flds I (S dom DoneFlds) ρ σ1 n)
                Args (DoneFlds++(field (C1,μ0) e)::flds) Mtds
                (DoneFlds ++ [field (C1, μ0) e])).
  subst; modus.
  lets: assign_new_dom H__assign.
  destruct IH__init
    as (Σ2 & σ2 & H__r & H__mn2 & H__stk2 & H__aty2 & H__st2 & H__wf2 & H__getType2)...
  + apply ss_trans with σ0...
  + rewrite app_assoc_reverse. simpl => //.
  + updates...
  + rewrite getType_update_same; updates...
  + (* Result *)
    updates.
    lets H__initP: H__r.
    eapply init_implies_initP with (DoneFlds := DoneFlds ++ [field (C1, μ0) e]) in H__initP;
      updates; try rewrite app_assoc_reverse...
    lets H__scpInit: scp_theorem_init H__initP.
    lets: scp_theorem_expr H__eval H1...
    exists Σ2, σ2; splits...
    * eauto with typ.
    * eauto with typ.
    * intros l ?C Ω H__getType.
      destruct_eq (I = l); subst; updates.
      -- rewrite getType_update_same in H__getType... steps.
      -- eapply H__aty0 in H__getType.
         eapply H__aty2. updates...
Qed.

Theorem soundness:
  forall n,
    (forall e ρ σ ψ r Γ Σ U T,
        expr_soundness n e ρ σ ψ r Γ Σ U T) /\
    (forall el ρ σ ψ r Γ Σ U Tl,
      expr_list_soundness n el ρ σ ψ r Γ Σ U Tl) /\
    (forall C flds I x ρ σ Γ Σ r,
       init_soundness n C flds I x ρ σ Γ Σ r).
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

  - eapply soundness_fld...

  - eapply soundness_mtd...

  - eapply soundness_new...

  - eapply soundness_asgn...

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
    destruct (⟦_ el _⟧ (σ0, ρ, ψ, n)) as [ | | σ' vl' ] eqn:H__eval1; try congruence;
    lets (Σ1 & vl & σ1 & H__r & H__mn1 & H__stk1 & H__aty1 & H__st1 & H__wf1 & H__v1):
      IH__list H12 H__env0 H__st0 H__wf0 H__eval1; try inverts H__r; try congruence ...

    (* Result *)
    exists Σ1, (v::vl), σ1; splits...
    lets (?T & ?T & ? & ? & ?): H__mn1 v ...
    apply et_cons...

  - (* init [] *)
    updates. simpl in *. repeat rewrite Nat.add_0_r in H6 |- *.
    exists Σ, σ. splits...
    + intros l ?C Ω H__getType.
      destruct_eq (I = l); subst; updates...
      rewrite getType_update_same in H__getType... steps.

  - (* init_cons *)
    eapply soundness_init_cons...
Qed.

Theorem Soundness :
  forall n e ρ σ ψ r Γ Σ Tthis T,
    ⟦e⟧(σ, ρ, ψ, n) = r ->
    r <> Timeout ->
    Σ ⊨ σ ->
    (Σ ⊨ ρ : Γ) ->
    (Σ ⊨ ψ : Tthis) ->
    ((Γ, Tthis) ⊢ e : T) ->
    wf σ ->
    (codom ρ ∪ {ψ} ⪽ σ) ->
    exists Σ' v σ',
      r = Success v σ' /\
        (Σ' ⊨ σ') /\
        (Σ' ⊨ v : T) /\
        Σ ≼ Σ' /\
        Σ ▷ Σ' /\
        Σ ≪ Σ'.
Proof with (eauto with typ).
  intros.
  lets [(Σ'& v& σ'& ?) _]: soundness n... steps.
  exists Σ', v, σ'; splits...
Qed.

Corollary Program_soundness :
  T_Prog ->
  forall n, eval_prog n <> Error.
Proof with (meta; eauto 2 with typ).
  unfold eval_prog, T_Prog.
  lets H__ct: EntryClass_ct. rewrite H__ct.
  destruct EntryClass.
  steps...
  lets: Soundness [(Entry, hot)] H0 H; eauto with typ; steps.
  + split; steps.
    assert (l = 0) by lia; steps.
    exists Entry, ([]: Env), hot; steps.
    eapply ot_hot...
    simpl; intros; lia.
  + eapply vt_sub; steps.
  + lets (? & ? & ?): H1; steps...
    intros l C ω ?H.
    lets: getObj_dom H2; simpl in *.
    assert (l=0) by lia; steps.
    lets: getVal_dom H6; simpl in *; try lia...
Qed.
