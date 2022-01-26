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
    eapply t_this_inv in H.
    exists Σ, ψ, σ; steps...
  - (* e = fld *)

    admit.
  - (* e = mtd e m l *)
    rename l into args.
    specialize (IHn n ltac:(lia)) as [IH__expr IH__list]...

    (* Induction on the typing judgment *)
    eapply t_mtd_inv in H as
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
    eval_dom. eval_wf...
    lets (?T & ?T & ? & ? & ?): H__mn0 ψ ...
    destruct_eval H__eval1 vl σ';
      lets (Σ1 & args_val & σ1 & H__r & H__mn1 & H__stk1 & H__aty1 & H__st1 & H__wf1 & H__v1) :
      IH__list HT__args H__env0 H__st0 H__wf0 H__eval1; try inverts H__r ...
    eapply eval_list_implies_evalp in H__eval1. eval_dom; eval_wf.

    (* Destruct evaluation of method body *)
    lets (?T & ?T & ? & ? & ?): H__mn1 ψ...
    lets (?T & ?T & ? & ? & ?): H__mn1 v0...
    assert (HT__em': (Args, (C1, μ__m)) ⊢ e__m : (C, μ__r)) by (eapply weakening with (Γ := Flds); eauto with typ).
    assert (codom args_val ∪ {v0} ⪽ σ1) by (apply storeSubset_union; [eapply wf_theorem_list |]; eauto with wf).
    destruct (⟦ e__m ⟧ (σ1, args_val, v0 )( n)) as [ | | σ' v' ] eqn:H__eval2; try congruence;
    lets (Σ2 & v2 & σ2 & H__r & H__mn2 & H__stk2 & H__aty2 & H__st2 & H__wf2 & H__v2) :
      IH__expr HT__em' H__v1 H__st1 H__wf1 H__eval2; try inverts H__r ...
    eapply eval_implies_evalp in H__eval2. clear H6.

    (* Result *)
    eval_dom; eval_wf.
    destruct H__hots as [? | [ H__hots ?] ]...
    + exists Σ2, v2, σ2; splits...
    + (* Local reasoning *)
      subst...
      destruct (local_reasoning2 Σ1 Σ2 σ1 σ2 (codom args_val ∪ { v0 }) {v2} ) as
        (Σ3 & ? & ? & ? & ? & H__v2)...
      * apply scopability_theorem with (e:=e__m); eauto with wf lia.
      * intros l' [l H__l | l H__l]; rch_set; [| exists C1]...
      * lets: H__v2 v2 In_singleton...
        lets (? & ? & ? & ? & ?): H12 v2...
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
