(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** Store typing *)

From Celsius Require Export Typing LibTactics Tactics Reachability Wellformedness.
Require Import Coq.ssr.ssreflect Coq.ssr.ssrbool Coq.Lists.List Coq.micromega.Psatz Ensembles Coq.Program.Tactics.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc) (L: LocSet) (Σ: StoreTyping) (T: Tpe) (μ: Mode) (Γ: EnvTyping).
(* Import ListNotations. *)
(* Open Scope nat_scope. *)


(** * Main definitions *)

(** ** Monotonicity *)
Definition monotonicity Σ1 Σ2 :=
  forall l, l < dom Σ1 -> (exists T1 T2, getType Σ1 l = Some T1 /\ getType Σ2 l = Some T2 /\ T2 <: T1).
Notation "Σ1 ≼ Σ2" := (monotonicity Σ1 Σ2) (at level 60).

(** ** Authority *)
Definition authority_st Σ1 Σ2 :=
  forall l C Ω, getType Σ1 l = Some (C, cool Ω) -> getType Σ2 l = Some (C, cool Ω).
Notation "Σ1 ▷ Σ2" := (authority_st Σ1 Σ2) (at level 60).

(** ** Value typing (with variants) *)

Inductive value_typing : StoreTyping -> Loc -> Tpe -> Prop :=
| vt_sub : forall Σ l T1 T2,
    getType Σ l = Some T1 ->
    (T1 <: T2) -> value_typing Σ l T2.
Global Instance notation_value_typing_Tpe : notation_dash_colon StoreTyping Loc Tpe :=
  { dash_colon_ := value_typing }.
Global Hint Unfold notation_value_typing_Tpe: notations.

Definition value_typing_mode Σ l μ :=
  exists C, Σ ⊨ l : (C, μ).
Global Instance notation_value_typing_Mode : notation_dash_colon StoreTyping Loc Mode :=
  { dash_colon_ := value_typing_mode }.
Global Hint Unfold notation_value_typing_Mode: notations.

Definition value_typing_cln Σ l C :=
  exists μ, Σ ⊨ l : (C, μ).
Global Instance notation_value_typing_ClN : notation_dash_colon StoreTyping Loc ClN :=
  { dash_colon_ := value_typing_cln }.
Global Hint Unfold notation_value_typing_ClN: notations.

Definition value_typing_mode_locset Σ L μ :=
  forall (l: Loc), (In Loc L l) -> Σ ⊨ l : μ.
Global Instance notation_value_typing_mode_LocSet : notation_dash_colon StoreTyping LocSet Mode :=
  { dash_colon_ := value_typing_mode_locset }.
Global Hint Unfold notation_value_typing_mode_LocSet: notations.

Definition value_typing_locset Σ (ll: list Loc) (vl: list Tpe) :=
  Forall2 (fun (l: Loc) (T:Tpe) => Σ ⊨ l : T) ll vl.
Global Instance notation_value_typing_LocSet : notation_dash_colon StoreTyping (list Loc) (list Tpe) :=
  { dash_colon_ := value_typing_locset }.
Global Hint Unfold notation_value_typing_LocSet: notations.

(** ** Stackability *)
Definition stackability_st Σ1 Σ2 :=
  forall l, l < dom Σ2 -> (Σ2 ⊨ l : warm) \/ (l < dom Σ1).
Global Instance notation_stackability_StoreTyping : notation_stackability StoreTyping :=
  { stackability_ := stackability_st }.
Global Hint Unfold notation_stackability_StoreTyping : notations.

(** ** Object typing **)
Inductive object_typing : StoreTyping -> Obj -> Tpe -> Prop :=

| ot_hot : forall Σ C ω Args Flds Mtds,
    ct C = class Args Flds Mtds ->
    (forall f D μ,
        f < length Flds ->
        fieldType C f = Some (D, μ) ->
        exists v,
          getVal ω f = Some v /\ (Σ ⊨ v : (D, hot))) ->
    object_typing Σ (C,ω) (C, hot)

| ot_warm : forall Σ C ω Args Flds Mtds,
    ct C = class Args Flds Mtds ->
    (forall f D μ,
        f < length Flds ->
        fieldType C f = Some (D, μ) ->
        exists v,
          getVal ω f = Some v /\ (Σ ⊨ v : (D, μ))) ->
    object_typing Σ (C,ω) (C, warm)

| ot_cool : forall Σ C ω n,
    (forall f v D μ,
        getVal ω f = Some v ->
        fieldType C f = Some (D, μ) ->
        Σ ⊨ v : (D, μ)) ->
    dom ω = n ->
    object_typing Σ (C,ω) (C, cool n)

| ot_cold : forall Σ C ω,
    object_typing Σ (C,ω) (C, cold).

Global Instance notation_object_typing : notation_dash_colon StoreTyping Obj Tpe :=
  { dash_colon_ := object_typing }.
Global Hint Unfold notation_object_typing: notations.

(** ** Store_typing *)
(** Here is the link between the abstract environment of types and the store used in execution *)
Definition store_typing Σ σ :=
  dom σ = dom Σ /\
  forall l, l < dom Σ ->
       exists C ω μ, getObj σ l = Some (C,ω) /\
                  getType Σ l = Some (C, μ) /\
                  Σ ⊨ (C, ω) : (C, μ).
Global Instance notation_store_typing: notation_dash StoreTyping Store :=
  { dash_ := store_typing }.
Global Hint Unfold notation_store_typing: notations.
Global Hint Unfold notation_store_typing store_typing: typ.

(** ** Environment typing *)
Inductive env_typing : StoreTyping -> Env -> EnvTyping -> Prop :=
| et_nil : forall Σ, env_typing Σ nil nil
| et_cons : forall Σ ρ Γ l T,
    env_typing Σ ρ Γ ->
    (Σ ⊨ l : T) ->
    env_typing  Σ (l :: ρ) (T :: Γ).
Global Instance notation_env_typing: notation_dash_colon StoreTyping Env EnvTyping :=
  { dash_colon_ := env_typing }.
Global Hint Unfold notation_env_typing: notations.


(** * Tactics *)
Ltac meta :=
  unfold Value, Var in *;
  repeat
    match goal with
    (* Cross rewrites *)
    | H: getObj ?σ ?l = Some ?O,
        H': getObj ?σ ?l = Some ?O' |- _ => rewrite H' in H; inverts H
    | H: getType ?Σ ?l = Some ?T,
        H': getType ?Σ ?l = Some ?T' |- _ => rewrite H' in H; inverts H
    | H: getVal ?ρ ?f = Some ?l,
        H': getVal ?ρ ?f = Some ?l' |- _ => rewrite H' in H; inverts H

    (* Dom hypothesis *)
    | H: getType ?Σ ?l = Some ?T |- _ =>
        match goal with
        | H': Σ ⊨ ?σ, H'': l < dom ?σ' |- _ => fail 1
        | H': Σ ⊨ ?σ, H'': S l <= dom ?σ' |- _ => fail 1
        | _ =>
            let fresh := fresh "H__dom" in
            add_hypothesis fresh (getType_dom l T Σ H)
        end
    | H: getVal ?ρ ?f = Some ?l |- _ =>
        match goal with
        | H': S f <= dom ρ |- _ => fail 1
        | H': f < dom ρ |- _ => fail 1
        | _ => let fresh := fresh "H__dom" in
              add_hypothesis fresh (getVal_dom ρ f l H)
        end

    (* Destructs *)
    | H: ?Σ ⊨ ?l : ?x |- _ =>
        match type of l with
        | Loc => match type of x with
                | Mode => let C := fresh "C" in destruct H as [C H]
                | (ClN*Mode)%type =>
                    inverts H
                end
        end
    | o:Obj |- _ => let C := fresh "C" in
                  let ω := fresh "ω" in
                  destruct o as [C ω]
    | T:Tpe |- _ => let C := fresh "C" in
                  let μ := fresh "μ" in
                  destruct T as [C μ]
    | H: ?μ ⊑ hot |- _ =>
        let H__eq := fresh "H__eq" in
        assert (H__eq: μ = hot) by (invert H; steps); subst;
        clear H
    | H: hot ⊑ ?μ |- _ => clear H
    | H: ((?C, ?μ) <: (?C', ?μ')) |- _ => inverts H
    | H: ?Σ ⊨ ?σ |- context [ dom ?Σ ] => rewrite <- (proj1 H)
    | H: ?Σ ⊨ ?σ, H':context [ dom ?Σ ] |- _ => rewrite <- (proj1 H) in H'
    end ; sort; cross_rewrites;
  try lia.

Ltac meta_clean :=
  move_top StoreTyping;
  move_top EnvTyping;
  move_top Env;
  move_top Store;
  move_top (list Loc);
  move_top Loc;
  move_top (list Tpe);
  move_top Mode; move_top ClN; move_top Expr.


(** * Monotonicity results *)

Lemma monotonicity_dom :
  forall Σ1 Σ2, Σ1 ≼ Σ2 -> (dom Σ1 <= dom Σ2).
Proof with meta; eauto with lia updates .
  intros.
  destruct Σ1; steps...
  specialize (H (dom Σ1)) as (? & ? & ?); steps ...
Qed.
Global Hint Resolve monotonicity_dom: typ.

Lemma value_typing_dom : forall Σ l T,
    Σ ⊨ l : T -> l < dom Σ.
Proof with meta; eauto.
  intros ...
Qed.
Global Hint Resolve value_typing_dom: typ.

Lemma value_typing_monotonicity: forall Σ1 Σ2 l T,
    Σ1 ≼ Σ2 -> Σ1 ⊨ l : T -> Σ2 ⊨ l : T.
Proof with (meta; eauto with lia typ).
  intros ...
  specialize (H l H0) as [T1 [T2 [Hs1 [Hs2 H__sub]]]] ...
  eapply vt_sub ...
Qed.
Global Hint Resolve value_typing_monotonicity: typ.

Lemma env_typing_monotonicity: forall Σ1 Σ2 Γ ρ,
    Σ1 ≼ Σ2 -> Σ1 ⊨ ρ : Γ -> Σ2 ⊨ ρ : Γ.
Proof.
  intros.
  autounfold with notations in H0. simpl in H0.
  induction H0.
  - steps.
  - specialize (IHenv_typing H).
    apply et_cons; steps; eauto with typ.
Qed.
Global Hint Resolve env_typing_monotonicity: typ.

Lemma object_typing_monotonicity: forall Σ1 Σ2 (o: Obj) T,
    Σ1 ≼ Σ2 -> Σ1 ⊨ o : T -> Σ2 ⊨ o : T.
Proof with (meta; eauto with lia typ).
  intros ...
  inversion H0; steps.

  - eapply ot_hot; [eassumption |].
    intros.
    specialize (H7 f D μ H1 H2); steps.
    exists v; split => //.
    exists (D, hot)...
    lets ([ ] & [ ] & ? & ? & ?): H H6...

  - eapply ot_warm; [eassumption |].
    intros.
    specialize (H7 f D μ H1 H2); steps.
    exists v; steps ...
    lets ([ ] & [ ] & ? & ? & ?): H H6.
    eexists...

  - apply ot_cool ...
Qed.
Global Hint Resolve object_typing_monotonicity: typ.

Lemma mn_refl: forall Σ,
    Σ ≼ Σ.
Proof with (meta; eauto with ss typ).
  intros Σ l; steps ...
  lets [? ?]: getType_Some H...
Qed.
Global Hint Resolve mn_refl : typ.

Lemma mn_trans: forall Σ1 Σ2 Σ3,
    Σ1 ≼ Σ2 -> Σ2 ≼ Σ3 -> Σ1 ≼ Σ3.
Proof with (meta; eauto with lia typ).
  intros.
  intros l; steps.
  specialize (H l H1); steps.
  specialize (H0 l) as [ ]; steps...
  eexists; eexists...
Qed.
Global Hint Resolve mn_trans: typ.

Lemma mn_hot: forall Σ1 Σ2 l,
    Σ1 ≼ Σ2 ->
    (Σ1 ⊨ l : hot) ->
    (Σ2 ⊨ l : hot).
Proof.
  intros; meta.
  specialize (H l H0); steps; meta.
  exists C.
  eapply vt_sub; eauto with typ.
Qed.
Global Hint Resolve mn_hot: typ.

Lemma mn_hot_set: forall Σ1 Σ2 (L: LocSet),
    Σ1 ≼ Σ2 ->
    (Σ1 ⊨ L : hot) ->
    (Σ2 ⊨ L : hot).
Proof.
  intros; meta.
  intros l.
  specialize (H0  l); eauto with typ.
Qed.

Lemma env_regularity: forall Γ Σ ρ x U T,
    Σ ⊨ ρ : Γ ->
    ((Γ, U) ⊢ (var x) : T) ->
    exists l, getVal ρ x = Some l /\ Σ ⊨ l : T.
Proof.
  intros ...
  remember (var x) as e.
  induction H0; try congruence.
  - specialize (IHT_Expr H Heqe) as [l [H__val Ht]].
    exists l; steps.
    inverts Ht.
    eapply vt_sub; eauto with typ.
  - inverts Heqe.
    gen U x.
    autounfold with notations in H. simpl in *.
    induction H; intros; destruct x; steps; eauto.
Qed.

Ltac storeTyping_update :=
  repeat (match goal with
          | H1: ?Σ ⊨ ?σ,
              H2: getObj ?σ ?l = Some (?C, ?ω) |- _ =>
              match goal with
              | H3: getType Σ l = Some (C, ?μ) |- _ => fail 1
              | _ => let H_obj := fresh "H__getObj" in
                    let H_tpe := fresh "H__getType" in
                    let H_vt := fresh "H__vt" in
                    destruct ((proj2 H1) l (ltac:(rewrite <-(proj1 H1); apply (getObj_dom l _ σ H2)))) as
                      (?C & ?ω & ?μ & H_obj & H_tpe & H_vt);
                    symmetry in H_obj;
                    rewrite H2 in H_obj; inverts H_obj
              end
          | H1: ?Σ ⊨ ?σ,
              H2: getType ?Σ ?l = Some (?C, ?μ) |- _ =>
              match goal with
              | H3: getObj ?σ l = Some (C, ?ω) |- _ => fail 1
              | _ => let H_obj := fresh "H__getObj" in
                    let H_tpe := fresh "H__getType" in
                    let H_vt := fresh "H__vt" in
                    destruct ((proj2 H1) l (ltac:(rewrite <-(proj1 H1); apply (getObj_dom l _ σ H2)))) as
                      (?C & ?ω & ?μ & H_obj & H_tpe & H_vt);
                    symmetry in H_tpe;
                    rewrite H2 in H_tpe; inverts H_tpe
              end
          end; cross_rewrites).

Lemma hot_transitivity : forall Σ σ l l',
    wf σ ->
    (Σ ⊨ l : hot) ->
    (Σ ⊨ σ) ->
    (σ ⊨ l ⇝ l') ->
    (Σ ⊨ l' : hot).
Proof with (storeTyping_update; meta; eauto 2 with lia typ).
  intros.
  gen Σ.
  induction H2; steps...
  inverts H__vt ...
  lets [? _]: H H1.
  lets: H3 H9.
  lets: getVal_dom H2...
  lets [?C [?μ ?]]:  fieldType_exists f ...
  lets [?v [ ]]: H10 H11 ...
  exists C...
  eexists...
Qed.


Lemma hot_transitivity_set : forall Σ σ L l,
    wf σ ->
    (Σ ⊨ L : hot) ->
    (Σ ⊨ σ) ->
    (σ ⊨ L ⇝ l) ->
    (Σ ⊨ l : hot).
Proof with (storeTyping_update; meta; eauto 2 with lia typ).
  intros. rch_set.
  eapply hot_transitivity...
Qed.

(** ** Authority results *)
Lemma aty_st_refl: forall Σ, Σ ▷ Σ.
Proof with (meta; eauto with typ lia).
  intros Σ l H.
  destruct (getType Σ l) eqn:E; eauto.
Qed.
Global Hint Resolve aty_st_refl : typ.

Lemma aty_st_trans: forall Σ1 Σ2 Σ3,
    Σ1 ▷ Σ2 ->
    Σ2 ▷ Σ3 ->
    Σ1 ▷ Σ3.
Proof with steps.
  intros. intros l ...
Qed.
Global Hint Resolve aty_st_trans : typ.


(** ** Stackability results *)
Lemma stk_st_refl: forall Σ, Σ ≪ Σ.
Proof.
  intros Σ l H. right => //.
Qed.
Global Hint Resolve stk_st_refl : typ.

Lemma stk_st_trans: forall Σ1 Σ2 Σ3,
    Σ1 ≪ Σ2 ->
    Σ2 ≪ Σ3 ->
    Σ2 ≼ Σ3 ->
    Σ1 ≪ Σ3.
Proof.
  intros.
  intros l ?.
  specialize (H0 l) as [ ]; eauto.
  specialize (H l H0) as [ ]; eauto.
  inverts H.
  inverts H3.
  left.
  specialize (H1 l) as [ ]; steps.
  rewrite H3 in H; steps.
  repeat eexists; eauto with typ.
Qed.
Global Hint Resolve stk_st_trans : typ.


(** ** Selection results *)
Lemma hot_selection : forall Σ σ l C ω,
    wf σ ->
    Σ ⊨ σ ->
    (Σ ⊨ l : (C, hot)) ->
    getObj σ l = Some (C, ω) ->
    (forall f D μ, fieldType C f = Some (D, μ) ->
              exists v, getVal ω f = Some v /\
                   Σ ⊨ v : (D, hot)).
Proof with (meta; eauto 3 with typ lia).
  intros ...
  lets [ ]: (proj2 H0) l ...
  steps ...
  inverts H8.
  lets [? _]: H H6.
  lets: H2 H9.
  lets [? [ ] ]: H10 f H3...
Qed.

Lemma warm_selection : forall Σ σ l C ω f T,
    Σ ⊨ σ ->
    (Σ ⊨ l : (C, warm)) ->
    getObj σ l = Some (C, ω) ->
    fieldType C f = Some T ->
    exists v, getVal ω f = Some v /\ Σ ⊨ v : T.
Proof with (meta; eauto 3 with typ lia).
  intros ...
  lets [ ]: (proj2 H) l ... steps ...
  inverts H6.
  - inverts H8.
    lets [?v [ ] ] : H9 H2 ...
  - inverts H8.
    lets [?v [ ] ] : H9 H2 ...
    exists v; split ...
    eapply vt_sub ...
Qed.

Lemma cool_selection : forall Σ σ C l Ω ω f T,
    Σ ⊨ σ ->
    (Σ ⊨ l : (C, cool Ω)) ->
    getObj σ l = Some (C, ω) ->
    fieldType C f = Some T ->
    f < Ω ->
    exists v, getVal ω f = Some v /\ Σ ⊨ v : T.
Proof with (meta; eauto 4 with typ lia).
  intros ...
  lets [ ]: (proj2 H) l ... steps ...
  inverts H9 ...
  - lets [?v [ ] ] : H12 H2 ...
    exists v; split ...
    eapply vt_sub ...
  - inversion H7; subst.
    + destruct (getVal ω f) eqn:?; try split ...
      apply nth_error_None in Heqo ...
    + destruct (getVal ω f) eqn:?; try split ...
      apply nth_error_None in Heqo ...
  - invert H7.
Qed.


(** ** Initialization results *)
Lemma field_initialization: forall C I σ ω T Σ v,
    wf σ ->
    Σ ⊨ σ ->
    getObj σ I = Some (C, ω) ->
    getType Σ I = Some (C, cool (dom ω)) ->
    fieldType C (dom ω) = Some T ->
    (Σ ⊨ v : T) ->
    forall σ' Σ',
      assign_new I v σ = Some σ' ->
      Σ' = [I ↦ (C, cool (S (dom ω)))]Σ ->
      (Σ' ⊨ σ') /\ Σ ≼ Σ' /\ Σ ≪ Σ'.
Proof with (updates; meta; eauto 2 with typ lia).
  intros. subst.
  unfold assign_new in *.
  assert (H__fo: forall A B C : Prop , (B -> A) -> B -> C -> A /\ B /\ C) by firstorder.
  apply H__fo; clear H__fo; steps.
  - (* ⊨ *)
    split...
    intros l H__l.
    lets (?C & ?ω & ?μ & ? & ? & ?): (proj2 H0) l...
    destruct_eq (I = l); subst...
    + exists C, (ω++(v::nil)), (cool (S dom ω)); splits...
      eapply ot_cool; [| updates; unfold Value; lia].
      intros.
      apply getVal_add in H2 as [(? & ?)|(H__f & H__getVal)]; subst...
      * destruct_eq (v0 = l); subst.
        -- exists (C, cool (S (dom ω))); try rewrite getType_update_same...
           eapply s_typ_mode...
           eapply s_mode_trans with (cool (dom ω)) ...
           eapply s_mode_cool...
        -- exists (D, μ); try rewrite getType_update_diff...
      * inverts H10.
        lets: H15 H11...
    + repeat eexists...

  - (* ≼ *)
    intros l H__l.
    destruct_eq (I = l); subst...
    + exists (C, cool (dom ω)), (C, cool (S dom ω)); splits ...
      eapply s_typ_mode.
      eapply s_mode_cool...
    + lets [?T ?]: getType_Some Σ l...
      eauto with typ lia.

  - (* ≪ *)
    intros l H__l. right...
Qed.

Lemma promotion: forall Σ1 Σ2 C I σ2 Args Flds Mtds,
    Σ1 ▷ Σ2 ->
    Σ1 ≼ Σ2 ->
    Σ1 ≪ [I ↦ (C, warm)] Σ2 ->
    ct C = class Args Flds Mtds ->
    I >= dom Σ1 ->
    getType Σ2 I = Some (C, cool (dom Flds)) ->
    Σ2 ⊨ σ2 ->
    forall Σ3,
      Σ3 = [I ↦ (C, warm)]Σ2 ->
      Σ1 ▷ Σ3 /\
        Σ1 ≼ Σ3 /\
        Σ1 ≪ Σ3 /\
        Σ3 ⊨ σ2.
Proof with (updates; meta; eauto 3 with typ lia).
  intros. subst.
  apply proj2 with (Σ2 ≼ [I ↦ (C, warm)] (Σ2)).
  assert (H__fo: forall A B C D E: Prop, B -> (A -> C) -> (A -> C -> E) -> D -> A -> A /\ B /\ C /\ D /\ E) by firstorder.
  apply H__fo; clear H__fo; intros.

  - (* ▷ *)
    intros l H__l Ω ?.
    destruct_eq (I = l); subst...

  - (* ≼ *)
    intros l H__l.
    lets ([C0 μ] & ?): getType_Some H__l.
    lets ([C1 μ1] & ?): getType_Some Σ2 l...
    lets (?T & ?T & ? &? &?): H0 H__l...
    exists (C0, μ).
    destruct_eq (I = l); subst.
    + exists (C, warm); split...
    + exists (C0, μ1); split...

  - (* ⊨ *)
    split...
    intros l H__l.
    lets: monotonicity_dom H6...
    lets (C0 & ω & ?): getObj_Some H__l...
    lets (?C & ?ω & ?μ & ? & ? & ?) : (proj2 H5) l...
    destruct_eq (I = l); subst...
    + exists C, ω, warm; splits; auto.
      eapply ot_warm; [eassumption |].
      intros f D μ' ? ?.
      inverts H13.
      lets (v & ?): getVal_Some ω f...
      eexists; split...
    + exists C0, ω, μ; splits...

  - (* ≪ *)
    intros l H__l...
    destruct (H1 l)...

  - (* ≼ *)
    intros l H__l.
    lets ([C0 μ] & ?): getType_Some H__l.
    exists (C0, μ).
    destruct_eq (I = l); subst;
      eexists; split...
Qed.

(** Env typing lemmas *)

Lemma env_typing_subs: forall Γ1 Γ2 Σ vl,
    Σ ⊨ vl : Γ2 ->
    S_Typs Γ1 Γ2 ->
    Σ ⊨ vl : Γ2.
Proof.
  induction Γ1; intros.
  - inverts H0; eauto with typ.
  - inverts H0; meta.
    inverts H; simpl in *.
    eapply IHΓ1 in H6; eauto.
    eapply et_cons; simpl in *; eauto with typ.
Qed.
Global Hint Resolve env_typing_subs: typ.


Lemma storeTyping_dom:
  forall Σ σ,
    Σ ⊨ σ -> dom σ = dom Σ.
Proof with (meta; eauto with typ lia).
  intros ...
Qed.
Global Hint Resolve storeTyping_dom: typ.




Lemma storeTyping_assgn:
  forall Σ σ l f v0 v C D ω μ μ0 μ__f,
    Σ ⊨ σ ->
    getObj σ l = Some (C, ω) ->
    getVal ω f = Some v0 ->
    fieldType C f = Some (D, μ__f) ->
    getType Σ v0 = Some (D, μ0) ->
    getType Σ v = Some (D, μ) ->
    μ ⊑ μ0 ->
    wf σ ->
    Σ ⊨ ([l ↦ (C, [f ↦ v]ω)]σ).
Proof with (updates; meta; eauto 3 with typ updates).
  intros.
  split...
  intros l' H__l'.
  lets (C' & ω' & μ' & ? & ? & ?): (proj2 H) l'...
  destruct_eq (l = l'); subst...
  - exists C, [f ↦ v]ω, μ'; splits...
    destruct (ct C) as [Args Flds Mtds] eqn:H__ct.
    assert (f < dom Flds)...
    inverts H11.
    + eapply ot_hot; [eassumption|].
      intros.
      lets [?v [ ]]: H17 f...
      lets [?v [ ]]: H17 f0...
      destruct_eq (f = f0); subst...
      exists v; split...
      eexists...
    + eapply ot_warm; [eassumption |].
      intros.
      lets [?v [ ]]: H17 f...
      lets [?v [ ]]: H17 f0...
      destruct_eq (f = f0); subst...
      exists v; split...
      eexists...
    + eapply ot_cool; updates; try reflexivity.
      intros.
      lets: H16 μ__f H1 H2...
      destruct_eq (f = f0); subst...
      exists (D0, μ)...
    + apply ot_cold.
  - exists C', ω', μ'; splits...
Qed.
