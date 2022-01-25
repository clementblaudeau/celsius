(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** Store typing *)

From Celsius Require Export Typing LibTactics Tactics Reachability Wellformedness.
Require Import Coq.ssr.ssreflect Coq.ssr.ssrbool Coq.Lists.List Coq.micromega.Psatz Ensembles Coq.Program.Tactics.
(* Import ListNotations. *)
(* Open Scope nat_scope. *)


(** * Main definitions *)

(** ** Monotonicity *)
Definition monotonicity Σ1 Σ2 :=
  forall l, l < dom Σ1 -> (exists T1 T2, getType Σ1 l = Some T1 /\ getType Σ2 l = Some T2 /\ T2 <: T1).
Notation "Σ1 ≼ Σ2" := (monotonicity Σ1 Σ2) (at level 60).

(** ** Authority *)
Definition authority Σ1 Σ2 :=
  forall l C Ω, getType Σ1 l = Some (C, cool Ω) -> getType Σ2 l = Some (C, cool Ω).
Notation "Σ1 ▷ Σ2" := (authority Σ1 Σ2) (at level 60).

(** ** Value typing (with variants) *)

Inductive value_typing : StoreTyping -> Loc -> Tpe -> Prop :=
| vt_sub : forall Σ l (T1 T2: Tpe),
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

Definition value_typing_mode_locset Σ L (μ:Mode) :=
  forall (l: Loc), (In Loc L l) -> Σ ⊨ l : μ.
Global Instance notation_value_typing_mode_LocSet : notation_dash_colon StoreTyping LocSet Mode :=
  { dash_colon_ := value_typing_mode_locset }.
Global Hint Unfold notation_value_typing_mode_LocSet: notations.

Definition value_typing_locset (Σ:StoreTyping) (L: list Loc) (vl: list Tpe) :=
  Forall2 (fun (l: Loc) (T:Tpe) => Σ ⊨ l : T) L vl.
Global Instance notation_value_typing_LocSet : notation_dash_colon StoreTyping (list Loc) (list Tpe) :=
  { dash_colon_ := value_typing_locset }.
Global Hint Unfold notation_value_typing_LocSet: notations.

(** ** Stackability *)
Definition stackability_st (Σ1 Σ2: StoreTyping) :=
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
| ot_cool : forall Σ C ω,
    (forall f v T μ,
        getVal ω f = Some v ->
        fieldType C f = Some (T, μ) ->
        Σ ⊨ v : (T, μ)) ->
    object_typing Σ (C,ω) (C, cool (dom ω))
| ot_cold : forall Σ C ω,
    (forall f v T μ,
        getVal ω f = Some v ->
        fieldType C f = Some (T, μ) ->
        Σ ⊨ v : (T, μ)) ->
    object_typing Σ (C,ω) (C, cold).

Global Instance notation_object_typing : notation_dash_colon StoreTyping Obj Tpe :=
  { dash_colon_ := object_typing }.
Global Hint Unfold notation_object_typing: notations.

(** ** Store_typing *)
(** Here is the link between the abstract environment of types and the store used in execution *)
Definition store_typing (Σ: StoreTyping) (σ: Store) :=
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
Inductive env_typing : EnvTyping -> StoreTyping -> Env -> Prop :=
| et_nil : forall Σ, env_typing nil Σ nil
| et_cons : forall Γ Σ ρ l T,
    env_typing Γ Σ ρ ->
    (Σ ⊨ l : T) ->
    env_typing (T :: Γ) Σ (l :: ρ).
Global Instance notation_env_typing: notation_dash (EnvTyping * StoreTyping) Env :=
  { dash_ := fun a b => env_typing (fst a) (snd a) b }.
Global Hint Unfold notation_env_typing: notations.

Implicit Type l : Loc.
Implicit Type T : Tpe.
Implicit Type Σ : StoreTyping.

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
            add_hypothesis fresh (getType_in_dom Σ l T H)
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

(** * Monotonicity results *)

Lemma monotonicity_dom :
  forall Σ1 Σ2, Σ1 ≼ Σ2 -> (dom Σ1 <= dom Σ2).
Proof with meta; eauto with lia updates .
  intros.
  destruct Σ1; steps...
  specialize (H (dom Σ1)) as (? & ? & ?); steps ...
Qed.
Global Hint Resolve monotonicity_dom: typ.

(* Ltac monotonicity_dom := *)
(*   repeat match goal with *)
(*          | H : ?Σ ≼ ?Σ', *)
(*              H': in_dom ?Σ ?l |- _ => *)
(*              let Hf := fresh "H__dom" in *)
(*              add_hypothesis Hf (monotonicity_dom Σ Σ' H l H') *)
(*          end. *)

Lemma value_typing_dom : forall Σ l T,
    Σ ⊨ l : T -> l < dom Σ.
Proof with meta; eauto.
  intros ...
Qed.
Global Hint Resolve value_typing_dom: typ.

Lemma value_typing_monotonicity: forall (Σ1 Σ2: StoreTyping) l T,
    Σ1 ≼ Σ2 -> Σ1 ⊨ l : T -> Σ2 ⊨ l : T.
Proof with (meta; eauto with lia typ).
  intros ...
  specialize (H l H0) as [T1 [T2 [Hs1 [Hs2 H__sub]]]] ...
  eapply vt_sub ...
Qed.
Global Hint Resolve value_typing_monotonicity: typ.

Lemma env_typing_monotonicity: forall (Σ1 Σ2: StoreTyping) (Γ:EnvTyping) (ρ: Env),
    Σ1 ≼ Σ2 -> (Γ, Σ1) ⊨ ρ -> (Γ, Σ2) ⊨ ρ.
Proof.
  intros.
  autounfold with notations in H0. simpl in H0.
  induction H0.
  - steps.
  - specialize (IHenv_typing H).
    apply et_cons; steps; eauto with typ.
Qed.
Global Hint Resolve env_typing_monotonicity: typ.


Lemma object_typing_monotonicity: forall (Σ1 Σ2: StoreTyping) (o: Obj) T,
    Σ1 ≼ Σ2 -> Σ1 ⊨ o : T -> Σ2 ⊨ o : T.
Proof with (meta; eauto with lia typ).
  intros ...
  autounfold with notations in H0.
  inversion H0; steps.
  - eapply ot_hot ...
    intros.
    specialize (H7 f D μ H1 H2); steps ...
    exists v ... split => //.
    exists (D, hot)...
    lets: H H6. steps ...
  - eapply ot_warm ...
    intros.
    specialize (H7 f D μ H1 H2); steps ...
    exists v; steps ...
    lets: H H6. steps ...
    exists (D, μ1) ...
  - apply ot_cool ...
  - apply ot_cold ...
Qed.
Global Hint Resolve object_typing_monotonicity: typ.

Lemma mn_refl: forall Σ,
    Σ ≼ Σ.
Proof with (meta; eauto with lia typ).
  intros Σ l; steps ...
  destruct (getType Σ l) eqn:H__l ...
  exfalso.
  apply getType_none in H__l...
Qed.
Global Hint Resolve mn_refl : typ.

Lemma mn_trans: forall Σ1 Σ2 Σ3,
    Σ1 ≼ Σ2 -> Σ2 ≼ Σ3 -> Σ1 ≼ Σ3.
Proof with (meta; eauto with lia typ).
  intros.
  intros l; steps.
  specialize (H l H1); steps...
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
  intros; meta. intros l. specialize (H0  l); eauto with typ.
Qed.

Lemma env_regularity: forall Γ Σ ρ x U T,
    (Γ, Σ) ⊨ ρ ->
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
  - steps.
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
                    destruct ((proj2 H1) l (ltac:(rewrite <-(proj1 H1); apply (getObj_dom σ _ l H2)))) as
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
                    destruct ((proj2 H1) l (ltac:(rewrite <-(proj1 H1); apply (getObj_dom σ _ l H2)))) as
                      (?C & ?ω & ?μ & H_obj & H_tpe & H_vt);
                    symmetry in H_tpe;
                    rewrite H2 in H_tpe; inverts H_tpe
              end
          end; cross_rewrites).

Lemma hot_transitivity : forall (Σ: StoreTyping) (σ: Store) l l',
    wf σ ->
    (Σ ⊨ l : hot) ->
    (Σ ⊨ σ) ->
    (σ ⊨ l ⇝ l') ->
    (Σ ⊨ l' : hot).
Proof with (storeTyping_update; meta; eauto with lia typ).
  intros.
  gen Σ.
  induction H2; steps...
  inverts H__vt ...
  lets [? _]: H H1.
  lets: H3 H10.
  lets [?C [?μ ?]]:  fieldType_exists f ...
  lets [?v [ ]]: H11 H9 ...
  exists C...
Qed.


(** ** Authority results *)
Lemma aty_refl: forall Σ, Σ ▷ Σ.
Proof with (meta; eauto with typ lia).
  intros Σ l H.
  destruct (getType Σ l) eqn:E; eauto.
Qed.
Global Hint Resolve aty_refl : typ.

Lemma aty_trans: forall Σ1 Σ2 Σ3,
    Σ1 ▷ Σ2 ->
    Σ2 ▷ Σ3 ->
    Σ1 ▷ Σ3.
Proof with steps.
  intros. intros l ...
Qed.
Global Hint Resolve aty_trans : typ.

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
  exists x, T2; steps; eauto with typ.
Qed.
Global Hint Resolve stk_st_trans : typ.



(** ** Selection results *)
Lemma hot_selection : forall Σ σ (l: Loc) C ω,
    wf σ ->
    Σ ⊨ σ ->
    (Σ ⊨ l : (C, hot)) ->
    getObj σ l = Some (C, ω) ->
    (forall f D μ, fieldType C f = Some (D, μ) ->
              exists v, getVal ω f = Some v /\
                   Σ ⊨ v : (D, hot)).
Proof with (meta; eauto with typ lia).
  intros ...
  lets [ ]: (proj2 H0) l ...
  steps ...
  inverts H8.
  lets [? _]: H H6.
  lets: H2 H9.
  lets [? [ ] ]: H10 f H3...
Qed.

Lemma warm_selection : forall Σ σ (l: Loc) C ω f T,
    Σ ⊨ σ ->
    (Σ ⊨ l : (C, warm)) ->
    getObj σ l = Some (C, ω) ->
    fieldType C f = Some T ->
    exists v, getVal ω f = Some v /\ Σ ⊨ v : T.
Proof with (meta; eauto with typ lia).
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

Lemma cool_selection : forall Σ σ C (l: Loc) Ω ω f T,
    Σ ⊨ σ ->
    (Σ ⊨ l : (C, cool Ω)) ->
    getObj σ l = Some (C, ω) ->
    fieldType C f = Some T ->
    f < Ω ->
    exists v, getVal ω f = Some v /\ Σ ⊨ v : T.
Proof with (meta; eauto with typ lia).
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


(* (** ** Initialization results *) *)
(* Lemma field_initialization: forall Σ σ l l' C Ω ω T, *)
(*     Σ ⊨ σ -> *)
(*     getType Σ l = Some (C, cool Ω) *)
(*     getObj σ l = Some (C, ω) -> *)
(*     fieldType C f = Some T -> *)
(*     (Σ ⊨ l' : T) -> *)
(*     let σ' := [l ↦ (C, [f ↦ l']ω)]σ in *)
(*     let Σ' := [ ]Σ *)

(** Env typing lemmas *)

Lemma env_typing_subs: forall ρ1 ρ2 Σ vl,
    (ρ1, Σ) ⊨ vl ->
    S_Typs ρ1 ρ2 ->
    (ρ2, Σ) ⊨ vl.
Proof.
  induction ρ1; intros.
  - inverts H0; eauto with typ.
  - inverts H0; meta.
    inverts H; simpl in *.
    eapply IHρ1 in H4; eauto.
    eapply et_cons; simpl in *; eauto with typ.
    meta.
    exists (C, μ1); eauto with typ.
Qed.
Global Hint Resolve env_typing_subs: typ.


Lemma storeTyping_dom:
  forall Σ σ,
    Σ ⊨ σ -> dom σ = dom Σ.
Proof with (meta; eauto with typ lia).
  intros ...
Qed.
Global Hint Resolve storeTyping_dom: typ.
