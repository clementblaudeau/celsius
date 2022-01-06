(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** Store typing *)

From Celsius Require Export Typing LibTactics Tactics Reachability.
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
  forall l, l < dom Σ1 -> (exists T, getType Σ1 l = Some T /\ getType Σ2 l = Some T).
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

Definition value_typing_locset Σ L (μ:Mode) :=
  forall (l: Loc), (In Loc L l) -> Σ ⊨ l : μ.
Global Instance notation_value_typing_LocSet : notation_dash_colon StoreTyping LocSet Mode :=
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
| ot_hot : forall Σ C ω,
  (exists args flds mtds,
    (ct C = Some (class args flds mtds)) /\
      (forall f, f < length ω ->
            exists v D μ,
              getVal ω f = Some v /\
              fieldType C f = Some (D, μ) /\
              Σ ⊨ v : (D, hot))) ->
    object_typing Σ (C,ω) (C, hot)
| ot_warm : forall Σ C ω,
    (exists args flds mtds,
        (ct C = Some (class args flds mtds)) /\
          (forall f, f < length flds ->
                exists v D μ,
                  getVal ω f = Some v ->
                  fieldType C f = Some (D, μ) ->
                  Σ ⊨ v : (D, μ))) ->
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
  forall l, l < dom Σ ->
       exists C ω μ, getObj σ l = Some (C,ω) /\
                  getType Σ l = Some (C, μ) /\
                  Σ ⊨ (C, ω) : (C, μ).
Global Instance notation_store_typing: notation_dash StoreTyping Store :=
  { dash_ := store_typing }.
Global Hint Unfold notation_store_typing: notations.

(** ** Environment typing *)
Inductive env_typing : EnvTyping -> StoreTyping -> Env -> Prop :=
| et_nil : forall Σ, env_typing nil Σ nil
| et_cons : forall Γ Σ ρ l T,
    env_typing Γ Σ ρ ->
    Σ ⊨ l : T ->
    env_typing (T :: Γ) Σ (l :: ρ).
Global Instance notation_env_typing: notation_dash (EnvTyping * StoreTyping) Env :=
  { dash_ := fun a b => env_typing (fst a) (snd a) b }.
Global Hint Unfold notation_env_typing: notations.

Implicit Type l : Loc.
Implicit Type T : Tpe.
Implicit Type Σ : StoreTyping.

(** * Tactics *)
Ltac meta :=
  repeat
    match goal with
    | H: getObj ?σ ?l = Some ?O,
        H': getObj ?σ ?l = Some ?O' |- _ => rewrite H' in H; inverts H
    | H: getType ?Σ ?l = Some ?T,
        H': getType ?Σ ?l = Some ?T' |- _ => rewrite H' in H; inverts H
    | H: getVal ?ρ ?f = Some ?l,
        H': getVal ?ρ ?f = Some ?l' |- _ => rewrite H' in H; inverts H
    | H: getType ?Σ ?l = Some ?T |- _ =>
        let fresh := fresh "H__dom" in
        add_hypothesis fresh (getType_dom Σ l T H)
    | H: getVal ?ρ ?f = Some ?l |- _ =>
        let fresh := fresh "H__dom" in
        add_hypothesis fresh (getVal_dom ρ f l H)
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
    | H: (?C, ?μ) <: (?C', ?μ') |- _ => inverts H
    end ; sort;
  try lia.

(** * Monotonicity results *)

Lemma monotonicity_dom :
  forall Σ1 Σ2, Σ1 ≼ Σ2 -> dom Σ1 <= dom Σ2.
Proof with meta.
  intros.
  edestruct PeanoNat.Nat.le_gt_cases; eauto.
  destruct (dom Σ1) eqn:E; steps; try lia ...
  specialize (H n) ...
  destruct H; steps ...
Qed.
Global Hint Resolve monotonicity_dom: typ.

Ltac monotonicity_dom :=
  repeat match goal with
         | H : ?Σ ≼ ?Σ' |- _ =>
             let Hf := fresh "H__dom" in
             add_hypothesis Hf (monotonicity_dom Σ Σ' H)
         end.

Lemma value_typing_dom : forall Σ l T,
    Σ ⊨ l : T -> l < dom Σ.
Proof with meta.
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
  - apply ot_hot.
    exists args, flds, mtds; split => //.
    intros.
    specialize (H3 f H1); steps.
    exists v, D, μ; steps ...
  - apply ot_warm.
    exists args, flds, mtds; split => //.
    intros.
    specialize (H3 f H1); steps.
    exists v, D, μ; steps ...
  - apply ot_cool.
    intros.
    specialize (H3 f v T μ H1 H2); steps ...
  - apply ot_cold.
    intros.
    specialize (H3 f v T μ H1 H2); steps ...
Qed.
Global Hint Resolve object_typing_monotonicity: typ.

Lemma mn_refl: forall Σ,
    Σ ≼ Σ.
Proof with (meta; eauto with lia typ).
  intros Σ l; steps ...
  destruct (getType Σ l) eqn:H__l ...
  exfalso.
  apply nth_error_Some in H ...
Qed.
Global Hint Resolve mn_refl : typ.

Lemma mn_trans: forall Σ1 Σ2 Σ3,
    Σ1 ≼ Σ2 -> Σ2 ≼ Σ3 -> Σ1 ≼ Σ3.
Proof with (meta; eauto with lia typ).
  intros.
  intros l; steps.
  monotonicity_dom.
  specialize (H l H1); steps.
  specialize (H0 l) as [ ]; steps; try lia.
  exists T1 T0; steps ...
Qed.
Global Hint Resolve mn_trans: typ.

Lemma env_regularity: forall Γ Σ ρ x U T,
    (Γ, Σ) ⊨ ρ ->
    (Γ, U) ⊢ (var x) : T ->
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

Lemma hot_transitivity : forall (Σ: StoreTyping) (σ: Store) l l',
    Σ ⊨ l : hot ->
    Σ ⊨ σ ->
    σ ⊨ l ⇝ l' ->
    Σ ⊨ l' : hot.
Proof with (meta; eauto with lia typ).
  intros.
  gen Σ.
  induction H1; steps ...
  specialize (H3 l0) as [ ] ...
  steps ...
  inverts H8; steps ...
  specialize (H9 f) as [ ] ; steps...
  eexists; steps ...
Qed.


(** ** Authority results *)

Lemma aty_refl: forall Σ, Σ ▷ Σ.
Proof with (meta; eauto with typ lia).
  intros Σ l H.
  destruct (getType Σ l) eqn:E; eauto.
  exfalso;
  eapply nth_error_Some; unfold getType in *; eauto.
Qed.

Lemma aty_trans: forall Σ1 Σ2 Σ3,
    Σ1 ▷ Σ2 ->
    dom Σ1 <= dom Σ2 ->
    Σ2 ▷ Σ3 ->
    Σ1 ▷ Σ3.
Proof with steps.
  intros. intros l ...
  specialize (H l) ...
  specialize (H1 l) ...
  exists T; split ...
  destruct H1 as [T' [ ]];
    eauto with lia.
Qed.

(** ** Stackability results *)

Lemma stk_st_refl: forall Σ, Σ ≪ Σ.
Proof.
  intros Σ l H. right => //.
Qed.

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
