From Celsius Require Export Language Notations Helpers.
Require Import List ListSet.
Open Scope nat_scope.
Import ListNotations.


(* Mode lattice *)
Inductive S_Mode: Mode -> Mode -> Prop :=
| s_mode_refl : forall μ, μ ⊑ μ
| s_mode_hot: forall μ, hot ⊑ μ
| s_mode_warm: forall Ω, warm ⊑ cool Ω
| s_mode_union: forall Ω1 Ω2, cool (Ω1 + Ω2) ⊑ cool Ω1
| s_mode_cold: forall μ, μ ⊑ cold
where "m1 ⊑ m2" := (S_Mode m1 m2).
Global Hint Resolve s_mode_cold s_mode_hot s_mode_warm s_mode_union: typ.

Lemma s_mode_trans: forall μ1 μ2 μ3, μ1 ⊑ μ2 -> μ2 ⊑ μ3 -> μ1 ⊑ μ3.
Proof.
  intros.
  inversion H; steps;
    inversion H0; steps.
  rewrite Plus.plus_assoc_reverse.
  eauto with typ.
Qed.
Global Hint Resolve s_mode_trans: typ.


(* Subtyping *)

Inductive S_Typ : Tpe -> Tpe -> Prop :=
| s_typ_mode (C: ClN) μ1 μ2: μ1 ⊑ μ2 -> (C, μ1) <: (C, μ2)
where "T1 <: T2" := (S_Typ T1 T2).

Inductive S_Typs : (list Tpe) -> (list Tpe) -> Prop :=
| s_typs_nil: S_Typs nil nil
| s_typs_cons: forall Ts1 Ts2 T1 T2,
    S_Typs Ts1 Ts2 ->
    T1 <: T2 ->
    S_Typs (T1::Ts1) (T2::Ts2).
Global Hint Resolve s_typ_mode: typ.

Lemma s_typ_refl:
  forall T, T <: T.
Proof.
  destruct T, m;
    eapply s_typ_mode, s_mode_refl.
Qed.
Global Hint Resolve s_typ_refl: typ.

Lemma s_typ_trans:
  forall T1 T2 T3, T1 <: T2 -> T2 <: T3 -> T1 <: T3.
Proof.
  intros; inversion H; inversion H0; steps; eauto with typ.
Qed.
Global Hint Resolve s_typ_trans: typ.

Definition P_hot (T: Tpe) :=
  match T with
  | (_, hot) => True
  | _ => False
  end.

Definition P_hots := Forall P_hot.

Lemma P_hots_In:
  forall Ts T, P_hots Ts -> List.In T Ts -> P_hot T.
Proof.
  unfold P_hots; intros; eapply Forall_forall; eauto.
Qed.

(** ** Expression Typing *)


(** e can have the type U with env Γ and `this` of type T *)
Inductive T_Expr : EnvTyping -> Tpe -> Expr -> Tpe -> Prop :=
| t_sub:
    forall Γ T e U U',
      (Γ, T) ⊢ e : U' ->
      (U' <: U) ->
      (Γ, T) ⊢ e : U

| t_var:
    forall Γ T x U,
      typeLookup Γ x = Some U ->
      (Γ, T) ⊢ (var x) : U

| t_this:
    forall Γ T,
      (Γ, T) ⊢ this : T

| t_selhot:
    forall Γ T e f C D μ,
      (Γ, T) ⊢ e : (D, hot) ->
      (fieldType D f = Some (C, μ)) ->
      (Γ, T) ⊢ (fld e f) : (C, hot)

| t_selwarm:
    forall Γ T e f U D,
      (Γ, T) ⊢ e : (D, warm) ->
      (fieldType D f = Some U) ->
      (Γ, T) ⊢ (fld e f) : U

| t_selcool:
    forall Γ T e f U D Ω,
      (Γ, T) ⊢ e : (D, cool Ω) ->
      f <= Ω ->
      (fieldType D f = Some U) ->
      (Γ, T) ⊢ (fld e f) : U

| t_new:
    forall Γ T C args paramTs fields methods,
      ct C = Some (class paramTs fields methods) ->
      (Γ, T) ⊩ args : paramTs ->
      (Γ, T) ⊢ (new C args) : (C, warm)

| t_new_hot:
    forall Γ T C args argsTs paramTs fields methods,
      ct C = Some (class paramTs fields methods) ->
      (Γ, T) ⊩ args : argsTs ->
      P_hots argsTs ->
      S_Typs argsTs paramTs ->
      (Γ, T) ⊢ (new C args) : (C, hot)

| t_block:
    forall Γ T U e1 f e2 e3 C μ,
      (Γ, T) ⊢ (fld e1 f) : (C, μ) ->
      (Γ, T) ⊢ e2 : (C, hot) ->
      (Γ, T) ⊢ e3 : U ->
      (Γ, T) ⊢ (asgn e1 f e2 e3) : U

| t_call:
    forall Γ T e m args paramTs retT body μ0 μ_m C,
      (Γ, T) ⊢ e : (C, μ0) ->
      μ0 ⊑ μ_m ->
      methodInfo C m = Some (μ_m, paramTs, retT, body) ->
      (Γ, T) ⊩ args : paramTs ->
      (Γ, T) ⊢ (mtd e m args) : retT

| t_call_hot:
    forall Γ T e m args argTs paramTs D body μ0 μ_r C,
      (Γ, T) ⊢ e : (C, hot) ->
      (C, hot) <: (C, μ0) ->
      methodInfo C m = Some (μ0, paramTs, (D, μ_r), body) ->
      (Γ, T) ⊩ args : argTs ->
      P_hots argTs ->
      S_Typs argTs paramTs ->
      (Γ, T) ⊢ (mtd e m args) : (D, hot)
where  "( Γ , T )  ⊢ e : U" := (T_Expr Γ T e U)

with T_Exprs: EnvTyping -> Tpe -> (list Expr) -> (list Tpe) -> Prop :=
| t_exprs_nil: forall Γ T, T_Exprs Γ T [] []
| t_exprs_cons: forall Γ T Ts es Th eh,
    (Γ, T) ⊩ es : Ts ->
    (Γ, T) ⊢ eh : Th ->
    (Γ, T) ⊩ (eh::es) : (Th::Ts)
where  "( Γ , T )  ⊩ es : Us" := (T_Exprs Γ T es Us).

(** ** Field typing *)
Definition T_Field (Γ:EnvTyping) T f :=
  match f with
  | field U e => ((nil:EnvTyping), T) ⊢ e : U
  end.

Inductive T_Fields: EnvTyping -> Tpe -> (list Field) -> Prop :=
| t_fields_nil: forall Γ T, T_Fields Γ T []
| f_fields_cool_cons: forall Γ C Ω f fs,
    T_Field Γ (C, cool Ω) f ->
    T_Fields Γ (C, cool (S Ω)) fs ->
    T_Fields Γ (C, cool Ω) (f::fs).

(** ** Method typing *)
Definition T_Method C m :=
  match m with
  | method μ argTs retT body => (argTs, (C, μ)) ⊢ body : retT
  end.
Definition T_Methods C (methods: Mtd -> option Method) :=
  forall id m, methods id = Some m -> T_Method C m.

(** ** Class typing *)
Definition T_Class C cl :=
  match cl with
  | class paramTs fields methods => T_Fields paramTs (C, cold) fields /\ T_Methods C methods
  end.

Fixpoint T_Classes (Ct: list Class) i :=
  match Ct with
  | nil => True
  | C::Ct' => (T_Class i C) /\ (T_Classes Ct' (S i))
  end.

(** ** Program typing *)

Definition T_Prog :=
  match (ct entry) with
  | Some (class nil nil methods) =>
    exists e T, methods main = Some (method hot nil T e) /\
    ((nil, (entry, hot)) ⊢ e : T) /\ T_Classes Ξ 0
  | _ => False
  end.
