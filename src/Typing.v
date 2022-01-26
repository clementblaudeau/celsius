From Celsius Require Export Language Notations Helpers LibTactics.
Require Import List ListSet Psatz.
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

Lemma s_mode_cool: forall Ω1 Ω2, cool Ω1 ⊑ cool Ω2 <-> Ω2 <= Ω1.
Proof.
  split; intros.
  - inversion H; subst; try lia.
  - assert (Ω2+(Ω1 - Ω2) = Ω1) by lia.
    pose proof (s_mode_union Ω2 (Ω1 - Ω2)).
    rewrite H0 in H1.
    assumption.
Qed.

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
      f < Ω ->
      (fieldType D f = Some U) ->
      (Γ, T) ⊢ (fld e f) : U

| t_new:
    forall Γ T C args Args Flds Mtds,
      ct C = class Args Flds Mtds ->
      (Γ, T) ⊩ args : Args ->
      (Γ, T) ⊢ (new C args) : (C, warm)

| t_new_hot:
    forall Γ T C args argsTs Args Flds Mtds,
      ct C = class Args Flds Mtds ->
      (Γ, T) ⊩ args : argsTs ->
      P_hots argsTs ->
      S_Typs argsTs Args ->
      (Γ, T) ⊢ (new C args) : (C, hot)

| t_block:
    forall Γ T U e1 f e2 e3 C μ,
      (Γ, T) ⊢ (fld e1 f) : (C, μ) ->
      (Γ, T) ⊢ e2 : (C, hot) ->
      (Γ, T) ⊢ e3 : U ->
      (Γ, T) ⊢ (asgn e1 f e2 e3) : U

| t_call:
    forall Γ T e m args argsT U e__m μ0 μ__m C,
      (Γ, T) ⊢ e : (C, μ0) ->
      μ0 ⊑ μ__m ->
      methodInfo C m = Some (μ__m, argsT, U, e__m) ->
      (Γ, T) ⊩ args : argsT ->
      (Γ, T) ⊢ (mtd e m args) : U

| t_call_hot:
    forall Γ T e m args argTs paramTs D body μ0 μ_r C,
      (Γ, T) ⊢ e : (C, hot) ->
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

(** ** Class typing *)
Definition T_Classes := forall C,
    match (ct C) with
    | class Args Flds Mtds =>
        T_Fields Args (C, cold) Flds /\
          (forall m μ ρ T e, Mtds m = Some (method μ ρ T e) -> (ρ, (C, μ)) ⊢ e : T)
    end.

(** ** Program typing *)
Definition T_Prog :=
  match ct entry with
  | class nil nil Mtds =>
    exists e T, Mtds main = Some (method hot nil T e) /\
             ((nil, (entry, hot)) ⊢ e : T) /\ T_Classes
  | _ => False
  end.





(** * Inversion lemmas *)

Lemma t_this_inv:
  forall Γ U T,
    (Γ, U) ⊢ this : T -> U <: T.
Proof.
  intros. remember this as e.
  induction H; steps; eauto with typ.
Qed.

Lemma t_mtd_inv: forall Γ T__this e m args T,
    ((Γ, T__this) ⊢ (mtd e m args) : T) ->
    exists C D e__m argTs paramTs μ__m μ0 μ__r,
      ((Γ, T__this) ⊢ e : (C, μ0)) /\
        methodInfo C m = Some (μ__m, paramTs, (D, μ__r),  e__m) /\
        μ0 ⊑ μ__m /\
        ((Γ, T__this) ⊩ args : argTs) /\
        S_Typs argTs paramTs /\
        ((D, hot) <: T) /\
        ((D, μ__r) <: T \/ P_hots argTs /\ μ0 = hot).
Proof with (eauto with typ wf lia).
  introv H.
  remember (mtd e m args) as E.
  induction H; steps...
  - repeat eexists...
  - repeat eexists; steps...
  - destruct U.
    repeat eexists...
    clear IHT_Expr H1 H H0 H2.
    induction argsT ; eauto using S_Typs with typ...
  - repeat eexists...
Qed.


(** ** Induction principle for typing *)

Section typing_ind.
  Variable P : forall Γ T e U, ((Γ, T) ⊢ e : U) -> Prop.
  Variable Pl : forall Γ T el Ul, ((Γ, T) ⊩ el : Ul) -> Prop.

  Variable P_sub: forall Γ T e U U' H__U' H__sub,
      P Γ T e U' H__U' ->
      P Γ T e U (t_sub Γ T e U U' H__U' H__sub).

  Variable P_var: forall Γ T x U H__lkp,
      P Γ T (var x) U (t_var Γ T x U H__lkp).

  Variable P_this: forall Γ T,
      P Γ T this T (t_this Γ T).

  Variable P_selhot: forall Γ T e f C D μ H__D H__field,
      P Γ T e (D, hot) H__D ->
      P Γ T (fld e f) (C, hot) (t_selhot Γ T e f C D μ H__D H__field).

  Variable P_selwarm: forall Γ T e f U D H__D H__field,
      P Γ T e (D, warm) H__D ->
      P Γ T (fld e f) U (t_selwarm Γ T e f U D H__D H__field).

  Variable P_selcool: forall Γ T e f U D Ω H__D H__f H__field,
      P Γ T e (D, cool Ω) H__D ->
      P Γ T (fld e f) U (t_selcool Γ T e f U D Ω H__D H__f H__field).

  Variable P_new: forall Γ T C args Args Flds Mtds H__ct H__args,
      Pl Γ T args Args H__args ->
      P Γ T (new C args) (C, warm) (t_new Γ T C args Args Flds Mtds H__ct H__args).

  Variable P_new_hot: forall Γ T C args argsTs Args Flds Mtds H__ct H__args H__hots H__subs,
      Pl Γ T args argsTs H__args ->
      P Γ T (new C args) (C, hot) (t_new_hot Γ T C args argsTs Args Flds Mtds H__ct H__args H__hots H__subs).

  Variable P_block: forall Γ T U e1 f e2 e3 C μ H__fld H__e2 H__e3,
      P Γ T (fld e1 f) (C, μ) H__fld ->
      P Γ T e2 (C, hot) H__e2 ->
      P Γ T e3 U H__e3 ->
      P Γ T (asgn e1 f e2 e3) U (t_block Γ T U e1 f e2 e3 C μ H__fld H__e2 H__e3).

  Variable P_call: forall Γ T e m args argsT U e__m μ0 μ__m C H__e H__sub H__mtd H__args,
      P Γ T e (C, μ0) H__e ->
      Pl Γ T args argsT H__args ->
      (* P argsT (C, μ__m) e__m U (typable_method m C μ__m argsT U e__m H__mtd) ->*)
      P Γ T (mtd e m args) U (t_call Γ T e m args argsT U e__m μ0 μ__m C H__e H__sub H__mtd H__args).

  Variable P_call_hot: forall Γ T e m args argTs paramTs D body μ0 μ_r C H__e H__mtd H__args H__hots H__subs,
      P Γ T e (C, hot) H__e ->
      Pl Γ T args argTs H__args ->
      P Γ T (mtd e m args) (D, hot) (t_call_hot Γ T e m args argTs paramTs D body μ0 μ_r C H__e H__mtd H__args H__hots H__subs).

  Variable Pl_nil: forall Γ T,
      Pl Γ T [] [] (t_exprs_nil Γ T).

  Variable Pl_cons: forall Γ T U Ul e el H__el H__e,
      P Γ T e U H__e ->
      Pl Γ T el Ul H__el ->
      Pl Γ T (e::el) (U::Ul) (t_exprs_cons Γ T Ul el U e H__el H__e).

  Fixpoint typing_ind Γ T e U (typing: (Γ, T) ⊢ e : U) : P Γ T e U typing :=
    match typing with
    | t_sub Γ T e U U' H__U' H__sub => P_sub Γ T e U U' H__U' H__sub (typing_ind Γ T e U' H__U')
    | t_var Γ T x U H__lkp => P_var Γ T x U H__lkp
    | t_this Γ T => P_this Γ T
    | t_selhot Γ T e f C D μ H__D H__field =>
        P_selhot Γ T e f C D μ H__D H__field
                 (typing_ind Γ T e (D, hot) H__D)
    | t_selwarm Γ T e f U D H__D H__field =>
        P_selwarm Γ T e f U D H__D H__field
                  (typing_ind Γ T e (D, warm) H__D)
    | t_selcool Γ T e f U D Ω H__D H__f H__field =>
        P_selcool Γ T e f U D Ω H__D H__f H__field
                  (typing_ind Γ T e (D, cool Ω) H__D)
    | t_new Γ T C args Args Flds Mtds H__ct H__args =>
        P_new Γ T C args Args Flds Mtds H__ct H__args
              (typing_list_ind Γ T args Args H__args)
    | t_new_hot Γ T C args argsTs Args Flds Mtds H__ct H__args H__hots H__subs =>
        P_new_hot Γ T C args argsTs Args Flds Mtds H__ct H__args H__hots H__subs
                  (typing_list_ind Γ T args argsTs H__args)
    | t_block Γ T U e1 f e2 e3 C μ H__fld H__e2 H__e3 =>
        P_block Γ T U e1 f e2 e3 C μ H__fld H__e2 H__e3
                (typing_ind Γ T (fld e1 f) (C, μ) H__fld)
                (typing_ind Γ T e2 (C, hot) H__e2)
                (typing_ind Γ T e3 U H__e3)
    | t_call Γ T e m args argsT U e__m μ0 μ__m C H__e H__sub H__mtd H__args =>
        P_call Γ T e m args argsT U e__m μ0 μ__m C H__e H__sub H__mtd H__args
               (typing_ind Γ T e (C, μ0) H__e)
               (typing_list_ind Γ T args argsT H__args)
    | t_call_hot Γ T e m args argTs paramTs D body μ0 μ_r C H__e H__mtd H__args H__hots H__subs =>
        P_call_hot Γ T e m args argTs paramTs D body μ0 μ_r C H__e H__mtd H__args H__hots H__subs
                   (typing_ind Γ T e (C, hot) H__e)
                   (typing_list_ind Γ T args argTs H__args)
    end
  with typing_list_ind Γ T el Ul (typing_list: (Γ, T) ⊩ el : Ul) : Pl Γ T el Ul typing_list :=
         match typing_list with
         | t_exprs_nil Γ T => Pl_nil Γ T
         | t_exprs_cons Γ T Ul el U e H__el H__e =>
             Pl_cons Γ T U Ul e el H__el H__e
                     (typing_ind Γ T e U H__e)
                     (typing_list_ind Γ T el Ul H__el)
         end.

End typing_ind.
