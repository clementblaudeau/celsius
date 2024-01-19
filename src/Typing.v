(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL & Inria 2020-2022 *)
(* ------------------------------------------------------------------------ *)
(* This file describes the typing rules *)

From Celsius Require Export Helpers.


(* ------------------------------------------------------------------------ *)
(** ** Mode lattice and subtyping *)

Inductive S_Mode: Mode -> Mode -> Prop :=
| s_mode_refl : forall μ, μ ⊑ μ
| s_mode_hot: forall μ, hot ⊑ μ
| s_mode_warm: forall Ω, warm ⊑ cool Ω
| s_mode_cool: forall Ω1 Ω2, Ω2 <= Ω1 -> cool Ω1 ⊑ cool Ω2
| s_mode_cold: forall μ, μ ⊑ cold
where "m1 ⊑ m2" := (S_Mode m1 m2).
Global Hint Constructors S_Mode: typ.

(* We then have basic results *)

Lemma s_mode_trans: forall μ1 μ2 μ3, μ1 ⊑ μ2 -> μ2 ⊑ μ3 -> μ1 ⊑ μ3.
Proof.
  intros.
  inversion H; steps;
    inversion H0; eauto with typ lia.
Qed.
Global Hint Resolve s_mode_trans: typ.

(* Subtyping *)

Inductive S_Typ : Tpe -> Tpe -> Prop :=
| s_typ_mode C μ1 μ2:
  μ1 ⊑ μ2 ->
  (C, μ1) <: (C, μ2)
where "T1 <: T2" := (S_Typ T1 T2).
Global Hint Resolve s_typ_mode: typ.

Ltac S_Typ:= repeat match goal with | H: _ <: _ |- _ => inverts H end.
Global Hint Extern 1 => S_Typ: typ. (* We want to invert subtyping as it is trivial *)

(* Subtyping between lists of types *)

Definition S_Typs := Forall2 (fun T1 T2 => S_Typ T1 T2).

(* Basic results *)

Lemma s_typ_refl:
  forall T, T <: T.
Proof.
  destruct T, m; eauto with typ.
Qed.
Global Hint Resolve s_typ_refl: typ.

Lemma s_typ_trans:
  forall T1 T2 T3, T1 <: T2 -> T2 <: T3 -> T1 <: T3.
Proof.
  intros; inversion H; inversion H0; steps; eauto with typ.
Qed.
Global Hint Resolve s_typ_trans: typ.

Lemma S_typs_refl:
  forall Ts, S_Typs Ts Ts.
Proof.
  intros. unfold S_Typs.
  induction Ts; eauto 3 using Forall2_cons with typ.
Qed.
Global Hint Resolve S_typs_refl: typ.

(* We then define predicate to check that all locations of a list are hot *)

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


(* ------------------------------------------------------------------------ *)
(** ** Expression Typing *)

Inductive expr_typing : EnvTyping -> Tpe -> Expr -> Tpe -> Prop :=

(* We have ambient subtyping *)
| t_sub:
    forall Γ Tthis e T T',
      (Γ, Tthis) ⊢ e : T' ->
      (T' <: T) ->
      (Γ, Tthis) ⊢ e : T

(* Lookup of a variable *)
| t_var:
    forall Γ Tthis x T,
      typeLookup Γ x = Some T ->
      (Γ, Tthis) ⊢ (e_var x) : T

(* Type of current object *)
| t_this:
    forall Γ Tthis,
      (Γ, Tthis) ⊢ e_this : Tthis

(* Accessing a field of an hot object gives an hot object *)
| t_selhot:
    forall Γ Tthis e f C D μ,
      (Γ, Tthis) ⊢ e : (D, hot) ->
      (fieldType D f = Some (C, μ)) ->
      (Γ, Tthis) ⊢ (e_fld e f) : (C, hot)

(* In other cases, accessing a defined fields give back its base type*)
| t_selcool:
    forall Γ Tthis e f T D Ω,
      (Γ, Tthis) ⊢ e : (D, cool Ω) ->
      f < Ω ->
      (fieldType D f = Some T) ->
      (Γ, Tthis) ⊢ (e_fld e f) : T

(* A newly created instance with hot arguments is also hot *)
| t_new_hot:
    forall Γ Tthis C args argsTs Args Flds Mtds,
      ct C = class Args Flds Mtds ->
      (Γ, Tthis) ⊩ args : argsTs ->
      P_hots argsTs ->
      S_Typs argsTs Args ->
      (Γ, Tthis) ⊢ (e_new C args) : (C, hot)

(* At least, a newly created instance is warm*)
| t_new:
    forall Γ Tthis C args Args Flds Mtds,
      ct C = class Args Flds Mtds ->
      (Γ, Tthis) ⊩ args : Args ->
      (Γ, Tthis) ⊢ (e_new C args) : (C, warm)

(* We restrict assignment to hot values to preserve monotonicity*)
| t_block:
    forall Γ Tthis T e1 f e2 e3 C μ,
      (Γ, Tthis) ⊢ (e_fld e1 f) : (C, μ) ->
      (Γ, Tthis) ⊢ e2 : (C, hot) ->
      (Γ, Tthis) ⊢ e3 : T ->
      (Γ, Tthis) ⊢ (e_asgn e1 f e2 e3) : T

(* Calling a method on an hot object with hot arguments produces a hot object*)
| t_call_hot:
    forall Γ Tthis e m args argTs paramTs D body μ0 μ_r C,
      (Γ, Tthis) ⊢ e : (C, hot) ->
      methodInfo C m = Some (μ0, paramTs, (D, μ_r), body) ->
      (Γ, Tthis) ⊩ args : argTs ->
      P_hots argTs ->
      S_Typs argTs paramTs ->
      (Γ, Tthis) ⊢ (e_mtd e m args) : (D, hot)

(* Otherwise, it produces the base type *)
| t_call:
    forall Γ Tthis e m args argsT T e__m μ C,
      (Γ, Tthis) ⊢ e : (C, μ) ->
      methodInfo C m = Some (μ, argsT, T, e__m) ->
      (Γ, Tthis) ⊩ args : argsT ->
      (Γ, Tthis) ⊢ (e_mtd e m args) : T

where  "( Γ , Tthis )  ⊢ e : T" := (expr_typing Γ Tthis e T)

with expr_list_typing: EnvTyping -> Tpe -> (list Expr) -> (list Tpe) -> Prop :=
| t_exprs_nil: forall Γ Tthis, expr_list_typing Γ Tthis [] []
| t_exprs_cons: forall Γ Tthis Ts es T e,
    (Γ, Tthis) ⊩ es : Ts ->
    (Γ, Tthis) ⊢ e : T ->
    (Γ, Tthis) ⊩ (e::es) : (T::Ts)
where  "( Γ , Tthis )  ⊩ es : Ts" := (expr_list_typing Γ Tthis es Ts).

Global Hint Constructors expr_typing: typ.

(* We add this lemma as if it were a rule (actually a consequence of t_selcool) *)

Lemma t_selwarm:
    forall Γ Tthis e f U D,
      (Γ, Tthis) ⊢ e : (D, warm) ->
      (fieldType D f = Some U) ->
      (Γ, Tthis) ⊢ (e_fld e f) : U.
Proof.
  eauto with typ.
Qed.

Lemma t_call_sub :
  forall Γ Tthis e m args argsT T e__m μ0 μ__m C,
   (Γ, Tthis) ⊢ e : (C, μ0) ->
   μ0 ⊑ μ__m ->
   methodInfo C m = Some (μ__m, argsT, T, e__m) ->
   (Γ, Tthis) ⊩ args : argsT ->
   (Γ, Tthis) ⊢ (e_mtd e m args) : T.
Proof.
  intros.
  eapply t_call; [ | eassumption | ]; eauto with typ.
Qed.


(* ------------------------------------------------------------------------ *)
(** ** Field typing *)

Definition T_Field (Γ:EnvTyping) T f :=
  match f with
  | field U e => (Γ, T) ⊢ e : U
  end.

Inductive T_Fields: EnvTyping -> Tpe -> (list Field) -> Prop :=
| t_fields_nil: forall Γ Tthis, T_Fields Γ Tthis []
| t_fields_cool_cons: forall Γ C Ω f fs,
    T_Field Γ (C, cool Ω) f ->
    T_Fields Γ (C, cool (S Ω)) fs ->
    T_Fields Γ (C, cool Ω) (f::fs).

Lemma T_Fields_In:
  forall Γ C Flds1 f Flds2 Ω,
    T_Fields Γ (C, cool Ω) (Flds1 ++ f :: Flds2) ->
    T_Field Γ (C, cool (Ω+dom Flds1)) f.
Proof with (eauto using T_Fields with typ lia).
  induction  Flds1; intros.
  - simpl in H. simpl. inverts H. rewrite <- plus_n_O...
  - simpl in H; simpl. inverts H. rewrite <- Nat.add_succ_comm ...
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Class typing *)

Definition T_Classes := forall C,
    match (ct C) with
    | class Args Flds Mtds =>
        T_Fields Args (C, cool 0) Flds /\
          (forall m μ ρ T e, Mtds m = Some (method μ ρ T e) -> (ρ, (C, μ)) ⊢ e : T)
    end.

(* ------------------------------------------------------------------------ *)
(** ** Program typing *)

Definition T_Prog :=
  T_Classes /\
  match EntryClass with
  | class nil nil Mtds => exists T e, Mtds main = Some (method hot nil T e)
  | _ => False
  end.

(* ------------------------------------------------------------------------ *)
(** * Inversion lemmas *)
(* Due to the ambient subtyping, we cannot invert typing judgments directly. We thus have to show
basic inversion lemmas. *)

Lemma t_this_inv:
  forall Γ U T,
    (Γ, U) ⊢ e_this : T -> U <: T.
Proof.
  intros. remember e_this as e.
  induction H; steps; eauto with typ.
Qed.

Lemma t_fld_inv:
  forall Γ T__this e f C μ,
    ((Γ, T__this) ⊢ (e_fld e f) : (C, μ)) ->
    exists D μ__e μ__f,
      ((Γ, T__this) ⊢ e : (D, μ__e)) /\
        fieldType D f = Some (C, μ__f) /\
        ((μ__e = hot) \/ (exists Ω, μ__e = cool Ω /\ f < Ω /\ μ__f ⊑ μ)).
Proof with (eauto with typ lia).
  introv H.
  remember (e_fld e f) as E.
  remember (C,μ) as T.
  gen C μ e f.
  induction H; steps...
  all: try destruct U' as [?C ?μ]; inverts H0.
  all: try specialize (IHT_Expr C μ0 eq_refl _ _ eq_refl)
    as (?D & ?μ__e & ?C & ?μ__f & ? & ? & [|[|]]); steps...
  all: repeat eexists...
  all: right; eexists...
Qed.

Lemma t_mtd_inv: forall Γ T__this e m args T,
    ((Γ, T__this) ⊢ (e_mtd e m args) : T) ->
    exists C D e__m argTs paramTs μ__m μ0 μ__r,
      ((Γ, T__this) ⊢ e : (C, μ0)) /\
        methodInfo C m = Some (μ__m, paramTs, (D, μ__r),  e__m) /\
        μ0 ⊑ μ__m /\
        ((Γ, T__this) ⊩ args : argTs) /\
        S_Typs argTs paramTs /\
        ((D, hot) <: T) /\
        ((D, μ__r) <: T \/ P_hots argTs /\ μ0 = hot).
Proof with (eauto with typ lia).
  introv H.
  remember (e_mtd e m args) as E.
  induction H; steps;
    try solve [repeat eexists; eauto with typ].
Qed.

Lemma t_new_inv:
  forall Γ T__this C args T,
    ((Γ, T__this) ⊢ (e_new C args) : T) ->
    exists Args Flds Mtds argsTs μ,
      T = (C, μ) /\
        ct C = class Args Flds Mtds /\
        ((Γ, T__this) ⊩ args : argsTs) /\
        S_Typs argsTs Args /\
        (warm ⊑ μ \/ (P_hots argsTs)).
Proof with (eauto with typ lia).
  introv H.
  remember (e_new C args) as E.
  induction H; subst; try discriminate...
  - S_Typ.
    destruct IHexpr_typing as (Args & Flds & Mtds & argsTs & μ0 & ? & ? & ? & ? & ?)...
    inverts H0; steps;
    repeat eexists; eauto with typ.
  - repeat eexists; steps...
  - inverts HeqE.
    exists Args Flds Mtds Args warm; splits ...
Qed.

Lemma t_asgn_inv:
  forall Γ T__this e1 f e2 e3 C μ,
    ((Γ, T__this) ⊢ (e_asgn e1 f e2 e3) : (C, μ)) ->
    exists D μ1 μ',
      ((Γ, T__this) ⊢ (e_fld e1 f) : (D, μ1)) /\
        ((Γ, T__this) ⊢ e2 : (D, hot)) /\
        (μ' ⊑ μ) /\
        ((Γ, T__this) ⊢ e3 : (C, μ')).
Proof with (eauto 3 with typ lia).
  introv H.
  remember (e_asgn e1 f e2 e3) as E.
  remember (C,μ) as T.
  gen C μ e1 f e2 e3.
  induction H; steps.
  - exists D, μ1, μ'; splits...
  - exists C, μ, μ0; splits...
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Induction principle for typing *)

Section typing_ind.
  Variable P : forall Γ Tthis e U, ((Γ, Tthis) ⊢ e : U) -> Prop.
  Variable Pl : forall Γ Tthis el Ul, ((Γ, Tthis) ⊩ el : Ul) -> Prop.

  Variable P_sub: forall Γ Tthis e U U' H__U' H__sub,
      P Γ Tthis e U' H__U' ->
      P Γ Tthis e U (t_sub Γ Tthis e U U' H__U' H__sub).

  Variable P_var: forall Γ Tthis x U H__lkp,
      P Γ Tthis (e_var x) U (t_var Γ Tthis x U H__lkp).

  Variable P_this: forall Γ Tthis,
      P Γ Tthis e_this Tthis (t_this Γ Tthis).

  Variable P_selhot: forall Γ Tthis e f C D μ H__D H__field,
      P Γ Tthis e (D, hot) H__D ->
      P Γ Tthis (e_fld e f) (C, hot) (t_selhot Γ Tthis e f C D μ H__D H__field).

  Variable P_selcool: forall Γ Tthis e f U D Ω H__D H__f H__field,
      P Γ Tthis e (D, cool Ω) H__D ->
      P Γ Tthis (e_fld e f) U (t_selcool Γ Tthis e f U D Ω H__D H__f H__field).

  Variable P_new: forall Γ Tthis C args Args Flds Mtds H__ct H__args,
      Pl Γ Tthis args Args H__args ->
      P Γ Tthis (e_new C args) (C, warm) (t_new Γ Tthis C args Args Flds Mtds H__ct H__args).

  Variable P_new_hot: forall Γ Tthis C args argsTs Args Flds Mtds H__ct H__args H__hots H__subs,
      Pl Γ Tthis args argsTs H__args ->
      P Γ Tthis (e_new C args) (C, hot) (t_new_hot Γ Tthis C args argsTs Args Flds Mtds H__ct H__args H__hots H__subs).

  Variable P_block: forall Γ Tthis U e1 f e2 e3 C μ H__fld H__e2 H__e3,
      P Γ Tthis (e_fld e1 f) (C, μ) H__fld ->
      P Γ Tthis e2 (C, hot) H__e2 ->
      P Γ Tthis e3 U H__e3 ->
      P Γ Tthis (e_asgn e1 f e2 e3) U (t_block Γ Tthis U e1 f e2 e3 C μ H__fld H__e2 H__e3).

  Variable P_call: forall Γ Tthis e m args argsT U e__m μ C H__e H__mtd H__args,
      P Γ Tthis e (C, μ) H__e ->
      Pl Γ Tthis args argsT H__args ->
      P Γ Tthis (e_mtd e m args) U (t_call Γ Tthis e m args argsT U e__m μ C H__e H__mtd H__args).

  Variable P_call_hot: forall Γ Tthis e m args argTs paramTs D body μ0 μ_r C H__e H__mtd H__args H__hots H__subs,
      P Γ Tthis e (C, hot) H__e ->
      Pl Γ Tthis args argTs H__args ->
      P Γ Tthis (e_mtd e m args) (D, hot) (t_call_hot Γ Tthis e m args argTs paramTs D body μ0 μ_r C H__e H__mtd H__args H__hots H__subs).

  Variable Pl_nil: forall Γ Tthis,
      Pl Γ Tthis [] [] (t_exprs_nil Γ Tthis).

  Variable Pl_cons: forall Γ Tthis U Ul e el H__el H__e,
      P Γ Tthis e U H__e ->
      Pl Γ Tthis el Ul H__el ->
      Pl Γ Tthis (e::el) (U::Ul) (t_exprs_cons Γ Tthis Ul el U e H__el H__e).

  Fixpoint typing_ind Γ Tthis e U (typing: (Γ, Tthis) ⊢ e : U) : P Γ Tthis e U typing :=
    match typing with
    | t_sub Γ Tthis e U U' H__U' H__sub => P_sub Γ Tthis e U U' H__U' H__sub (typing_ind Γ Tthis e U' H__U')
    | t_var Γ Tthis x U H__lkp => P_var Γ Tthis x U H__lkp
    | t_this Γ Tthis => P_this Γ Tthis
    | t_selhot Γ Tthis e f C D μ H__D H__field =>
        P_selhot Γ Tthis e f C D μ H__D H__field
                 (typing_ind Γ Tthis e (D, hot) H__D)
    | t_selcool Γ Tthis e f U D Ω H__D H__f H__field =>
        P_selcool Γ Tthis e f U D Ω H__D H__f H__field
                  (typing_ind Γ Tthis e (D, cool Ω) H__D)
    | t_new Γ Tthis C args Args Flds Mtds H__ct H__args =>
        P_new Γ Tthis C args Args Flds Mtds H__ct H__args
              (typing_list_ind Γ Tthis args Args H__args)
    | t_new_hot Γ Tthis C args argsTs Args Flds Mtds H__ct H__args H__hots H__subs =>
        P_new_hot Γ Tthis C args argsTs Args Flds Mtds H__ct H__args H__hots H__subs
                  (typing_list_ind Γ Tthis args argsTs H__args)
    | t_block Γ Tthis U e1 f e2 e3 C μ H__fld H__e2 H__e3 =>
        P_block Γ Tthis U e1 f e2 e3 C μ H__fld H__e2 H__e3
                (typing_ind Γ Tthis (e_fld e1 f) (C, μ) H__fld)
                (typing_ind Γ Tthis e2 (C, hot) H__e2)
                (typing_ind Γ Tthis e3 U H__e3)
    | t_call Γ Tthis e m args argsT U e__m μ C H__e H__mtd H__args =>
        P_call Γ Tthis e m args argsT U e__m μ C H__e H__mtd H__args
               (typing_ind Γ Tthis e (C, μ) H__e)
               (typing_list_ind Γ Tthis args argsT H__args)
    | t_call_hot Γ Tthis e m args argTs paramTs D body μ0 μ_r C H__e H__mtd H__args H__hots H__subs =>
        P_call_hot Γ Tthis e m args argTs paramTs D body μ0 μ_r C H__e H__mtd H__args H__hots H__subs
                   (typing_ind Γ Tthis e (C, hot) H__e)
                   (typing_list_ind Γ Tthis args argTs H__args)
    end
  with typing_list_ind Γ Tthis el Ul (typing_list: (Γ, Tthis) ⊩ el : Ul) : Pl Γ Tthis el Ul typing_list :=
         match typing_list with
         | t_exprs_nil Γ Tthis => Pl_nil Γ Tthis
         | t_exprs_cons Γ Tthis Ul el U e H__el H__e =>
             Pl_cons Γ Tthis U Ul e el H__el H__e
                     (typing_ind Γ Tthis e U H__e)
                     (typing_list_ind Γ Tthis el Ul H__el)
         end.

End typing_ind.
