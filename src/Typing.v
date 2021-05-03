From Celsius Require Export Trees.
Require Import List.
Import ListNotations.
Open Scope nat_scope.


Parameter ct: ClassTable.

Definition fieldType C f :=
  match ct C with
  | None => None
  | Some (class _ flds _ ) =>
    match nth_error flds f with
    | Some (field (T, μ) _) => Some (T, μ)
    | _ => None
    end
  end.

(* Mode lattice *)
Definition mode_leq (m1 m2 : mode) :=
  match (m1, m2) with
  | (hot, _ ) => true
  | (warm, hot) => true
  | (warm, warm) => true
  | ( _ , cold) => true
  | ( _ , _ ) => false end.
Notation "m1 ⊑ m2" := (mode_leq m1 m2) (at level 100).

Definition mode_max (m1 m2 : mode) : mode :=
  match (m1 ⊑ m2) with
  | true => m2
  | false => m1
  end.

Definition mode_min (m1 m2 : mode) : mode :=
  mode_max m2 m1.

Notation "m1 ⊓ m2" := (mode_min m1 m2) (at level 100).
Notation "m1 ⊔ m2" := (mode_max m1 m2) (at level 100).

(* Subtyping *)

Reserved Notation "T1 ≲ T2" (at level 100, right associativity).
Inductive subTyping : Tpe -> Tpe -> Prop :=
| s_refl (T : Tpe) : (T ≲ T)
| s_trans (T1 T2 T3 : Tpe) : (T1 ≲ T2) -> (T2 ≲ T3) -> (T1 ≲ T3)
| s_mode (C: ClN) (μ1 μ2 : mode) (H : (μ1 ⊑ μ2) = true) : (C, μ1) ≲ (C, μ2)
where "T1 ≲ T2" := (subTyping T1 T2).

Reserved Notation "'[' Γ ',' T '⊢' e ':' U ']'" (at level 60, Γ at level 60, e at level 60). (* e can have the type T in env Γ and `this` of type U *)

Definition Env := list (Var * Tpe).

Inductive exp_typing : Env -> Tpe -> Expr -> Tpe -> Prop :=
| t_sub :
    forall Γ T e U U',
      [Γ, T ⊢ e : U'] ->
      (U' ≲ U) ->
      [Γ, T ⊢ e : U]
| t_var :
    forall Γ T x U,
      List.In (x, U) Γ ->
      [Γ, T ⊢ (var x) : U]
| t_this :
    forall Γ T,
      [Γ, T ⊢ this : T]
| t_selhot :
    forall Γ T e f C D μ,
      [Γ, T ⊢ e : (D, hot)] ->
      (fieldType D f = Some (C, μ)) ->
      [Γ, T ⊢ (fld e f) : (C, hot)]
| t_selwarm :
    forall Γ T e f U D,
      [Γ, T ⊢ e : (D, warm)] ->
      (fieldType D f = Some U) ->
      [Γ, T ⊢ (fld e f) : U]

(*
 | t_block : forall e1 f e2 e3 C μ T1,
    e = asgn e1 f e2 e3 ->
    [Γ, T ⊢ e1.f : (C, μ)] ->
    [Γ, T ⊢ e2 : (C, hot)] ->
    [Γ, T ⊢ e3 : U] ->
    [Γ, T ⊢ e : U] *)

where  "'[' Γ ',' T '⊢' e ':' U ']'" := (exp_typing Γ T e U).


(* Typing *)
