From Coq Require Import Lists.List.
Import ListNotations.

(* Read the pen/paper proofs of scopability *)
(* Github repo  ? *)

(* Type modifiers *)
Inductive mode: Set := hot | warm | cold.
Notation "'@' u " := (u) (at level 20).
Check @hot.

(* Basic types *)
Definition Var : Type := nat.
Definition Mtd : Type := nat.
Definition ClN : Type := nat.
Definition Tpe : Type := ClN.
Definition Loc : Type := nat.

(* Expression constructors *)
Inductive Expr: Type :=
  | var   : Var -> Expr
  | this
  | fld   : Expr -> Var -> Expr
  | mtd   : Expr -> Mtd -> (list Expr) -> Expr
  | new   : ClN -> (list Expr) -> Expr
  | asgn  : Expr -> Var -> Expr -> Expr -> Expr.

Inductive Method: Type :=
  | method(μ : mode)(args : list (Var * Tpe))(out_type : Tpe)(body :Expr).

Inductive Field: Type :=
  | field(x : Var)(type: Tpe)(expr: Expr).

Inductive Class: Type :=
  | class(args: list (Var * Tpe))(fields : list Field)(methods : Mtd -> (option Method)).

Inductive Program: Type :=
  | program(C: list Class)(entry: Expr).

(* Constructs *)
Definition Value : Type := Loc.
Definition ClassTable: Type := (ClN -> option Class).
Definition Env: Type   := list Value.
Definition Obj: Type   := (ClN * Env).
Definition Store: Type := list Obj.

(* Evaluation result *)
Inductive Result : Type :=
  | Timeout
  | Error
  | Success : Value -> Store -> Result
  | Success_list : (list Value) -> Store -> Result.

(* Helpers *)
Definition getObj (l : list Obj):= nth_error l.
Definition getVal (l : list Value) := nth_error l.

Fixpoint removeTypes (l : list (Var*Tpe)) : (list Var) :=
  match l with
    | [] => []
    | ((v, t) :: l') => (v::(removeTypes l')) end.

Fixpoint update_one {X : Type} (position : nat) (value : X)(l : list X) : list X :=
  match (l, position) with
    | ([], _) => []
    | (_::t, 0) => value::t
    | (_::l', S n) => update_one n value l' end.

Fixpoint update_list {X : Type} (positions : list nat) (values : list X) (l : list X) : list X :=
  match (positions, values) with
    | (x::xt, v::vt) => update_list xt vt (update_one x v l)
    | (_, _) => l end.

Notation "∅" := ([]).
Notation "[ x ↦ v ] σ" := (update_one x v σ) (at level 0).
Notation "[ x ⟼ v ] σ" := (update_list x v σ) (at level 0).

Check [0].
Check [0 ↦ 1] ∅.
Check [[0] ⟼ [1]] [1 ; 2 ; 3].
