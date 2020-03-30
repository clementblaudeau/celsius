From Coq Require Import Strings.String.
Open Scope string_scope.
Open Scope list_scope.

(* Read the pen/paper proofs of scopability *)
(* Github repo  ? *)

Inductive mode: Set := hot | warm | cold.
Notation "'@' u " := (u) (at level 20).
Check @hot.

Definition Var : Type := nat.
Definition Mtd : Type := nat.
Definition ClN : Type := nat.
Definition Tpe : Type := ClN.
Definition Loc : Type := nat.


Inductive Expr: Type :=
  | var   : Var -> Expr
  | this
  | fld   : Expr -> Var -> Expr
  | mtd   : Expr -> Mtd -> (list Expr) -> Expr
  | new   : ClN -> (list Expr) -> Expr
  | asgn  : Expr -> Var -> Expr -> Expr -> Expr
.


Inductive Method: Type :=
  | method(μ : mode)(args : list (Var * Tpe))(out_type : Tpe)(body :Expr).

Inductive Field: Type :=
  | field(x : Var)(type: Tpe)(expr: Expr).

Inductive Class: Type :=
  | class(args: list (Var * Tpe))(fields : list Field)(methods : Mtd -> (option Method)).

Inductive Program: Type :=
  | program(C: list Class)(entry: Expr).


Definition Value : Type := Loc.
Definition ClassTable: Type := (ClN -> option Class).
Definition Obj: Type := (ClN * (Var -> option Value)).
Definition Store: Type := (Loc -> option Obj).
Definition Env: Type := (Var -> option Value).

Inductive Result : Type :=
  | Timeout
  | Error
  | Success : Value -> Store -> Result
  | Success_list : (list Value) -> Store -> Result.




