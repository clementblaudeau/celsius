(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL 2021 *)
(** This file defines all the basic structures (as inductive types) of the project. *)
Require Import Coq.Lists.List Psatz Ensembles.
Import ListNotations.
From Celsius Require Export Tactics.

(** * Language structures *)

(** ** Basic types *)
Definition Var : Type := nat.
Definition Mtd : Type := nat.
Definition Loc : Type := nat.
Variant ClN : Type := cln(n: nat).


(** ** Expression constructors *)
Inductive Expr: Type :=
| var   : Var -> Expr
| this
| fld   : Expr -> Var -> Expr
| mtd   : Expr -> Mtd -> (list Expr) -> Expr
| new   : ClN -> (list Expr) -> Expr
| asgn  : Expr -> Var -> Expr -> Expr -> Expr.

Inductive Mode: Type :=
| hot
| warm
| cool : nat -> Mode
| cold.

Notation "'Tpe'" := (prod ClN Mode).

Variant Field   : Type := field(type: Tpe)(expr: Expr).
Variant Method  : Type := method(μ: Mode)(args: list Tpe)(out_type: Tpe)(body: Expr).
Variant Class   : Type := class(args: list Tpe)(fields: list Field)(methods: Mtd -> (option Method)).
Variant Program : Type := program(C: list Class)(entry: Expr).


(** ** Constructs *)
Definition Value : Type := Loc.
Definition Env: Type   := list Value.
Definition EnvTyping: Type := list Tpe.
Definition Obj: Type   := (ClN * Env).
Definition Store: Type := list Obj.
Definition StoreTyping : Type := list Tpe.

Definition LocSet := (Ensemble Loc).

(** ** Global Parameters *)
Parameter Ξ: list Class.
Parameter Entry: ClN.
Parameter EntryClass: Class.

Definition ct (C:ClN) := match C with | cln n => nth n Ξ EntryClass end.
Definition main: Mtd := 0.
