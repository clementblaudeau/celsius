(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL & Inria 2020-2022 *)

(** This file defines all the basic structures of the language (as inductive types). *)

From Celsius Require Export Tactics.
Require Import Coq.Lists.List Psatz Ensembles.
Import ListNotations.

(** * Language structures *)

(** ** Basic types *)
Definition Var : Type := nat.
Variant Mtd : Type := mtd(n: nat).
Definition Loc : Type := nat.
Variant ClN : Type := cln(n: nat).

(** ** Expression constructors *)
Inductive Expr: Type :=
| e_var   : Var -> Expr
| e_this
| e_fld   : Expr -> Var -> Expr
| e_mtd   : Expr -> Mtd -> (list Expr) -> Expr
| e_new   : ClN -> (list Expr) -> Expr
| e_asgn  : Expr -> Var -> Expr -> Expr -> Expr.

(** ** Modes *)
Inductive Mode: Type :=
| hot
| warm
| cool : nat -> Mode
| cold.

(** ** Types *)
Notation "'Tpe'" := (prod ClN Mode).

(** ** Other language constructions *)
Variant Field   : Type := field(type: Tpe)(expr: Expr).
Variant Method  : Type := method(μ: Mode)(args: list Tpe)(out_type: Tpe)(body: Expr).
Variant Class   : Type := class(args: list Tpe)(fields: list Field)(methods: Mtd -> (option Method)).
Variant Program : Type := program(C: list Class)(entry: Expr).

(** ** Other Types *)
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
Parameter EntryClass_ct : ct Entry = EntryClass.
Definition main: Mtd := mtd(0).
