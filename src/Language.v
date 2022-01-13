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
Parameter ClN_count : nat.
Definition ClN : Type := {C: nat | C < ClN_count}.
Definition Loc : Type := nat.


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
Notation "'@' u " := (u:Mode) (at level 20).

Definition Tpe : Type := ClN * Mode.

Inductive Field: Type :=
| field(type: Tpe)(expr: Expr).

Inductive Method: Type :=
| method(μ: Mode)(args: list Tpe)(out_type: Tpe)(body: Expr).

Inductive Class: Type :=
| class(args: list Tpe)(fields: list Field)(methods: Mtd -> (option Method)).

Inductive Program: Type :=
| program(C: list Class)(entry: Expr).


(** ** Constructs *)
Definition Value : Type := Loc.
Definition Env: Type   := list Value.
Definition EnvTyping: Type := list Tpe.
Definition Obj: Type   := (ClN * Env).
Definition Store: Type := list Obj.
Definition StoreTyping : Type := list (Loc * Tpe).

Definition LocSet := (Ensemble Loc).

(** ** Global Parameters *)
Parameter entry: ClN.
Parameter Ξ : {l : list Class | length l = ClN_count}.
Definition EntryClass: {c:Class | nth_error (proj1_sig Ξ) (proj1_sig entry) = Some c}.
Proof.
  destruct ( nth_error (proj1_sig Ξ) (proj1_sig entry)) eqn:H.
  - exists c; reflexivity.
  - apply nth_error_None in H.
    pose proof (proj2_sig entry).
    pose proof (proj2_sig Ξ).
    simpl in *.
    lia.
Qed.

Definition ct (C:ClN) := nth (proj1_sig C) (proj1_sig Ξ) (proj1_sig EntryClass).
Definition main: Mtd := 0.
