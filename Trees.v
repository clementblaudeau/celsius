From Coq Require Import Lists.List.
Import ListNotations.
Require Import ssreflect ssrbool.

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
Definition Tpe : Type := (ClN * mode).
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
  | method(μ: mode)(args: list Tpe)(out_type: Tpe)(body: Expr).

Inductive Field: Type :=
  | field(type: Tpe)(expr: Expr).

Inductive Class: Type :=
  | class(args: list Tpe)(fields: list Field)(methods: Mtd -> (option Method)).

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
Definition dom {X: Type} (x: list X) : nat := (length x).
Definition getObj (l : list Obj):= nth_error l.
Definition getVal (l : list Value) := nth_error l.


Lemma getObj_last : forall (σ: Store) (C: ClN) (ρ: Env), getObj (σ++[(C,ρ)]) (length σ) = Some (C, ρ).
Proof.
  induction σ; simpl; intros => //.
  Qed.

Fixpoint removeTypes (l : list (Var*Tpe)) : (list Var) :=
  match l with
    | [] => []
    | ((v, t) :: l') => (v::(removeTypes l')) end.

Fixpoint update_one {X : Type} (position : nat) (value : X)(l : list X) : list X :=
  match (l, position) with
  | ([], _) => []
  | (_::t, 0) => value::t
  | (h::l', S n) => h::(update_one n value l')
  end.

Fixpoint update_list {X : Type} (positions : list nat) (values : list X) (l : list X) : list X :=
  match (positions, values) with
    | (x::xt, v::vt) => update_list xt vt (update_one x v l)
    | (_, _) => l end.

Notation "∅" := ([]).
Notation "[ x ↦ v ] σ" := (update_one x v σ) (at level 0).
Notation "[ x ⟼ v ] σ" := (update_list x v σ) (at level 0).


Lemma update_one1 : forall (X: Type) (p: nat) (v: X) (l: list X),
    p < (length l) ->
    (nth_error [p ↦ v]l p) = Some v.
  Proof.
    intros X p v.
    generalize dependent p.
    induction p.
    - simpl.
    destruct l.
    simpl.
    move :(PeanoNat.Nat.lt_irrefl 0) => h1 => //.
    reflexivity.
    - destruct l => H.
      simpl in H.
      move :(PeanoNat.Nat.nlt_0_r (S p)) => h1 => //.
      simpl.
      move :(Lt.lt_S_n p (length l)) => H1.
      simpl in H.
      apply H1 in H.
      apply IHp in H => //.
Qed.

Lemma update_one2 : forall (X: Type) (p p': nat) (v: X) (l: list X),
    p < (length l) ->
    p <> p' ->
    (nth_error [p ↦ v]l p') = (nth_error l p').
  Proof.
    intros X p.
    generalize dependent p.
    induction p; intros; destruct l ; destruct p' => //.
    - simpl in H.
      move : (iffLR (PeanoNat.Nat.succ_inj_wd_neg p p') H0) => H1.
      simpl in H.
      move : (Lt.lt_S_n p (length l) H) => H2.
      apply (IHp p' v)  => //.
Qed.      
      
  Lemma update_one3 : forall (X: Type) (p: nat) (v: X) (l: list X),
      length ([p ↦ v]l) = length l.
  Proof.
    intros X.
    induction p; intros; destruct l => //.
    apply (eq_S _ _(IHp _ _ )).
Qed.
  
Check [0].
Check [0 ↦ 1] ∅.
Check [[0] ⟼ [1]] [1 ; 2 ; 3].



  Lemma getObj_update1 : forall (σ: Store) (o: Obj) (x: nat),
      x < dom σ -> (getObj [x ↦ o]σ x) = Some o.
  Proof.
    rewrite /dom /getObj => σ o x.
    apply : (update_one1 Obj x o σ) => //.
  Qed.  
  
  Lemma getObj_update2 : forall (σ: Store) (o: Obj) (x x': nat),
      x < dom σ ->
      x <> x' ->
      (getObj [x ↦ o]σ x') = (getObj σ x').
  Proof.
    rewrite /dom /getObj => σ o x x'.
    move : (update_one2 Obj x x' o σ) => //.
  Qed.

  Lemma getObj_dom : forall (σ: Store) (o: Obj) (l: nat),
      (getObj σ l) = Some o ->
      l < (dom σ).
  Proof.
    intros σ o.
    induction σ ; destruct l => //.    
    + move: (PeanoNat.Nat.lt_0_succ (dom σ)) => //.
    + simpl => H. apply (Lt.lt_n_S _ _ (IHσ _ H)) . 
  Qed.
