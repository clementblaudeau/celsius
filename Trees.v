From Coq Require Import Lists.List.
Import ListNotations.
Require Import ssreflect ssrbool.
Require Import Sets.Ensembles.
Require Import Celsius.Tactics.

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

Definition LocSet := (Ensemble Loc).
Notation "l ∈ L" := (In Loc L l) (at level 80).
Notation "L ⊆ L'" := (Included Loc L L') (at level 80).
Notation "L ∪ L'" := (Union Loc L L') (at level 80).
Notation "{ l }" := (Singleton Loc l).


(* Helpers *)
Definition dom {X: Type} (x: list X) : nat := (length x).
Definition getObj (l : list Obj):= nth_error l.
Definition getVal (l : list Value) := nth_error l.


Lemma getObj_last : forall (σ: Store) (C: ClN) (ρ: Env), getObj (σ++[(C,ρ)]) (length σ) = Some (C, ρ).
Proof.
  induction σ; simpl; intros => //.
  Qed.

Lemma getObj_last2 : forall σ C ρ l, l < dom σ -> getObj (σ++[(C,ρ)]) l = getObj σ l.
Proof.
  induction σ; simpl; intros => //; try Psatz.lia.
  destruct l; steps; eauto.
  apply IHσ. Psatz.lia.
Qed.

Lemma getObj_last_empty : forall σ C C' ω l f v,
    getObj (σ++[(C,[])]) l = Some (C', ω) ->
    getVal ω f = Some v ->
    getObj σ l = Some (C', ω) /\ l < dom σ.
Proof.
  intros.
  assert (l <= (length σ)). {
    unfold getObj in *.
    epose proof (nth_error_Some (σ ++ [(C, [])]) l).
    rewrite_anywhere app_length.
    rewrite_anywhere PeanoNat.Nat.add_1_r.
    steps.
    apply le_S_n.
    apply_any.
    steps.
    rewrite H in H1.
    discriminate.
  }
  apply Lt.le_lt_or_eq in H1 as [H1 | H1]; unfold dom in *.
  + split => //.
    rewrite getObj_last2 in H => //.
  + rewrite H1 getObj_last in H.
    invert_constructor_equalities; steps;
      destruct f; steps.
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
    p <> p' ->
    (nth_error [p ↦ v]l p') = (nth_error l p').
  Proof.
    intros X p.
    generalize dependent p.
    induction p; intros; destruct l ; destruct p' => //.
    - simpl; apply IHp. eauto.
Qed.

  Lemma update_one3 : forall (X: Type) (p: nat) (v: X) (l: list X),
      length ([p ↦ v]l) = length l.
  Proof.
    intros X.
    induction p; intros; destruct l => //.
    apply (eq_S _ _(IHp _ _ )).
Qed.

  Lemma update_dom : forall (σ:Store) p v,
      dom [p ↦ v]σ = dom σ.
  Proof.
    unfold dom; eauto using update_one3.
  Qed.

  Lemma update_one4 : forall (X:Type) (p:nat) (v v': X) l,
      nth_error [p ↦ v]l p = Some v' -> v = v'.
  Proof.
    intros.
    assert (p < length l). {
      pose proof (nth_error_Some [p↦v]l p).
      rewrite update_one3 in H0. apply H0. rewrite H. discriminate.
    }
    rewrite update_one1 in H; eauto. injection H => //.
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

  Lemma nth_error_Some2 : forall {T:Type} e (v:T) f l,
      nth_error (e ++ [v]) f = Some l ->
      v = l \/ nth_error e f = Some l.
  Proof.
    intros.
    assert (f < length (e++[v])) by (apply nth_error_Some; rewrite H; discriminate).
    move: H0; rewrite app_length; simpl; rewrite PeanoNat.Nat.add_1_r => H0.
    apply Lt.le_lt_or_eq in H0. destruct H0 as [H0 | H0].
    right. apply Lt.lt_S_n in H0. rewrite nth_error_app1 in H => //.
    left. injection H0 => H1; subst. rewrite nth_error_app2 in H => //.
    rewrite <- Minus.minus_diag_reverse in H. simpl in H. injection H => //.
  Qed.
