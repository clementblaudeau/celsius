From Coq Require Import Lists.List.
Import ListNotations.
Require Import ssreflect ssrbool.
Require Import Sets.Ensembles.
Require Import Celsius.Tactics.

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

Lemma dom_app: forall σ (C: ClN) (ω: Env), dom (σ ++ ((C, ω)::nil)) = S (dom σ).
Proof.
  intros.
  unfold dom; rewrite app_length; simpl.
  Psatz.lia.
Qed.

Hint Resolve update_one1: updates.
Hint Resolve update_one2: updates.
Hint Resolve update_one3: updates.
Hint Resolve update_one4: updates.

Lemma getVal_update1 :
  forall ω o x,
    x < length ω -> (getVal [x ↦ o]ω x) = Some o.
Proof.
  unfold getVal; eauto with updates.
Qed.

Lemma getVal_update2 :
  forall ω o x x',
    x < length ω ->
    x <> x' ->
    getVal [x ↦ o]ω x' = getVal ω x'.
Proof.
  unfold getVal; eauto with updates.
Qed.


Lemma getObj_update1 : forall (σ: Store) (o: Obj) (x: nat),
    x < dom σ -> (getObj [x ↦ o]σ x) = Some o.
Proof.
  unfold getObj; eauto with updates.
Qed.

Lemma getObj_update2 : forall (σ: Store) (o: Obj) (x x': nat),
    x < dom σ ->
    x <> x' ->
    (getObj [x ↦ o]σ x') = (getObj σ x').
Proof.
  unfold getObj; eauto with updates.
Qed.

Lemma getObj_update3: forall σ o o' x x',
    getObj [x ↦ o]σ x' = Some o' ->
    x < dom σ ->
    ((x = x' /\ o = o') \/ (x <> x' /\ (getObj σ x' = Some o'))).
Proof.
  steps;
    destruct (PeanoNat.Nat.eq_dec x x') as [Heq | Hneq]; subst;
      [ rewrite getObj_update1 in H |
        rewrite getObj_update2 in H ]; steps.
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

Lemma getVal_add:
  forall ω l l' f,
    getVal (ω ++ [l]) f = Some l' ->
    (f = length ω /\ l = l') \/ (f < length ω /\ getVal ω f = Some l').
Proof.
  unfold getVal.
  steps.
  assert (f < length ω \/ f = length ω) as [Hf | Hf];
    [
      apply Lt.le_lt_or_eq, Lt.lt_n_Sm_le;
      pose proof (nth_error_Some (ω ++ [l]) f) as Hf;
      rewrite app_length PeanoNat.Nat.add_1_r in Hf;
      apply Hf
    | rewrite_anywhere nth_error_app1
    | rewrite_anywhere nth_error_app2 ] ;
    steps;
    rewrite_anywhere PeanoNat.Nat.sub_diag; steps.
Qed.

Lemma getVal_update:
  forall ω l l' f f',
    getVal ([f ↦ l] ω) f' = Some l' ->
    (f = f' /\ l = l') \/ (f <> f' /\ getVal ω f' = Some l').
Proof.
  unfold getVal; steps.
  destruct (PeanoNat.Nat.eq_dec f f') as [Heq | Hneq]; subst.
  + apply update_one4 in H ; steps.
  + rewrite update_one2 in H; eauto ; steps.
Qed.

Hint Resolve getObj_dom: updates.


Ltac getObj_update :=
  match goal with
  | H: getObj [?x ↦ ?o] (?σ) ?x' = Some ?o' |- _ => eapply getObj_update3 in H; eauto with updates
  end.
Ltac getVal_update :=
  match goal with
  | H: getVal [?x ↦ ?o] (?σ) ?x' = Some ?o' |- _ => eapply getVal_update in H; eauto with updates
  end.


Ltac update_dom :=
  repeat rewrite_anywhere update_dom;
  repeat rewrite update_dom.


Ltac inSingleton :=
  match goal with
  | H: ?a ∈ Singleton Loc ?b |- _ => induction H
  | H: {?x} ?y |- _ => induction H
  end.
