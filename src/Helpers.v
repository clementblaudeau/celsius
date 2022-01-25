From Celsius Require Import Language Notations Tactics LibTactics.
Import List ListNotations Psatz Ensembles.
Require Import ssreflect ssrbool Coq.Sets.Finite_sets_facts.
Open Scope list_scope.

(** ** Helper functions *)
Definition getObj (l : list Obj)    : Loc -> option Obj := nth_error l.
Definition getVal (l : list Value)  : Loc -> option Value := nth_error l.
Definition getType (Σ : StoreTyping): Loc -> option Tpe := nth_error Σ.
Definition typeLookup (Γ: EnvTyping): Loc -> option Tpe := nth_error Γ.

Fixpoint removeTypes (l : list (Var*Tpe)) : (list Var) :=
  match l with
  | [] => []
  | ((v, t) :: l') => (v::(removeTypes l'))
  end.

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

Notation "[ x ↦  v ] σ" := (update_one x v σ) (at level 0).
Notation "[ x ⟼ v ] σ" := (update_list x v σ) (at level 0).

(** Update store with new value in local env : adds a new field to an existing object *)
Definition assign_new (obj: Value) (v: Value) (σ: Store) : option Store :=
  match (getObj σ obj) with
  | Some (C, fields) => Some ([ obj ↦ (C, fields++[v])] σ)
  | None => None (* ? *)
  end.

(** Update store with update in local env : update an already-existing field of an existing object*)
Definition assign (obj: Value) (f: Var) (v: Value) (σ: Store) : Store :=
  match (getObj σ obj) with
  | Some (C, fields) => ([ obj ↦ (C, [f ↦ v]fields)] σ)
  | None => σ (* ? *)
  end.

(** Update store with new values : update already existing fields of an existing object*)
Definition assign_list (v0: Value) (x: list Var) (v: list Value) (σ: Store) : Store :=
  match (getObj σ v0) with
  | Some (C, fields) => [v0 ↦ (C, [x ⟼ v]fields)] σ
  | None => σ
  end.

Definition fieldType C f :=
  match ct C with
  | class _ flds _  =>
    match nth_error flds f with
    | Some (field (T, μ) _) => Some (T, μ)
    | _ => None
    end
  end.

Definition methodInfo C m :=
  match ct C with
  | class _ _ methods =>
    match methods m with
    | None => None
    | Some (method μ Ts retT e) => Some (μ, Ts, retT, e)
    end
  end.



(** ** Basic results on helper functions *)
(** We then have multiple easy results on those helper functions *)
Lemma getObj_last :
  forall σ C ρ,
    getObj (σ++[(C,ρ)]) (length σ) = Some (C, ρ).
Proof.
  induction σ; steps.
Qed.

Lemma getObj_last2 :
  forall σ C ρ l,
    l < (dom σ) ->
    getObj (σ++[(C,ρ)]) l = getObj σ l.
Proof.
  induction σ; simpl; intros; try lia.
  destruct l;
    steps;
    eauto with lia.
Qed.

Lemma getObj_last_empty :
  forall (σ: Store) C C' ω l f v,
    getObj (σ++[(C,[])]) l = Some (C', ω) ->
    getVal ω f = Some v ->
    getObj σ l = Some (C', ω) /\ l < dom σ.
Proof.
  intros.
  assert (l < dom (σ ++ [(C,[])])).
  {
    unfold getObj in *.
    eapply nth_error_Some.
    rewrite H; steps.
  }
    rewrite app_length in H1 ;
    simpl in H1;
    fold (dom σ) in H1;
    rewrite_anywhere PeanoNat.Nat.add_1_r.
  apply Lt.le_lt_or_eq in H1 as [H1 | H1].
  + rewrite getObj_last2 in H; eauto using Lt.lt_S_n.
  + inversion H1; subst.
    rewrite getObj_last in H.
    invert_constructor_equalities; steps;
      destruct f; steps.
Qed.


Lemma update_one1 :
  forall X p v (l: list X),
    p < (length l) ->
    (nth_error [p ↦ v]l p) = Some v.
Proof.
  intros X p v; generalize dependent p.
  induction p; steps; eauto with lia.
Qed.

Lemma update_one2 :
  forall X p p' v (l: list X),
    p <> p' ->
    (nth_error [p ↦ v]l p') = (nth_error l p').
Proof.
  induction p; intros; destruct l ; destruct p' => //.
  simpl; eauto.
Qed.

Lemma update_one3 :
  forall X p v (l: list X),
    length ([p ↦ v]l) = length l.
Proof.
  intros X.
  induction p; steps.
Qed.

Lemma update_dom :
  forall (σ:Store) p v,
    dom [p ↦ v]σ = dom σ.
Proof.
   eauto using update_one3.
Qed.

Lemma update_one4 :
  forall X p (v v': X) l,
    nth_error [p ↦ v]l p = Some v' -> v = v'.
Proof.
  intros.
  assert (p < length l). {
    pose proof (nth_error_Some [p↦v]l p).
    rewrite update_one3 in H0; apply H0.
    rewrite H. discriminate.
  }
  rewrite update_one1 in H; eauto.
Qed.

Lemma dom_app:
  forall (σ: Store) (C: ClN) (ω:Env),
    dom (σ ++ ((C, ω)::nil)) = S (dom σ).
Proof.
  intros.
   rewrite app_length; simpl; lia.
Qed.

Lemma length_plus_1:
  forall (ρ:Env) v,
    length(ρ ++ [v]) = S(length(ρ)).
Proof.
  intros.
  rewrite app_length; simpl; lia.
Qed.


#[export] Hint Extern 1 => rewrite (update_one3): updates.
#[export] Hint Extern 1 => rewrite (update_dom): updates.
#[export] Hint Extern 1 => rewrite (length_plus_1): updates.
Global Hint Resolve update_one1: updates.
Global Hint Resolve update_one2: updates.
Global Hint Resolve update_one3: updates.
Global Hint Resolve update_one4: updates.

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


Lemma getObj_update1 :
  forall (σ: Store) o x,
    x < dom σ -> (getObj [x ↦ o]σ x) = Some o.
Proof.
  unfold getObj; eauto with updates.
Qed.

Lemma getObj_update2 :
  forall (σ: Store) o x x',
    x < dom σ ->
    x <> x' ->
    (getObj [x ↦ o]σ x') = (getObj σ x').
Proof.
  unfold getObj; eauto with updates.
Qed.

Lemma getObj_update3:
  forall σ o o' x x',
    getObj [x ↦ o]σ x' = Some o' ->
    x < dom σ ->
    ((x = x' /\ o = o') \/ (x <> x' /\ (getObj σ x' = Some o'))).
Proof.
  steps;
    destruct (PeanoNat.Nat.eq_dec x x') as [Heq | Hneq]; subst;
      [ rewrite getObj_update1 in H |
        rewrite getObj_update2 in H ]; steps.
Qed.

Lemma getObj_dom :
  forall (σ: Store) o l,
    (getObj σ l) = Some o ->
    l < (dom σ).
Proof.
  intros σ o.
  induction σ ; destruct l; steps; eauto with lia.
  apply (Lt.lt_n_S _ _ (IHσ _ H)) .
Qed.

Lemma nth_error_Some2 :
  forall {T:Type} e (v:T) f l,
    nth_error (e ++ [v]) f = Some l ->
    v = l \/ nth_error e f = Some l.
Proof.
  intros.
  assert (f < length (e++[v])) by (apply nth_error_Some; rewrite H; discriminate).
  move: H0; rewrite app_length; simpl; rewrite PeanoNat.Nat.add_1_r => H0.
  apply Lt.le_lt_or_eq in H0. destruct H0 as [H0 | H0].
  + right.
    apply Lt.lt_S_n in H0.
    rewrite nth_error_app1 in H => //.
  + left.
    injection H0 => H1; subst.
    rewrite nth_error_app2 in H => //.
    rewrite <- Minus.minus_diag_reverse in H.
    simpl in H. injection H => //.
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

Global Hint Resolve getObj_dom: updates.

(*
Lemma getType_dom:
  forall (Σ: StoreTyping) l T,
    getType Σ l = Some T -> l < dom Σ.
Proof.
  intros.
  unfold getType in *.
  destruct (find (fun '(l', _) => Nat.eqb l l') Σ) eqn:H__e; steps.
  apply find_some in H__e; steps.
  Search (nth _ _ _ = _ -> _).
  apply  in H; steps.

  apply nth_error_Some.
  unfold getType in *; eauto.
Qed. *)
Lemma getType_in_dom:
  forall (Σ: StoreTyping) l T,
    getType Σ l = Some T -> l < dom Σ.
Proof.
  intros.
  unfold getType, option_map in H; steps.
  apply nth_error_Some; eauto.
Qed.

Lemma dom_map:
  forall (Σ: StoreTyping) (l: Loc) (f: Tpe -> Tpe),
    dom (map (fun T => f T) Σ) = dom Σ.
Proof.
  intros.
  rewrite map_length. auto.
Qed.

Lemma getType_none:
  forall (Σ: StoreTyping) l,
    l < dom Σ ->
    getType Σ l <> None.
Proof.
  intros.
  unfold getType, option_map in *; steps.
  apply nth_error_None in H0. lia.
Qed.

Lemma getType_map:
  forall (Σ: StoreTyping) f l T,
    getType Σ l = Some T ->
    getType (map (fun T => f T) Σ) l = Some (f T).
Proof.
  unfold getType. intros.
  rewrite nth_error_map H. steps.
Qed.

Lemma getVal_dom:
  forall ρ f l,
    getVal ρ f = Some l -> f < dom ρ.
Proof.
  intros.
  apply nth_error_Some.
  unfold getVal in *; eauto.
Qed.


(** ** Tactics *)
(** Finally some tactics : *)

Ltac getObj_update :=
  match goal with
  | H: getObj [?x ↦ ?o] (?σ) ?x' = Some ?o' |- _ => eapply getObj_update3 in H; eauto with updates
  end.
Ltac getVal_update :=
  match goal with
  | H: getVal [?x ↦ ?o] (?σ) ?x' = Some ?o' |- _ => eapply getVal_update in H; eauto with updates
  end.


Ltac update_dom :=
  repeat
    match goal with
  | [H: context[dom (?a ++ ?b)] |- _ ] => rewrite app_length in H; simpl in H
    end || rewrite_anywhere update_dom || rewrite update_dom || (rewrite app_length; simpl).

Global Hint Extern 1 => update_dom: updates.


Ltac inSingleton :=
  match goal with
  | H: ?a ∈ Singleton Loc ?b |- _ => induction H
  | H: {?x} ?y |- _ => induction H
  end.

(** Store Subset results *)

(** A set of locations is contained in a store: [L ⪽ σ] *)
Definition storeSubset (σ: Store) L :=
  forall l, l ∈ L ->
       l < dom σ.

(** The codomain of an environment is the set of locations it contains *)
Definition codom (ρ: Env) : (LocSet) :=
  fun l => (List.In l ρ).

Notation "L ⪽ σ" := (storeSubset σ L) (at level 80).
Notation " a ∪ { b } " := (Union Loc a (Singleton Loc b)) (at level 80).

(** ** Basic results *)

Global Hint Resolve Union_intror: wf.
Global Hint Resolve Union_introl: wf.
Global Hint Resolve In_singleton: wf.


Lemma storeSubset_trans :
  forall a s s',
    dom s <= dom s' ->
    a ⪽ s ->
    a ⪽ s'.
Proof.
  unfold storeSubset; steps.
  eapply H0 in H1 ; lia.
Qed.

Lemma storeSubset_union :
  forall a b s,
    a ⪽ s ->
    b ⪽ s ->
    (a∪b) ⪽ s.
Proof.
  unfold storeSubset; intros.
  induction H1; eauto.
Qed.

Lemma storeSubset_union_l :
  forall a b s,
    (a∪b) ⪽ s -> a ⪽ s.
Proof.
  unfold storeSubset; eauto with wf.
Qed.

Lemma storeSubset_union_r :
  forall a b s,
    (a∪b) ⪽ s -> b ⪽ s.
Proof.
  unfold storeSubset; eauto with wf.
Qed.

Lemma storeSubset_add :
  forall v a s,
    codom (v :: a) ⪽ s <-> v < dom s /\ codom a ⪽ s.
Proof.
  unfold codom, List.In, In, storeSubset in *; split.
  + steps; eapply_any; steps; right => //.
  + steps; move: H0 => [Hl|Hl]; steps.
Qed.

Lemma storeSubset_singleton :
  forall a b σ,
    a ∪ {b} ⪽ σ -> b < dom σ.
Proof.
  intros.
  eapply_any; eauto with wf.
Qed.

Lemma storeSubset_singleton2 :
  forall a σ,
    (Singleton Loc a) ⪽ σ -> a < dom σ.
Proof.
  unfold storeSubset; steps.
  induction (H a) ; steps.
Qed.

Lemma storeSubset_singleton3 :
  forall a σ,
    a < dom σ -> (Singleton Loc a) ⪽ σ.
Proof.
  unfold storeSubset; steps;
    induction H0 ; steps.
Qed.

Lemma storeSubset_codom_empty : forall s, codom [] ⪽ s.
Proof.
  unfold storeSubset; steps.
Qed.

Lemma codom_empty_union: forall a, (codom [] ∪ a) = a.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included;
    repeat steps || destruct H;
    eauto with wf.
Qed.

Lemma codom_cons:
  forall a ρ, codom (a::ρ) = ({a} ∪ (codom ρ)).
Proof.
  intros; apply Extensionality_Ensembles.
  unfold Same_set; steps; intros l; steps; try inversion H; steps;
    try inSingleton;
    eauto using Union_introl, Union_intror.
Qed.


Lemma storeSubset_update:
  forall L l o σ,
    L ⪽ [l ↦ o] (σ) -> L ⪽ σ.
Proof.
  unfold storeSubset; steps; update_dom; eauto.
Qed.


Lemma getVal_codom : forall x l ρ,
    getVal ρ x = Some l -> l ∈ codom ρ.
Proof.
  intros.
  eapply nth_error_In in H. auto.
Qed.

Lemma storeSubset_finite: forall σ L,
    L ⪽ σ ->
    Finite Loc L.
Proof.
  induction σ; steps.
  - assert (L = Empty_set Loc); subst; eauto using Empty_is_finite.
    apply Extensionality_Ensembles.
    unfold Same_set, Included; steps; try specialize (H x); steps; try lia.
    inversion H0.
  - assert ((Subtract Loc L (dom σ)) ⪽ σ).
    + intros l; steps.
      inverts H0.
      specialize (H l H1). simpl in H.
      assert (l < dom σ \/ l = dom σ) as [ ] by lia; steps.
      exfalso. apply H2.
      steps.
    + apply IHσ in H0.
      apply Finite_downward_closed with (A:= Union Loc ( (Subtract Loc L dom σ)) ({dom σ})).
      apply Union_preserves_Finite; eauto using Singleton_is_finite.
      intros l; steps.
      destruct_eq (l = dom σ).
      * apply Union_intror; steps.
      * apply Union_introl; steps.
        unfold Subtract, Setminus, In.
        split; steps. apply Heq. inSingleton. steps.
Qed.

Lemma finite_sets_ind: forall {T: Type} (P: (Ensemble T) -> Prop),
    (P (Empty_set T)) ->
    (forall (F: Ensemble T) (a:T), Finite T F -> P F -> P (Add T F a)) ->
    (forall (F: Ensemble T), Finite T F -> P F).
Proof.
  intros.
  apply Generalized_induction_on_finite_sets; eauto.
  intros.
  induction H2; eauto.
  eapply H0; eauto.
  apply IHFinite.
  intros.
  apply H3.
  unfold Strict_Included, Included, In, Add in *; steps.
  - apply Union_introl; eauto.
    apply H6; eauto.
  - apply H7, Extensionality_Ensembles.
    unfold Same_set, Included; steps.
    apply Union_introl; eauto.
Qed.



Global Hint Resolve storeSubset_update: wf.
Global Hint Resolve storeSubset_trans: wf.
Global Hint Resolve storeSubset_union: wf.
Global Hint Resolve storeSubset_union_l: wf.
Global Hint Resolve storeSubset_add: wf.
Global Hint Resolve storeSubset_union_r: wf.
Global Hint Resolve storeSubset_singleton: wf.
Global Hint Resolve storeSubset_singleton2: wf.
Global Hint Resolve storeSubset_singleton3: wf.
Global Hint Resolve storeSubset_codom_empty: wf.
Global Hint Resolve getVal_codom: wf.
Global Hint Rewrite codom_cons: wf.


Lemma fieldType_exists: forall C Args Flds Mtds f,
    ct C = class Args Flds Mtds ->
    f < dom Flds ->
    exists D μ, fieldType C f = Some (D, μ).
Proof.
  intros.
  destruct (fieldType C f) as [[D μ] |] eqn:?; eauto.
  unfold fieldType in *.
  steps.
  apply nth_error_None in matched0. lia.
Qed.
Global Hint Resolve fieldType_exists: typ.

Lemma fieldType_some : forall C Args Flds Mtds f T,
    ct C = class Args Flds Mtds ->
    fieldType C f = Some T ->
    f < dom Flds.
Proof.
  intros.
  unfold fieldType in *. steps.
  eapply nth_error_Some; eauto.
Qed.
Global Hint Resolve fieldType_some: typ.
