(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL & Inria 2020-2022 *)
(* ------------------------------------------------------------------------ *)
(* This files defines basic getters (getObj, getVal, getType), update functions, some lemmas and
some tactics *)

From Celsius Require Export Notations LibTactics Tactics.
Require Export ssreflect ssrbool Coq.Sets.Finite_sets_facts.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc) (L: LocSet) (Σ: StoreTyping) (T: Tpe) (μ: Mode) (Γ: EnvTyping).

(* ------------------------------------------------------------------------ *)
(** ** Helper functions *)

Definition getObj (l : list Obj)    : Loc -> option Obj := nth_error l.
Definition getVal (l : list Loc)  : Loc -> option Loc := nth_error l.
Definition getType (Σ : StoreTyping): Loc -> option Tpe := nth_error Σ.
Definition typeLookup (Γ: EnvTyping): Loc -> option Tpe := nth_error Γ.
Local Hint Unfold getObj getVal getType: updates.

(* ------------------------------------------------------------------------ *)
(** * Updates **)

Fixpoint update {X : Type} (position : nat) (value : X) (l : list X) : list X :=
  match (l, position) with
  | ([], _) => []
  | (_::t, 0) => value::t
  | (h::l', S n) => h::(update n value l')
  end.
Notation "[ x ↦  v ] l" := (update x v l) (at level 0).

(** ** Updates lemmas *)
Lemma update_same :
  forall X p v (l: list X),
    p < (length l) ->
    (nth_error [p ↦ v]l p) = Some v.
Proof.
  intros X p v; generalize dependent p.
  induction p; steps; eauto with lia.
Qed.
Global Hint Resolve update_same: updates.

Lemma getObj_update_same:
  forall σ l O, l < dom σ -> getObj ([l ↦ O]σ) l = Some O.
Proof.
  eauto using update_same.
Qed.

Lemma getVal_update_same:
  forall ρ l v, l < dom ρ -> getVal ([l ↦ v]ρ) l = Some v.
Proof.
  eauto using update_same.
Qed.

Lemma getType_update_same:
  forall Σ l T, l < dom Σ -> getType ([l ↦ T]Σ) l = Some T.
Proof.
  eauto using update_same.
Qed.

Lemma update_diff :
  forall X p p' v (l: list X),
    p <> p' ->
    (nth_error [p ↦ v]l p') = (nth_error l p').
Proof.
  induction p; intros; destruct l ; destruct p' => //.
  simpl; eauto.
Qed.
Global Hint Resolve update_diff: updates.

Lemma getObj_update_diff:
  forall σ l l' O,
    l <> l' ->
    getObj ([l ↦ O]σ) l' = getObj σ l'.
Proof.
  eauto using update_diff.
Qed.

Lemma getVal_update_diff:
  forall ρ l l' v,
    l <> l' ->
    getVal ([l ↦ v]ρ) l' = getVal ρ l'.
Proof.
  eauto using update_diff.
Qed.

Lemma getType_update_diff:
  forall Σ l l' T,
    l <> l' ->
    getType ([l ↦ T]Σ) l' = getType Σ l'.
Proof.
  eauto using update_diff.
Qed.

Lemma update_length :
  forall X p v (l: list X),
    length ([p ↦ v]l) = length l.
Proof.
  intros X.
  induction p; steps.
Qed.
Global Hint Resolve update_length: updates.

Lemma getObj_dom:
  forall l O σ, getObj σ l = Some O -> l < dom σ.
Proof.
  unfold getObj.
  intros; eapply nth_error_Some; eauto.
Qed.
Global Hint Resolve getObj_dom: updates.

Lemma getVal_dom:
  forall l v ρ, getVal ρ l = Some v -> l < dom ρ.
Proof.
  unfold getVal.
  intros; eapply nth_error_Some; eauto.
Qed.
Global Hint Resolve getVal_dom: updates.

Lemma getType_dom:
  forall l O Σ, getType Σ l = Some O -> l < dom Σ.
Proof.
  unfold getType.
  intros; eapply nth_error_Some; eauto.
Qed.
Global Hint Resolve getType_dom: updates.


(* ------------------------------------------------------------------------ *)
(** ** Domains lemmas *)

Lemma getObj_Some : forall σ l,
    l < dom σ ->
    exists C ω, getObj σ l = Some (C, ω).
Proof.
  intros.
  destruct (getObj σ l) as [[C ω]|] eqn:?.
  exists C, ω; auto.
  exfalso. eapply nth_error_None in Heqo. lia.
Qed.

Lemma getVal_Some : forall ρ f,
    f < dom ρ ->
    exists v, getVal ρ f = Some v.
Proof.
  intros.
  destruct (getVal ρ f) as [|] eqn:?; eauto.
  exfalso. eapply nth_error_None in Heqo. lia.
Qed.

Lemma getType_Some : forall Σ l,
    l < dom Σ ->
    exists T, getType Σ l = Some T.
Proof.
  intros.
  destruct (getType Σ l) as [|] eqn:?; eauto.
  exfalso. eapply nth_error_None in Heqo. lia.
Qed.


(* ------------------------------------------------------------------------ *)
(** ** Assignments *)

(* This function tries to add the new field of index x to an existing object, and does nothing if
the object already exists with not the right number of fields *)
Definition assign_new l x v σ : option Store :=
  match (getObj σ l) with
  | Some (C, ω) => if (x =? length ω) then
                    Some [l ↦ (C, ω++[v])]σ
                  else
                    Some σ
  | None => None (* Error : adding a field to non-existing object *)
end.

Lemma assign_new_dom:
  forall σ l x v σ',
    assign_new l x v σ = Some σ' ->
    dom σ = dom σ'.
Proof.
  unfold assign_new; steps; try rewrite update_length; done.
Qed.

(* Update store with update in local env : update an already-existing field of an existing object *)
Definition assign l x v σ : Store :=
  match (getObj σ l) with
  | Some (C, ω) => [ l ↦ (C, [x ↦ v]ω)] σ
  | None => σ (* ? *)
  end.


(* ------------------------------------------------------------------------ *)
(** ** Class info *)

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


(* ------------------------------------------------------------------------ *)
(** ** Additions of new objects *)

Lemma getObj_last :
  forall σ C ρ,
    getObj (σ++[(C,ρ)]) (dom σ) = Some (C, ρ).
Proof.
  induction σ; steps.
Qed.
Global Hint Resolve getObj_last: core.

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

Lemma getType_last :
  forall Σ T,
    getType (Σ++[T]) (dom Σ) = Some T.
Proof.
  induction Σ; steps.
Qed.
Global Hint Resolve getType_last: core.

Lemma getType_last2 :
  forall Σ T l,
    l < (dom Σ) ->
    getType (Σ++[T]) l = getType Σ l.
Proof.
  induction Σ; simpl; intros; try lia.
  destruct l;
    steps;
    eauto with lia.
Qed.

Lemma getObj_last_empty :
  forall σ C C' ω l f v,
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


(* ------------------------------------------------------------------------ *)
(** ** Tactics *)

Ltac ct_lookup C :=
  destruct (ct C) as [?Args ?Flds ?Mtds] eqn:?H__ct.

Ltac updates :=
  repeat
    match goal with
    (* appends *)
    |  |- context [ dom (_ ++ _) ] => rewrite app_length; simpl
    | H: context [ dom (_ ++ _) ] |- _ => rewrite app_length in H; simpl in H
    |  |- context [ dom ([_ ↦ _] _) ] => rewrite update_length
    | H: context [ dom ([_ ↦ _] _) ] |- _ => rewrite update_length in H

    (* assign_new *)
    | H: assign_new ?C ?v ?σ = Some ?σ' |- _ =>
        let H1 := fresh "H__dom" in
        add_hypothesis H1 (assign_new_dom σ C v σ' H)

    (* update_same *)
    | H: context [ getObj ([?l ↦ ?O]?σ) ?l = Some ?O'] |- _ =>
        let H1 := fresh "H__dom" in
        add_hypothesis H1 (getObj_dom _ _ _ H);
        rewrite update_length in H1;
        rewrite (getObj_update_same σ l O H1) in H;
        inverts H

    | |- context [ getObj ([?l ↦ ?O]?σ) ?l ] => rewrite (getObj_update_same σ l O)
    | |- context [ getType ([?l ↦ ?O]?σ) ?l ] => rewrite (getType_update_same σ l O)
    | |- context [ getVal ([?l ↦ ?O]?σ) ?l ] => rewrite (getVal_update_same σ l O)

    | H: context [ getVal ([?l ↦ ?O]?σ) ?l = Some ?O'] |- _ =>
        let H1 := fresh "H__dom" in
        add_hypothesis H1 (getVal_dom _ _ _ H);
        rewrite update_length in H1;
        rewrite (getVal_update_same σ l O H1) in H;
        inverts H


    (* update_diff *)
    | H1: ?l <> ?l',
        H2: context [ getObj ([?l ↦ ?O]?σ) ?l' ] |- _ => rewrite (getObj_update_diff σ l l' O H1) in H2
    | H1: ?l <> ?l' |-
        context [ getObj ([?l ↦ ?O]?σ) ?l' ] => rewrite (getObj_update_diff σ l l' O H1)

    | H1: ?l <> ?l',
        H2: context [ getVal ([?l ↦ ?O]?σ) ?l' ] |- _ => rewrite (getVal_update_diff σ l l' O H1) in H2
    | H1: ?l <> ?l' |-
        context [ getVal ([?l ↦ ?O]?σ) ?l' ] => rewrite (getVal_update_diff σ l l' O H1)

    | H1: ?l <> ?l',
        H2: context [ getType ([?l ↦ ?O]?σ) ?l' ] |- _ => rewrite (getType_update_diff σ l l' O H1) in H2
    | H1: ?l <> ?l' |-
        context [ getType ([?l ↦ ?O]?σ) ?l' ] => rewrite (getType_update_diff σ l l' O H1)

    (* get last *)
    | |- context [getObj (?σ ++ _) (dom ?σ) ] => rewrite getObj_last

    end.
Global Hint Extern 1 => updates: updates.


(* ------------------------------------------------------------------------ *)
(** ** Maps *)

Lemma dom_map:
  forall Σ (f: Tpe -> Tpe),
    dom (map (fun T => f T) Σ) = dom Σ.
Proof.
  intros.
  rewrite map_length. auto.
Qed.


Lemma getType_map:
  forall Σ f l T,
    getType Σ l = Some T ->
    getType (map (fun T => f T) Σ) l = Some (f T).
Proof.
  unfold getType. intros.
  rewrite nth_error_map H. steps.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** List Loc *)

Ltac inSingleton :=
  match goal with
  | H: ?a ∈ Singleton Loc ?b |- _ => induction H
  | H: {?x} ?y |- _ => induction H
  end.


(* ------------------------------------------------------------------------ *)
(** ** Store Subset *)

(** A set of locations is contained in a store: [L ⪽ σ] *)
Definition storeSubset σ L :=
  forall l, l ∈ L -> l < dom σ.

(** The codomain of an environment is the set of locations it contains *)
Definition codom ρ : LocSet :=
  fun l => (List.In l ρ).

Notation "L ⪽ σ" := (storeSubset σ L) (at level 80).
Notation " a ∪ { b } " := (Union Loc a (Singleton Loc b)) (at level 80).
Notation "{ l } ⪽ σ" := (storeSubset σ (Singleton Loc l)) (at level 80).

Local Hint Unfold storeSubset: ss.
Global Hint Resolve Union_intror Union_introl In_singleton: core.

Lemma ss_trans :
  forall a s s',
    dom s <= dom s' ->
    a ⪽ s ->
    a ⪽ s'.
Proof.
  unfold storeSubset; steps.
  eapply H0 in H1 ; lia.
Qed.
Lemma ss_union :
  forall a b s,
    a ⪽ s ->
    b ⪽ s ->
    (a∪b) ⪽ s.
Proof.
  unfold storeSubset; intros.
  induction H1; eauto.
Qed.

Lemma ss_union_l :
  forall a b s,
    (a∪b) ⪽ s -> a ⪽ s.
Proof.
  eauto with ss.
Qed.

Lemma ss_union_r :
  forall a b s,
    (a∪b) ⪽ s -> b ⪽ s.
Proof.
  eauto with ss.
Qed.

Lemma ss_add :
  forall v a s,
    codom (v :: a) ⪽ s <-> v < dom s /\ codom a ⪽ s.
Proof.
  unfold codom, List.In, In, storeSubset in *; split.
  + steps; eapply_any; steps; right => //.
  + steps; move: H0 => [Hl|Hl]; steps.
Qed.

Lemma ss_singleton :
  forall a σ,
    a < dom σ -> {a} ⪽ σ.
Proof.
  unfold storeSubset; steps;
    induction H0 ; steps.
Qed.

Lemma ss_singleton_inv :
  forall a σ,
    {a} ⪽ σ -> a < dom σ.
Proof.
  unfold storeSubset; steps.
Qed.

Lemma ss_codom_empty : forall s, codom [] ⪽ s.
Proof.
  unfold storeSubset; steps.
Qed.
Global Hint Resolve ss_codom_empty: core.

Lemma codom_empty_union: forall a, (codom [] ∪ a) = a.
Proof.
  intros.
  apply Extensionality_Ensembles.
  unfold Same_set, Included;
    repeat steps || destruct H;
    eauto with ss.
Qed.

Lemma codom_cons:
  forall a ρ, codom (a::ρ) = ({a} ∪ (codom ρ)).
Proof.
  intros; apply Extensionality_Ensembles.
  unfold Same_set; steps; intros l; steps; try inversion H; steps;
    try inSingleton;
    eauto using Union_introl, Union_intror.
Qed.

Lemma ss_update:
  forall L l o σ,
    L ⪽ [l ↦ o] (σ) -> L ⪽ σ.
Proof.
  unfold storeSubset; steps; updates; eauto.
Qed.

Lemma ss_update_inv:
  forall L l o σ,
     L ⪽ σ -> L ⪽ [l ↦ o] (σ).
Proof.
  unfold storeSubset; steps; updates; eauto.
Qed.

Lemma getVal_codom : forall x l ρ,
    getVal ρ x = Some l -> l ∈ codom ρ.
Proof.
  intros.
  eapply nth_error_In in H. auto.
Qed.
Global Hint Resolve getVal_codom: ss.

Ltac ss_trans :=
  repeat match goal with
         | H: dom ?s <= dom ?s' |- ?a ⪽ ?s => apply (ss_trans a s s' H)
         | H: dom ?s <= dom ?s', H': ?a ⪽ ?s |- ?a ⪽ ?s' => apply (ss_trans a s s' H)
         end.

Ltac ss_union :=
  try match goal with
  | |- (?a ∪ ?b) ⪽ ?s => apply ss_union
  | H1: (?a ∪ ?b) ⪽ ?s |- ?a ⪽ ?s => apply (ss_union_l a b s H1)
  | H1: (?a ∪ ?b) ⪽ ?s |- ?b ⪽ ?s => apply (ss_union_r a b s H1)
  end.

Ltac ss :=
  ss_trans;
  repeat match goal with
         | H: { ?a } ⪽ ?σ |- _ => apply ss_singleton_inv in H
         | |- { ?a } ⪽ ?σ => apply ss_singleton
         | |- ?L ⪽ [?l ↦ ?o] ?σ => apply ss_update_inv
         | H: ?a ∪ {?l} ⪽ ?σ |- ?l < dom ?σ => apply ss_singleton_inv, ss_union_r with a, H
         | H: {?l} ∪ ?b ⪽ ?σ |- ?l < dom ?σ => apply ss_singleton_inv, ss_union_l with b, H
         end || ss_union.
Global Hint Extern 1 => ss : core.


(* ------------------------------------------------------------------------ *)
(** ** Finite sets results **)

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
      destruct_eq (l = dom σ); eauto.
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
Qed.


(* ------------------------------------------------------------------------ *)
(** ** FieldType *)

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


(* ------------------------------------------------------------------------ *)
(** ** List lemmas *)

Lemma app_inv_tail_length:
  forall (A: Type) (l l' l1 l2: list A),
    l++l1 = l'++l2 ->
    length l = length l' ->
    l1 = l2.
Proof.
  induction l; steps.
  - symmetry in H0.
    apply length_zero_iff_nil in H0.
    steps.
  - destruct l'; steps; eauto.
Qed.
