(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the evaluator of the language and some general results *)

From Celsius Require Export Trees Tactics.
Require Import ssreflect ssrbool.
Require Import Celsius.strongInduction.
Require Import List.
Require Import Psatz.
Import ListNotations.
Open Scope nat_scope.

(** The classtable is assumed generaly accessible *)
Parameter ct: ClassTable.

(** ** Helper functions *)

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

(** ** Evaluation results *)

(* Evaluation result *)
Inductive result : Type :=
| Timeout
| Error
| Success : Value -> Store -> result.

Inductive result_l : Type :=
| Timeout_l
| Error_l
| Success_l : (list Value) -> Store -> result_l.


(** ** Big step evaluator (with fuel) *)
(** We define the [eval] function along with its notations *)

Reserved Notation "'⟦' e '⟧' '(' σ ',' ρ ',' v ')(' k ')'"   (at level 80).
Reserved Notation "'⟦_' e '_⟧' '(' σ ',' ρ ',' v ')(' k ')'" (at level 80).
Fixpoint eval e σ ρ v k :=
  match k with
  | 0 => Timeout
  | S n => match e with
          (** Var: simple lookup of the store *)
          | var x => (**r [e = x] *)
            (match (getVal ρ x) with
             | Some v => (Success v σ)
             | _ => Error
             end )

          (** This: returns current value *)
          | this => (Success v σ) (**r [e = this] *)

          (** Field access: compute object value and access field *)
          | fld e0 x => (**r [e = e0.x] *)
            ( match (⟦e0⟧(σ, ρ, v)(n)) with
              | Success v0 σ1 =>
                match (getObj σ1 v0) with
                | Some (c, f) =>
                  match (getVal f x) with
                  | Some v1 => Success v1 σ1
                  | _ => Error end
                | _ => Error end
              | _ => Error end )

          (** Method call : compute object value, compute arguments and do the call*)
          | mtd e0 m el => (**r [e = e0.m(el)] *)
            (match (⟦e0⟧(σ, ρ, v)(n)) with
             | Success v0 σ1 => (
                 match (getObj σ1 v0) with
                 | Some (C, _) => (
                     match (ct C)  with
                     | Some (class _  _ methods) => (
                         match methods m with
                         | Some (method μ x _ e1) => (
                             match (⟦_ el _⟧(σ1, ρ, v)(n)) with
                             | Success_l args_val σ2 =>
                               let ρ1 := args_val in ⟦e1⟧(σ2, ρ1, v0)(n)
                             | _ => Error end)
                         | _ => Error end)
                     | _ => Error end)
                 | _ => Error end)
             | _ => Error end)

          (** New class *)
          | new C args => (**r [e = new C(args)] *)
            (match (⟦_ args _⟧(σ, ρ, v)(n)) with
             | Success_l args_val σ1 => (
                 let I := (length σ1) in (* Fresh location for new object *)
                 let ρ_init := args_val in (* Local env during initialisation *)
                 let σ2 := σ1 ++ [(C, ∅)] in (* New object with empty local env *)
                 match (init I ρ_init C σ2 n) with
                 | Some σ3 => (Success I σ3) (* Returns new object and updated store *)
                 | None => Error end )
             | _ => Error end) (* Invalid args *)

          (** Field assignement *)
          | asgn e1 x e2 e' => (**r [e = (e1.x ← e2 ; e')] *)
            (match (⟦e1⟧(σ, ρ, v)(n)) with
             | Success v1 σ1 => match (⟦e2⟧(σ1, ρ, v)(n)) with
                               | Success v2 σ2 => (
                                   let σ3 := (assign v1 x v2 σ2) in
                                   ⟦e'⟧(σ3, ρ, v)(n))
                               | _ => Error end
             | _ => Error end )
          end
  end
where "'⟦' e '⟧' '(' σ ',' ρ ',' v ')(' k ')'"  := (eval e σ ρ v k)
(** Evaluation of a list of expressions (fold) *)
with eval_list (e_l: list Expr) (σ: Store) (ρ: Env) (v: Value) (k: nat) :=
       match k with
       | 0 => Timeout_l
       | S n => fold_left (eval_list_aux ρ v n) e_l (Success_l [] σ) end
where  "'⟦_' e '_⟧' '(' σ ',' ρ ',' v ')(' k ')'" := (eval_list e σ ρ v k)
with eval_list_aux (ρ: Env) (v: Value) (k: nat) acc (e: Expr) :=
       match k with
       | 0 => Timeout_l
       | S n => match acc with
               | Success_l vs σ1 => match (⟦e⟧(σ1, ρ, v)(n)) with
                                   | Success v σ2 => Success_l (v::vs) σ2
                                   | Timeout => Timeout_l
                                   | Error => Error_l
                                   end
               | z => z end end
(** Initialization of a list of fields using (fold) *)
with init (I : Var) (args_values: list Var) (C: ClN) (σ: Store) (k :nat) : option Store :=
       match k with | 0 => None | S n =>
                                 match (ct C) with
                                 | Some (class x F M) => (fold_left (init_field args_values I n) F (Some σ))
                                 | None => None
                                 end
       end
with init_field (args_values: list Var) (this: Var) (k: nat) (σ_opt: option Store)  (f: Field): option Store :=
       match k with
       | 0 => None
       | S n =>
         match σ_opt with
         | None => None
         | Some σ => ( match f with
                      | field t e => (
                          match (⟦e⟧(σ, args_values, this)(n)) with
                          | Success v1 σ1 => (assign_new this v1 σ1)
                          | _ => None
                          end) end) end end.

(** A usefull lemma to show that folds on computations that got stuck (error or timeout) will stay stuck *)
Lemma foldLeft_constant : forall (A B: Type) (l: list B) (res: A) (f : A -> B -> A),
    (forall (y:B), f res y = res) -> fold_left f l res = res.
Proof.
  intros.
  induction l => //.
  simpl. rewrite H. apply IHl.
Qed.

(** Associated ltac tactics : *)
Ltac destruct_eval :=
  match goal with
  | H: context[⟦ ?e ⟧ (?σ, ?ρ, ?ψ )( ?k)] |- _ =>
    let fresh_H := fresh H in
    destruct (⟦ e ⟧ (σ, ρ, ψ )( k)) eqn:fresh_H ;
    try solve [rewrite foldLeft_constant in H => //]
  end.

Ltac destruct_eval_with_name fresh_H :=
  match goal with
  | H: context[⟦ ?e ⟧ (?σ, ?ρ, ?ψ )( ?k)] |- _ =>
    destruct (⟦ e ⟧ (σ, ρ, ψ )( k)) eqn:fresh_H ;
    try solve [rewrite foldLeft_constant in H => //]
  end.

(** A simple result on lengths *)
Lemma EvalListLength :
  forall n el σ σ' ρ ψ l ,
    ⟦_ el _⟧(σ, ρ, ψ)(n) = Success_l l σ' ->
    length el = length l.
Proof.
  destruct n; simpl; try discriminate.
  assert
    (forall l σ σ' ρ v v_list1 v_list2,
        fold_left (eval_list_aux ρ v n) l (Success_l v_list1 σ) = Success_l v_list2 σ'
        -> length l + length v_list1 = length v_list2) as H_fold.
  {
    induction l as [| e l] ; steps.
    destruct n; simpl in H ; [rewrite foldLeft_constant in H => // |].
    destruct_eval.
    apply IHl in H.
    simpl in H.
    rewrite plus_n_Sm => //.
  }
  steps;
    eapply_anywhere H_fold;
    rewrite_anywhere PeanoNat.Nat.add_0_r => // .
Qed.


(** ** Results *)
(** As we will show, if a relationship between stores verifies certain properties, it will be maintained by the evaluator. This is used to prove the partial-monotonicity, compatibility, wellformedness and stackability theorems. The scopability theorem is more involved, as it is a relationship involving both the stores and the locations. *)

Definition Reflexive (P: Store -> Store -> Prop) : Prop :=
  forall σ, P σ σ.
Definition Transitive (P: Store -> Store -> Prop)  : Prop :=
  forall σ1 σ2 σ3, P σ1 σ2 ->  P σ2 σ3 ->  P σ1 σ3.
Definition Assignment (P: Store -> Store -> Prop)  : Prop :=
  forall σ σ' l C ω ω',
    getObj σ l = Some (C, ω) ->
    length ω <= length ω' ->
    σ' = [l ↦ (C, ω')]σ -> P σ σ'.
Definition Freshness (P: Store -> Store -> Prop) : Prop :=
  forall s c ω, P s (s ++ [(c, ω)]).

(** A relation maintained by the evaluator. All local-reasoning theorems are about showing that some relations are eval maintained. *)
Definition EvalMaintained (P: Store -> Store -> Prop)  k : Prop :=
  forall e σ σ' ρ v v',
    ⟦e⟧(σ, ρ, v)(k) = Success v' σ' ->
    P σ σ'.

(** *** Initialization *)
(** One sub-case is to show relations are maintained through initialization of a new object. This could be the consequence of some general properties, or can be proved ad hoc (like for stackability). It's written for a strong-induction-style proof *)
Definition InitMaintained (P: Store -> Store -> Prop) (n:nat) : Prop :=
  (forall k, k < n -> EvalMaintained P k) -> (**r strong induction hypothesis *)
  forall k,
    k < n ->
    forall l0 s σ' c,
      init (length s) l0 c (s ++ [(c, [])]) k = Some σ' ->
      P s σ'.

(** Notably, if a relation verifies [Freshness] (and other properties), it will be maintained through initialization. *)
Lemma FreshnessInitMaintained :
  forall (P: Store -> Store -> Prop) n,
    Reflexive P -> Transitive P -> Assignment P -> Freshness P -> InitMaintained P n.
Proof.
  intros P n H_refl H_trans H_asgn H_fresh H_strong.
  assert ( forall k, k < n ->
                forall l0 σ σ' c I , init I l0 c σ k = Some σ' -> P σ σ'); eauto.
  destruct k; simpl; try discriminate.
  intros Hn; intros.
  repeat destruct_match; try discriminate. clear matched0 matched.
  move : H. move: σ σ'.
  induction fields as [| [x e] fields]; [steps | simpl; intros].
  destruct k; simpl in H; [ rewrite foldLeft_constant in H => // |].
  destruct_eval_with_name E; eauto.
  unfold assign_new in *.
  repeat destruct_match; try solve [rewrite foldLeft_constant in H => //].
  subst.
  apply PeanoNat.Nat.lt_succ_l, PeanoNat.Nat.lt_succ_l in Hn.
  apply H_strong in E => //.
  eapply (H_trans _ _ _ E).
  apply (H_trans _  [I ↦ (c1, e0 ++ [v])] (s) ) ; eauto.
  apply (H_asgn _ _ _ _ _ (e0 ++ [v])  matched); eauto.
  rewrite app_length; steps; lia.
Qed.

(** *** Evaluation of lists of expressions *)
(** Another sub-case is to show that [Reflexive] and [Transitive] eval-maintained relations are also maintained when evaluating a list of expressions *)
Lemma EvalListMaintained :
  forall (P: Store -> Store -> Prop) n,
    Reflexive P ->
    Transitive P ->
    (forall k, k < n -> EvalMaintained P k) -> (**r strong induction hypothesis *)
    forall k,
      k < n ->
      forall l σ σ' ρ v v_list,
        ⟦_ l _⟧(σ, ρ, v)(k) = Success_l v_list σ' ->
        P σ σ'.
Proof.
  intros P n H_refl H_trans H_strong.
  destruct k; simpl; try discriminate.
  assert (forall l σ σ' ρ v v_list1 v_list2,
             (k < n) ->
             fold_left (eval_list_aux ρ v k) l (Success_l v_list1 σ) = Success_l v_list2 σ' ->
             P σ σ'); eauto using PeanoNat.Nat.lt_succ_l.
  induction l as [| e l]; [steps | simpl; intros].
  destruct k; simpl in *; [rewrite foldLeft_constant in H0 => // |].
  move /(_ _ _ _ _ _ _ H):IHl => IHl.
  move /(_ _ (PeanoNat.Nat.lt_succ_l _ _ H)):H_strong => H_strong.
  destruct_eval ; eauto.
Qed.

(** *** Main evaluation result *)
(** We show here that a relation that is [Reflexive], [Transitive], that is maintained through assignment and initialization is maintained by the evaluator. We use strong induction *)

Lemma EvalMaintainedProp :
  forall (P: Store -> Store -> Prop),
    Reflexive P -> Transitive P ->  Assignment P -> (forall n, InitMaintained P n) -> forall n, EvalMaintained P n.
  intros P H_refl H_trans  H_asgn H_init.
  apply strong_induction.
  unfold EvalMaintained.
  intros n H_strong.
  move /(_ n H_strong):H_init => H_init.
  (** To get one step of the evaluator, we destruct n *)
  destruct n => //.
  move : (PeanoNat.Nat.lt_succ_diag_r n) => Hn.
  destruct e;
    repeat light || invert_constructor_equalities || destruct_match || eauto 3;
    try solve [eapply_anywhere EvalListMaintained; eauto].
  (** Only one case remaining *)
  eapply H_trans with s; eauto.
  eapply H_trans with s0; eauto.
  eapply H_trans with (assign v1 v v2 s0); eauto.
  unfold assign; repeat destruct_match; eauto using PeanoNat.Nat.eq_le_incl, update_one3.
Qed.

(** Usefull Ltac when using the above theorem *)
Ltac unfoldProps :=
  unfold Reflexive, Transitive, Assignment, Freshness, InitMaintained, EvalMaintained.
