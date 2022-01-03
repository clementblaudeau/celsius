(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the big-step evaluator of the language (with fuel). It is then shown equivalent to the predicate version *)

From Celsius Require Export Semantics Tactics.
Require Import ssreflect ssrbool.
Require Import List Psatz Arith.
Import ListNotations.
Open Scope nat_scope.

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
               | Success v0 σ1 =>
                   ( match (getObj σ1 v0) with
                     | Some (C, _) =>
                         ( match (ct C)  with
                           | Some (class _  _ methods) =>
                               ( match methods m with
                                 | Some (method μ x _ e1) =>
                                     ( match (⟦_ el _⟧(σ1, ρ, v)(n)) with
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
               | Success_l args_val σ1 =>
                   ( let I := (length σ1) in (* Fresh location for new object *)
                     let ρ_init := args_val in (* Local env during initialization *)
                     let σ2 := σ1 ++ [(C, [])] in (* New object with empty local env *)
                     match (init I ρ_init C σ2 n) with
                     | Some σ3 => (Success I σ3) (* Returns new object and updated store *)
                     | None => Error end )
               | _ => Error end) (* Invalid args *)

          (** Field assignement *)
          | asgn e1 x e2 e' => (**r [e = (e1.x ← e2 ; e')] *)
              (match (⟦e1⟧(σ, ρ, v)(n)) with
               | Success v1 σ1 =>
                   match (⟦e2⟧(σ1, ρ, v)(n)) with
                   | Success v2 σ2 =>
                       ( let σ3 := (assign v1 x v2 σ2) in
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
               | Success_l vs σ1 =>
                   match (⟦e⟧(σ1, ρ, v)(n)) with
                   | Success v σ2 => Success_l (vs++[v]) σ2
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
           | Some σ =>
               ( match f with
                 | field t e =>
                     ( match (⟦e⟧(σ, args_values, this)(n)) with
                       | Success v1 σ1 => (assign_new this v1 σ1)
                       | _ => None
                       end)
                 end)
           end
       end.



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
  + induction l as [| e l] ; steps.
    destruct n; simpl in H ; [rewrite foldLeft_constant in H => // |].
    destruct_eval.
    apply IHl in H.
    rewrite app_length in H.
    simpl in H. lia.
  + steps;
    eapply_anywhere H_fold;
    rewrite_anywhere PeanoNat.Nat.add_0_r => // .
Qed.


(** ** Evaluator step-monotonicity *)
Lemma fold_left_app:
  forall (n0 : nat) (ρ : Env) (ψ : Value) (σ' : Store) (el0 : list Expr)
    (vl0 : list Value) (σ1 : Store) vl acc,
    fold_left (eval_list_aux ρ ψ n0) el0 (Success_l vl σ1) = Success_l vl0 σ' <->
      fold_left (eval_list_aux ρ ψ n0) el0 (Success_l (acc++vl) σ1) = Success_l (acc++vl0) σ'.
Proof.
  intros.
  move: n0 σ1 σ' vl acc.
  induction el0; split; intros.
  + inversion H; steps.
  + inversion H. steps.
    eapply app_inv_head in H1. steps.
  + inversion H; steps.
    destruct n0; try solve [rewrite foldLeft_constant in H => //].
    simpl in H |- *.
    destruct_eval.
    specialize (IHel0 (S n0) s σ' (vl++[v]) acc) as [IHel0 _].
    rewrite app_assoc_reverse.
    eauto.
  + inversion H; steps.
    destruct n0; try solve [rewrite foldLeft_constant in H => //].
    simpl in H |- *.
    destruct_eval.
    specialize (IHel0 (S n0) s σ' (vl++[v]) acc) as [ ].
    rewrite app_assoc_reverse in H.
    eauto.
Qed.

Lemma fold_left_app_inv:
  forall n el σ ρ ψ vl σ' acc,
    fold_left (eval_list_aux ρ ψ n) el (Success_l acc σ) = Success_l vl σ' ->
    exists vl', vl = acc ++ vl'.
Proof.
  induction el; intros; steps.
  - exists ([]: list Value). rewrite app_nil_r => //.
  - destruct n; try solve [rewrite foldLeft_constant in H => //].
    simpl in H.
    destruct_eval.
    eapply IHel in H as [vl' H].
    exists (v::vl').
    rewrite -app_assoc in H => //.
Qed.

Lemma eval_step_monotonicity_aux: forall n,
    (forall m, m > n ->
          (forall e σ ρ ψ v σ', ⟦ e ⟧ (σ, ρ, ψ)(n) = Success v σ' ->
                           ⟦ e ⟧ (σ, ρ, ψ)(m) = Success v σ')) /\
      (forall m, m > n ->
            (forall el σ ρ ψ vl σ', ⟦_ el _⟧ (σ, ρ, ψ)(n) = Success_l vl σ' ->
                               ⟦_ el _⟧ (σ, ρ, ψ)(m) = Success_l vl σ')) /\
      (forall m, m > n ->
            (forall C σ σ' l vl, init l vl C σ n = Some σ' ->
                            init l vl C σ m = Some σ')).
Proof with (try lia).
  induction n as [n IHn] using lt_wf_ind. destruct n.
  - repeat split; intros; inversion H0.
  - repeat split; intros ; destruct m...
    + (* expression *)
      destruct (IHn n) as [Hexp [Hlist Hinit]]...
      destruct e ; try solve [steps; eauto].
      * inversion H0; repeat destruct_match => //; subst.
        eapply (Hexp m) in matched; steps...
      * inversion H0; repeat destruct_match => //.
        rewrite_any.
        eapply (Hexp m) in matched, H2...
        eapply (Hlist m) in matched6...
        steps.
      * inversion H0; repeat destruct_match => //.
        rewrite_any.
        eapply (Hlist m) in matched...
        eapply (Hinit m) in matched0...
        steps.
      * inversion H0; repeat destruct_match => //; sort.
        rewrite_any.
        eapply (Hexp m) in matched, matched0, H2...
        steps.
    + (* lists *)
      simpl in *. move: vl σ σ' H0.
      set (acc := []).
      generalize acc.
      clear acc.
      induction el => //. intros; simpl in *.
      destruct n; try solve [rewrite foldLeft_constant in H0 => //]; simpl in * => //.
      destruct m...
      destruct_eval. destruct (IHn n) as [He _]...
      eapply (He m) in H1...
      steps.
    + (* init *)
      simpl in *; destruct_match; steps.
      gen σ.
      clear matched.
      induction fields => //.
      intros; simpl in *.
      destruct n; try solve [rewrite foldLeft_constant in H0 => //]; simpl in * => //.
      destruct m...
      simpl. destruct a.
      destruct_eval.
      destruct (IHn n) as [He _]...
      eapply (He m) in H1...
      rewrite H1.
      unfold assign_new in *.
      destruct (getObj s l); steps; eauto.
      rewrite foldLeft_constant in H0 => //.
Qed.

Theorem eval_step_monotonicity:
  forall n m e σ ρ ψ l σ',
    n < m ->
    ⟦ e ⟧ (σ, ρ, ψ)(n) = Success l σ' ->
    ⟦ e ⟧ (σ, ρ, ψ)(m) = Success l σ'.
Proof.
  intros.
  pose proof (eval_step_monotonicity_aux n) as [He _].
  eauto with lia.
Qed.

Theorem evalList_step_monotonicity:
  forall n m el σ ρ ψ vl σ',
    n < m ->
    ⟦_ el _⟧ (σ, ρ, ψ)(n) = Success_l vl σ' ->
    ⟦_ el _⟧ (σ, ρ, ψ)(m) = Success_l vl σ'.
Proof.
  intros.
  pose proof (eval_step_monotonicity_aux n) as [_ [Hel _]].
  eauto with lia.
Qed.

Theorem init_step_monotonicity:
  forall n m Flds ρ ψ σ σ',
    n < m ->
    fold_left (init_field ρ ψ n) Flds (Some σ)  = Some σ' ->
    fold_left (init_field ρ ψ m) Flds (Some σ)  = Some σ'.
Proof with try lia.
  intros. move: σ σ' H0.
  induction Flds as [| [T e] flds]; [steps |].
  intros.
  destruct m ...
  destruct n ; simpl in H0 |- * ; try solve [rewrite foldLeft_constant in H0 => //].
  destruct_eval.
  eapply eval_step_monotonicity with (m := m) in H1...
  rewrite H1.
  destruct (assign_new ψ v s); try solve [rewrite foldLeft_constant in H0 => //].
  eauto.
Qed.


Theorem evalListP_eval_list :
  forall e σ ρ ψ l σ', ⟦ e ⟧p (σ, ρ, ψ) --> (l,σ') <-> exists n, ⟦ e ⟧ (σ, ρ, ψ)(n) = Success l σ'.
Proof with (eauto; try lia).
  split; intros.
  - induction H using evalP_ind2 with
      (Pl := fun el σ ρ ψ vl σ' (H__el : evalListP el σ ρ ψ vl σ') =>
               exists n, ⟦_ el _⟧ (σ, ρ, ψ)(n) = Success_l vl σ')
      (Pin := fun fls I ρ σ σ' (H__init : initP fls I ρ σ σ') =>
               exists n, fold_left (init_field ρ I n) fls (Some σ) = Some σ');
      try solve [exists 1; steps].
    + destruct IHevalP as [n__e0 H__e0].
      exists (S n__e0); steps.
    + clear H H__el H0.
      destruct IHevalP1 as [n__e0 H__e0], IHevalP2 as [n__el H__el], IHevalP3 as [n__e2 H__e2].
      set (n := S (max n__e0 (max n__el n__e2))).
      eapply eval_step_monotonicity with (m := n) in H__e0, H__e2...
      eapply evalList_step_monotonicity with (m := n) in H__el...
      exists (S n); steps.
    + clear H__args H__init.
      destruct IHevalP as [n__args H__args], IHevalP0 as [n__init H__init].
      remember (S (max n__args n__init)) as n.
      eapply evalList_step_monotonicity with (m := (S n)) in H__args...
      eapply init_step_monotonicity with (m := n) in H__init...
      exists (S (S n)). simpl in H__args |- * .
      steps.
    + clear H H0 H1.
      destruct IHevalP1 as [n__e1 H__e1], IHevalP2 as [n__e2 H__e2], IHevalP3 as [n__e3 H__e3].
      remember (S (max n__e1 (max n__e2 n__e3))) as n.
      eapply eval_step_monotonicity with (m := n) in H__e1, H__e2, H__e3 ...
      exists (S n). steps.
    + clear H H__el.
      destruct IHevalP as [n__e H__e], IHevalP0 as [n__el H__el].
      remember (S (max n__e n__el)) as n.
      eapply eval_step_monotonicity with (m := n) in H__e ...
      eapply evalList_step_monotonicity with (m := (S (S n))) in H__el...
      exists (S (S n)); simpl in H__el |- *.
      rewrite H__e.
      eapply fold_left_app with (n0 := S n) (acc := [v1]) in H__el => //.
    + clear H H__flds.
      destruct IHevalP as [n__e H__e], IHevalP0 as [n__flds H__flds].
      remember (S (max n__e n__flds)) as n.
      eapply eval_step_monotonicity with (m := n) in H__e ...
      eapply init_step_monotonicity with (m := (S n)) in H__flds...
      exists (S n). steps.
  - destruct H as [n H].
    gen e σ ρ ψ l σ'.
    eapply proj1 with (
        (forall el σ ρ ψ vl σ',
              ⟦_ el _⟧ (σ, ρ, ψ)(n) = Success_l vl σ' ->
              ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ')) /\
          (forall C Tps Mtds Flds ψ ρ σ σ',
              ct C = Some (class Tps Flds Mtds) ->
              fold_left (init_field ρ ψ n) Flds (Some σ) = Some σ' ->
              initP Flds ψ ρ σ σ' )).
    induction n as [n IHn] using lt_wf_ind. destruct n.
    + clear IHn.
      repeat split => // ; intros; simpl in * => //.
      destruct Flds; steps; eauto.
      rewrite foldLeft_constant in H0 => //.
    + repeat split.
      * intros.
        move : (IHn n) => [ ] // => IHn__e [IHn__el _].
        destruct (IHn (n - 1)) as [_ [ _ IH__init]]...
        destruct_eval; steps;
          eauto using evalP.
        ++ destruct n; [steps |].
           assert (S n - 1 = n) by lia. rewrite H in IH__init.
           simpl in matched0.
           repeat destruct_match; [| steps].
           eapply e_new; eauto.
      * move /(_ n): IHn => [ ] // => IHn__e [IHn__el _].
        induction el; [ steps; eauto |].
        intros.
        destruct n ; simpl in H |- *; try solve [rewrite foldLeft_constant in H => //].
        destruct_eval.
        lets [vl' Hv] : fold_left_app_inv (S n) [v] H; subst.
        eapply eval_step_monotonicity with (m := S n) in H0...
        eapply el_cons; eauto.
        eapply IHel, fold_left_app with (acc := [v]) => //.
      * intros.
        move /(_ n): IHn => [ ] // => IHn__e [IHn__el _].
        clear H.
        move: σ σ' H0.
        induction Flds as [| [T e] flds]; [steps; eauto|].
        intros.
        simpl in H0. destruct_eval.
        destruct (assign_new ψ v s) eqn:H__assign; eauto using initP.
        rewrite foldLeft_constant in H0 => //.
Qed.
