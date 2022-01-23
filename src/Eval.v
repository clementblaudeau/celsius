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

Inductive result_i : Type :=
| Timeout_i
| Error_i
| Success_i : Store -> result_i.

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
                | z => z end )

          (** Method call : compute object value, compute arguments and do the call*)
          | mtd e0 m el => (**r [e = e0.m(el)] *)
              (match (⟦e0⟧(σ, ρ, v)(n)) with
               | Success v0 σ1 =>
                   ( match (getObj σ1 v0) with
                     | Some (C, _) =>
                         ( match (ct C)  with
                           | (class _  _ Mtds) =>
                               ( match Mtds m with
                                 | Some (method μ x _ e1) =>
                                     ( match (⟦_ el _⟧(σ1, ρ, v)(n)) with
                                       | Success_l args_val σ2 =>
                                           let ρ1 := args_val in ⟦e1⟧(σ2, ρ1, v0)(n)
                                       | Error_l => Error
                                       | Timeout_l => Timeout
                                       end)
                                 | _ => Error end)
                           end )
                     | _ => Error end)
               | z => z end)

          (** New class *)
          | new C args => (**r [e = new C(args)] *)
              (match (⟦_ args _⟧(σ, ρ, v)(n)) with
               | Success_l args_val σ1 =>
                   ( let I := (length σ1) in (* Fresh location for new object *)
                     let ρ_init := args_val in (* Local env during initialization *)
                     let σ2 := σ1 ++ [(C, [])] in (* New object with empty local env *)
                     let 'class Args Flds Mtds := (ct C) in
                     match (init C Flds I ρ_init σ2 n) with
                     | Success_i σ3 => (Success I σ3) (* Returns new object and updated store *)
                     | Error_i => Error
                     | Timeout_i => Timeout
                     end )
               | Error_l => Error
               | Timeout_l => Timeout
               end) (* Invalid args *)

          (** Field assignment *)
          | asgn e1 x e2 e' => (**r [e = (e1.x ← e2 ; e')] *)
              (match (⟦e1⟧(σ, ρ, v)(n)) with
               | Success v1 σ1 =>
                   match (⟦e2⟧(σ1, ρ, v)(n)) with
                   | Success v2 σ2 =>
                       ( let σ3 := (assign v1 x v2 σ2) in
                         ⟦e'⟧(σ3, ρ, v)(n))
                   | z => z end
               | z => z end )
          end
  end
where "'⟦' e '⟧' '(' σ ',' ρ ',' v ')(' k ')'"  := (eval e σ ρ v k)
(** Evaluation of a list of expressions (fold) *)
with eval_list (e_l: list Expr) (σ: Store) (ρ: Env) (ψ: Value) (n: nat) :=
       match n with
       | 0 => Timeout_l
       | S n => match e_l with
               | [] => Success_l [] σ
               | e::e_l =>
                   match (⟦e⟧(σ, ρ, ψ)(n)) with
                   | Success v σ' =>
                       match ⟦_ e_l _⟧(σ', ρ, ψ)(n) with
                       | Success_l vl σ'' => Success_l (v::vl) σ''
                       | z => z
                       end
                   | Error => Error_l
                   | Timeout => Timeout_l
                   end
               end
       end
where  "'⟦_' e '_⟧' '(' σ ',' ρ ',' v ')(' k ')'" := (eval_list e σ ρ v k)
(** Initialization of a list of fields using (fold) *)
with init (C: ClN) (flds: list Field) (I : Var) (ρ: list Var) (σ: Store) (n :nat) : result_i :=
       match n with
       | 0 => Timeout_i
       | S n => match flds with
               | [] => Success_i σ
               | (field T e)::flds =>
                   match ⟦e⟧(σ, ρ, I)(n) with
                   | Success v σ' =>
                       match (assign_new I v σ') with
                       | Some σ'' => init C flds I ρ σ'' n
                       | _ => Error_i
                       end
                   | Error => Error_i
                   | Timeout => Timeout_i
                   end
               end
       end.

(** Associated ltac tactics : *)
Ltac destruct_eval He v σ' :=
  match goal with
  | H: context[ match ⟦ ?e ⟧ (?σ, ?ρ, ?ψ )(?k) with _ => _ end ] |- _ =>
      destruct (⟦ e ⟧ (σ, ρ, ψ )( k)) as [ | | v σ' ] eqn:He
  | H: context[ match ⟦_ ?el _⟧ (?σ, ?ρ, ?ψ )(?k) with _ => _ end ] |- _ =>
      destruct (⟦_ el _⟧ (σ, ρ, ψ )( k)) as [ | | v σ' ] eqn:He
  end; try congruence.

Ltac destruct_eval_f :=
  let freshH := fresh "H" in
  let freshv := fresh "v" in
  let freshσ := fresh "σ" in
  destruct_eval freshH freshv freshσ.

(** A simple result on lengths *)
Lemma EvalListLength :
  forall el n σ σ' ρ ψ l ,
    ⟦_ el _⟧(σ, ρ, ψ)(n) = Success_l l σ' ->
    length el = length l.
Proof.
  induction el; steps;
    destruct n; simpl; try discriminate.
  - inversion H; steps.
  - inversion H.
    destruct_eval_f ; steps.
    eapply IHel in matched1. steps.
Qed.


(** ** Evaluator fuel-monotonicity *)
Lemma eval_step_monotonicity_aux: forall n,
    (forall m, m > n ->
          (forall e σ ρ ψ v σ', ⟦ e ⟧ (σ, ρ, ψ)(n) = Success v σ' ->
                           ⟦ e ⟧ (σ, ρ, ψ)(m) = Success v σ')) /\
      (forall m, m > n ->
            (forall el σ ρ ψ vl σ', ⟦_ el _⟧ (σ, ρ, ψ)(n) = Success_l vl σ' ->
                               ⟦_ el _⟧ (σ, ρ, ψ)(m) = Success_l vl σ')) /\
      (forall m, m > n ->
            (forall C flds I ρ σ σ', init C flds I ρ σ n = Success_i σ' ->
                                init C flds I ρ σ m = Success_i σ')).
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
        eapply (Hlist m) in matched5...
        steps.
      * inversion H0; repeat destruct_match => //.
        rewrite_any.
        eapply (Hlist m) in matched...
        eapply (Hinit m) in matched1...
        steps.
      * inversion H0; repeat destruct_match => //; sort.
        rewrite_any.
        eapply (Hexp m) in matched, matched0, H2...
        steps.
    + (* lists *)
      simpl in *.
      destruct el; eauto.
      destruct_eval_f.
      eapply (IHn n)  with (m := m) in H1; eauto with lia.
      destruct_match; try discriminate.
      destruct_eval_f.
      inversion H1; subst.
      eapply (IHn n) with (m := m) in H2; eauto with lia.
      steps.
    + (* init *)
      simpl in *.
      destruct flds as [| [_ e]]; eauto.
      destruct_eval_f.
      eapply (IHn n)  with (m := m) in H1; eauto with lia.
      steps.
      eapply (IHn n) with (m := m); eauto with lia.
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
  forall n m C flds ρ I σ σ',
    n < m ->
    init C flds ρ I σ n = Success_i σ' ->
    init C flds ρ I σ m = Success_i σ'.
Proof with try lia.
  intros.
  pose proof (eval_step_monotonicity_aux n) as [_ [_ H__init]].
  eauto with lia.
Qed.


Theorem evalP_eval :
  forall e σ ρ ψ l σ', ⟦ e ⟧p (σ, ρ, ψ) --> (l,σ') <-> exists n, ⟦ e ⟧ (σ, ρ, ψ)(n) = Success l σ'.
Proof with (eauto; try lia).
  split; intros.
  - induction H using evalP_ind2 with
      (Pl := fun el σ ρ ψ vl σ' (H__el : evalListP el σ ρ ψ vl σ') =>
               exists n, ⟦_ el _⟧ (σ, ρ, ψ)(n) = Success_l vl σ')
      (Pin := fun C flds I ρ σ σ' (H__init : initP C flds I ρ σ σ') =>
                exists n, init C flds I ρ σ n = Success_i σ');
      try solve [exists 1; steps];
      repeat match goal with
             | H: exists n, _ |- _ => destruct H as [?n H]
             end.
    + exists (S n); steps.
    + set (n2 := S (max n1 (max n0 n))).
      eapply eval_step_monotonicity with (m := n2) in IHevalP1, IHevalP3...
      eapply evalList_step_monotonicity with (m := n2) in IHevalP2...
      exists (S n2); steps.
    + remember (S (max n n0)) as n1.
      eapply evalList_step_monotonicity with (m := (S n1)) in IHevalP...
      eapply init_step_monotonicity with (m := (S n1)) in IHevalP0...
      exists (S (S n1)). steps.
    + remember (S (max n (max n0 n1))) as n2.
      eapply eval_step_monotonicity with (m := n2) in IHevalP1, IHevalP2, IHevalP3...
      exists (S n2). steps.
    + remember (S (max n n0)) as n1.
      eapply eval_step_monotonicity with (m := n1) in IHevalP...
      eapply evalList_step_monotonicity with (m := n1) in IHevalP0...
      exists (S n1). steps.
    + remember (S (max n n0)) as n1.
      eapply eval_step_monotonicity with (m := n1) in IHevalP...
      eapply init_step_monotonicity with (m := n1) in IHevalP0...
      exists (S n1). steps.
  - destruct H as [n H].
    gen e σ ρ ψ l σ'.
    eapply proj1 with (
        (forall el σ ρ ψ vl σ',
            ⟦_ el _⟧ (σ, ρ, ψ)(n) = Success_l vl σ' ->
            ⟦_ el _⟧p (σ, ρ, ψ) --> (vl, σ')) /\
          (forall C flds I ρ σ σ',
              init C flds I ρ σ n = Success_i σ' ->
              initP C flds I ρ σ σ')).
    induction n as [n IHn] using lt_wf_ind.
    destruct n; repeat split => //; intros;
      move : (IHn n) => [ ] // => IHn__e [IHn__el IHn__init]; clear IHn.
    + simpl in H. steps; eauto using evalP.
    + steps; eauto using evalP...
      apply IHn__e in matched.
      apply IHn__el in matched0.
      eapply el_cons...
    + steps; eauto using evalP...
      apply IHn__e in matched.
      apply IHn__init in H.
      eapply init_cons...
Qed.


Corollary eval_implies_evalp :
  forall e σ ρ ψ l σ' n, ⟦ e ⟧ (σ, ρ, ψ)(n) = Success l σ' -> ⟦ e ⟧p (σ, ρ, ψ) --> (l,σ').
Proof.
  intros.
  apply evalP_eval; eauto.
Qed.

Corollary eval_list_implies_evalp :
  forall el σ ρ ψ vl σ' n, ⟦_ el _⟧ (σ, ρ, ψ)(n) = Success_l vl σ' -> ⟦_ el _⟧p (σ, ρ, ψ) --> (vl,σ').
Proof.
  induction el; intros.
  - destruct n; steps.
  - destruct n; steps.
    eapply el_cons;
      eauto using evalP, eval_implies_evalp.
Qed.
