(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL & Inria 2020-2022 *)
(* ------------------------------------------------------------------------ *)
(* This file defines the definitional interpreter of the language. It is then shown equivalent to
the big step-semantics (when it succeeds) *)

From Celsius Require Import Semantics.
Implicit Type (σ: Store) (ρ ω: Env) (l: Loc).

(* ------------------------------------------------------------------------ *)
(** ** Evaluation results *)

(* Evaluation result *)
Inductive result : Type :=
| Timeout
| Error
| Success : Loc -> Store -> result.

Inductive result_l : Type :=
| Timeout_l
| Error_l
| Success_l ρ σ : result_l.

Inductive result_i : Type :=
| Timeout_i
| Error_i
| Success_i σ : result_i.

(* ------------------------------------------------------------------------ *)
(** ** Definitional Evaluator (with fuel) *)

Fixpoint eval e σ ρ v k :=
  match k with
  | 0 => Timeout
  | S n => match e with
          (** Var: simple lookup of the store *)
          | e_var x => (**r [e = x] *)
              (match (getVal ρ x) with
               | Some v => (Success v σ)
               | _ => Error
               end )

          (** This: returns current value *)
          | e_this => (Success v σ) (**r [e = this] *)

          (** Field access: compute object value and access field *)
          | e_fld e0 x => (**r [e = e0.x] *)
              ( match (⟦e0⟧(σ, ρ, v, n)) with
                | Success v0 σ1 =>
                    match (getObj σ1 v0) with
                    | Some (c, f) =>
                        match (getVal f x) with
                        | Some v1 => Success v1 σ1
                        | _ => Error end
                    | _ => Error end
                | z => z end )

          (** Method call : compute object value, compute arguments and do the call*)
          | e_mtd e0 m el => (**r [e = e0.m(el)] *)
              (match (⟦e0⟧(σ, ρ, v, n)) with
               | Success v0 σ1 =>
                   ( match (getObj σ1 v0) with
                     | Some (C, _) =>
                         ( match (ct C)  with
                           | (class _  _ Mtds) =>
                               ( match Mtds m with
                                 | Some (method μ x _ e1) =>
                                     ( match (⟦_ el _⟧(σ1, ρ, v, n)) with
                                       | Success_l args_val σ2 =>
                                           let ρ1 := args_val in ⟦e1⟧(σ2, ρ1, v0, n)
                                       | Error_l => Error
                                       | Timeout_l => Timeout
                                       end)
                                 | _ => Error end)
                           end )
                     | _ => Error end)
               | z => z end)

          (** New class *)
          | e_new C args => (**r [e = new C(args)] *)
              (match (⟦_ args _⟧(σ, ρ, v, n)) with
               | Success_l args_val σ1 =>
                   ( let I := (length σ1) in (* Fresh location for new object *)
                     let ρ_init := args_val in (* Local env during initialization *)
                     let σ2 := σ1 ++ [(C, [])] in (* New object with empty local env *)
                     match (init C I 0 ρ_init σ2 n) with
                     | Success_i σ3 => (Success I σ3) (* Returns new object and updated store *)
                     | Error_i => Error
                     | Timeout_i => Timeout
                     end )
               | Error_l => Error
               | Timeout_l => Timeout
               end) (* Invalid args *)

          (** Field assignment *)
          | e_asgn e1 x e2 e' => (**r [e = (e1.x ← e2 ; e')] *)
              (match (⟦e1⟧(σ, ρ, v, n)) with
               | Success v1 σ1 =>
                   match (⟦e2⟧(σ1, ρ, v, n)) with
                   | Success v2 σ2 =>
                       ( let σ3 := (assign v1 x v2 σ2) in
                         ⟦e'⟧(σ3, ρ, v, n))
                   | z => z end
               | z => z end )
          end
  end

where "⟦ e ⟧ ( σ , ρ , ψ , n )" := (eval e σ ρ ψ n)

(** Evaluation of a list of expressions (fold) *)
with eval_list (e_l: list Expr) σ ρ ψ n :=
       match n with
       | 0 => Timeout_l
       | S n => match e_l with
               | [] => Success_l [] σ
               | e::e_l =>
                   match (⟦e⟧(σ, ρ, ψ, n)) with
                   | Success v σ' =>
                       match ⟦_ e_l _⟧(σ', ρ, ψ, n) with
                       | Success_l vl σ'' => Success_l (v::vl) σ''
                       | z => z
                       end
                   | Error => Error_l
                   | Timeout => Timeout_l
                   end
               end
       end
where  "⟦_ el _⟧ ( σ , ρ , ψ , n )" := (eval_list el σ ρ ψ n)

(** Initialization for the list of fields (when fields up to x have been initialized) *)
with init (C: ClN) (ψ : Loc) x ρ σ n : result_i :=
       match n with
       | 0 => Timeout_i
       | S n =>
           let 'class _ fields _ := ct C in
           match nth_error fields x with
               | None => if (x =? dom fields) then Success_i σ else Error_i
               | Some (field T e) =>
                   match ⟦e⟧(σ, ρ, ψ, n) with
                   | Success v σ1 =>
                       match (assign_new ψ x v σ1) with
                       | Some σ2 => init C ψ (S x) ρ σ2 n
                       | _ => Error_i
                       end
                   | Error => Error_i
                   | Timeout => Timeout_i
                   end
               end
       end.

(* The evaluation of a program is defined as the evaluation of the [main] of the Entryclass *)
Definition eval_prog n :=
  match ct Entry with
  | class nil nil Mtds =>
      match Mtds main  with
      | Some (method hot nil T e) => ⟦e⟧([(Entry, [])], [], 0, n)
      | _ => Error
      end
  | _ => Error
  end.


(* Associated tactics *)
Ltac destruct_eval He v σ' :=
  match goal with
  | H: context[ match ⟦ ?e ⟧(?σ, ?ρ, ?ψ , ?k) with _ => _ end ] |- _ =>
      destruct (⟦ e ⟧ (σ, ρ, ψ, k)) as [ | | v σ' ] eqn:He
  | H: context[ match ⟦_ ?el _⟧ (?σ, ?ρ, ?ψ, ?k) with _ => _ end ] |- _ =>
      destruct (⟦_ el _⟧ (σ, ρ, ψ, k)) as [ | | v σ' ] eqn:He
  end; try congruence.

Ltac destruct_eval_f :=
  let freshH := fresh "H" in
  let freshv := fresh "v" in
  let freshσ := fresh "σ" in
  destruct_eval freshH freshv freshσ.

(* ------------------------------------------------------------------------ *)
(** A simple result on lengths *)

Lemma EvalListLength :
  forall el n σ σ' ρ ψ vl ,
    ⟦_ el _⟧(σ, ρ, ψ, n) = Success_l vl σ' ->
    length el = length vl.
Proof.
  induction el; steps;
    destruct n; simpl; try discriminate.
  - inversion H; steps.
  - inversion H.
    destruct_eval_f ; steps.
    eapply IHel in matched1. steps.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Evaluator fuel-monotonicity *)
(* We show that adding more fuel does not changes a succeeding evaluation *)

Lemma eval_step_monotonicity_aux: forall n,
    (forall m, m > n ->
          (forall e σ ρ ψ v σ', ⟦ e ⟧ (σ, ρ, ψ, n) = Success v σ' ->
                           ⟦ e ⟧ (σ, ρ, ψ, m) = Success v σ')) /\
      (forall m, m > n ->
            (forall el σ ρ ψ vl σ', ⟦_ el _⟧ (σ, ρ, ψ, n) = Success_l vl σ' ->
                               ⟦_ el _⟧ (σ, ρ, ψ, m) = Success_l vl σ')) /\
      (forall m, m > n ->
            (forall C ψ x ρ σ σ', init C ψ x ρ σ n = Success_i σ' ->
                                  init C ψ x ρ σ m = Success_i σ')).
Proof with (try lia).
  induction n as [n IHn] using lt_wf_ind. destruct n.
  - repeat split; intros; inversion H0.
  - repeat split; intros ; destruct m...
    + (* expression *)
      destruct (IHn n) as [Hexp [Hlist Hinit]]...
      destruct e.
      * steps; eauto.
      * steps; eauto.
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
        eapply (Hinit m) in matched0...
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
      ct_lookup C.
      destruct (nth_error Flds x) as [[_ e]|]; eauto.
      destruct_eval_f.
      eapply (IHn n)  with (m := m) in H1; eauto with lia.
      steps.
      eapply (IHn n) with (m := m); eauto with lia.
Qed.

Theorem eval_step_monotonicity:
  forall n m e σ ρ ψ l σ',
    n < m ->
    ⟦ e ⟧ (σ, ρ, ψ, n) = Success l σ' ->
    ⟦ e ⟧ (σ, ρ, ψ, m) = Success l σ'.
Proof.
  intros.
  pose proof (eval_step_monotonicity_aux n) as [He _].
  eauto with lia.
Qed.

Theorem evalList_step_monotonicity:
  forall n m el σ ρ ψ vl σ',
    n < m ->
    ⟦_ el _⟧ (σ, ρ, ψ, n) = Success_l vl σ' ->
    ⟦_ el _⟧ (σ, ρ, ψ, m) = Success_l vl σ'.
Proof.
  intros.
  pose proof (eval_step_monotonicity_aux n) as [_ [Hel _]].
  eauto with lia.
Qed.

Theorem init_step_monotonicity:
  forall n m C ρ ψ x σ σ',
    n < m ->
    init C ψ x ρ σ n = Success_i σ' ->
    init C ψ x ρ σ m = Success_i σ'.
Proof with try lia.
  intros.
  pose proof (eval_step_monotonicity_aux n) as [_ [_ H__init]].
  eauto with lia.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** Equivalence *)

(* The success of the big step predicates implies the success of the eval function *)
Lemma evalP_implies_eval :
  (forall e σ ρ ψ l σ',
      ⟦ e ⟧ (σ, ρ, ψ) --> (l,σ') ->
      exists n, ⟦ e ⟧ (σ, ρ, ψ, n) = Success l σ') /\
    (forall el σ ρ ψ vl σ',
        ⟦el⟧ (σ, ρ, ψ) --> (vl, σ') ->
        exists n, ⟦_ el _⟧ (σ, ρ, ψ, n) = Success_l vl σ') /\
    (forall C ψ x ρ σ σ',
        initP C ψ x ρ σ σ' ->
        exists n, init C ψ x ρ σ n = Success_i σ').
Proof with (cross_rewrites; eauto 3 using evalP, evalListP, initP; try lia).
  apply evalP_multi_ind; intros;
    try solve [exists 1; steps];
    repeat match goal with
      | H: exists n, _ |- _ => destruct H as [?n H]
      end.
  + exists (S n); steps.
  + remember (S (max n1 (max n0 n))) as n2.
    eapply eval_step_monotonicity with (m := n2) in IH__e0, IH__e2...
    eapply evalList_step_monotonicity with (m := n2) in IH__el...
    exists (S n2). simpl; repeat rewrite_any => //.
  + remember (S (max n n0)) as n1.
    eapply evalList_step_monotonicity with (m := n1) in IH__args...
    eapply init_step_monotonicity with (m := n1) in IH__init...
    exists (S n1). simpl; subst.
    rewrite IH__args IH__init => //.
  + remember (S (max n (max n0 n1))) as n2.
    eapply eval_step_monotonicity with (m := n2) in IH__e1, IH__e2, IH__e'...
    exists (S n2). simpl. rewrite IH__e1 IH__e2 IH__e'...
  + remember (S (max n n0)) as n1.
    eapply eval_step_monotonicity with (m := n1) in IH__e...
    eapply evalList_step_monotonicity with (m := n1) in IH__el...
    exists (S n1). simpl. rewrite IH__e IH__el...
  + exists 1; simpl. rewrite H__ct.
    lets [_ ?]: nth_error_None Flds (dom Flds).
    rewrite H...
    rewrite Nat.eqb_refl...

  + remember (S (max n n0)) as n1.
    eapply eval_step_monotonicity with (m := n1) in IH__e...
    eapply init_step_monotonicity with (m := n1) in IH__init...
    exists (S n1).
    simpl in *. rewrite H__ct H__fld IH__e H__assign...
Qed.

(* Conversely, the success of the eval function implies the success of the predicate *)
Lemma eval_implies_evalP :
  forall n,
    (forall e σ ρ ψ v σ',
        ⟦ e ⟧(σ, ρ, ψ, n) = Success v σ' -> ⟦ e ⟧(σ, ρ, ψ) --> (v, σ')) /\
      (forall el σ ρ ψ vl σ',
          ⟦_ el _⟧(σ, ρ, ψ, n) = Success_l vl σ' -> ⟦ el ⟧(σ, ρ, ψ) --> (vl,σ')) /\
      (forall C ψ x ρ σ σ',
          init C ψ x ρ σ n = Success_i σ' ->
          initP C ψ x ρ σ σ').
Proof with (eauto using evalP, evalListP, initP; try lia).
  induction n as [n IHn] using lt_wf_ind.
  destruct n; repeat split => //.
  all: intros; move : (IHn n) => [ ] // => IHn__e [IHn__el IHn__init]; clear IHn.
  + simpl in H. steps...
  + steps; eauto using evalP...
  + steps; eauto using initP...
    apply Nat.eqb_eq in matched1; subst...
Qed.

(* Then the theorem : *)
Theorem evalP_eval :
  forall e σ ρ ψ l σ',
    ⟦ e ⟧p (σ, ρ, ψ) --> (l,σ') <-> exists n, ⟦ e ⟧(σ, ρ, ψ, n) = Success l σ'.
Proof.
  split; intros;
    [eapply evalP_implies_eval| inverts H; eapply eval_implies_evalP]; eauto.
Qed.

(* Specialized lemmas *)
Corollary eval_implies_evalP_expr :
  forall e σ ρ ψ l σ' n,
    ⟦ e ⟧ (σ, ρ, ψ, n) = Success l σ' -> ⟦ e ⟧(σ, ρ, ψ) --> (l,σ').
Proof.
  intros; eapply eval_implies_evalP; eauto.
Qed.

Corollary eval_implies_evalP_list :
  forall el σ ρ ψ vl σ' n,
    ⟦_ el _⟧ (σ, ρ, ψ, n) = Success_l vl σ' -> ⟦ el ⟧(σ, ρ, ψ) --> (vl,σ').
Proof.
  intros; eapply eval_implies_evalP; eauto.
Qed.

Corollary init_implies_initP :
  forall C ψ x ρ σ n σ',
    init C ψ x ρ σ n = Success_i σ' ->
    initP C ψ x ρ σ σ'.
Proof.
  intros; eapply eval_implies_evalP; eauto.
Qed.
