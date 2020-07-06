From Celsius Require Export Trees Tactics.
Require Import ssreflect ssrbool.

Require Import List.
Import ListNotations.
Open Scope nat_scope.

Module Evaluator.
  Parameter ct: ClassTable.

  (* Update store with new value in local env *)
  Definition assign_new (obj: Value) (v: Value) (σ: Store) : option Store :=
    match (getObj σ obj) with
    | Some (C, fields) => Some ([ obj ↦ (C, fields++[v])] σ)
    | None => None (* ? *)
    end.

  (* Update store with update in local env *)
  Definition assign (obj: Value) (f: Var) (v: Value) (σ: Store) : Store :=
    match (getObj σ obj) with
    | Some (C, fields) => ([ obj ↦ (C, [f ↦ v]fields)] σ)
    | None => σ (* ? *)
    end.

  (* Update store with new values *)
  Definition assign_list (v0: Value) (x: list Var) (v: list Value) (σ: Store) : Store :=
    match (getObj σ v0) with
    | Some (C, fields) => [v0 ↦ (C, [x ⟼ v]fields)] σ
    | None => σ
    end.

  Reserved Notation "'⟦' e '⟧' '(' σ ',' ρ ',' v ')(' k ')'"   (at level 80).
  Reserved Notation "'⟦_' e '_⟧' '(' σ ',' ρ ',' v ')(' k ')'" (at level 80).

  Fixpoint eval (e: Expr) (σ: Store) (ρ: Env) (v: Value) (k: nat) : Result :=
    match k with
    | 0 => Timeout
    | S n => match e with
            (* e = x *)
            (* Var: simple lookup of the store *)
            | var x => (
                match (getVal ρ x) with
                | Some v => (Success v σ)
                | _ => Error
                end )

            (* e = this *)
            (* This: returns current value *)
            | this => (Success v σ)

            (* e = e0.x *)
            (* Field access: compute object value and access field *)
            | fld e0 x => (
                match (⟦e0⟧(σ, ρ, v)(n)) with
                | Success v0 σ1 =>
                  match (getObj σ1 v0) with
                  | Some (c, f) =>
                    match (getVal f x) with
                    | Some v1 => Success v1 σ1
                    | _ => Error end
                  | _ => Error end
                | _ => Error end )

            (* e = e.m(el) *)
            (* Method call : compute object value, compute arguments and do the call*)
            | mtd e0 m el => (
                match (⟦e0⟧(σ, ρ, v)(n)) with
                | Success v0 σ1 => (
                    match (getObj σ1 v0) with
                    | Some (C, _) => (
                        match (ct C)  with
                        | Some (class _  _ methods) => (
                            match methods m with
                            | Some (method μ x _ e1) => (
                                match (⟦_ el _⟧(σ1, ρ, v)(n)) with
                                | Success_list args_val σ2 =>
                                  let ρ1 := args_val in ⟦e1⟧(σ2, ρ1, v)(n)
                                | _ => Error end)
                            | _ => Error end)
                        | _ => Error end)
                    | _ => Error end)
                | _ => Error end)

            (* e = new C(args) *)
            (* New class *)
            | new C args => (
                match (⟦_ args _⟧(σ, ρ, v)(n)) with
                | Success_list args_val σ1 => (
                    let I := (length σ1) in (* Fresh location for new object *)
                    let ρ_init := args_val in (* Local env during initialisation *)
                    let σ2 := σ1 ++ [(C, ∅)] in (* New object with empty local env *)
                      match (init I ρ_init C σ2 n) with
                      | Some σ3 => (Success I σ3) (* Returns new object and updated store *)
                      | None => Error end )
                | _ => Error end) (* Invalid args *)

            (* e = (e1.x ← e2 ; e') *)
            (* Field assignement *)
            | asgn e1 x e2 e' => (
                match (⟦e1⟧(σ, ρ, v)(n)) with
                | Success v1 σ1 => match (⟦e2⟧(σ1, ρ, v)(n)) with
                                  | Success v2 σ2 => (
                                      let σ3 := (assign v1 x v2 σ2) in
                                      ⟦e'⟧(σ3, ρ, v)(n))
                                  | _ => Error end
                | _ => Error end )
            end
    end
  where "'⟦' e '⟧' '(' σ ',' ρ ',' v ')(' k ')'"  := (eval e σ ρ v k)
  with eval_list (e_l: list Expr) (σ: Store) (ρ: Env) (v: Value) (k: nat) :  Result :=
         match k with
         | 0 => Timeout
         | S n => fold_left (eval_list_aux σ ρ v n) e_l (Success_list [] σ) end
  where  "'⟦_' e '_⟧' '(' σ ',' ρ ',' v ')(' k ')'" := (eval_list e σ ρ v k)
  with eval_list_aux (σ: Store) (ρ: Env) (v: Value) (k: nat) (acc: Result) (e: Expr) :=
         match k with
         | 0 => Timeout
         | S n => match acc with
                 | Success_list vs σ1 => match (⟦e⟧(σ1, ρ, v)(n)) with
                                        | Success v σ2 => Success_list (v::vs) σ2
                                        | z => z end
                 | z => z end end
  with init (I : Var) (args_values: list Var) (C: ClN) (σ: Store) (k :nat) : option Store :=
         match k with | 0 => None | S n =>
           match (ct C) with
           | Some (class x F M) => (fold_left (init_field args_values I n) F (Some σ))
           | None => None
           end
         end
  with init_field (args_values: list Var) (this: Var) (k: nat) (σ_opt: option Store)  (f: Field): option Store :=
         match k with | 0 => None | S n =>
         match σ_opt with
         | None => None
         | Some σ => ( match f with
         | field t e => (
            match (⟦e⟧(σ, args_values, this)(n)) with
            | Success v1 σ1 => (assign_new this v1 σ1)
            | _ => None
            end) end) end end.



  Lemma eval_not_success_list: forall  (k: nat) (e: Expr) (σ σ': Store) (ρ: Env) (v: Value) (l: list Value),
      not (⟦e⟧(σ, ρ, v)(k) = Success_list l σ').
    induction k; repeat light || eauto || destruct_match. Qed.

  Ltac eval_not_success_list :=
    match goal with
    | H:⟦?e⟧(?σ, ?ρ, ?v)(?k) = Success_list ?l ?σ' |- _ => apply eval_not_success_list in H => //
    end.

  Lemma foldLeft_constant : forall (A B: Type) (l: list B) (res: A) (f : A -> B -> A),
      (forall (y:B), f res y = res) -> fold_left f l res = res.
    intros.
    induction l => //.
    simpl. rewrite H. apply IHl.
  Qed.

  Lemma eval_list_prop : forall (P: Store -> Store -> Prop) n,
      (forall σ, P σ σ) -> (* reflexivity *)
      (forall σ1 σ2 σ3, P σ1 σ2 -> P σ2 σ3 -> P σ1 σ3) -> (* transitivity *)
      (forall k, (k < n) -> forall e σ σ' ρ v v',  ⟦e⟧(σ, ρ, v)(k) = (Success v' σ') -> (P σ σ')) -> (* Strong induction *)
      (forall k, (k < n) -> forall l σ σ' ρ v v_list,  ⟦_ l _⟧(σ, ρ, v)(k) = (Success_list v_list σ') -> (P σ σ')).
    intros P n H_refl H_trans H_strong.
    destruct k; simpl; try discriminate.
    assert (forall (l : list Expr) (σ σ' : Store) (ρ : Env) (v : Value) (v_list1 v_list2 : list Value),
               (k < n) -> fold_left (eval_list_aux σ ρ v k) l (Success_list v_list1 σ) = Success_list v_list2 σ' -> P σ σ') as H_fold . {
      induction l as [| e l]; simpl; intros.
      + invert_constructor_equalities; eauto.
      + destruct k; simpl in H0. rewrite foldLeft_constant in H0 => //.
        move /(_ _ _ _ _ _ _ H):IHl => IHl.
        move /(_ _ (PeanoNat.Nat.lt_succ_l k n H)):H_strong => H_strong.
        destruct (⟦ e ⟧ (σ, ρ, v )( k)) eqn: E; try solve [ rewrite foldLeft_constant in H0 => //] ; eauto; try eval_not_success_list.
    }
    intros.
    eapply H_fold; eauto using PeanoNat.Nat.lt_succ_l .
  Qed.


  End Evaluator.
