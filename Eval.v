From Celsius Require Export Trees Tactics.
Require Import ssreflect ssrbool.
Require Import Celsius.strongInduction.

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
                                  let ρ1 := args_val in ⟦e1⟧(σ2, ρ1, v0)(n)
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
         | S n => fold_left (eval_list_aux ρ v n) e_l (Success_list [] σ) end
  where  "'⟦_' e '_⟧' '(' σ ',' ρ ',' v ')(' k ')'" := (eval_list e σ ρ v k)
  with eval_list_aux (ρ: Env) (v: Value) (k: nat) (acc: Result) (e: Expr) :=
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


  Definition Reflexive (P: Store -> Store -> Prop) : Prop := (forall σ, P σ σ).
  Definition Transitive (P: Store -> Store -> Prop)  : Prop := forall (σ1 σ2 σ3: Store), P σ1 σ2 ->  P σ2 σ3 ->  P σ1 σ3.
  Definition Assignment (P: Store -> Store -> Prop)  : Prop := forall σ σ' l C ω ω',
          getObj σ l = Some (C, ω) ->
          length ω <= length ω' ->
          σ' = [l ↦ (C, ω')]σ -> P σ σ'.
  Definition Freshness (P: Store -> Store -> Prop) : Prop := forall s c ω, P s (s ++ [(c, ω)]).


  Definition EvalMaintained (P: Store -> Store -> Prop)  k : Prop := forall e σ σ' ρ v v',  ⟦e⟧(σ, ρ, v)(k) = (Success v' σ') -> (P σ σ') .

  Definition InitMaintained (P: Store -> Store -> Prop) (n:nat) : Prop :=
    (forall (k: nat), (k < n) -> EvalMaintained P k) ->
    (forall (k: nat), (k < n) ->
               forall (l0: list Var) (s σ': Store) (c: ClN),
                 init (length s) l0 c (s ++ [(c, [])]) k = Some σ' -> P s σ').




  Lemma eval_list_prop : forall (P: Store -> Store -> Prop) n,
      Reflexive P -> Transitive P -> (forall k, (k < n) -> EvalMaintained P k) ->
      (forall k, (k < n) -> forall l σ σ' ρ v v_list,  ⟦_ l _⟧(σ, ρ, v)(k) = (Success_list v_list σ') -> (P σ σ')).
    intros P n H_refl H_trans H_strong.
    destruct k; simpl; try discriminate.
    assert (forall (l : list Expr) (σ σ' : Store) (ρ : Env) (v : Value) (v_list1 v_list2 : list Value),
               (k < n) -> fold_left (eval_list_aux ρ v k) l (Success_list v_list1 σ) = Success_list v_list2 σ' -> P σ σ') as H_fold . {
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

  Lemma freshnessInitMaintained : forall (P: Store -> Store -> Prop) n,
      Reflexive P -> Transitive P -> Assignment P -> Freshness P -> InitMaintained P n.
    Proof.
      intros P n H_refl H_trans H_asgn H_fresh H_strong.
      assert ( forall k : nat,
  k < n ->
  forall (l0 : list Var) (σ σ' : Store) (c : ClN) I , init I l0 c σ k = Some σ' -> P σ σ'). {
    destruct k; simpl; try discriminate.
    intros Hn; intros.
    repeat destruct_match; try discriminate. clear matched0. clear matched.
    generalize dependent σ. generalize dependent σ'.
      induction fields as [| [x e] fields]; simpl; intros.
      + invert_constructor_equalities; eauto.
      + destruct k; simpl in H. rewrite foldLeft_constant in H => //.
        destruct ((⟦ e ⟧ (σ, l0, I )( k))) eqn:E ; try solve [ rewrite foldLeft_constant in H => //] ; eauto; try eval_not_success_list.
        unfold assign_new in H.
        repeat destruct_match; try solve [rewrite foldLeft_constant in H => //].
        subst.
        move /(_ _ _ H):IHfields => IHfields.
        apply PeanoNat.Nat.lt_succ_l in Hn.
        apply PeanoNat.Nat.lt_succ_l in Hn.
        move /(_ k Hn _ _ _ _ _ _ E):H_strong => H_strong.
        apply (H_trans _ _ _ H_strong).
        apply (H_trans _  [I ↦ (c1, e0 ++ [v])] (s)  _ ) => //.
        apply (H_asgn _ _ _ _ _ (e0 ++ [v])  matched); eauto using app_length.
        rewrite app_length.
        rewrite PeanoNat.Nat.add_1_r. eauto.
      } eauto.
    Qed.

    Lemma eval_prop : forall (P: Store -> Store -> Prop),
        Reflexive P -> Transitive P ->  Assignment P -> (forall n, InitMaintained P n) -> forall n, EvalMaintained P n.
      intros P H_refl H_trans  H_asgn H_init.
      apply strong_induction.
      unfold EvalMaintained.
      intros n H_strong.
      move /(_ n H_strong):H_init => H_init.
    (* To get one step of the evaluator, we destruct n *)
    destruct n => //. (* n = 0 is discarded automatically *)
    (* n > 0 - case analysis over e *)
    move : (PeanoNat.Nat.lt_succ_diag_r n) => Hn.
    destruct e;
      (* Trivial cases are handled automatically *)
      repeat light || invert_constructor_equalities || destruct_match || eauto 3.
    - (* case e = e0.m(ē) *)
      apply (iff_sym (PeanoNat.Nat.le_succ_l n (S n))) in Hn.
      pose proof (eval_list_prop P (S n) H_refl H_trans H_strong n Hn _ _ _ _ _ _ matched3); eauto.
    - (* case e = new C(l) *)
      apply (iff_sym (PeanoNat.Nat.le_succ_l n (S n))) in Hn.
      move /(_ n Hn l0 s σ' c matched0):H_init => H_init.
      pose proof (eval_list_prop P (S n) H_refl H_trans H_strong n Hn _ _ _ _ _ _ matched).
      eauto.
    - (* case e1.v0 = e2 ; e3 *)
      apply (H_trans σ s σ'); eauto.
      apply (H_strong n Hn _ _ _ _ _ _ ) in matched0.
      apply (H_trans s _ _ matched0).
      apply (H_strong n Hn _ _ _ _ _ _ ) in H.
      apply (H_trans s0 (assign v1 v v2 s0) σ') => //.
      unfold assign. repeat destruct_match; eauto using PeanoNat.Nat.eq_le_incl, update_one3.
    Qed.

    Lemma eval_list_length : forall n el σ σ' ρ ψ l ,
        ⟦_ el _⟧(σ, ρ, ψ)(n) = Success_list l σ' ->
        length el = length l.
    Proof.
      intros n.
      destruct n; simpl; try discriminate.
      assert
        (forall (l : list Expr) (σ σ' : Store) (ρ : Env) (v : Value) (v_list1 v_list2 : list Value),
            fold_left (eval_list_aux ρ v n) l (Success_list v_list1 σ) = Success_list v_list2 σ'
            -> length l + length v_list1 = length v_list2) as H_fold. {
        induction l as [| e l] ; steps.
        destruct n; simpl in H. rewrite foldLeft_constant in H => //.
        destruct (⟦ e ⟧ (σ, ρ, v )( n)) eqn: E;
          try solve [ rewrite foldLeft_constant in H => //] ;
          eauto; try eval_not_success_list.
        apply IHl in H.
        simpl in H.
        rewrite plus_n_Sm => //. }
      intros.
      pose proof (H_fold _ _ _ _ _ _ _ H); simpl in H0.
      rewrite PeanoNat.Nat.add_0_r in H0 => //.
    Qed.

(*
    Lemma eval_list_prop2 : forall (P: Store -> Store -> Env ->Loc -> Loc -> Prop) n,
      (* (forall s v1 v2 ρ, P s s ρ v1 v2) -> *)
      (forall k, (k < n) -> forall e  σ σ' ρ ψ v, ⟦e⟧(σ, ρ, ψ)(k) = Success v σ' -> P σ σ' ρ ψ v) ->
      (forall k, (k < n) -> forall el σ σ' ρ ψ v2 vl1 vl2,
           ⟦e⟧(σ', ρ, ψ)(k) = Success v σ' ->
           fold_left (eval_list_aux ρ ψ k) el (Success_list (vl1) σ) = Success_list (v2::vl2) σ' -> P σ σ' ρ ψ v2).
      intros P n H_strong k Hk.
      induction el as [| e el].
      + simpl; intros.
        invert_constructor_equalities; subst; eauto.
      + intros. simpl in H.
        set (eval_list_aux ρ ψ k) as f.
        rewrite -{1}/f in H. rewrite -/f in IHel.
        destruct k; simpl in H; try solve [rewrite foldLeft_constant in H => //].
        destruct ( ⟦ e ⟧ (σ, ρ, ψ )( k) ) eqn:E; try solve [rewrite foldLeft_constant in H => //]; eauto; try eval_not_success_list.
        apply H_strong in E; eauto using PeanoNat.Nat.lt_succ_l.




    intros P n H_refl H_strong k Hk. intros.
    destruct k; simpl; try discriminate.
    assert (forall  (el : list Expr) (σ σ' : Store) (ρ : Env) (ψ v : Value) (v_list1 v_list2 : list Value),
               (k < n) -> fold_left (eval_list_aux σ ρ ψ k) el (Success_list v_list1 σ) = Success_list (v::v_list2) σ' -> P σ σ' v) as H_fold . {
      induction el0 as [| e1 el0]; simpl; intros.
      + invert_constructor_equalities; eauto.
      + destruct k; simpl in H1. rewrite foldLeft_constant in H1 => //.
        move /(_ _ _ _ _ _ _ _ H0):IHel0 => IHel0.
        move /(_ _ (PeanoNat.Nat.lt_succ_l k n H0)):H_strong => H_strong.
        destruct (⟦ e1 ⟧ (σ0, ρ0, ψ0 )( k)) eqn: E; try solve [ rewrite foldLeft_constant in H1 => //] ; eauto; try eval_not_success_list.
        pose proof (IHel0 σ σ0 ρ ψ0 v0 (v1::v_list1) v_list2 H1).
    }
    intros.
    eapply H_fold; eauto using PeanoNat.Nat.lt_succ_l .
  Qed.
*)








  End Evaluator.
