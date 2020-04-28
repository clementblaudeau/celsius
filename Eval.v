From Celsius Require Export Trees.
Require Import ssreflect ssrbool.

Require Import List.
Import ListNotations.
Open Scope nat_scope.

Module Evaluator.
  Parameter ct: ClassTable.
  
  Definition assign (v0: Value) (x: Var) (v: Value) (σ: Store) : Store :=
    match (getObj σ v0) with
    | Some (C, fields) => [ v0 ↦ (C, [x ↦ v]fields)] σ
    | None => σ (* ? *)
    end.

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
            (* Var: simple lookup of the store *)
            | var x => (
                match (getVal ρ x) with
                | Some v => (Success v σ)
                | _ => Error
                end )

            (* This: returns current value *)
            | this => (Success v σ) 

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
                                | Success_list args_val σ2 => let ρ1 := [(removeTypes x) ⟼ args_val]∅ in
                                                             ⟦e1⟧(σ2, ρ1, v)(n)
                                | _ => Error end)
                            | _ => Error end)
                        | _ => Error end)
                    | _ => Error end)
                | _ => Error end)
                               
            (* New class *)
            | new C args => (
                match (⟦_ args _⟧(σ, ρ, v)(n)) with
                | Success_list args_val σ1 => (
                    let I := (length σ1) + 1 in
                    let σ2 := [I ↦ (C, ∅)] σ1 in (
                      match (init I args_val C σ2 n) with
                      | Some σ3 => (Success I σ3)
                      | None => Error end ))
                | _ => Error end) (* Unknown class *) 

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
  with init (I : Var) (v : list Var) (C: ClN) (σ: Store) (k :nat) : option Store :=
         match k with
         | 0 => None
         | S n =>
           match (ct C) with
           | Some (class x F M) => (
               let σ1 := (assign_list I (removeTypes x) v σ) in
               let f  := (fun (σ: Store) (f: Field) => match f with
                                                    |field x t e => (
                                                       match (⟦e⟧(σ, ∅, I)(n)) with
                                                       | Success v1 σ1 => (assign I x v1 σ1)
                                                       | _ => σ (* In case or error, we keep σ to help for some proofs *)
                                                       end) end) in
               Some (fold_left f F σ)) 
           | None => None
           end
         end.



  Lemma eval_not_success_list: forall  (k: nat) (e: Expr) (σ σ': Store) (ρ: Env) (v: Value) (l: list Value),
      not (⟦e⟧(σ, ρ, v)(k) = Success_list l σ').
    induction k => //.
    intros.
    destruct e => //.
    - simpl.
      destruct (getVal ρ v0) => //.
    - simpl.
      destruct (⟦ e ⟧ (σ, ρ, v )( k)) => //.
      destruct (getObj s v1) => //.
      destruct o => //.
      destruct (getVal e0 v0) => //.
    - simpl.
      destruct (⟦ e ⟧ (σ, ρ, v )( k)) => //.
      destruct (getObj s v0) => //.
      destruct o => //.
      destruct (ct c) => //.
      destruct c0 => //.
      destruct (methods m) => //.
      destruct m0 => //.
      destruct (⟦_ l0 _⟧ ( s, ρ, v )( k)) => //.
    - simpl.
      destruct (⟦_ l0 _⟧ (σ, ρ, v )( k)) => //.
      destruct (init (length s + 1) l1 c [length s + 1 ↦ (c, [])] (s) k) => //.
    - simpl.
      destruct (⟦ e1 ⟧ (σ, ρ, v )( k)) => //.
      destruct (⟦ e2 ⟧ (s, ρ, v )( k)) => //.
  Qed.


  (*
  Lemma eval_preserves_types: forall (k: nat) (e: Expr) (σ σ': Store) (ρ ω ω': Env) (v v': Value) (l: Loc) (C C': ClN),
      (⟦e⟧(σ, ρ, v)(k) = Success v' σ') ->
      (getObj σ l) = Some (C, ω) ->
      (getObj σ' l) = Some (C', ω') -> C=C'.
    induction k => //.
    destruct e; simpl ; intros.
    - destruct (getVal ρ v) => //.
      injection H => H2 H3.
      rewrite -H2 in H1.
      rewrite H0 in H1.
      injection H1  => //.
    - injection H => H2 H3.
      rewrite -H2 in H1.
      rewrite H0 in H1.
      injection H1  => //.
    - destruct (⟦ e ⟧ (σ, ρ, v0 )( k)) eqn:E => //.
      destruct (getObj s v1) eqn:S => //.
      destruct o => //.
      destruct (getVal e0 v) => //.
      injection H => H2 H3.
      rewrite -H2 in H1.
      apply : (IHk e σ s ρ ω ω' v0 v1 l C C' E H0 H1).
    -  Admitted.      
*)      
    
      
  

  End Evaluator.
