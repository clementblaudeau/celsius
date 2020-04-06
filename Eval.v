From Celsius Require Export Trees.

Require Import List.
Import ListNotations.
Open Scope nat_scope.

Check fold_left.

Definition assign (v0: Value) (x: Var) (v: Value) (σ: Store) : Store :=
  match (getObj σ v0) with
    | Some (C, fields) => [ v0 ↦ (C, [x ↦ v]fields)] σ
    | None => ∅ (* ? *)
  end.

Definition assign_list (v0: Value) (x: list Var) (v: list Value) (σ: Store) : Store :=
  match (getObj σ v0) with
    | Some (C, fields) => [v0 ↦ (C, [x ⟼ v]fields)] σ
    | None => ∅
  end.

Reserved Notation "'⟦' e '⟧' '(' ct ',' σ ',' ρ ',' v ')(' k ')'" (at level 200).
Reserved Notation "'⟦_' e '_⟧' '(' ct ',' σ ',' ρ ',' v ')(' k ')'" (at level 200).

Fixpoint eval (e: Expr) (ct: ClassTable) (σ: Store) (ρ: Env) (v: Value) (k: nat) : Result :=
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
              match (⟦e0⟧(ct, σ, ρ, v)(n)) with
              | Success v0 σ1 =>
                match (getObj σ1 v0) with
                | Some (c, f) =>
                  match (getVal f x) with
                  | Some v1 => Success v1 σ1
                  | _ => Error end
                | _ => Error end
              | r => r end )

          (* Method call : compute object value, compute arguments and do the call*)
          | mtd e0 m e_l => (
              match (⟦e0⟧(ct, σ, ρ, v)(n)) with
              | Success v0 σ1 => (
                  match (getObj σ1 v0) with
                   | Some (C, _) => (
                       match (ct C)  with
                        | Some (class _  _ methods) => (
                            match methods m with
                             | Some (method μ x _ e1) => (
                                match (⟦_ e_l _⟧(ct, σ1, ρ, v)(n)) with
                                 | Success_list args_val σ2 => let ρ1 := [(removeTypes x) ⟼ args_val]∅ in
                                                           ⟦e1⟧(ct, σ2, ρ1, v)(n)
                                 | r => r end)
                            | _ => Error end)
                       | _ => Error end)
                   | _ => Error end)
              | r => r end)
                             
          (* New class *)
          | new C args => (
              match (⟦_ args _⟧(ct, σ, ρ, v)(n)) with
                | Success_list args_val σ1 => (
                    let I := (length σ1) + 1 in
                    let σ2 := [I ↦ (C, ∅)] σ1 in
                    let σ3 := (init I args_val C ct σ2 n) in
                    (Success I σ3))
                | _ => Error end) (* Unknown class *) 

          (* Field assignement *)
          | asgn e1 x e2 e' => (
              match (⟦e1⟧(ct, σ, ρ, v)(n)) with
                | Success v1 σ1 => match (⟦e2⟧(ct, σ1, ρ, v)(n)) with
                                    | Success v2 σ2 => (
                                        let σ3 := (assign v1 x v2 σ2) in
                                        ⟦e'⟧(ct, σ3, ρ, v)(n))
                                    | z => z end
                | z => z end ) 
          end
  end
where "'⟦' e '⟧' '(' ct ',' σ ',' ρ ',' v ')(' k ')'" := (eval e ct σ ρ v k)
with eval_list (e_l: list Expr) (ct: ClassTable) (σ: Store) (ρ: Env) (v: Value) (k: nat) :  Result :=
   match k with
     | 0 => Timeout
     | S n => fold_left (fun (acc: Result) (e: Expr) =>
                          match acc with
                            | Success_list vs σ1 => match (⟦e⟧(ct, σ1, ρ, v)(n)) with
                                                     | Success v σ2 => Success_list (v::vs) σ2
                                                     | z => z end
                            | z => z end )
                       e_l (Success_list [] σ) end
where "'⟦_' e '_⟧' '(' ct ',' σ ',' ρ ',' v ')(' k ')'" := (eval_list e ct σ ρ v k)
with init (I : Var) (v : list Var) (C: ClN) (ct: ClassTable) (σ: Store) (k :nat) : Store :=
   match k with
     | 0 => ∅
     | S n =>
       match (ct C) with
         | Some (class x F M) => (
             let σ1 := (assign_list I (removeTypes x) v σ) in
             let f  := (fun (σ: Store) (f: Field) => match f with
                          |field x t e => (
                             match (⟦e⟧(ct, σ, ∅, I)(n)) with
                               | Success v1 σ1 => (assign I x v1 σ1)
                               | _ => ∅ end) end) in
             (fold_left f F σ)) 
         | None => ∅
       end
   end.

