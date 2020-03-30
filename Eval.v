From Celsius Require Export Trees.

Require Import List.
Import ListNotations.
Open Scope nat_scope.

(*
Notation "'_(' x ',' y ')'" := (Some (Some (x, y))) (at level 20).
Notation "'Err'" := (Some None) (at level 20).
Notation "'Timeout'" := (None).
*)


Definition empty_env:Env := (fun (v: Var) => None).
Check fun l : list (Var * Tpe) => fst (split l).


Fixpoint aux (y : Var) (x: list (Var * Tpe)) (v : list Value) {struct v} :=
      match (x, v) with
       | ((y', _)::xt, v::vt) => match (Nat.eqb y y') with
                               | true  => Some v
                               | false => aux y xt vt end
       | _ => None end.
Definition list_match (x: list (Var * Tpe)) (v : list Value) : Env := fun (y : Var) => aux y x v.
Notation "x ↦ v" := (list_match x v) (at level 100).

Definition empty_store := (fun (l: Loc) => None : option Obj).
Notation "'∅'" := (empty_store) (at level 200).


Definition update {Y: Type} (x : Loc) (v : Y) (σ: Loc -> (option Y)) :=
  fun (y: Var) => if (Nat.eqb x y) then (Some v) else (σ y).
Notation  "[ x ↦ v ] σ" := (update x v σ) (at level 100, x at level 90).

Fixpoint update_list (y : Var) (x : list Var) (v : list Value) (σ: Var -> (option Value)) :=
  match (x, v) with
   | (x::xt, v::vt) => if (Nat.eqb x y) then (Some v) else update_list y xt vt σ
   | _ => (σ y) end.
Notation  "[ x ⟼ v ] σ" := (fun (y:Loc) => update_list y x v σ) (at level 100, x at level 90).


Definition assign (v0: Value) (x: Var) (v: Value) (σ: Store) : Store :=
  match (σ v0) with
    | Some (C, fields) => [v0 ↦ (C, [x ↦ v]fields)] σ
    | None => ∅
  end.

Definition assign_list (v0: Value) (x: list Var) (v: list Value) (σ: Store) : Store :=
  match (σ v0) with
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
              match (ρ x) with
              | Some v => (Success v σ)
              | _ => Error
              end )

          (* This: returns current value *)
          | this => (Success v σ) 

          (* Field access: compute object value and access field *)
          | fld e0 x => (
              match (⟦e0⟧(ct, σ, ρ, v)(n)) with
              | Success v0 σ1 =>
                match (σ1 v0) with
                | Some (c, f) =>
                  match (f x) with
                  | Some v1 => Success v1 σ1
                  | _ => Error end
                | _ => Error end
              | r => r end )

          (* Method call : compute object value, compute arguments and do the call*)
          | mtd e0 m e_l => (
              match (⟦e0⟧(ct, σ, ρ, v)(n)) with
              | Success v0 σ1 => (
                  match (σ1 v0) with
                   | Some (C, _) => (
                       match (ct C)  with
                        | Some (class _  _ methods) => (
                            match methods m with
                             | Some (method μ x _ e1) => (
                                match (⟦_ e_l _⟧(ct, σ1, ρ, v)(n)) with
                                 | Success_list args_val σ2 => let ρ1 := (x ↦ args_val) in
                                                           ⟦e1⟧(ct, σ2, ρ1, v)(n)
                                 | r => r end)
                            | _ => Error end)
                       | _ => Error end)
                   | _ => Error end)
              | r => r end)
                             
          (* New class
          | new C args => (
              match (⟦_ args _⟧(ct, σ, ρ, v)(n)) with
                | Success_list args_val σ1 => *)

          (* Field assignement *)
          | asgn e1 x e2 e' => (
              match (⟦e1⟧(ct, σ, ρ, v)(n)) with
                | Success v1 σ1 => match (⟦e2⟧(ct, σ1, ρ, v)(n)) with
                                    | Success v2 σ2 => (
                                        let σ3 := (assign v1 x v2 σ2) in
                                        ⟦e'⟧(ct, σ3, ρ, v)(n))
                                    | z => z end
                | z => z end ) 
          | _ => (Success v σ) end
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
where "'⟦_' e '_⟧' '(' ct ',' σ ',' ρ ',' v ')(' k ')'" := (eval_list e ct σ ρ v k).

