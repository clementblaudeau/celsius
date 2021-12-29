(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the evaluator as a predicate and shows the equivalence with the functional version *)

From Celsius Require Export Trees LibTactics.
Require Import ssreflect ssrbool.
Require Import List Psatz Arith.
Import ListNotations.
Open Scope nat_scope.

Reserved Notation "'⟦'  e  '⟧p' '(' σ ',' ρ ',' v ')'  '-->'  '(' v0 ',' σ0 ')'" (at level 80).
Reserved Notation "'⟦_' e '_⟧p' '(' σ ',' ρ ',' v ')'  '-->'  '(' vl ',' σl ')'" (at level 80).

Inductive evalP : Expr -> Store -> Env -> Value -> Value -> Store -> Prop :=
| e_var : forall σ x ρ ψ l,
    getVal ρ x = Some l ->
    ⟦ var x ⟧p (σ, ρ, ψ) --> (l, σ)
| e_this : forall σ ρ ψ,
    ⟦ this ⟧p (σ, ρ, ψ) --> (ψ, σ)
| e_fld : forall σ ρ ψ e0 x l1 σ1 C f v1,
    ⟦ e0 ⟧p (σ, ρ, ψ) --> (l1, σ1) ->
    getObj σ1 l1 = Some (C, f) ->
    getVal f x = Some v1 ->
    ⟦ (fld e0 x) ⟧p (σ, ρ, ψ) --> (v1, σ1)
| e_mtd : forall σ e0 m el e2 ρ ψ l1 vl2 l3 σ1 σ2 σ3 C f argsC argsM fields methods T μ,
    ⟦ e0 ⟧p (σ, ρ, ψ) --> (l1, σ1) ->
    getObj σ1 l1 = Some (C, f) ->
    ct C = Some (class argsC fields methods) ->
    methods m = Some (method μ argsM T e2) ->
    ⟦_ el _⟧p (σ1, ρ, ψ) --> (vl2, σ2) ->
    ⟦ e2 ⟧p (σ2, vl2, l1) --> (l3, σ3) ->
    ⟦ mtd e0 m el ⟧p (σ, ρ, ψ) --> (l3, σ3)
| e_new : forall σ ρ ψ C args vl__args σ1 σ3 Tps Flds Mtds,
    ⟦_ args _⟧p (σ, ρ, ψ) --> (vl__args, σ1) ->
    ct C = Some (class Tps Flds Mtds) ->
    let I := (length σ1) in
    initP Flds I vl__args (σ1 ++ [(C, [])]) σ3 ->
    ⟦ new C args ⟧p (σ, ρ, ψ) --> (I, σ3)
| e_asgn : forall σ ρ ψ e1 x e2 e' σ1 v1 σ2 v2 σ3 v3,
    ⟦ e1 ⟧p (σ, ρ, ψ) --> (v1, σ1) ->
    ⟦ e2 ⟧p (σ1, ρ, ψ) --> (v2, σ2) ->
    ⟦ e' ⟧p ((assign v1 x v2 σ2), ρ, ψ) --> (v3, σ3) ->
    ⟦ asgn e1 x e2 e' ⟧p (σ, ρ, ψ) --> (v3, σ3)

where "'⟦' e '⟧p' '(' σ ',' ρ ',' v ')' '-->' '(' v0 ',' σ0 ')' "  := (evalP e σ ρ v v0 σ0)

with evalListP : list Expr -> Store -> Env -> Value -> list Value -> Store -> Prop :=
| el_nil : forall σ ρ ψ,
    ⟦_ [] _⟧p (σ, ρ, ψ) --> ([], σ)
| el_cons : forall σ ρ ψ e el l1 σ1 vl σ2,
    ⟦ e ⟧p (σ, ρ, ψ) --> (l1, σ1) ->
    ⟦_ el _⟧p (σ1, ρ, ψ) --> (vl, σ2) ->
    ⟦_ (e::el) _⟧p (σ, ρ, ψ) --> (l1::vl, σ2)
where "'⟦_' el '_⟧p' '(' σ ',' ρ ',' v ')' '-->' '(' vl ',' σ0 ')' "  := (evalListP el σ ρ v vl σ0)

with initP : list Field -> Var -> Env -> Store -> Store -> Prop :=
| init_nil : forall I ρ σ,
    initP [] I ρ σ σ
| init_cons : forall I ρ σ v T e flds σ1 σ2 σ3,
    ⟦ e ⟧p (σ, ρ, I) --> (v, σ1) ->
    assign_new I v σ1 = Some σ2 ->
    initP flds I ρ σ2 σ3 ->
    initP (field T e :: flds) I ρ σ σ3.

Section evalP_ind.
  Variable P : forall e σ ρ ψ v σ', (evalP e σ ρ ψ v σ') -> Prop.
  Variable Pl : forall el σ ρ ψ vl σ', (evalListP el σ ρ ψ vl σ') -> Prop.
  Variable Pin : forall flds ψ ρ σ σ', (initP flds ψ ρ σ σ') -> Prop.

  Variable P_var : forall σ x ρ ψ l Hget,
      P (var x) σ ρ ψ l σ (e_var σ x ρ ψ l Hget).

  Variable P_this : forall σ ρ ψ,
      P this σ ρ ψ ψ σ (e_this σ ρ ψ).

  Variable P_fld : forall σ ρ ψ e0 x l1 σ1 C f v1 H__e0 Hobj Hval,
    P e0 σ ρ ψ l1 σ1 (H__e0) ->
    P (fld e0 x) σ ρ ψ v1 σ1 (e_fld σ ρ ψ e0 x l1 σ1 C f v1 H__e0 Hobj Hval).

  Variable P_mtd : forall σ e0 m el e2 ρ ψ v1 vl2 v3 σ1 σ2 σ3 C f argsC argsM fields methods T μ H__e0 Hobj Hct Hmth H__el H__e2,
    P e0 σ ρ ψ v1 σ1 H__e0 ->
    Pl el σ1 ρ ψ vl2 σ2 H__el ->
    P e2 σ2 vl2 v1 v3 σ3 H__e2 ->
    P( mtd e0 m el) σ ρ ψ v3 σ3 (e_mtd σ e0 m el e2 ρ ψ v1 vl2 v3 σ1 σ2 σ3 C f argsC argsM fields methods T μ H__e0 Hobj Hct Hmth H__el H__e2).

  Variable P_new : forall σ ρ ψ C args vl__args σ1 σ3 Tps Flds Mtds H__args H__ct H__init,
    Pl args σ ρ ψ vl__args σ1 H__args ->
    Pin Flds (length σ1) vl__args (σ1 ++ [(C, [])]) σ3 H__init ->
    P (new C args) σ ρ ψ (length σ1) σ3 (e_new σ ρ ψ C args vl__args σ1 σ3 Tps Flds Mtds H__args H__ct H__init).

  Variable P_asgn :  forall σ ρ ψ e1 x e2 e' σ1 v1 σ2 v2 σ3 v3 H__e1 H__e2 H__e',
    P e1 σ ρ ψ v1 σ1 H__e1 ->
    P e2 σ1 ρ ψ v2 σ2 H__e2 ->
    P e' (assign v1 x v2 σ2) ρ ψ v3 σ3 H__e' ->
    P (asgn e1 x e2 e') σ ρ ψ v3 σ3 (e_asgn σ ρ ψ e1 x e2 e' σ1 v1 σ2 v2 σ3 v3 H__e1 H__e2 H__e').

  Variable Pl_nil : forall σ ρ ψ, Pl [] σ ρ ψ [] σ (el_nil σ ρ ψ).

  Variable Pl_cons : forall σ ρ ψ e el v1 σ1 vl σ2 H__e H__el,
      P e σ ρ ψ v1 σ1 H__e ->
      Pl el σ1 ρ ψ vl σ2 H__el ->
      Pl (e::el) σ ρ ψ (v1::vl) σ2 (el_cons σ ρ ψ e el v1 σ1 vl σ2 H__e H__el).

  Variable Pin_nil: forall I (ρ: Env) (σ: Store), Pin [] I ρ σ σ (init_nil I ρ σ).

  Variable Pin_cons : forall I ρ σ v T e flds σ1 σ2 σ3 H__e H__assign H__flds,
      P e σ ρ I v σ1 H__e ->
      Pin flds I ρ σ2 σ3 H__flds ->
      Pin (field T e :: flds) I ρ σ σ3 (init_cons I ρ σ v T e flds σ1 σ2 σ3 H__e H__assign H__flds).

  Variable Pin_magic : forall flds ψ ρ σ σ' H__init, Pin flds ψ ρ σ σ' H__init.

  Fixpoint evalP_ind2 e σ ρ ψ v σ' (eval : evalP e σ ρ ψ v σ') : P e σ ρ ψ v σ' eval :=
    match eval with
    | e_var σ x ρ ψ v Hget => P_var σ x ρ ψ v Hget
    | e_this σ ρ ψ => P_this σ ρ ψ
    | e_fld σ ρ ψ e0 x l1 σ1 C f v1 H__e0 Hobj Hval =>
        P_fld σ ρ ψ e0 x l1 σ1 C f v1 H__e0 Hobj Hval (evalP_ind2 e0 σ ρ ψ l1 σ1 H__e0)
    | e_mtd σ e0 m el e2 ρ ψ l1 vl2 l3 σ1 σ2 σ3 C f argsC argsM fields methods T μ H__e0 Hobj Hct Hmth H__el H__e2 =>
        P_mtd σ e0 m el e2 ρ ψ l1 vl2 l3 σ1 σ2 σ3 C f argsC argsM fields methods T μ H__e0 Hobj Hct Hmth H__el H__e2
              (evalP_ind2 e0 σ ρ ψ l1 σ1 H__e0)
              (evalListP_ind2 el σ1 ρ ψ vl2 σ2 H__el)
              (evalP_ind2 e2 σ2 vl2 l1 l3 σ3 H__e2)
    | e_new σ ρ ψ C args vl__args σ1 σ3 Tps Flds Mtds H__args H__ct H__init =>
        P_new σ ρ ψ C args vl__args σ1 σ3 Tps Flds Mtds H__args H__ct H__init
              (evalListP_ind2 args σ ρ ψ vl__args σ1 H__args)
              (initP_ind2 Flds (length σ1) vl__args (σ1 ++ [(C, [])]) σ3 H__init )
    | e_asgn σ ρ ψ e1 x e2 e' σ1 v1 σ2 v2 σ3 v3 H__e1 H__e2 H__e' =>
        P_asgn σ ρ ψ e1 x e2 e' σ1 v1 σ2 v2 σ3 v3 H__e1 H__e2 H__e'
               (evalP_ind2 e1 σ ρ ψ v1 σ1 H__e1)
               (evalP_ind2 e2 σ1 ρ ψ v2 σ2 H__e2)
               (evalP_ind2 e' (assign v1 x v2 σ2) ρ ψ v3 σ3 H__e')
    end

  with evalListP_ind2 el σ ρ ψ vl σ' evalList : Pl el σ ρ ψ vl σ' evalList :=
         match evalList  with
         | el_nil σ ρ ψ  => Pl_nil σ ρ ψ
         | el_cons σ ρ ψ e el l1 σ1 vl σ2 H__e H__el =>
             Pl_cons σ ρ ψ e el l1 σ1 vl σ2 H__e H__el
                     (evalP_ind2 e σ ρ ψ l1 σ1 H__e)
                     (evalListP_ind2 el σ1 ρ ψ vl σ2 H__el)
         end

  with initP_ind2 flds ψ (ρ:Env) (σ σ':Store) H__init : Pin flds ψ ρ σ σ' H__init :=
         match H__init with
         | init_nil ψ ρ σ => Pin_nil ψ ρ σ
         | init_cons ψ ρ σ v T e flds σ1 σ2 σ3 H__e H__assign H__flds =>
                       Pin_cons ψ ρ σ v T e flds σ1 σ2 σ3 H__e H__assign H__flds
                                (evalP_ind2 e σ ρ ψ v σ1 H__e)
                                (initP_ind2 flds ψ ρ σ2 σ3 H__flds)
         end.


End evalP_ind.

Check evalP_ind2.
