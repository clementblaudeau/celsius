(* Celsius project *)
(* Clément Blaudeau - LAMP@EPFL 2021 *)
(** This file defines the evaluator as a predicate and shows the equivalence with the functional version *)

From Celsius Require Export Eval LibTactics.
Require Import ssreflect ssrbool.
Require Import List Psatz Arith.
Import ListNotations.
Open Scope nat_scope.

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
      * inversion H0; repeat destruct_match => //; sort.
        rewrite_any.
        eapply (Hexp m) in matched, H2...
        eapply (Hlist m) in matched6...
        steps.
      * inversion H0; repeat destruct_match => //; sort.
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
