Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Omega.
Require Import Psatz.

Open Scope string.

Hint Extern 50 => omega: omega.
Hint Extern 50 => lia: lia.
Hint Extern 50 => cbn: cbn.
Hint Extern 50 => cbn; intuition auto: cbn_intuition.

Ltac options :=
unfold option_map in *.

Ltac invert_constructor_equalities :=
match goal with
| H: ?F _ = ?F _ |- _ => is_constructor F; inversion H; clear H
| H: ?F _ _ = ?F _ _ |- _ => is_constructor F; inversion H; clear H
| H: ?F _ _ _ = ?F _ _ _ |- _ => is_constructor F; inversion H; clear H
| H: ?F _ _ _ _ = ?F _ _ _ _ |- _ => is_constructor F; inversion H; clear H
| H: ?F _ _ _ _ _ = ?F _ _ _ _ _ |- _ => is_constructor F; inversion H; clear H
| H: ?F _ _ _ _ _ _ = ?F _ _ _ _ _ _ |- _ => is_constructor F; inversion H; clear H
end.

Ltac destruct_exists :=
match goal with
| H: exists x, _ |- _ => let freshX := fresh x in
                  let matched := fresh "matched_exists" in
                  destruct H as [ freshX ] eqn:matched
end.

Ltac destruct_and :=
  match goal with
  | H: _ /\ _ |- _ => destruct H
  end.


Ltac destruct_match :=
match goal with
| [ |- context[match ?t with _ => _ end]] =>
let matched := fresh "matched" in
destruct t eqn:matched
| [ H: context[match ?t with _ => _ end] |- _ ] =>
let matched := fresh "matched" in
destruct t eqn:matched
end.

Ltac light :=
  (intros) ||
  (intuition auto) ||
  (congruence) ||
  (subst) ||
  (cbn in *) ||
  (autounfold in *)
.
(** Taken from Cpdt **)
(** Succeed iff [x] is in the list [ls], represented with left-associated nested tuples. *)
Ltac inList x ls :=
  match ls with
    | x => idtac
    | (_, x) => idtac
    | (?LS, _) => inList x LS
  end.

(** Taken from Cpdt **)
Ltac step_inversion predicates :=
  let invert H F :=
    inList F predicates;
      (inversion H; fail) ||
      (inversion H; [ idtac ]; clear H)
  in
  match goal with
    | [ H: ?F _ |- _ ] => invert H F
    | [ H: ?F _ _ |- _ ] => invert H F
    | [ H: ?F _ _ _ |- _ ] => invert H F
    | [ H: ?F _ _ _ _ |- _ ] => invert H F
    | [ H: ?F _ _ _ _ _ |- _ ] => invert H F
    | [ H: ?F _ _ _ _ _ _ |- _ ] => invert H F
  end.

Ltac containsExistential := match goal with
  | [ |- ?G ]  => has_evar G
  end.

Ltac noExistential := tryif containsExistential then fail else idtac.

Ltac removeDuplicateProps := match goal with
  | [ H1: ?P, H2: ?P |- _ ] =>
    match type of P with
    | Prop => idtac
    end;  clear H2
  end.

Ltac isThere P := match goal with
  | H: ?Q |- _ => unify P Q
(*  | |- ?Q => unify P Q *)
  end.

Ltac notThere P := tryif (isThere P) then fail else idtac.
Ltac not_var P := tryif (is_var P) then fail else idtac.
Ltac noUnify P Q := tryif (unify P Q) then fail else idtac.

Lemma strong_and:
  forall (A B: Prop), A -> (A -> B) -> (exists _: A, B).
Proof.
  eauto.
Qed.


Ltac step_gen := match goal with
  | _ => progress light
  | _ => apply strong_and
  | H: exists x, _ |- _ =>
    let x' := fresh x in
    destruct H as [ x' ]
  | [ p: ?A*?B |- _ ] => destruct p
  | [ H: (_,_) = (_,_) |- _ ] => inversion H; clear H
  | [ H: context[Nat.eq_dec ?U ?V] |- _ ] => destruct (Nat.eq_dec U V)
  | H: _ |- _ => injection H; clear H
  | |- NoDup _ => constructor
  | H: forall a, _ -> _ |- _ => pose proof (H _ eq_refl); clear H
  | H: forall a b, _ -> _ |- _ => pose proof (H _ _ eq_refl); clear H
  | H: forall a b c, _ -> _ |- _ => pose proof (H _ _ _ eq_refl); clear H
  | H: forall a b c d, _ -> _ |- _ => pose proof (H _ _ _ _ eq_refl); clear H
  | H: forall a b c d e, _ -> _ |- _ => pose proof (H _ _ _ _ _ eq_refl); clear H
  | [ |- context[match ?t with _ => _ end]] =>
      let matched := fresh "matched" in
      destruct t eqn:matched
  | [ H: context[match ?t with _ => _ end] |- _ ] =>
      let matched := fresh "matched" in
      destruct t eqn:matched
  | _ => removeDuplicateProps
  | H := _: ?T |- _ => noUnify T string; clearbody H
  | _ => noExistential; solve [ constructor ]
  | _ => noExistential; solve [ constructor; constructor ]
  end.

Ltac step := step_gen || step_inversion (List.Forall, List.In).
Ltac steps := repeat step.
