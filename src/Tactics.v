(* Celsius project *)
(* Clément Blaudeau - Lamp@EPFL & Inria 2020-2022 *)
(* ------------------------------------------------------------------------ *)
(* Adapted from SystemFR project : https://github.com/epfl-lara/SystemFR *)
Require Export String List Psatz Coq.Program.Tactics Arith.
Import ListNotations.

Global Hint Extern 50 => lia: lia.
Global Hint Extern 50 => cbn: cbn.
Global Hint Extern 50 => cbn; intuition auto: cbn_intuition.

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

Global Hint Rewrite Bool.andb_true_iff: bools.
Global Hint Rewrite Bool.andb_false_iff: bools.
Global Hint Rewrite Bool.orb_true_iff: bools.
Global Hint Rewrite Bool.orb_false_iff: bools.
Global Hint Rewrite Bool.negb_true_iff: bools.
Global Hint Rewrite Bool.negb_false_iff: bools.
Ltac bools := autorewrite with bools in *.

Ltac destruct_match :=
match goal with
| [ |- context[match ?t with _ => _ end]] =>
let matched := fresh "matched" in
destruct t eqn:matched
| [ H: context[match ?t with _ => _ end] |- _ ] =>
let matched := fresh "matched" in
destruct t eqn:matched
end.


Ltac flatten :=
  repeat subst ||
         match goal with
         | H : _ \/ _ |- _ => let fresh1 := fresh H in
                           let fresh2 := fresh H in destruct H as [fresh1 | fresh2]
         | H : _ /\ _ |- _ => let fresh1 := fresh H in
                           let fresh2 := fresh H in destruct H as [fresh1 fresh2]
         | H : exists a, _  |- _ => let fresh_a := fresh a in destruct H as [fresh_a H]
         end || invert_constructor_equalities.

Ltac ground :=
  repeat destruct_match || flatten.

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


Ltac apply_any :=
  match goal with
  | H: _ |- _ => apply H
  end.

Ltac rewrite_any :=
  match goal with
  | H: _ |- _ => rewrite H in *
  end.

Ltac erewrite_any :=
  match goal with
  | H: _ |- _ => erewrite H in *
  end.

Ltac rewrite_back_any :=
  match goal with
  | H: _ |- _ => rewrite <- H in *
  end.

Ltac eapply_any :=
  match goal with
  | H: _ |- _ => eapply H
  end.

Ltac apply_anywhere f :=
  match goal with
  | H: _ |- _ => apply f in H
  end.

Ltac eapply_anywhere f :=
  match goal with
  | H: _ |- _ => eapply f in H
  end.

Ltac rewrite_anywhere f :=
  match goal with
  | H: _ |- _ => rewrite f in H
  end.

Ltac erewrite_anywhere f :=
  match goal with
  | H: _ |- _ => erewrite f in H
  end.

Ltac destruct_eq H :=
  match H with
  | ?a = ?b =>
      let fresh_H := fresh "Heq" in pose proof (PeanoNat.Nat.eq_dec a b) as [fresh_H | fresh_H]
  end.

Ltac modus_ponens :=
  repeat match goal with
         | H1 : ?P -> ?Q, H2: ?P |- _ => pose proof (H1 H2) ; clear H1 end.

Ltac nat_le_trans :=
  repeat match goal with
  |H1: ?a <= ?b, H2: ?b <= ?c |- _ =>
   match goal with
   | H3 : a <= c |- _ => fail 1
   | _ => assert (a <= c) by lia
   end
  end.

Ltac modus :=
  repeat match goal with
         | H: ?A -> ?B, H': ?A |- _ => specialize (H H')
         end.


Ltac move_top t :=
  try match goal with
  | H1:t, H2:t, H3:t, H4:t, H5:t, H6:t, H7:t, H8:t, H9:t, H10:t |- _ =>
     move H1 at top;
     move H2 at top;
     move H3 at top;
     move H4 at top;
     move H5 at top;
     move H6 at top;
     move H7 at top;
     move H8 at top;
     move H9 at top;
     move H10 at top
  | H1:t, H2:t, H3:t, H4:t, H5:t, H6:t, H7:t, H8:t, H9:t |- _ =>
     move H1 at top;
     move H2 at top;
     move H3 at top;
     move H4 at top;
     move H5 at top;
     move H6 at top;
     move H7 at top;
     move H8 at top;
     move H9 at top
  | H1:t, H2:t, H3:t, H4:t, H5:t, H6:t, H7:t, H8:t |- _ =>
     move H1 at top;
     move H2 at top;
     move H3 at top;
     move H4 at top;
     move H5 at top;
     move H6 at top;
     move H7 at top;
     move H8 at top
  | H1:t, H2:t, H3:t, H4:t, H5:t, H6:t, H7:t |- _ =>
     move H1 at top;
     move H2 at top;
     move H3 at top;
     move H4 at top;
     move H5 at top;
     move H6 at top;
     move H7 at top
  | H1:t, H2:t, H3:t, H4:t, H5:t, H6:t |- _ =>
     move H1 at top;
     move H2 at top;
     move H3 at top;
     move H4 at top;
     move H5 at top;
     move H6 at top
  | H1:t, H2:t, H3:t, H4:t, H5:t |- _ =>
     move H1 at top;
     move H2 at top;
     move H3 at top;
     move H4 at top;
     move H5 at top
  | H1:t, H2:t, H3:t, H4:t |- _ =>
     move H1 at top;
     move H2 at top;
     move H3 at top;
     move H4 at top
  | H1:t, H2:t, H3:t |- _ =>
     move H1 at top;
     move H2 at top;
     move H3 at top
  | H1:t, H2:t |- _ =>
     move H1 at top;
     move H2 at top
  | H1:t |- _ =>
     move H1 at top
  end.


Ltac app_eq_nil :=
  repeat match goal with
         | H: nil = _ ++ (_ :: _) |- _ => symmetry in H
         | H: _ ++ (_ :: _) = nil |- _ =>
             exfalso; apply app_eq_nil in H as [_ H];
             inversion H
    end.

Global Hint Extern 1 => app_eq_nil: core.


From Celsius Require Export LibTactics.
Ltac cross_rewrites :=
  repeat match goal with
         | H: ?A = ?B, H': ?A = ?C |- _ => rewrite H in H'; inverts H'
         end.
Global Hint Extern 1 => cross_rewrites: core.

Ltac destruct_if_eqb:=
  match goal with
  | H : context [if Nat.eqb ?a ?b then _ else _ ] |- _ =>
      let Heq := fresh "Heq" in
      destruct (Nat.eqb a b) eqn:Heq;
      [apply PeanoNat.Nat.eqb_eq in Heq ; rewrites Heq in * ; clear Heq | apply PeanoNat.Nat.eqb_neq in Heq ]
  end.
