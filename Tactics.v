Require Import Coq.Bool.Bool.
Open Scope bool_scope.

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

Hint Rewrite Bool.andb_true_iff: bools.
Hint Rewrite Bool.andb_false_iff: bools.
Hint Rewrite Bool.orb_true_iff: bools.
Hint Rewrite Bool.orb_false_iff: bools.
Hint Rewrite Bool.negb_true_iff: bools.
Hint Rewrite Bool.negb_false_iff: bools.
Ltac bools :=
  autorewrite with bools in *.
