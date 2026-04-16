Require Import
  Arith.

Ltac match_if' :=
  repeat
  (simpl; try rewrite Nat.eqb_refl; match goal with
  | [ |- context[if ?a then _ else _] ] =>
    destruct a eqn:?
  | [ |- context[match ?a with _ => _ end] ] =>
    destruct a eqn:?
  end); try reflexivity.

Ltac match_if_apply IH :=
  repeat
  (match goal with
  | [ |- context[if ?a then _ else _] ] =>
    destruct a
  | [ |- context[match ?a with _ => _ end] ] =>
    destruct a
  end); try apply IH; auto.
