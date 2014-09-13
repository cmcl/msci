Require Export Arith.EqNat.

Ltac destruct_if := 
  (repeat 
    match goal with 
      | [ |- context[if ?B then _ else _ ] ] => destruct B 
    end);
  try (rewrite eq_nat_is_eq in *).

