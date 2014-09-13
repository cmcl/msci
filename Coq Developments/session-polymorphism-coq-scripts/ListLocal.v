Require Export List.
Require Import TacticsSF.
Require Import TacticsCPDT.

(* List lemmas.  Some from CPDT. *)

Lemma In_app1 : forall T (x : T) ls2 ls1, In x ls1 -> In x (ls1 ++ ls2).
Proof.
  induction ls1; intuition.
Qed.

Lemma In_app2 : forall T (x : T) ls2 ls1, In x ls2 -> In x (ls1 ++ ls2).
Proof.
  induction ls2; intuition.
Qed.

Lemma in_cons_nil : forall A (x y : A), In x (y :: nil) -> x = y.
Proof.
  unfold In; intuition.
Qed.

Lemma singleton_list_eq : forall A, forall (x y : A), x :: nil = y :: nil -> x = y.
Proof.
  crush.
Qed.

Lemma in_eq_singleton : 
  forall A (x y : A), In x (y :: nil) -> y = x.
Proof.
  intros A x y Hin.
  destruct (@in_inv _ _ _ _ Hin); intuition.
Qed.

Lemma flat_map_dist_app : 
  forall (A B:Type) (f:A -> list B) (xs ys : list A), 
    flat_map f (xs ++ ys) = (flat_map f xs) ++ (flat_map f ys).
Proof.
  intros A B f xs ys.  induction xs; simpl; intuition.
  rewrite IHxs.
  intuition.
Qed.

