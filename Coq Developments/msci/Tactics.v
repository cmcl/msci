(** Set of tatics to simplify the development. The names are suggestive of
    their insipration.
 *)

Require Import Prelude Eqdep_dec.

Hint Unfold not.

(* Like destruct_all but applied to the goal. *)
Ltac des_goal t :=
  repeat
    match goal with
      | |- context[t] =>
        let H := fresh in
        destruct t as [H|H]; try now (contradict H)
      | _ => idtac
    end.

Ltac desT t :=
  repeat
    match goal with
      | [H: context[t] |- _] =>
          let H := fresh in
            destruct t as [H|H]; try now (contradict H)
      | _ => idtac
    end.

(* Destruct some simple propositional formulas. *)
Ltac des :=
  repeat
    match goal with
      | [H: ?P /\ ?Q |- _] =>
          let HP := fresh H in
          let HQ := fresh H in
          destruct H as [HP HQ]
      | [H: ?P \/ ?Q |- _] =>
          let HP := fresh H in
          let HQ := fresh H in
          destruct H as [HP|HQ]
      | _ => idtac
    end.

Ltac simpl_existT :=
  try (match goal with
         | [H: existT _ _ _ = existT _ _ _ |- _]
           => apply inj_pair2_eq_dec in H; auto
         | _ => idtac
       end).

Tactic Notation "dup" hyp(H) := let H' := fresh H in assert (H' := H).

Ltac s := simpl.
Ltac ss := repeat (unfold not in *; simpl in *).
Ltac i := intros.
Ltac ii := intros; ss.
Ltac inv H := inversion H; ss; subst.

