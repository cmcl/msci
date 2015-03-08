(** Set of tatics to simplify the development. The names are suggestive of
    their insipration.
 *)

Require Import Basics Prelude Eqdep_dec.
Require Export SFLibTactics.
Declare ML Module "ssreflect".

Global Set Bullet Behavior "Strict Subproofs".

Hint Unfold not.

(* Haskell-inspired infix function application operator. *)
Infix "$" := apply (at level 100).

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

Ltac simpl_existT :=
  repeat match goal with
           | [H: existT _ _ _ = existT _ _ _ |- _]
             => apply inj_pair2_eq_dec in H; auto
         end.

Tactic Notation "dup" hyp(H) := let H' := fresh H in assert (H' := H).

Tactic Notation "s" "in" hyp(H) := simpl in H.

Ltac s := simpl.
Ltac ss := repeat (unfold not in *; simpl in *).
Ltac i := intros.
Ltac ii := repeat (intros; ss).
Ltac inv H := inversion H; ss; subst.

(** ssreflect doesn't play nice with parentheses (in ii above, for example).
    So I have stolen done and by definitions from the library. *)
Ltac done :=
  unfold not in *; trivial; hnf; intros
  ; solve [ do ![solve [trivial | apply: sym_equal; trivial]
                | discriminate | contradiction | split]
          | match goal with
                H : _ -> False |- _ => solve [case H; trivial]
            end ].

Tactic Notation "by" tactic(tac) := tac; done.

(* Courtesy of CompCert. *)

Lemma modusponens: forall (P Q: Prop), P -> (P -> Q) -> Q.
Proof. auto. Qed.

Ltac exploit x :=
 refine (modusponens _ _
  (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 ||
 refine (modusponens _ _ 
  (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 ||
 refine (modusponens _ _
  (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 ||
 refine (modusponens _ _
  (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 ||
 refine (modusponens _ _
  (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 ||
 refine (modusponens _ _
  (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 ||
 refine (modusponens _ _
  (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 ||
 refine (modusponens _ _
  (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 ||
 refine (modusponens _ _
  (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 ||
 refine (modusponens _ _
  (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 ||
 refine (modusponens _ _
  (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 ||
 refine (modusponens _ _
  (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 ||
 refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _ _) _)
 || refine (modusponens _ _ (x _ _ _) _)
 || refine (modusponens _ _ (x _ _) _)
 || refine (modusponens _ _ (x _) _).

