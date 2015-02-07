(** Set of tatics to simplify the development. The names are suggestive of
    their insipration.
 *)

Require Import Metatheory Prelude Eqdep_dec.
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
      | |- context[?X == ?Y] => des_goal (X == Y)
      | [H: context[?X == ?Y] |- _] => desT (X == Y)
      | |- context[match ?X with _ => _ end] => destruct X; subst
      | [H: context[match ?X with _ => _ end] |- _] => destruct X; subst
      | [H: ?P <-> ?Q |- _] =>
        let HP := fresh H in
        let HQ := fresh H in destruct H as [HP HQ]
      | |- ?P <-> ?Q => split
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

(* Destruct some `in` equations in similar style to the [destruct_notin]
   tactic. *)
Ltac destruct_in :=
  match goal with
    | H :  _ `in` empty |- _ =>
      apply AtomSetFacts.empty_iff in H; inv H
    | H : ?y `in` (add ?x ?s) |- _ =>
      apply AtomSetFacts.add_iff in H; des; destruct_in
    | H : ?y `in` (singleton ?x) |- _ =>
      apply AtomSetFacts.singleton_iff in H; destruct_in
    | H : ?y `in` (remove ?x ?s) |- _ =>
      apply AtomSetFacts.remove_iff in H; des; destruct_in
    | H : ?x `in` (union ?s ?s') |- _ =>
      apply AtomSetFacts.union_iff in H; des; destruct_in
    | H : ?x `in` (inter ?s ?s') |- _ =>
      apply AtomSetFacts.inter_iff in H; des; destruct_in
    | H : ?x `in` (AtomSetImpl.diff ?s ?s') |- _ =>
      apply AtomSetFacts.diff_iff in H; des; destruct_in
    | _ =>
      idtac
  end.

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

