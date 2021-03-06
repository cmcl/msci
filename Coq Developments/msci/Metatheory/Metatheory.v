(* This file is distributed under the terms of the MIT License, also
   known as the X11 Licence.  A copy of this license is in the README
   file that accompanied the original distribution of this file.

   Based on code written by:
     Brian Aydemir
     Arthur Charg\'eraud *)

Require Export Coq.Arith.Arith.
Require Export Coq.FSets.FSets.
Require Export Coq.Lists.List.

Require Export AssocList.
Require Export CoqEqDec.
Require Export CoqListFacts.
Require Export LibTactics.
Require Export MetatheoryAtom.
Require Export Tactics.

(* ********************************************************************** *)
(** * Decidable equality *)

(** We prefer that "==" refer to decidable equality at [eq], as
    defined by the [EqDec_eq] class from the CoqEqDec library. *)

Notation " x == y " := (eq_dec x y) (at level 70) : coqeqdec_scope.

Open Scope coqeqdec_scope.


(* ********************************************************************** *)
(** * Notations for finite sets of atoms *)

(** Common set operations and constants may be written using more
    convenient notations. *)

Notation "E [=] F" :=
  (AtomSetImpl.Equal E F)
  (at level 70, no associativity)
  : set_scope.

Notation "E [<=] F" :=
  (AtomSetImpl.Subset E F)
  (at level 70, no associativity)
  : set_scope.

Notation "{}" :=
  (AtomSetImpl.empty)
  : set_scope.

Notation "{{  x  }}" :=
  (AtomSetImpl.singleton x)
  : set_scope.

Notation "x `in` E" :=
  (AtomSetImpl.In x E)
  (at level 70)
  : set_hs_scope.

Notation "x `notin` E" :=
  (~ AtomSetImpl.In x E)
  (at level 70)
  : set_hs_scope.

Notation "E `union` F" :=
  (AtomSetImpl.union E F)
  (at level 65, right associativity, format "E  `union`  '/' F")
  : set_hs_scope.

Notation "E `inter` F" :=
  (AtomSetImpl.inter E F)
  (at level 65, right associativity, format "E `inter` '/' F")
  : set_hs_scope.

(** We define some abbreviations for the empty set, singleton
    sets, and the union of two sets. *)

Notation add := AtomSetImpl.add.
Notation empty := AtomSetImpl.empty.
Notation remove := AtomSetImpl.remove.
Notation singleton := AtomSetImpl.singleton.
Notation union := AtomSetImpl.union.
Notation inter := AtomSetImpl.inter.

(** Open the notation scopes declared above. *)

Open Scope set_scope.
Open Scope set_hs_scope.


(* ********************************************************************** *)
(** * Environments *)

(** We can use our implementation of association lists (in AssocList)
    to implement association lists whose keys are atoms.  Thanks to
    parameter inlining, the types in the instantiated functor will all
    use [atom] for the type for keys. *)

Module Export EnvImpl := AssocList.Make AtomDT AtomSetImpl.

(** We provide alternative names for the tactics on association lists
    to reflect our use of association lists for environments. *)

Ltac simpl_env :=
  simpl_alist.

Tactic Notation "simpl_env" "in" hyp(H) :=
  simpl_alist in H.

Tactic Notation "simpl_env" "in" "*" :=
  simpl_alist in *.

Tactic Notation "rewrite_env" constr(E) :=
  rewrite_alist E.

Tactic Notation "rewrite_env" constr(E) "in" hyp(H) :=
  rewrite_alist E in H.

Tactic Notation "env" "induction" ident(E) :=
  alist induction E.

Tactic Notation "env" "induction" ident(E) "as" simple_intropattern(P) :=
  alist induction E as P.

(** As an alternative to the [x ~ a] notation, we also provide more
    list-like notation for writing association lists consisting of a
    single binding.

    Implementation note: The following notation overlaps with the
    standard recursive notation for lists, e.g., the one found in the
    Program library of Coq's standard library. *)

Notation "[ x ]" := (EnvImpl.one x) : env_scope.

Open Scope env_scope.


(* ********************************************************************** *)
(** * Cofinite quantification *)

(** Consider a rule [H] (equivalently, constructor, lemma, etc.) whose
    type begins with [forall L, ...] and contains hypotheses of the
    form [(forall y, y `notin` L -> ...)].

    The tactic [(pick fresh x excluding F and apply H)] applies [H] to
    the current goal, instantiating [H]'s first argument ([L]) with
    the finite set of atoms [F].  In each new subgoal of the form
    [(forall y, y `notin` F -> ...)], the atom [y] is introduced as
    [x], and [(y `notin` F)] is introduced using a generated name.

    If we view [H] as a rule that uses cofinite quantification, the
    tactic can be read as picking a sufficiently fresh atom to open a
    term with. *)

Tactic Notation
  "pick" "fresh" ident(atom_name)
  "excluding" constr(L)
  "and" "apply" constr(H)
  :=
    first [apply (@H L) | eapply (@H L)];
      match goal with
        | |- forall _, _ `notin` _ -> _ =>
          let Fr := fresh "Fr" in intros atom_name Fr
        | |- forall _, _ `notin` _ -> _ =>
          fail 1 "because" atom_name "is already defined"
        | _ =>
          idtac
      end.

(** The following variant of the tactic excludes the set of atoms
    returned by the [gather_atoms] tactic.  Redefine [gather_atoms] if
    you wish to modify the behavior of this tactic. *)

Tactic Notation
  "pick" "fresh" ident(atom_name)
  "and" "apply" constr(H)
  :=
    let L := gather_atoms in
    let L := beautify_fset L in
    pick fresh atom_name excluding L and apply H.


(* ********************************************************************** *)
(** * Lemma aliases *)

(** A number of useful lemmas are given standardized, if somewhat
    unintuitive, names.  Here, we define some intuitive aliases for
    them. *)

Notation uniq_one := uniq_one_1.
Notation uniq_cons := uniq_cons_3.
Notation uniq_app := uniq_app_4.
Notation uniq_map := uniq_map_2.

Notation binds_one := binds_one_3.
Notation binds_cons := binds_cons_3.
Notation binds_app_l := binds_app_2.
Notation binds_app_r := binds_app_3.
Notation binds_map := binds_map_2.

Notation notin_empty := notin_empty_1.
Notation notin_add := notin_add_3.
Notation notin_singleton := notin_singleton_2.
Notation notin_union := notin_union_3.

(** Exporting required entities from AtomSetImpl, AtomSetFacts and
    AtomSetProperties. *)
Definition elements := AtomSetImpl.elements.
Definition elements_3w := AtomSetImpl.elements_3w.
Definition elements_iff := AtomSetFacts.elements_iff.
Definition equal_sym := AtomSetProperties.equal_sym.
Definition remove_iff := AtomSetFacts.remove_iff.
Definition union_2 := AtomSetImpl.union_2.
Definition union_3 := AtomSetImpl.union_3.

(* ********************************************************************** *)
(** * Hints *)

(** The next block of hints is to help [auto] discharge many of the
    inequality and freshness goals that arise in programming language
    metatheory proofs.

    Implementation note (BEA): The [eassumption] step is intended to
    address those cases where [eauto] tries to use a cofinite
    rule. The pattern goes something like this:

      - Apply a cofinite rule with no idea what "[L]" should be.
        This adds a hypothesis [x `notin` ?1] to the context.
      - Apply the IH.
      - [eassumption] resolves the [x `notin` L] obligation of
        the IH against the previously introduced [x `notin` ?1]
        hypothesis.

    This ensures that the [autorewrite] step does not trigger an
    infinite loop. *)

Ltac hint_extern_solve_notin :=
  try eassumption;
  autorewrite with rewr_dom in *;
  destruct_notin;
  repeat first [ apply notin_union_3
               | apply notin_add_3
               | apply notin_singleton_2
               | apply notin_empty_1
               ];
  try tauto.

Hint Extern 1 (_ <> _ :> _) => hint_extern_solve_notin.

Hint Extern 1 (_ `notin` _) => hint_extern_solve_notin.

(** The next block of hints are occasionally useful when reasoning
    about finite sets.  In some instances, they obviate the need to
    use [auto with set]. *)

Hint Resolve
  AtomSetImpl.add_1 AtomSetImpl.add_2 AtomSetImpl.remove_1
  AtomSetImpl.remove_2 AtomSetImpl.singleton_2 AtomSetImpl.union_2
  AtomSetImpl.union_3 AtomSetImpl.inter_3 AtomSetImpl.diff_3.


(* ********************************************************************** *)
(** * Ott compatibility *)

(** Implementation note (BEA): The following definitions make this
    library usable with the output of Ott's locally nameless backend.
    They may disappear or change as Ott changes. *)

Notation var := atom (only parsing).

Notation vars := atoms (only parsing).

Notation eq_var := eq_dec (only parsing).

Notation "x  ===  y" :=
  (x == y)
  (at level 70, only parsing)
  : coqeqdec_scope.

Notation "x \in s" :=
  (x `in` s)
  (at level 70, only parsing)
  : set_sl_scope.

Notation "x \notin s" :=
  (x `notin` s)
  (at level 70, only parsing)
  : set_sl_scope.

Notation "s \u t" :=
  (s `union` t)
  (at level 65, right associativity, only parsing)
  : set_sl_scope.

Open Scope set_sl_scope.

Ltac gather_vars_with F := gather_atoms_with.

Ltac pick_fresh_gen L Y := pick fresh Y for L.

Tactic Notation "auto" "*" := auto.

Ltac apply_fresh_base H gather_vars atom_name :=
  let L := gather_vars in
  let L := beautify_fset L in
  pick fresh x excluding L and apply H.

(** Helper tactic to obtain all the atoms in the context of a goal. *)
Tactic Notation
  "obtain" "atoms" ident(atoms_name) "as" ident(H)
   :=
     let L := gather_atoms in
     let L := beautify_fset L in
     set (atoms_name:=L); def_to_eq atoms_name H L.

(* SCW added this one for list support *)
Set Implicit Arguments.
Definition union_map (A:Set) (f:A -> vars) (l:list A) := 
 (List.fold_right (fun t acc => f t \u acc) {}) l.

(** This tactic is somewhat fragile when destructing matches. Destructing
    if-then-else's as a subject of a match results in unprovable subgoals;
    one requires to destruct all pnames in the context first.

    Needs to be defined when we have the correct interpretation for == i.e.
    equality on atoms. *)
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

(** Helpful tactic for handling In predicate destruction. *)

Ltac analyze_in x :=
  match goal with
    | [H: x `in` dom ?E |- _] =>
      let a := fresh "a" in
      let E1 := fresh "E1" in
      let E2 := fresh "E2" in
      let EQ := fresh "EQ" in
      apply in_env_split in H
      ; inversion_clear H as (a & E1 & E2 & EQ)
      ; substs~
  end.

(* Find co-finitely quantified hypotheses to specialise. *)
Ltac find_specializes :=
  repeat match goal with
         | [H: forall x, x `notin` ?L -> _, H1: ?y `notin` ?L |- _]
           => specializes H H1
         end.