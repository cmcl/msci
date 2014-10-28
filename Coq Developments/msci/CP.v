(** Beginning of the file for CP mechanisation as described in

    Philip Wadler. 2012. Propositions as sessions. In Proceedings of the 17th
    ACM SIGPLAN international conference on Functional programming (ICFP '12).
    ACM, New York, NY, USA, 273-286. DOI=10.1145/2364527.2364568
    http://doi.acm.org/10.1145/2364527.2364568

*)
Require Import Metatheory.Metatheory.

(** Propositional variables are represented as natural numbers. *)
Definition pvar := nat.

(** Propositions ranged over by A, B and C. *)
Inductive prop : Type :=
  | pp_var : pvar -> prop
  | pp_dvar : pvar -> prop (* dual of a pvar *)
  | pp_times : prop -> prop -> prop
  | pp_par : prop -> prop -> prop
  | pp_plus : prop -> prop -> prop
  | pp_with : prop -> prop -> prop
  | pp_accept : prop -> prop (* !A *)
  | pp_request : prop -> prop (* ?A *)
  | pp_forall : pvar -> prop -> prop
  | pp_exists : pvar -> prop -> prop
  | pp_one : prop (* unit for times *)
  | pp_bot : prop (* unit for par *)
  | pp_zero : prop (* unit for plus *)
  | pp_top : prop (* unit for with *).

(** Define some friendly notation. *)
Notation "A `times` B" := (pp_times A B) (at level 68, left associativity)
                                         : cp_scope.
Notation "A `par` B" := (pp_par A B) (at level 68, left associativity)
                                     : cp_scope.
Notation "A `plus` B" := (pp_plus A B) (at level 68, left associativity)
                                       : cp_scope.
Notation "A `with` B" := (pp_with A B) (at level 68, left associativity)
                                       : cp_scope.
Notation "'!' A" := (pp_accept A) (at level 68, left associativity)
                                  : cp_scope.
Notation "'?' A" := (pp_request A) (at level 68, left associativity)
                                   : cp_scope.
Reserved Notation "'¬' A" (at level 67, left associativity).

Delimit Scope cp_scope with cp.
Open Scope cp_scope.

(** Return the dual of the proposition [pp]. *)
Fixpoint prop_dual (pp : prop) : prop :=
  match pp with
  | pp_var X => pp_dvar X
  | pp_dvar X => pp_var X
  | A `times` B => ¬A `par` ¬B
  | A `par` B => ¬A `times` ¬B
  | A `plus` B => ¬A `with` ¬B
  | A `with` B => ¬A `plus` ¬B
  | ! A => ? ¬A
  | ? A => ! ¬A
  | pp_forall X A => pp_exists X (¬A)
  | pp_exists X A => pp_forall X (¬A)
  | pp_one => pp_bot
  | pp_bot => pp_one
  | pp_zero => pp_top
  | pp_top => pp_zero
  end
where "'¬' A" := (prop_dual A) : cp_scope.

Lemma prop_dual_involutive: forall A,
  A = ¬(¬A).
Proof.
  induction A; simpl; f_equal; auto.
Qed.

(** Substitution of proposition [A] for [X] in [B] is denoted by
    {{ A // X }} B -- double syntax used to get Coq to accept it. *)
Reserved Notation "'{{' A '//' X '}}' B" (at level 66, left associativity).

(** Substitution structural recurses over the definition of a proposition.
    Note that there is an assumption (TODO: Enforce this?) that binders are
    unique. That is, forall and exist will not capture the propositional
    variable. Essentially, we only perform this substitution on open
    propositions.
*)
Fixpoint prop_subst (B A : prop) (X : pvar) : prop :=
  match B with
  | pp_var Y => if X == Y then A else pp_var Y
  | pp_dvar Y => if X == Y then ¬A else pp_dvar Y
  | A' `times` B' => {{A // X}}A' `times` {{A // X}} B'
  | A' `par` B' => {{A // X}}A' `par` {{A // X}} B'
  | A' `plus` B' => {{A // X}}A' `plus` {{A // X}} B'
  | A' `with` B' => {{A // X}}A' `with` {{A // X}} B'
  | ! A' => ! {{A // X}}A'
  | ? A' => ? {{A // X}}A'
  | pp_forall Y A' => pp_forall Y ({{A // X}}A')
  | pp_exists Y A' => pp_exists Y ({{A // X}}A')
  | _ => B
  end
where "'{{' A '//' X '}}' B" := (prop_subst B A X) : cp_scope.

Lemma prop_dual_preserves_subst: forall A B X,
  ¬({{A // X}}B) = {{A // X}}(¬B).
Proof.
  intros; induction B; simpl; f_equal; auto
  ; match goal with
    | |- context[?X == ?Y] => destruct (X == Y)
    end; auto using prop_dual_involutive.
Qed.

(** Definition of a processes ranged over by P, Q and R. *)
Inductive proc : Set :=
  | p_link : atom -> atom -> proc
  | p_par : atom -> prop -> proc -> proc -> proc
  | p_output : atom -> atom -> proc -> proc
  | p_input : atom -> atom -> proc
  | p_left : atom -> proc -> proc
  | p_right : atom -> proc -> proc
  | p_choice : atom -> proc -> proc -> proc
  | p_accept : atom -> atom -> proc -> proc
  | p_request : atom -> atom -> proc -> proc
  | p_send : atom -> prop -> proc -> proc
  | p_recv : atom -> pvar -> proc -> proc
  | p_empout : atom -> proc
  | p_empin : atom -> proc -> proc
  | p_empcho : atom -> proc.

(** Environments for the process calculus are mappings of atoms to
    propositions. *)
Definition penv := list (atom * prop).

(** Well-formed process environments are defined as follows: An environment
    [env] is well-formed ([wf_penv env]) if all names are unique. *)
Inductive wf_penv : penv -> Prop :=
  | wf_penv_nil : wf_penv nil
  | wf_penv_cons:
      forall (x : atom) (p : prop) (xs : penv)
             (NIN: x `notin` dom xs),
        wf_penv ((x,p) :: xs).