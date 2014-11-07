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

Hint Constructors prop.

(** Define some friendly notation. Level 48 to have higher precedence than
    the ~ notation for environments; prevents need for parens. *)
Notation "A ⨂ B" := (pp_times A B) (at level 48, left associativity)
                                         : cp_scope.
Notation "A ⅋ B" := (pp_par A B) (at level 48, left associativity)
                                     : cp_scope.
Notation "A ⨁ B" := (pp_plus A B) (at level 48, left associativity)
                                       : cp_scope.
Notation "A & B" := (pp_with A B) (at level 48, left associativity)
                                       : cp_scope.
Notation "'!' A" := (pp_accept A) (at level 48, left associativity)
                                  : cp_scope.
Notation "'?' A" := (pp_request A) (at level 48, left associativity)
                                   : cp_scope.
Reserved Notation "'¬' A" (at level 47, left associativity).

Delimit Scope cp_scope with cp.
Open Scope cp_scope.

(** Return the dual of the proposition [pp]. *)
Fixpoint prop_dual (pp : prop) : prop :=
  match pp with
  | pp_var X => pp_dvar X
  | pp_dvar X => pp_var X
  | A ⨂ B => ¬A ⅋ ¬B
  | A ⅋ B => ¬A ⨂ ¬B
  | A ⨁ B => ¬A & ¬B
  | A & B => ¬A ⨁ ¬B
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
Reserved Notation "'{{' A '//' X '}}' B" (at level 46, left associativity).

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
  | A' ⨂ B' => {{A // X}}A' ⨂ {{A // X}} B'
  | A' ⅋ B' => {{A // X}}A' ⅋ {{A // X}} B'
  | A' ⨁ B' => {{A // X}}A' ⨁ {{A // X}} B'
  | A' & B' => {{A // X}}A' & {{A // X}} B'
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
  | p_output : atom -> atom -> proc -> proc -> proc
  | p_input : atom -> atom -> proc -> proc
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

Hint Constructors proc.

(** Some helpful notations. *)
Notation "x ⟷ y" := (p_link x y) (at level 68) : cp_scope.
Notation "'ν' x ':' A '→' P '|' Q" := (p_par x A P Q) (at level 68, x ident,
                                                       right associativity)
                                                      : cp_scope.
(** Example of using parallel composition :

    Parameter y : atom.
    Print Grammar constr.
    Check ν y : ((pp_var 0) ⅋ (pp_dvar 1)) →
             p_empin y (p_empout y) | p_empout y.
*)
(** Change of notation from the paper; Coq doesn't seem to like the x coming
    first. *)
Notation "'[' y ']' x '→' P '|' Q" := (p_output x y P Q) (at level 68,
                                                          y ident, x ident,
                                                         right associativity)
                                                         : cp_scope.
(** We use ⟨⟩ instead of () in the input cases. *)
Notation "'⟨' y '⟩' x '→' P" := (p_input x y P) (at level 68, y ident,
                                                right associativity)
                                                : cp_scope.

Notation "x '[inl]' → P" := (p_left x P) (at level 68,
                                          right associativity) : cp_scope.
Notation "x '[inr]' → P" := (p_right x P) (at level 68,
                                          right associativity) : cp_scope.
Notation "x 'CASE' P 'OR' Q" := (p_choice x P Q) (at level 68,
                                                  right associativity)
                                                 : cp_scope.
Notation "'!' x '⟨' y '⟩' → P" := (p_accept x y P) (at level 68, x ident,
                                                    y ident,
                                                    right associativity)
                                                   : cp_scope.
Notation "'?' x '[' y ']' → P" := (p_request x y P) (at level 68, x ident,
                                                     y ident,
                                                     right associativity)
                                                    : cp_scope.
Notation "x '→' 0" := (p_empout x) (at level 68) : cp_scope.
Notation "⟨⟩ x → P" := (p_empin x P) (at level 68, x ident,
                                      right associativity) : cp_scope.
Notation "x 'CASE' 0" := (p_empcho x) (at level 68) : cp_scope.

(** Example using some notations (demonstrates the right associativity of the
    rules):

Parameter x y: atom.
Check ν x : (pp_var 0) ⨁ (pp_var 1) → x ⟷ y | x → 0.

*)

(** Environments for the process calculus are mappings of atoms to
    propositions. *)
Definition penv := list (atom * prop).

(** Encoding an environment as all requests; for the server accept process
    rule. *)
Inductive all_requests : penv -> Prop :=
  | all_requests_nil : all_requests nil
  | all_requests_cons : forall Γ x A (REQS: all_requests Γ),
                          all_requests (Γ ++ (x ~ ? A)).

Reserved Notation "P '⊢cp' Γ" (at level 69).

(** The uniqueness assumption is necessary to ensure environments are only
    combined if they contain distinct names.
    Note in some cases we utilise cofinite quantification to provide a
    suitably fresh name for some channels. Some cases could be written has
    x `notin` Γ for some x, Γ but I elected to maintain uniq assumptions
    wherever possible to keep the development symmetrical (in theory, this
    could help proofs since all rules follow a similar structure).
*)
Inductive cp_rules : proc -> penv -> Prop :=
  | cp_fwd : forall x w A (NEQ: x <> w), w ⟷ x ⊢cp ((w ~ ¬ A) ++ (x ~ A))
  | cp_cut : forall P Q x A Γ Δ
                    (UN: uniq (Γ ++ Δ ++ (x ~ A)))
                    (CPP: P ⊢cp Γ ++ (x ~ A))
                    (CPQ: Q ⊢cp Δ ++ (x ~ ¬A)),
               ν x : A → P | Q ⊢cp Γ ++ Δ
  | cp_output : forall P Q Γ Δ x y A B
                       (NING: y `notin` dom Γ)
                       (UN: uniq (Γ ++ Δ ++ (x ~ A ⨂ B)))
                       (CPP: P ⊢cp Γ ++ (y ~ A))
                       (CPQ: Q ⊢cp Δ ++ (x ~ B)),
                  [y]x → P | Q ⊢cp Γ ++ Δ ++ (x ~ A ⨂ B)
  | cp_input : forall P Γ x y A B
                      (UN: uniq (Γ ++ (y ~ A) ++ (x ~ A ⅋ B)))
                      (CPP: P ⊢cp Γ ++ (y ~ A) ++ (x ~ B)),
                 ⟨y⟩x → P ⊢cp Γ ++ (x ~ A ⅋ B)
  | cp_left : forall P Γ x A B
                     (UN: uniq (Γ ++ (x ~ A ⨁ B)))
                     (CPP: P ⊢cp Γ ++ (x ~ A)),
                x[inl] → P ⊢cp Γ ++ (x ~ A ⨁ B)
  | cp_right : forall P Γ x A B
                     (UN: uniq (Γ ++ (x ~ A ⨁ B)))
                     (CPP: P ⊢cp Γ ++ (x ~ B)),
                x[inr] → P ⊢cp Γ ++ (x ~ A ⨁ B)
  | cp_choice : forall P Q Γ x A B
                       (UN: uniq (Γ ++ (x ~ A & B)))
                       (CPP: P ⊢cp Γ ++ (x ~ A))
                       (CPQ: Q ⊢cp Γ ++ (x ~ B)),
                  x CASE P OR Q ⊢cp Γ ++ (x ~ A & B)
  | cp_accept : forall P Γ x y A
                       (NING: y `notin` dom Γ)
                       (REQS: all_requests Γ)
                       (UN: uniq (Γ ++ (x ~ ! A)))
                       (CPP: P ⊢cp Γ ++ (y ~ A)),
                  !x⟨y⟩ → P ⊢cp Γ ++ (x ~ ! A)
  | cp_request : forall P Γ x y A
                        (NING: y `notin` dom Γ)
                        (UN: uniq (Γ ++ (x ~ ? A)))
                        (CPP: P ⊢cp Γ ++ (y ~ A)),
                   ? x[y] → P ⊢cp Γ ++ (x ~ ? A)
  | cp_empout : forall x, x → 0 ⊢cp (x ~ pp_one)
  | cp_empin : forall P Γ x (UN: uniq (Γ ++ (x ~ pp_bot))) (CPP: P ⊢cp Γ),
                 ⟨⟩ x → P ⊢cp Γ ++ (x ~ pp_bot)
  | cp_empcho : forall Γ x (UN: uniq (Γ ++ (x ~ pp_top))),
                  x CASE 0 ⊢cp Γ ++ (x ~ pp_top)
where "P '⊢cp' Γ" := (cp_rules P Γ) : cp_scope.