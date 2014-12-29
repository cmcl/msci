(** Beginning of the file for CP mechanisation as described in

    Philip Wadler. 2012. Propositions as sessions. In Proceedings of the 17th
    ACM SIGPLAN international conference on Functional programming (ICFP '12).
    ACM, New York, NY, USA, 273-286. DOI=10.1145/2364527.2364568
    http://doi.acm.org/10.1145/2364527.2364568

*)
Require Import Metatheory.Metatheory Tactics.

Set Implicit Arguments.

(** Propositional variables are represented as natural numbers (bound) or
    atoms (free).
*)
Inductive pvar :=
  | pvar_bvar : nat -> pvar
  | pvar_fvar : atom -> pvar.

Coercion pvar_bvar : nat >-> pvar.
Coercion pvar_fvar : atom >-> pvar.

Hint Resolve eq_nat_dec.

Lemma eq_pvar_dec : forall (x y : pvar), {x = y} + {x <> y}.
Proof. decide equality. Qed.

Hint Resolve eq_pvar_dec.

(** Propositions ranged over by A, B and C.

    Note binding is de Bruijn indices with forall/exists being binders.
*)
Inductive prop : Type :=
  | pp_var : pvar -> prop
  | pp_dvar : pvar -> prop (* dual of a pvar *)
  | pp_times : prop -> prop -> prop
  | pp_par : prop -> prop -> prop
  | pp_plus : prop -> prop -> prop
  | pp_with : prop -> prop -> prop
  | pp_accept : prop -> prop (* !A *)
  | pp_request : prop -> prop (* ?A *)
  | pp_forall : prop -> prop
  | pp_exists : prop -> prop
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
  | pp_forall A => pp_exists (¬A)
  | pp_exists A => pp_forall (¬A)
  | pp_one => pp_bot
  | pp_bot => pp_one
  | pp_zero => pp_top
  | pp_top => pp_zero
  end
where "'¬' A" := (prop_dual A) : cp_scope.

Inductive dual_props : prop -> prop -> Prop :=
  | dual_var : forall X, dual_props (pp_var X) (pp_dvar X)
  | dual_mul : forall A B dA dB (DUA: dual_props A dA) (DUB: dual_props B dB),
                 dual_props (A ⨂ B) (dA ⅋ dB)
  | dual_add : forall A B dA dB (DUA: dual_props A dA) (DUB: dual_props B dB),
                  dual_props (A ⨁ B) (dA & dB)
  | dual_exp : forall A dA (DUA: dual_props A dA), dual_props (! A) (? dA)
  | dual_quant : forall A dA (DUA: dual_props A dA),
                   dual_props (pp_forall A) (pp_exists dA)
  | dual_umul : dual_props pp_one pp_bot
  | dual_uadd : dual_props pp_zero pp_top
  | dual_sym : forall P dP (DP: dual_props P dP),
                 dual_props dP P.

Hint Constructors dual_props.

Lemma eq_prop_dec: forall (x y : prop), {x = y} + {x <> y}.
Proof. decide equality. Qed.

Hint Resolve eq_prop_dec.

Instance EqDec_prop : @EqDec_eq prop.
Proof. exact eq_prop_dec. Defined.

Lemma prop_dual_involutive: forall A,
  A = ¬(¬A).
Proof.
  induction A; simpl; f_equal; auto.
Qed.

Lemma prop_dual_self: forall A,
  dual_props A (¬A).
Proof. induction A; ss; eauto. Qed.

Lemma prop_dual_equiv_dual_props : forall A dA
    (DUA: dual_props A dA),
  dA = ¬A.
Proof. ii; induction DUA; subst; auto using prop_dual_involutive. Qed.

Lemma dual_props_equiv_prop_dual : forall A dA
    (DUA: dA = ¬A),
  dual_props A dA.
Proof. ii. induction A; ss; rewrite DUA; eauto using prop_dual_self. Qed.

Lemma prop_dual_iff: forall A dA,
  dA = ¬A <-> dual_props A dA.
Proof.
  ii; split; auto using prop_dual_equiv_dual_props,
                        dual_props_equiv_prop_dual.
Qed.

Lemma prop_dual_eq: forall A B
    (EQ: ¬A = ¬B),
  A = B.
Proof.
  ii; induction A; by rewrite ->prop_dual_iff in EQ; apply dual_sym in EQ
  ; rewrite <-prop_dual_iff in EQ; rewrite <-!prop_dual_involutive in EQ
  ; subst; reflexivity.
Qed.

(** Substitution of proposition [A] for [X] in [B] is denoted by
    {{ A // X }} B -- double syntax used to get Coq to accept it. *)
Reserved Notation "'{{' A '//' X '}}' B" (at level 46, left associativity).

(** The following definition of substitution for a free propositional variable
    assumes the term to be substituted is locally closed.
*)
Fixpoint prop_subst (x: atom) (u: prop) (pp: prop) : prop :=
  match pp with
  | pp_var v
    => match v with
       | pvar_fvar y => if x == y then u else pp
       | _ => pp
       end
  | pp_dvar v
    => match v with
       | pvar_fvar y => if x == y then ¬u else pp
       | _ => pp
       end
  | A ⨂ B => {{ u // x }} A ⨂ {{ u // x }} B
  | A ⅋ B => {{ u // x }} A ⅋ {{ u // x }} B
  | A ⨁ B => {{ u // x }} A ⨁ {{ u // x }} B
  | A & B => {{ u // x }} A & {{ u // x }} B
  | ! A => ! {{ u // x }} A
  | ? A => ? {{ u // x }} A
  | pp_forall A => pp_forall ({{ u // x }} A)
  | pp_exists A => pp_exists ({{ u // x }} A)
  | _ => pp
  end
where "'{{' A '//' X '}}' B" := (prop_subst X A B) : cp_scope.

(** Opening a prop pp is replacing an unbound prop variable with index k with
    free propositional variable u.
*)
Fixpoint prop_open_rec (k: nat) (u: atom) (pp: prop) :=
  match pp with
  | pp_var v
    => match v with
       | pvar_bvar n => if k == n then pp_var u else pp
       | _ => pp
       end
  | pp_dvar v
    => match v with
       | pvar_bvar n => if k == n then pp_dvar u else pp
       | _ => pp
       end
  | A ⨂ B => (prop_open_rec k u A) ⨂ (prop_open_rec k u B)
  | A ⅋ B => (prop_open_rec k u A) ⅋ (prop_open_rec k u B)
  | A ⨁ B => (prop_open_rec k u A) ⨁ (prop_open_rec k u B)
  | A & B => (prop_open_rec k u A) & (prop_open_rec k u B)
  | ! A => ! (prop_open_rec k u A)
  | ? A => ? (prop_open_rec k u A)
  | pp_forall A => pp_forall (prop_open_rec (S k) u A)
  | pp_exists A => pp_exists (prop_open_rec (S k) u A)
  | _ => pp
  end.

Definition open_prop t u := prop_open_rec 0 u t.

Lemma prop_dual_preserves_subst: forall A B X,
  ¬({{A // X}}B) = {{A // X}}(¬B).
Proof.
  intros; induction B; simpl; f_equal; auto; destruct p; auto
  ; match goal with
    | |- context[?X == ?Y] => destruct (X == Y)
    end; auto using prop_dual_involutive.
Qed.

(** Names within processes; represent channel identifiers. *)
Inductive pname : Set :=
  | p_bn : nat -> pname
  | p_fn : atom -> pname.

Coercion p_bn : nat >-> pname.
Coercion p_fn : atom >-> pname.

(** Definition of a processes ranged over by P, Q and R. *)
Inductive proc : Set :=
  | p_link : pname -> pname -> proc
  | p_par : prop -> proc -> proc -> proc
  | p_output : pname -> prop -> proc -> proc -> proc
  | p_input : pname -> prop -> proc -> proc
  | p_left : pname -> proc -> proc
  | p_right : pname -> proc -> proc
  | p_choice : pname -> proc -> proc -> proc
  | p_accept : pname -> prop -> proc -> proc
  | p_request : pname -> prop -> proc -> proc
  | p_send : pname -> prop -> proc -> proc
  | p_recv : pname -> proc -> proc
  | p_empout : pname -> proc
  | p_empin : pname -> proc -> proc
  | p_empcho : pname -> proc.

Hint Constructors proc.

(** Some helpful notations. *)
Notation "x ⟷ y" := (p_link x y) (at level 68) : cp_scope.
Notation "'ν' A '→' P '‖' Q" := (p_par A P Q) (at level 68, x ident,
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
Notation "'[' A ']' x '→' P '‖' Q" := (p_output x A P Q) (at level 68,
                                                          right associativity)
                                                         : cp_scope.
(** We use ⟨⟩ instead of () in the input cases. *)
Notation "'⟨' A '⟩' x '→' P" := (p_input x A P) (at level 68,
                                                right associativity)
                                                : cp_scope.

Notation "x '[inl]' → P" := (p_left x P) (at level 68,
                                          right associativity) : cp_scope.
Notation "x '[inr]' → P" := (p_right x P) (at level 68,
                                          right associativity) : cp_scope.
Notation "x 'CASE' P 'OR' Q" := (p_choice x P Q) (at level 68,
                                                  right associativity)
                                                 : cp_scope.
Notation "'!' '⟨' A '⟩' x → P" := (p_accept x A P) (at level 68,
                                                    right associativity)
                                                   : cp_scope.
Notation "'?' '[' A ']' x → P" := (p_request x A P) (at level 68,
                                                     right associativity)
                                                    : cp_scope.
Notation "x '→' 0" := (p_empout x) (at level 68) : cp_scope.
Notation "⟨⟩ x → P" := (p_empin x P) (at level 68,
                                      right associativity) : cp_scope.
Notation "x 'CASE' 0" := (p_empcho x) (at level 68) : cp_scope.

(** Example using some notations (demonstrates the right associativity of the
    rules):

Parameter x y: atom.
Check ν x : (pp_var 0) ⨁ (pp_var 1) → x ⟷ y | x → 0.

*)

(** The following definition of substitution for a free name
    assumes the term to be substituted is locally closed.
*)
Fixpoint proc_subst (x y: atom) (p: proc) : proc :=
  let
    sub := fun u => match u with
                    | p_fn z => if z == x then y else u
                    | _ => u
                    end
  in
    match p with
    | w ⟷ z => sub w ⟷ sub z
    | ν A → P ‖ Q => ν A → (proc_subst x y P) ‖ (proc_subst x y Q)
    | [A] z → P ‖ Q => [A] (sub z) → (proc_subst x y P) ‖ (proc_subst x y Q)
    | ⟨A⟩ z → P => ⟨A⟩ (sub z) → (proc_subst x y P)
    | z [inl] → P => (sub z) [inl] → (proc_subst x y P)
    | z [inr] → P => (sub z) [inr] → (proc_subst x y P)
    | z CASE P OR Q => (sub z) CASE (proc_subst x y P) OR (proc_subst x y Q)
    | ! ⟨A⟩ z → P => ! ⟨A⟩ (sub z) → (proc_subst x y P)
    | ? [A] z → P => ? [A] (sub z) → (proc_subst x y P)
    | p_send z A P => p_send (sub z) A (proc_subst x y P)
    | p_recv z P => p_recv (sub z) (proc_subst x y P)
    | z → 0 => (sub z) → 0
    | ⟨⟩ z → P => ⟨⟩ (sub z) → (proc_subst x y P)
    | z CASE 0 => (sub z) CASE 0
    end.

Notation "[ x ~> y ] P" := (proc_subst x y P) (at level 68) : cp_scope.

(** Opening a proc p is replacing an unbound name with index k with
    free name x.
*)
Fixpoint proc_open_rec (k: nat) (x: atom) (p: proc) :=
  let
    sub := fun u => match u with
                    | p_bn n => if n == k then p_fn x else u
                    | _ => u
                    end
  in
    match p with
    | w ⟷ z => sub w ⟷ sub z
    | ν A → P ‖ Q
      => ν A → (proc_open_rec (S k) x P) ‖ (proc_open_rec (S k) x Q)
    | [A] z → P ‖ Q
      => [A] (sub z) → (proc_open_rec (S k) x P) ‖ (proc_open_rec (S k) x Q)
    | ⟨A⟩ z → P => ⟨A⟩ (sub z) → (proc_open_rec (S k) x P)
    | z [inl] → P => (sub z) [inl] → (proc_open_rec k x P)
    | z [inr] → P => (sub z) [inr] → (proc_open_rec k x P)
    | z CASE P OR Q
      => (sub z) CASE (proc_open_rec k x P) OR (proc_open_rec k x Q)
    | ! ⟨A⟩ z → P => ! ⟨A⟩ (sub z) → (proc_open_rec (S k) x P)
    | ? [A] z → P => ? [A] (sub z) → (proc_open_rec (S k) x P)
    | p_send z A P => p_send (sub z) A (proc_open_rec k x P)
    | p_recv z P => p_recv (sub z) (proc_open_rec k x P)
    | z → 0 => sub z → 0
    | ⟨⟩ z → P => ⟨⟩ (sub z) → (proc_open_rec k x P)
    | z CASE 0 => (sub z) CASE 0
    end.

Notation "{ k ~> u } t" := (proc_open_rec k u t) (at level 68) : cp_scope.

Definition open_proc P x := proc_open_rec 0 x P.
Notation "P ^^ x" := (open_proc P x) (at level 68) : cp_scope.

Hint Unfold open_proc.

(** Environments for the process calculus are mappings of atoms to
    propositions. *)
Definition penv := list (atom * prop).

(** Encoding an environment as all requests; for the server accept process
    rule. *)
Inductive all_requests : penv -> Prop :=
  | all_requests_nil : all_requests nil
  | all_requests_cons : forall Γ x A (REQS: all_requests Γ),
                          all_requests (Γ ++ (x ~ ? A)).

(** Locally closed processes. *)
Inductive lc_proc : proc -> Prop :=
  | lc_p_fwd : forall (w x:atom), lc_proc (w ⟷ x)
  | lc_p_cut : forall (L:atoms) P Q A
                    (COP: forall (x:atom) (NL: x `notin` L),
                            lc_proc (open_proc P x))
                    (COQ: forall (x:atom) (NL: x `notin` L),
                            lc_proc (open_proc Q x)),
               lc_proc (ν A → P ‖ Q)
  | lc_p_output : forall (L:atoms) P Q (x:atom) A
                         (COP: forall (y:atom) (NL: y `notin` L),
                                 lc_proc (open_proc P y))
                         (COQ: forall (y:atom) (NL: y `notin` L),
                                 lc_proc (open_proc Q y)),
                    lc_proc ([A]x → P ‖ Q)
  | lc_p_input : forall (L:atoms) P (x:atom) A
                        (COP: forall (y:atom) (NL: y `notin` L),
                                lc_proc (open_proc P y)),
                   lc_proc (⟨A⟩x → P)
  | lc_p_left : forall P (x:atom) (COP: lc_proc P),
                  lc_proc (x[inl] → P)
  | lc_p_right : forall P (x:atom) (COP: lc_proc P),
                   lc_proc (x[inr] → P)
  | lc_p_choice : forall P Q (x:atom) (COP: lc_proc P) (COQ: lc_proc Q),
                    lc_proc (x CASE P OR Q)
  | lc_p_accept : forall (L:atoms) P (x:atom) A
                         (COP: forall (y:atom) (NL: y `notin` L),
                                 lc_proc (open_proc P y)),
                    lc_proc (! ⟨A⟩ x → P)
  | lc_p_request : forall (L:atoms) P (x:atom) A
                          (COP: forall (y:atom) (NL: y `notin` L),
                                  lc_proc (open_proc P y)),
                     lc_proc (? [A] x → P)
  | lc_p_send : forall P (x:atom) A (COP: lc_proc P), lc_proc (p_send x A P)
  | lc_p_recv : forall P (x:atom) (COP: lc_proc P), lc_proc (p_recv x P)
  | lc_p_empout : forall (x:atom), lc_proc (x → 0)
  | lc_p_empin : forall P (x:atom) (COP: lc_proc P), lc_proc (⟨⟩ x → P)
  | lc_p_empcho : forall (x:atom), lc_proc (x CASE 0).

Hint Constructors lc_proc.

Reserved Notation "P '⊢cp' Γ" (at level 69).

(** The uniqueness assumption is necessary to ensure environments are only
    combined if they contain distinct names.
    Note in some cases we utilise cofinite quantification to provide a
    suitably fresh name for some channels. Some cases could be written as
    x `notin` Γ for some x, Γ but I elected to maintain uniq assumptions
    wherever possible to keep the development symmetrical (in theory, this
    could help proofs since all rules follow a similar structure).
*)
Inductive cp_rule : proc -> penv -> Prop :=
  | cp_fwd : forall (x w: atom) A (NEQ: x <> w),
               w ⟷ x ⊢cp ((w ~ ¬ A) ++ (x ~ A))
  | cp_cut : forall (L:atoms) P Q A Γ Δ
                    (UN: uniq (Γ ++ Δ))
                    (CPP: forall (x:atom) (NL: x `notin` L),
                            (open_proc P x) ⊢cp Γ ++ (x ~ A))
                    (CPQ: forall (x:atom) (NL: x `notin` L),
                            (open_proc Q x) ⊢cp Δ ++ (x ~ ¬A)),
               ν A → P ‖ Q ⊢cp Γ ++ Δ
  | cp_output : forall (L:atoms) P Q Γ Δ x A B
                       (UN: uniq (Γ ++ Δ ++ (x ~ A ⨂ B)))
                       (CPP: forall (y:atom) (NL: y `notin` L),
                               (open_proc P y) ⊢cp Γ ++ (y ~ A))
                       (CPQ: Q ⊢cp Δ ++ (x ~ B)),
                  [A]x → P ‖ Q ⊢cp Γ ++ Δ ++ (x ~ A ⨂ B)
  | cp_input : forall (L:atoms) P Γ x A B
                      (CPP: forall (y:atom) (NL: y `notin` L),
                              (open_proc P y) ⊢cp Γ ++ (y ~ A) ++ (x ~ B)),
                 ⟨A⟩x → P ⊢cp Γ ++ (x ~ A ⅋ B)
  | cp_left : forall P Γ x A B
                     (CPP: P ⊢cp Γ ++ (x ~ A)),
                x[inl] → P ⊢cp Γ ++ (x ~ A ⨁ B)
  | cp_right : forall P Γ x A B
                     (CPP: P ⊢cp Γ ++ (x ~ B)),
                x[inr] → P ⊢cp Γ ++ (x ~ A ⨁ B)
  | cp_choice : forall P Q Γ x A B
                       (CPP: P ⊢cp Γ ++ (x ~ A))
                       (CPQ: Q ⊢cp Γ ++ (x ~ B)),
                  x CASE P OR Q ⊢cp Γ ++ (x ~ A & B)
  | cp_accept : forall (L:atoms) P Γ (x:atom) A
                       (REQS: all_requests Γ)
                       (UN: uniq (Γ ++ (x ~ ! A)))
                       (CPP: forall (y:atom) (NL: y `notin` L),
                               (open_proc P y) ⊢cp Γ ++ (y ~ A)),
                  ! ⟨A⟩ x → P ⊢cp Γ ++ (x ~ ! A)
  | cp_request : forall (L:atoms) P Γ (x:atom) A
                        (UN: uniq (Γ ++ (x ~ ? A)))
                        (CPP: forall (y:atom) (NL: y `notin` L),
                                (open_proc P y) ⊢cp Γ ++ (y ~ A)),
                   ? [A] x → P ⊢cp Γ ++ (x ~ ? A)
  | cp_send : forall (L:atoms) Γ P x A B
                     (CPP: forall (y:atom) (NL: y `notin` L),
                             P ⊢cp Γ ++ x ~ {{ A // y }} (open_prop B y)),
                p_send x A P ⊢cp Γ ++ x ~ pp_exists B
  | cp_recv : forall (L:atoms) Γ P x B
                     (CPP: forall (y:atom) (NL: y `notin` L),
                             P ⊢cp Γ ++ x ~ (open_prop B y)),
                p_recv x P ⊢cp Γ ++ x ~ pp_forall B
  | cp_empout : forall (x: atom), x → 0 ⊢cp (x ~ pp_one)
  | cp_empin : forall P Γ (x:atom) (CPP: P ⊢cp Γ)
                      (UN: uniq (Γ ++ (x ~ pp_bot))),
                 ⟨⟩ x → P ⊢cp Γ ++ (x ~ pp_bot)
  | cp_empcho : forall Γ (x:atom) (UN: uniq (Γ ++ (x ~ pp_top))),
                  x CASE 0 ⊢cp Γ ++ (x ~ pp_top)
where "P '⊢cp' Γ" := (cp_rule P Γ) : cp_scope.

(** Example presented in journal version of ``Propositions as Sessions''.

    We have a buyer/seller example where the client (buyer) sends a product
    name and payment details to a seller and the seller will send a receipt.

TODO: Will only work once I've abstracted away binders in the cp_rules:

Definition buyer :=
  [Name] 0 →
        (1 .. output name 
        | [Credit] 0 → (output credit ... | ⟨ Receipt ⟩ 0 → ⟨⟩ 0 → ...))

*)

Lemma cp_implies_uniq: forall Γ P
    (CP: P ⊢cp Γ),
  uniq Γ.
Proof.
  ii; induction CP; auto; try solve_uniq
  ; by pick fresh y; destruct_notin; specialize (H _ Fr); solve_uniq.
Qed.

Reserved Notation "P '==>cp' Q" (at level 69, right associativity).

Inductive fresh_enough : atom -> proc -> Prop :=
  | fr_enough : forall (L:atoms) (w:atom) (P:proc) (FR: w `notin` L),
                  fresh_enough w P.

Inductive proc_red : proc -> proc -> Prop :=
  | redp_axcut : forall P A dA (w x:atom) (DUA: dual_props A dA),
                   ν A → w ⟷ 0 ‖ P ==>cp (open_proc P w)
where "P '==>cp' Q" := (proc_red P Q) : cp_scope.

Lemma axiom_env: forall Γ (w x:atom)
    (NEQ: w <> x)
    (WT: w ⟷ x ⊢cp Γ),
  exists A, Γ = ((w ~ ¬ A) ++ (x ~ A)).
Proof.
  ii; inversion WT; subst; eexists; simpl_env; eauto.
(*
subst; destruct_binds_hyp BW; [|exfalso; auto using NEQ0].
  destruct_binds_hyp BX; [exfalso; auto using NEQ0|]; clear.
  simpl_env; reflexivity.*)
Qed.

Lemma env_not_match: forall {A B} (Γ:list(A*B)) Δ y A dA
    (EQ: Γ ++ (y ~ A) = Δ ++ y ~ dA)
    (NEQ: A <> dA),
  False.
Proof.
  ii; apply app_inj_tail in EQ; des; inversion EQ1; auto.
Qed.

Lemma ignore_env_order: forall Γ Δ P
    (INB: forall x A, binds x A Γ <-> binds x A Δ)
    (WT: P ⊢cp Γ),
  P ⊢cp Δ.
Proof.
Admitted.

Theorem proc_sub_red: forall Γ P Q
    (WT: P ⊢cp Γ)
    (RED: P ==>cp Q),
  Q ⊢cp Γ.
Proof.
  ii; induction RED; subst; inversion WT; subst.
  pick fresh y; destruct_notin; specialize (CPP _ Fr).

  unfold open_proc in CPP; ss; apply axiom_env in CPP; auto.
  inversion CPP as [A' Fr'].
  destruct (A == A'); [|exfalso; apply env_not_match in Fr'; auto].

  subst; apply app_inv_tail in Fr'; subst.
  assert (NL: w `notin` L) by admit.
  apply CPQ in NL; apply ignore_env_order with (Γ := Δ ++ w ~ ¬A'); auto.
  split; ii; destruct_binds_hyp H; auto.
Qed.