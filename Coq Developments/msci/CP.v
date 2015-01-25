(** Beginning of the file for CP mechanisation as described in

    Philip Wadler. 2012. Propositions as sessions. In Proceedings of the 17th
    ACM SIGPLAN international conference on Functional programming (ICFP '12).
    ACM, New York, NY, USA, 273-286. DOI=10.1145/2364527.2364568
    http://doi.acm.org/10.1145/2364527.2364568

*)
Require Import Metatheory.Metatheory Tactics.
Require Import List Coq.Sorting.Permutation.

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

Lemma prop_eq_dual:
  forall A (EQ: A = ¬A),
    False.
Proof. ii; induction A; ss; tryfalse. Qed.

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

Fixpoint fv_proc (p : proc) : atoms :=
  let
    fv := fun u => match u with
                   | p_fn z => singleton z
                   | _ => empty
                   end
  in
    match p with
    | w ⟷ z => fv w `union` fv z
    | ν A → P ‖ Q => fv_proc P `union` fv_proc Q
    | [A] z → P ‖ Q => fv z `union` fv_proc P `union` fv_proc Q
    | ⟨A⟩ z → P => fv z `union` fv_proc P
    | z [inl] → P => fv z `union` fv_proc P
    | z [inr] → P => fv z `union` fv_proc P
    | z CASE P OR Q => fv z `union` fv_proc P `union` fv_proc Q
    | ! ⟨A⟩ z → P => fv z `union` fv_proc P
    | ? [A] z → P => fv z `union` fv_proc P
    | p_send z A P => fv z `union` fv_proc P
    | p_recv z P => fv z `union` fv_proc P
    | z → 0 => fv z
    | ⟨⟩ z → P => fv z `union` fv_proc P
    | z CASE 0 => fv z
    end.

(** Environments for the process calculus are mappings of atoms to
    propositions. *)
Definition penv := list (atom * prop).

(** Encoding an environment as all requests; for the server accept process
    rule. *)
Inductive all_requests : penv -> Prop :=
  | all_reqs_nil : all_requests nil
  | all_reqs_cons : forall x A Γ (REQS: all_requests Γ),
                          all_requests ((x ~ ? A) ++ Γ).

Hint Constructors all_requests.

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

    The proof scripts use the location of the forall quantifiers to simplify
    application of the constructors. For example, the position of L as the
    first quantified variable is essential for the "pick fresh" tactics. In
    principle, one could change this by utilising the SFLibTactics.v applys
    et al. tactics. However, the position of the "all requests" environments
    Ω cannot be similar changed from the second position without having to
    place double underscores to miss out quantified variables of the same
    type. It remains to look for a syntactic/with construct to be use with
    Ltac.
*)
Inductive cp_rule : proc -> penv -> Prop :=
  | cp_fwd : forall Γ Ω (x w: atom) A
                    (PER: Permutation Γ (w ~ ¬A ++ x ~ A ++ Ω))
                    (UN: uniq Γ)
                    (REQS: all_requests Ω),
               w ⟷ x ⊢cp Γ
  | cp_cut : forall (L:atoms) P Q A Γ ΔP ΔQ
                    (PER: Permutation Γ (ΔP ++ ΔQ))
                    (UN: uniq Γ)
                    (CPP: forall (x:atom) (NL: x `notin` L),
                            (open_proc P x) ⊢cp (x ~ A) ++ ΔP)
                    (CPQ: forall (x:atom) (NL: x `notin` L),
                            (open_proc Q x) ⊢cp (x ~ ¬A) ++ ΔQ),
               ν A → P ‖ Q ⊢cp Γ
  | cp_output : forall (L:atoms) P Q Γ ΔP ΔQ x A B
                       (PER: Permutation Γ ((x ~ A ⨂ B) ++ ΔP ++ ΔQ))
                       (UN: uniq Γ)
                       (CPP: forall (y:atom) (NL: y `notin` L),
                               (open_proc P y) ⊢cp (y ~ A) ++ ΔP)
                       (CPQ: Q ⊢cp (x ~ B) ++ ΔQ),
                  [A]x → P ‖ Q ⊢cp Γ
  | cp_input : forall (L:atoms) P Γ ΔP x A B
                      (PER: Permutation Γ ((x ~ A ⅋ B) ++ ΔP))
                      (UN: uniq Γ)
                      (CPP: forall (y:atom) (NL: y `notin` L),
                           (open_proc P y) ⊢cp (y ~ A) ++ (x ~ B) ++ ΔP),
                 ⟨A⟩x → P ⊢cp Γ
  | cp_left : forall P Γ Δ x A B
                     (PER: Permutation Γ ((x ~ A ⨂ B) ++ Δ))
                     (CPP: P ⊢cp (x ~ A) ++ Δ),
                x[inl] → P ⊢cp Γ
  | cp_right : forall P Γ Δ x A B
                      (PER: Permutation Γ ((x ~ A ⨂ B) ++ Δ))
                      (CPP: P ⊢cp (x ~ B) ++ Δ),
                 x[inr] → P ⊢cp Γ
  | cp_choice : forall P Q Γ Δ x A B
                       (PER: Permutation Γ ((x ~ A & B) ++ Δ))
                       (CPP: P ⊢cp (x ~ A) ++ Δ)
                       (CPQ: Q ⊢cp (x ~ B) ++ Δ),
                  x CASE P OR Q ⊢cp Γ
  | cp_accept : forall (L:atoms) P Γ Δ (x:atom) A
                       (PER: Permutation Γ (x ~ ! A ++ Δ))
                       (REQSΓ: all_requests Δ)
                       (UN: uniq Γ)
                       (CPP: forall (y:atom) (NL: y `notin` L),
                               (open_proc P y) ⊢cp (y ~ A) ++ Δ),
                  ! ⟨A⟩ x → P ⊢cp Γ
  | cp_request : forall (L:atoms) P Γ Δ (x:atom) A
                        (PER: Permutation Γ (x ~ ? A ++ Δ))
                        (UN: uniq Γ)
                        (CPP: forall (y:atom) (NL: y `notin` L),
                                (open_proc P y) ⊢cp (y ~ A) ++ Δ),
                   ? [A] x → P ⊢cp Γ
  (* | cp_contract : forall P Γ (x x' x'':atom) A *)
  (*                        (UN: uniq (Γ ++ (x ~ ? A))) *)
  (*                        (CPP: P ⊢cp Γ ++ (x' ~ ? A) ++ (x'' ~ ? A)), *)
  (*                   [x' ~> x]([x'' ~> x]P) ⊢cp Γ ++ (x ~ ? A) *)
  | cp_send : forall (L:atoms) Γ Δ P x A B
                     (PER: Permutation Γ (x ~ pp_exists B ++ Δ))
                     (CPP: forall (y:atom) (NL: y `notin` L),
                           P ⊢cp x ~ {{ A // y }} (open_prop B y) ++ Δ),
                p_send x A P ⊢cp Γ
  | cp_recv : forall (L:atoms) Γ Δ P x B
                     (PER: Permutation Γ (x ~ pp_forall B ++ Δ))
                     (CPP: forall (y:atom) (NL: y `notin` L),
                             P ⊢cp x ~ (open_prop B y) ++ Δ),
                p_recv x P ⊢cp Γ
  | cp_empout : forall Ω Γ (x: atom)
                       (PER: Permutation Γ (x ~ pp_one ++ Ω))
                       (UN: uniq Γ)
                       (REQS: all_requests Ω),
                  x → 0 ⊢cp Γ
  | cp_empin : forall P Γ Δ (x:atom)
                      (PER: Permutation Γ (x ~ pp_bot ++ Δ))
                      (UN: uniq Γ)
                      (CPP: P ⊢cp Δ),
                 ⟨⟩ x → P ⊢cp Γ
  | cp_empcho : forall Γ Δ (x:atom)
                       (PER: Permutation Γ (x ~ pp_top ++ Δ))
                       (UN: uniq Γ),
                  x CASE 0 ⊢cp Γ
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

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * prop) => dom x) in
  let D := gather_atoms_with (fun x : proc => fv_proc x) in
  constr:(A `union` B `union` C `union` D).

Lemma cp_implies_uniq: forall Γ P
    (CP: P ⊢cp Γ),
  uniq Γ.
Proof.
  ii; induction CP; auto; try (by destruct_uniq; eauto)
  ; by pick fresh y; destruct_notin; specializes H Fr; destruct_uniq
  ; eauto.
Qed.

Lemma requests_one:
  forall x A,
    all_requests (x ~ ? A).
Proof. ii; apply* all_reqs_cons. Qed.

Lemma requests_app: forall xs ys
    (REQXS: all_requests xs)
    (REQYS: all_requests ys),
  all_requests (xs ++ ys).
Proof with auto.
  induction xs as [|x xs']...
  introv REQXS REQYS; inverts REQXS; simpl_env...
Qed.

Lemma requests_inv_app:
  forall xs ys
         (REQS: all_requests (xs++ys)),
    all_requests xs /\ all_requests ys.
Proof with auto.
  induction xs as [|x xs']...
  ii; inverts REQS; specializes IHxs' REQS0; des; splits; simpl_env...
Qed.

Lemma requests_perm:
  forall xs ys
         (PER: Permutation xs ys)
         (REQS: all_requests xs),
    all_requests ys.
Proof.
  i; induction PER; auto.
  - destruct x; rewrite !cons_app_one; inverts REQS; auto.
  - destruct x; destruct y; rewrite !cons_app_one; inverts REQS
    ; inverts REQS0; auto.
Qed.

Ltac des_reqs :=
  repeat match goal with
           | [H: all_requests (_ ++ _) |- _] =>
             apply requests_inv_app in H; des
         end.

Hint Resolve requests_one requests_app.

Lemma ignore_env_order: forall Γ Δ P
    (INB: Permutation Γ Δ)
    (WT: P ⊢cp Γ),
  P ⊢cp Δ.
Proof.
  ii; gen Δ; induction WT; ii; try (by econstructor; ss; eauto).
Qed.

Tactic Notation
  "obtain" "atoms" ident(atoms_name) "as" ident(H)
   :=    
     let L := gather_atoms in
     let L := beautify_fset L in
     set (atoms_name:=L); def_to_eq atoms_name H L.

Ltac bring_to_start X :=
  try (eapply Permutation_trans
       ; [|by repeat first [apply (Permutation_app_comm X _)
                           |apply Permutation_app_head]])
  ; first [apply Permutation_app_head
          |eapply Permutation_trans
           ; [| by repeat first [apply (three_way_perm X)
                                |apply Permutation_app_head]]
           ; bring_to_start X].

Ltac solve_perm :=
  by repeat first [rewrite <-!app_assoc
                  |rewrite !cons_app_one
                  |match goal with 
                       |- Permutation (?x ++ _) _ => bring_to_start x
                   end].

Lemma typing_weaken:
  forall Γ Δ E P
         (WT: P ⊢cp Γ ++ E) (UN: uniq(Γ ++ Δ ++ E))
         (REQS: all_requests Δ),
    P ⊢cp Γ ++ Δ ++ E.
Proof.
  ii; apply ignore_env_order with (Γ:=Γ++E++Δ)
  ; apply uniq_perm with (F:=Γ++E++Δ) in UN; try solve_perm
  ; rewrite app_assoc in *; induction WT; forwards~: uniq_perm_app PER UN.
  - eapply Permutation_app with (m:=Δ) in PER; auto. 
    apply Permutation_sym in PER; applys ignore_env_order PER.
    rewrite <-!app_assoc; eauto using cp_fwd.
  - obtain atoms L' as LEQ; applys cp_cut L' (ΔP++Δ) ΔQ
    ; i; substs; destruct_notin; auto.
    { eapply Permutation_trans; [apply Permutation_app|]; [exact PER|auto |].
      solve_perm. }
    { apply~ H; destruct_uniq; solve_uniq. }
  - obtain atoms L' as LEQ; applys cp_output L' (ΔP++Δ) ΔQ
    ; try (exact WT); i; substs; destruct_notin; auto.
    { eapply Permutation_trans; [apply Permutation_app|]; [exact PER|auto |].
      solve_perm. }
    { apply~ H; solve_uniq. }
  - obtain atoms L' as LEQ; applys cp_input L' (ΔP++Δ); i; substs
    ; destruct_notin; auto.
    { eapply Permutation_trans; [apply Permutation_app|]; [exact PER|auto |].
      solve_perm. }
    { apply~ H; solve_uniq. }
  - applys cp_left (Δ0++Δ); rewrite app_assoc
    ; [apply Permutation_app; [exact PER|auto]|]; []; apply IHWT; solve_uniq.
  - applys cp_right (Δ0++Δ); rewrite app_assoc
    ; [apply Permutation_app; [exact PER|auto]|]; []; apply IHWT; solve_uniq.
  - applys cp_choice (Δ0++Δ); rewrite app_assoc
    ; [apply Permutation_app; [exact PER|auto]| |]
    ; by first [apply IHWT1 | apply IHWT2]; solve_uniq.
  - obtain atoms L' as LEQ; applys cp_accept L' (Δ0++Δ); i; substs
    ; destruct_notin; auto.
    { eapply Permutation_trans; [apply Permutation_app|]; [exact PER|auto |].
      solve_perm. }
    { apply~ H; solve_uniq. }
  - obtain atoms L' as LEQ; applys cp_request L' (Δ0++Δ); i; substs
    ; destruct_notin; auto.
    { eapply Permutation_trans; [apply Permutation_app|]; [exact PER|auto |].
      solve_perm. }
    { apply~ H; solve_uniq. }
  - obtain atoms L' as LEQ; applys cp_send L' (Δ0++Δ); i; substs
    ; destruct_notin; auto.
    { eapply Permutation_trans; [apply Permutation_app|]; [exact PER|auto |].
      solve_perm. }
    { apply~ H; solve_uniq. }
  - obtain atoms L' as LEQ; applys cp_recv L' (Δ0++Δ); i; substs
    ; destruct_notin; auto.
    { eapply Permutation_trans; [apply Permutation_app|]; [exact PER|auto |].
      solve_perm. }
    { apply~ H; solve_uniq. }
  - applys cp_empout (Ω++Δ); eauto.
  - applys~ cp_empin (Δ0++Δ); try rewrite app_assoc
    ; [apply Permutation_app; [exact PER|auto]|]; []; apply IHWT; solve_uniq.
   - applys cp_empcho (Δ0++Δ); substs~; rewrite !app_assoc
     ; apply Permutation_app; [exact PER|auto].
Qed.

Lemma cp_weaken:
  forall P Γ x A
         (UN: uniq (Γ ++ x ~ ? A))
         (WT: P ⊢cp Γ),
    P ⊢cp Γ ++ (x ~ ? A).
Proof. ii; apply typing_weaken with (Δ:=x~? A); simpl_env; auto. Qed.

Lemma cp_strengthen:
  forall P Γ x A
         (UN: uniq (Γ ++ x ~ ? A))
         (WT: P ⊢cp Γ ++ x ~ ? A),
    P ⊢cp Γ.
Proof.
Admitted.

Lemma perm_dom_uniq:
  forall Γ Δ1 Δ2 x (A B:prop)
         (UN: uniq (Γ++x~A))
         (PER: Permutation (Γ++x~A) (Δ1++x~B++Δ2)),
    Permutation Γ (Δ1++Δ2).
Proof.
  intros; forwards UN1: uniq_perm PER; [solve_uniq|].
  eapply uniq_perm in UN; [|apply Permutation_app_comm].
  inv UN1; inv UN; destruct (B == A); substs~.
  - rewrite <-H0 in *; apply Permutation_sym,Permutation_nil in PER.
    apply app_eq_nil in PER; des; substs~. eauto.
    rewrite !cons_app_one in *; apply nil_eq_app in H0; des.
    apply app_eq_nil in H3; des; substs~; auto.
  - rewrite <-H0 in *; apply Permutation_sym,Permutation_nil in PER.
    apply app_eq_nil in PER; des; substs~. eauto.
    rewrite !cons_app_one in *; apply nil_eq_app in H0; des.
    apply app_eq_nil in H3; des; substs~; auto.
  - eapply Permutation_trans in PER; [|apply Permutation_app_comm].
    applys~ Permutation_cons_app_inv PER.
  - apply Permutation_in with (x:=(x,A)) in PER
    ; [|apply in_or_app; s; branch~ 2].
    apply in_app_or in PER; des; [|ss; des; [inv PER0|]; exfalso; eauto]
    ; by match goal with
           | [H: In (?x,?A) ?E |- _] =>
             let E1 := fresh "E" in
             let E2 := fresh "E" in
             apply binds_env_split in H; inversion_clear H as (E1 & E2 & ?)
             ; substs~; destruct_uniq; solve_notin
         end.
Qed.

Lemma perm_cod_uniq:
  forall Γ Δ1 Δ2 x (A B:prop)
         (UN: uniq (Γ++x~A))
         (PER: Permutation (Γ++x~A) (Δ1++x~B++Δ2)),
    A = B.
Proof.
  intros; forwards UN1: uniq_perm PER; [solve_uniq|].
  eapply uniq_perm in UN; [|apply Permutation_app_comm].
  inv UN1; inv UN; destruct (B == A); substs~.
  - rewrite <-H0 in *; apply Permutation_sym,Permutation_nil in PER.
    apply app_eq_nil in PER; des; tryfalse.
  - apply Permutation_in with (x:=(x,A)) in PER
    ; [|apply in_or_app; s; branch~ 2].
    apply in_app_or in PER; des; [|ss; des; [inv PER0|]; exfalso; eauto]
    ; by match goal with
           | [H: In (?x,?A) ?E |- _] =>
             let E1 := fresh "E" in
             let E2 := fresh "E" in
             apply binds_env_split in H; inversion_clear H as (E1 & E2 & ?)
             ; substs~; destruct_uniq; solve_notin
         end.
Qed.

Lemma open_fv_proc:
  forall x y k P
         (NEQ: x <> y)
         (FV: x `notin` fv_proc ({k ~> y}P)),
    x `notin` fv_proc P.
Proof.
  i; gen k; induction P; ii; solve [ii; destruct_notin; destruct_in; eauto
                                   | destruct_all pname; fsetdec].
Qed.

Hint Resolve open_fv_proc.

Lemma fv_env_proc:
  forall Γ P x
         (FV: x `notin` dom Γ)
         (WT: P ⊢cp Γ),
    x `notin` fv_proc P.
Proof.
  i; induction WT
  ; try (by ii; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER
         ; auto
         ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
         ; s; fsetdec).
  - ii; destruct_in; pick fresh y; destruct_notin. 
    + apply (@open_fv_proc x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; auto.
      apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
    + apply (@open_fv_proc x y 0) in H3; auto.
      ii; apply (H0 y); auto; ii; destruct_in; auto.
      apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_fv_proc x y 0) in H0; auto.
      ii; apply (H y); auto; ii; destruct_in; auto.
      apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
    + apply IHWT; auto; i.
      apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_fv_proc x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; substs~
      ; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_fv_proc x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; substs~
      ; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_fv_proc x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; substs~
      ; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_fv_proc x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; substs~
      ; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_fv_proc x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; substs~
      ; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  Qed.

Section CPBasicSubstOpenProperties.

  Lemma open_rec_same :
    forall t j v i u
           (NEQ: i <> j)
           (EQ: {i ~> u}({j ~> v} t) = {j ~> v} t),
      {i ~> u} t = t.
  Proof.
    induction t; ii; des; subst; solve [exfalso; auto
                                       |f_equal; inversion EQ; firstorder].
  Qed.

  Lemma lc_no_bvar:
    forall t u k
           (LC: lc_proc t),
      {k ~> u}t = t.
  Proof.
    ii; generalize dependent k; induction LC; s; ii; f_equal; auto
    ; try (by unfold open_proc in *; pick fresh z for L
           ; apply open_rec_same with (j := 0)(v := z); auto).
  Qed.

  Lemma lc_open_subst:
    forall t u (x y: atom) k
           (NEQ: x <> y),
      {k ~> y} ([x ~> u]t) = [x ~> u]({k ~> y} t).
  Proof.
    ii; unfold open_proc; generalize dependent k.
    induction t; by ii; destruct_all pname; des; subst; f_equal; auto.
  Qed.

  Lemma subst_fresh:
    forall (x:atom) u t
           (NIN: x `notin` fv_proc t),
      [x ~> u]t = t.
  Proof.
    induction t; ii; try (destruct_all pname; des; subst; f_equal
                          ; solve [auto | fsetdec]).
  Qed.

  Lemma subst_open_var :
    forall (x y : atom) u t
           (NEQ: y <> x),
      open_proc ([x ~> u] t) y = [x ~> u] (open_proc t y).
  Proof.
    ii; unfold open_proc; auto using lc_open_subst.
  Qed.

  Lemma subst_intro :
    forall (x : atom) u t
           (NIN: x `notin` (fv_proc t)),
      open_proc t u = [x ~> u](open_proc t x).
  Proof.
    ii; unfold open_proc; generalize 0.
    induction t; intros bv; ss; try (destruct_all pname; des; subst; f_equal
                                     ; solve [auto | fsetdec]).
  Qed.

  Lemma subst_id:
    forall (x:atom) t,
      [x ~> x]t = t.
  Proof.
    induction t; ss; try (destruct_all pname; des; substs; f_equal
                                     ; solve [auto | fsetdec]).
  Qed.

  Ltac subst_lc_tac Constructor :=
    pick fresh y and apply Constructor
    ; by unfold open_proc in *; rewrite lc_open_subst; auto.

  Lemma subst_lc :
    forall t u x
           (LCT: lc_proc t),
      lc_proc ([ x ~> u ] t).
  Proof.
    ii; induction LCT; s; des; subst; auto
    ; solve [subst_lc_tac lc_p_cut
            |subst_lc_tac lc_p_output
            |subst_lc_tac lc_p_input
            |subst_lc_tac lc_p_accept
            |subst_lc_tac lc_p_request].
  Qed.

  Lemma requests_binds_cod:
    forall (x:atom) A Ω
           (REQS: all_requests Ω)
           (BNDS: binds x A Ω),
    exists B, A = ? B.
  Proof.
    ii; induction REQS; analyze_binds BNDS; eauto.
  Qed.

  Lemma typing_subst_fwd:
    forall Γ Ω w x y z A B
           (UNY: uniq (Γ ++ y ~ A))
           (UNX: uniq (Γ ++ z ~ A))
           (REQS: all_requests Ω)
           (PER: Permutation (Γ ++ z ~ A) (w ~ ¬B ++ x ~ B ++ Ω)),
      [z ~> y](w ⟷ x) ⊢cp Γ ++ y ~ A.
  Proof.
    ii; des; substs.
    - apply uniq_perm in PER; auto; []; inv PER; ss; substs; fsetdec.
    - apply cp_fwd with (A:=¬A)(Ω:=Ω); first [auto|solve_uniq].
      rewrite <-prop_dual_involutive.
      rewrite cons_app_one in PER; rewrite <- app_nil_l in PER
      ; forwards EQ: perm_cod_uniq PER; apply perm_dom_uniq in PER; substs~.
      eapply Permutation_trans; [apply Permutation_app|]; [exact PER|auto|].
      rewrite <-prop_dual_involutive; solve_perm.
    - apply cp_fwd with (A:=A)(Ω:=Ω); first [auto|solve_uniq].
      rewrite !cons_app_one in *.
      forwards EQ: perm_cod_uniq PER; apply perm_dom_uniq in PER; substs~.
      eapply Permutation_trans; [apply Permutation_app|]; [exact PER|auto|].
      solve_perm.
    - forwards~ PER2: Perm_binds z A PER; analyze_binds PER2.
      forwards~ EQC: requests_binds_cod BindsTac0
      ; apply binds_env_split in BindsTac0
      ; inversion_clear BindsTac0 as (E1 & E2 & ?); inversion EQC as (A0)
      ; substs~.
      rewrite !cons_app_one,2 app_assoc in PER; apply perm_dom_uniq in PER
      ; [|solve_uniq]; des_reqs.
      apply cp_fwd with (A:=B)(Ω:=E1++E2++y~? A0); auto.
      eapply Permutation_trans; [apply Permutation_app|]; [eassumption|auto|].
      solve_perm.
  Qed.

  Lemma typing_subst:
    forall Γ P (x y:atom) A
           (NINX: uniq (Γ ++ y ~ A))
           (WT: P ⊢cp Γ ++ (x ~ A)),
      [x ~> y]P ⊢cp Γ ++ (y ~ A).
  Proof.
    ii; destruct (x == y); substs; [by rewrite subst_id|].
    remember (Γ++x~A) as Γ'; assert (PER: Permutation Γ' (Γ++x~A)) by substs~.
    clear HeqΓ'; gen A Γ; induction WT; i; substs~.
    - applys* typing_subst_fwd.
    - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
      forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
      ; forwards~ BNDS: Perm_binds x A0 PER.
      analyze_binds_uniq BNDS; try rewrite !dom_app in *; destruct_notin
      ; apply binds_env_split in BindsTac
      ; inversion_clear BindsTac as (Γ1 & Γ2 & EQ); substs~
      ; [rewrite <-!app_assoc in *|rewrite app_assoc in *]
      ; apply perm_dom_uniq in PER; auto; s; obtain atoms L' as LEQ.
      + eapply cp_cut with (L:=L')(ΔP:=Γ1++Γ2++y~A0)(ΔQ:=ΔQ)
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite~ subst_open_var; rewrite cons_app_one.
          rewrite !app_assoc; apply~ H; rewrite <-!app_assoc; try solve_perm.
          apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX.
          destruct_uniq; solve_uniq. }
        { specializes CPQ NL; forwards FV: fv_env_proc x CPQ; [solve_notin|].
          rewrite* subst_fresh. }
      + eapply cp_cut with (L:=L')(ΔP:=ΔP)(ΔQ:=Γ1++Γ2++y~A0)
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|].
          solve_perm. }
        { specializes CPP NL; forwards FV: fv_env_proc x CPP; [solve_notin|].
          rewrite* subst_fresh. }
        { rewrite~ subst_open_var; rewrite cons_app_one.
          rewrite !app_assoc; apply~ H0; rewrite <-!app_assoc; try solve_perm.
          apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX.
          destruct_uniq; solve_uniq. }
    - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
      forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
      ; forwards~ BNDS: Perm_binds x A0 PER.
      analyze_binds_uniq BNDS; try rewrite !dom_app in *; destruct_notin.
      + s; des; clear H1; rewrite <-app_nil_l in PER
        ; apply perm_dom_uniq in PER; auto; ss; obtain atoms L' as LEQ
        ; eapply cp_output with (L:=L')(ΔP:=ΔP)(ΔQ:=ΔQ); ii; substs~
        ; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { specializes CPP NL; forwards~ FV: fv_env_proc x0 CPP
          ; rewrite* subst_fresh. }
        { rewrite !cons_app_one.
          eapply ignore_env_order; [apply Permutation_app_comm|].
          forwards UNX: uniq_perm_app PER NINX.
          apply~ IHWT; [destruct_uniq; solve_uniq|solve_perm]. }
      + apply binds_env_split in BindsTac0
        ; inversion_clear BindsTac0 as (Γ1 & Γ2 & EQ); substs~.
        rewrite <-!app_assoc in *; rewrite app_assoc in *.
        apply perm_dom_uniq in PER; auto; ss; obtain atoms L' as LEQ.
        destruct_notin; destruct (x0 == x); tryfalse.
        clear n0; eapply cp_output with (L:=L')(ΔP:=Γ1++Γ2++y~A0)(ΔQ:=ΔQ)
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite~ subst_open_var; rewrite cons_app_one.
          rewrite !app_assoc; apply~ H; rewrite <-!app_assoc; try solve_perm.
          apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX.
          destruct_uniq; solve_uniq. }
        { rewrite~ subst_fresh; forwards~ FV: fv_env_proc x WT. }
      + apply binds_env_split in BindsTac0
        ; inversion_clear BindsTac0 as (Γ1 & Γ2 & EQ); substs~.
        rewrite 2 app_assoc in *; apply perm_dom_uniq in PER; auto; ss
        ; obtain atoms L' as LEQ; destruct_notin; destruct (x0 == x)
        ; tryfalse.
        clear n0; eapply cp_output with (L:=L')(ΔP:=ΔP)(ΔQ:=Γ1++Γ2++y~A0)
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { specializes CPP NL; forwards FV: fv_env_proc x CPP; [solve_notin|].
          rewrite* subst_fresh. }
        { rewrite cons_app_one; rewrite !app_assoc.
          apply~ IHWT; rewrite <-!app_assoc; try solve_perm.
          apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
          ; destruct_uniq; [solve_uniq|solve_notin]. }
    - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
      forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
      ; forwards~ BNDS: Perm_binds x A0 PER.
      analyze_binds_uniq BNDS; try rewrite !dom_app in *; destruct_notin.
      + s; des; clear H1; rewrite <-app_nil_l in PER
        ; apply perm_dom_uniq in PER; auto; ss; obtain atoms L' as LEQ
        ; eapply cp_input with (L:=L')(ΔP:=ΔP); ii; substs~
        ; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite~ subst_open_var; rewrite !cons_app_one.
          eapply ignore_env_order
          ; [apply Permutation_app|]; [auto|apply Permutation_app_comm|].
          rewrite app_assoc; forwards UNX: uniq_perm_app PER NINX.
          apply~ H; [destruct_uniq; solve_uniq|solve_perm]. }
      + apply binds_env_split in BindsTac
        ; inversion_clear BindsTac as (Γ1 & Γ2 & EQ); substs~.
        rewrite app_assoc in *; apply perm_dom_uniq in PER; auto; ss
        ; obtain atoms L' as LEQ; destruct_notin; destruct (x0 == x)
        ; tryfalse.
        clear n0; eapply cp_input with (L:=L')(ΔP:=Γ1++Γ2++y~A0)
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite~ subst_open_var; rewrite !cons_app_one.
          rewrite !app_assoc; apply~ H; rewrite <-!app_assoc; try solve_perm.
          apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX.
          destruct_uniq; solve_uniq. }
    - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
      forwards~ UN2: cp_implies_uniq WT; apply Permutation_sym in PER
      ; forwards~ UN3: uniq_perm PER; [solve_uniq|]
      ; apply Permutation_sym in PER.
      forwards~ BNDS: Perm_binds x A0 PER.
      analyze_binds_uniq BNDS; try rewrite !dom_app in *; destruct_notin.
      + s; des; clear H0; rewrite <-app_nil_l in PER
        ; apply perm_dom_uniq in PER; auto; ss; eapply cp_left with (Δ:=Δ)
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite !cons_app_one.
          eapply ignore_env_order; [apply Permutation_app_comm|].
          forwards UNX: uniq_perm_app PER NINX.
          apply~ IHWT; [destruct_uniq; solve_uniq|solve_perm]. }
      + apply binds_env_split in BindsTac
        ; inversion_clear BindsTac as (Γ1 & Γ2 & EQ); substs~.
        rewrite app_assoc in *; apply perm_dom_uniq in PER; auto; ss
        ; destruct_notin; destruct (x0 == x); tryfalse.
        clear n0; eapply cp_left with (Δ:=Γ1++Γ2++y~A0); ii; substs~.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite !cons_app_one; rewrite !app_assoc.
          apply~ IHWT; rewrite <-!app_assoc; try solve_perm.
          apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
          ; destruct_uniq; [solve_uniq|solve_notin]. }
    - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
      forwards~ UN2: cp_implies_uniq WT; apply Permutation_sym in PER
      ; forwards~ UN3: uniq_perm PER; [solve_uniq|]
      ; apply Permutation_sym in PER.
      forwards~ BNDS: Perm_binds x A0 PER.
      analyze_binds_uniq BNDS; try rewrite !dom_app in *; destruct_notin.
      + s; des; clear H0; rewrite <-app_nil_l in PER
        ; apply perm_dom_uniq in PER; auto; ss; eapply cp_right with (Δ:=Δ)
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite !cons_app_one.
          eapply ignore_env_order; [apply Permutation_app_comm|].
          forwards UNX: uniq_perm_app PER NINX.
          apply~ IHWT; [destruct_uniq; solve_uniq|solve_perm]. }
      + apply binds_env_split in BindsTac
        ; inversion_clear BindsTac as (Γ1 & Γ2 & EQ); substs~.
        rewrite app_assoc in *; apply perm_dom_uniq in PER; auto; ss
        ; destruct_notin; destruct (x0 == x); tryfalse.
        clear n0; eapply cp_right with (Δ:=Γ1++Γ2++y~A0); ii; substs~.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite !cons_app_one; rewrite !app_assoc.
          apply~ IHWT; rewrite <-!app_assoc; try solve_perm.
          apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
          ; destruct_uniq; [solve_uniq|solve_notin]. }
    - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
      forwards~ UN2: cp_implies_uniq WT1; apply Permutation_sym in PER
      ; forwards~ UN3: uniq_perm PER; [solve_uniq|]
      ; apply Permutation_sym in PER.
      forwards~ BNDS: Perm_binds x A0 PER.
      analyze_binds_uniq BNDS; try rewrite !dom_app in *; destruct_notin.
      + s; des; clear H0; rewrite <-app_nil_l in PER
        ; apply perm_dom_uniq in PER; auto; ss; eapply cp_choice with (Δ:=Δ)
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite !cons_app_one.
          eapply ignore_env_order; [apply Permutation_app_comm|].
          forwards UNX: uniq_perm_app PER NINX.
          apply~ IHWT1; [destruct_uniq; solve_uniq|solve_perm]. }
        { rewrite !cons_app_one.
          eapply ignore_env_order; [apply Permutation_app_comm|].
          forwards UNX: uniq_perm_app PER NINX.
          apply~ IHWT2; [destruct_uniq; solve_uniq|solve_perm]. }
      + apply binds_env_split in BindsTac
        ; inversion_clear BindsTac as (Γ1 & Γ2 & EQ); substs~.
        rewrite app_assoc in *; apply perm_dom_uniq in PER; auto; ss
        ; destruct_notin; destruct (x0 == x); tryfalse.
        clear n0; eapply cp_choice with (Δ:=Γ1++Γ2++y~A0); ii; substs~.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite !cons_app_one; rewrite !app_assoc.
          apply~ IHWT1; rewrite <-!app_assoc; try solve_perm.
          apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
          ; destruct_uniq; [solve_uniq|solve_notin]. }
        { rewrite !cons_app_one; rewrite !app_assoc.
          apply~ IHWT2; rewrite <-!app_assoc; try solve_perm.
          apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
          ; destruct_uniq; [solve_uniq|solve_notin]. }
    - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
      forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
      ; forwards~ BNDS: Perm_binds x A0 PER.
      analyze_binds_uniq BNDS; try rewrite !dom_app in *; destruct_notin.
      + s; des; clear H1; rewrite <-app_nil_l in PER
        ; apply perm_dom_uniq in PER; auto; ss; obtain atoms L' as LEQ
        ; eapply cp_accept with (L:=L')(Δ:=Δ); ii; substs~
        ; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { specializes CPP NL; forwards~ FV: fv_env_proc x0 CPP
          ; rewrite* subst_fresh. }
      + forwards~ EQC: requests_binds_cod BindsTac
        ; apply binds_env_split in BindsTac
        ; inversion_clear BindsTac as (Γ1 & Γ2 & EQ)
        ; inversion_clear EQC as (B); substs~.
        rewrite app_assoc in *; apply perm_dom_uniq in PER; auto; ss
        ; obtain atoms L' as LEQ; destruct_notin; destruct (x0 == x)
        ; tryfalse; des_reqs.
        clear n0; eapply cp_accept with (L:=L')(Δ:=Γ1++Γ2++y~? B); ii
        ; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite~ subst_open_var; rewrite !cons_app_one; rewrite !app_assoc.
          apply~ H; rewrite <-!app_assoc; try solve_perm.
          apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
          ; destruct_uniq; solve_uniq. }
    - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
      forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
      ; forwards~ BNDS: Perm_binds x A0 PER.
      analyze_binds_uniq BNDS; try rewrite !dom_app in *; destruct_notin.
      + s; des; clear H1; rewrite <-app_nil_l in PER
        ; apply perm_dom_uniq in PER; auto; ss; obtain atoms L' as LEQ
        ; eapply cp_request with (L:=L')(Δ:=Δ); ii; substs~
        ; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { specializes CPP NL; forwards~ FV: fv_env_proc x0 CPP
          ; rewrite* subst_fresh. }
      +  apply binds_env_split in BindsTac
        ; inversion_clear BindsTac as (Γ1 & Γ2 & EQ); substs~.
        rewrite app_assoc in *; apply perm_dom_uniq in PER; auto; ss
        ; obtain atoms L' as LEQ; destruct_notin; destruct (x0 == x)
        ; tryfalse; des_reqs.
        clear n0; eapply cp_request with (L:=L')(Δ:=Γ1++Γ2++y~A0); ii
        ; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite~ subst_open_var; rewrite !cons_app_one; rewrite !app_assoc.
          apply~ H; rewrite <-!app_assoc; try solve_perm.
          apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
          ; destruct_uniq; solve_uniq. }
    - pick fresh z; destruct_notin; specializes CPP Fr
      ; forwards UN0: cp_implies_uniq CPP; inversion UN0; substs~; clears z.
      eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
      forwards~ UN3: uniq_perm (Permutation_sym PER)
      ; forwards~ BNDS: Perm_binds x A0 PER; try solve_uniq.
      analyze_binds_uniq BNDS; try rewrite !dom_app in *; destruct_notin.
      + s; des; clear H1; rewrite <-app_nil_l in PER
        ; apply perm_dom_uniq in PER; auto; ss; obtain atoms L' as LEQ
        ; eapply cp_send with (L:=L')(Δ:=Δ); ii; substs~
        ; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite !cons_app_one.
          eapply ignore_env_order; [apply Permutation_app_comm|].
          forwards UNX: uniq_perm_app PER NINX.
          apply~ H; try solve_perm; auto.
          destruct_uniq; solve_uniq. }
      + apply binds_env_split in BindsTac
        ; inversion_clear BindsTac as (Γ1 & Γ2 & EQ); substs~.
        rewrite app_assoc in *; apply perm_dom_uniq in PER; auto; ss
        ; obtain atoms L' as LEQ; destruct_notin; destruct (x0 == x)
        ; tryfalse; des_reqs.
        clear n0; eapply cp_send with (L:=L')(Δ:=Γ1++Γ2++y~A0); ii
        ; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite !cons_app_one; rewrite !app_assoc.
          apply~ H; try solve_perm; auto.
          apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
          ; destruct_uniq; solve_uniq. }
    - pick fresh z; destruct_notin; specializes CPP Fr
      ; forwards UN0: cp_implies_uniq CPP; inversion UN0; substs~; clears z.
      eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
      forwards~ UN3: uniq_perm (Permutation_sym PER)
      ; forwards~ BNDS: Perm_binds x A PER; try solve_uniq.
      analyze_binds_uniq BNDS; try rewrite !dom_app in *; destruct_notin.
      + s; des; clear H1; rewrite <-app_nil_l in PER
        ; apply perm_dom_uniq in PER; auto; ss; obtain atoms L' as LEQ
        ; eapply cp_recv with (L:=L')(Δ:=Δ); ii; substs~
        ; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite !cons_app_one.
          eapply ignore_env_order; [apply Permutation_app_comm|].
          forwards UNX: uniq_perm_app PER NINX.
          apply~ H; try solve_perm; auto.
          destruct_uniq; solve_uniq. }
      + apply binds_env_split in BindsTac
        ; inversion_clear BindsTac as (Γ1 & Γ2 & EQ); substs~.
        rewrite app_assoc in *; apply perm_dom_uniq in PER; auto; ss
        ; obtain atoms L' as LEQ; destruct_notin; destruct (x0 == x)
        ; tryfalse; des_reqs.
        clear n0; eapply cp_recv with (L:=L')(Δ:=Γ1++Γ2++y~A); ii
        ; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite !cons_app_one; rewrite !app_assoc.
          apply~ H; try solve_perm; auto.
          apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
          ; destruct_uniq; solve_uniq. }
    - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
      forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
      ; forwards~ BNDS: Perm_binds x A PER.
      analyze_binds_uniq BNDS; try rewrite !dom_app in *; destruct_notin.
      + s; des; clear H0; rewrite <-app_nil_l in PER
        ; apply perm_dom_uniq in PER; auto; ss; eapply cp_empout with (Ω:=Ω)
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
      + forwards~ EQC: requests_binds_cod BindsTac
        ; apply binds_env_split in BindsTac
        ; inversion_clear BindsTac as (Γ1 & Γ2 & EQ)
        ; inversion_clear EQC as (B); substs~.
        rewrite app_assoc in *; apply perm_dom_uniq in PER; auto; ss
        ; destruct_notin; destruct (x0 == x); tryfalse; des_reqs.
        clear n0; eapply cp_empout with (Ω:=Γ1++Γ2++y~? B)
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
    - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
      forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
      ; forwards~ BNDS: Perm_binds x A PER.
      analyze_binds_uniq BNDS; try rewrite !dom_app in *; destruct_notin.
      + s; des; clear H0; rewrite <-app_nil_l in PER
        ; apply perm_dom_uniq in PER; auto; ss; eapply cp_empin with (Δ:=Δ)
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { forwards~ FV: fv_env_proc x0 WT; rewrite~ subst_fresh. }
      + apply binds_env_split in BindsTac
        ; inversion_clear BindsTac as (Γ1 & Γ2 & EQ); substs~.
        rewrite app_assoc in *; apply perm_dom_uniq in PER; auto; ss
        ; destruct_notin; destruct (x0 == x)
        ; tryfalse; des_reqs.
        clear n0; eapply cp_empin with (Δ:=Γ1++Γ2++y~ A)
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite app_assoc; apply IHWT; try solve_perm.
          forwards UNX: uniq_perm_app PER NINX; destruct_uniq; solve_uniq. }
    - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
      forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
      ; forwards~ BNDS: Perm_binds x A PER.
      analyze_binds_uniq BNDS; try rewrite !dom_app in *; destruct_notin.
      + s; des; clear H0; rewrite <-app_nil_l in PER
        ; apply perm_dom_uniq in PER; auto; ss; eapply cp_empcho
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
      + apply binds_env_split in BindsTac
        ; inversion_clear BindsTac as (Γ1 & Γ2 & EQ); substs~.
        rewrite app_assoc in *; apply perm_dom_uniq in PER; auto; ss
        ; destruct_notin; destruct (x0 == x)
        ; tryfalse; des_reqs.
        clear n0; eapply cp_empcho with (Δ:=Γ1++Γ2++y~ A)
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
  Qed.

  Lemma typing_rename:
    forall Γ P (x y : atom) A
           (NINX: x `notin` dom Γ `union` fv_proc P)
           (NINY: y `notin` dom Γ `union` fv_proc P)
           (WTX: P ^^ x ⊢cp Γ ++ (x ~ A)),
      P ^^ y ⊢cp Γ ++ (y ~ A).
  Proof.
    ii; destruct (x == y); subst; auto.
    assert (UN: uniq ((x ~ A) ++ Γ)) by (eapply uniq_reorder_1
                                         ; eapply cp_implies_uniq; eauto).
    assert (UN': uniq Γ) by (inversion UN; auto).
    rewrite (@subst_intro x); auto.
    rewrite_env (Γ ++ (y ~ A) ++ nil).
    apply typing_subst with (A := A); auto.
  Qed.    

End CPBasicSubstOpenProperties.

Lemma perm_cod_dual:
  forall Γ Δ (x y:atom) A B
         (UN: uniq (Γ++x~A++y~A))
         (PER: Permutation (Γ++x~A++y~A) (x~¬B++y~B++Δ)),
    False.
Proof.
  i; eapply Permutation_trans in PER
  ; [|apply Permutation_app]; [|auto|apply Permutation_app_comm]
  ; rewrite <-app_nil_l in PER; rewrite app_assoc in PER.
  forwards EQ1: perm_cod_uniq PER; [solve_uniq|].
  rewrite <-app_assoc,app_nil_l in PER; eapply Permutation_trans in PER
  ; [|apply Permutation_app]; [|auto|apply Permutation_app_comm].
  rewrite app_assoc in PER.
  forwards EQ2: perm_cod_uniq PER; [solve_uniq|]; substs~.
  eauto using prop_eq_dual.
Qed.

Lemma cp_contract:
  forall P Γ x x' x'' A
         (UN: uniq (x ~ ? A ++ Γ))
         (WT: P ⊢cp Γ ++ x' ~ ? A ++ x'' ~ ? A),
    [x'' ~> x]([x' ~> x]P) ⊢cp Γ ++ (x ~ ? A).
Proof.
  ii; rewrite !cons_app_one in *; remember (Γ++x'~? A++x''~? A) as Γ'.
  gen Γ; induction WT; ii; substs~.
  - des; substs~; try (by rewrite !cons_app_one in *
                       ; forwards: uniq_perm PER UN; solve_uniq).
rewrite !cons_app_one in *; exfalso; eauto using perm_cod_dual.
Focus 2.
rewrite !cons_app_one in *; exfalso; eauto using perm_cod_dual.
Focus 3.
rewrite !cons_app_one in *; eapply Permutation_trans in PER
; [|apply Permutation_app]; [|auto|apply Permutation_app_comm].
apply perm_cod_dual in PER; [|solve_uniq]; tryfalse.
Focus 3.
rewrite !cons_app_one in *; eapply Permutation_trans in PER
; [|apply Permutation_app]; [|auto|apply Permutation_app_comm].
apply perm_cod_dual in PER; [|solve_uniq]; tryfalse.

rewrite !cons_app_one in *; eapply Permutation_trans in PER
; [|apply Permutation_app]; [|auto|apply Permutation_app_comm].
rewrite app_assoc in PER; rewrite <-app_nil_l in PER.
forwards EQ: perm_cod_uniq PER; try solve_uniq.
rewrite prop_dual_iff in EQ; apply dual_sym in EQ
; rewrite <-prop_dual_iff in EQ; substs; rewrite <-prop_dual_involutive in *.
apply perm_dom_uniq in PER; [|solve_uniq]; rewrite app_nil_l in PER.
forwards UN1: uniq_perm PER; try solve_uniq.
forwards~ BNDS: Perm_binds x'' (? A) PER; analyze_binds_uniq BNDS.
apply binds_env_split in BindsTac; inversion_clear BindsTac as (E1 & E2 & EQ)
; substs~; des_reqs.
apply Permutation_sym in PER; applys ignore_env_order PER.
rewrite !app_assoc; eapply ignore_env_order; [apply Permutation_app|]
; [apply Permutation_app_comm|auto|].
rewrite <-!app_assoc. apply cp_fwd with (A:=!¬A)(Ω:=E1++E2); auto.
s; rewrite <-prop_dual_involutive; solve_perm.
solve_uniq.


rewrite !cons_app_one in *; eapply Permutation_trans in PER
; [|apply Permutation_app]; [|auto|apply Permutation_app_comm].
rewrite app_assoc in PER; rewrite <-app_nil_l in PER.
forwards EQ: perm_cod_uniq PER; try solve_uniq.
rewrite prop_dual_iff in EQ; apply dual_sym in EQ
; rewrite <-prop_dual_iff in EQ; substs; rewrite <-prop_dual_involutive in *.
apply perm_dom_uniq in PER; [|solve_uniq]; rewrite app_nil_l in PER.
forwards UN1: uniq_perm PER; try solve_uniq.
forwards~ BNDS: Perm_binds x'' (? A) PER; analyze_binds_uniq BNDS.
apply binds_env_split in BindsTac; inversion_clear BindsTac as (E1 & E2 & EQ)
; substs~; des_reqs.
rewrite app_assoc in PER; apply perm_dom_uniq in PER; [|solve_uniq].
eapply Permutation_app with (m:=x~? A) in PER; auto.
forwards UN3: uniq_perm PER; try solve_uniq.
apply Permutation_sym in PER; applys ignore_env_order PER.
eapply ignore_env_order; [apply Permutation_app_comm|]; auto.
rewrite <-!app_assoc. apply cp_fwd with (A:=!¬A)(Ω:=E1++E2); auto.
s; rewrite <-prop_dual_involutive; solve_perm.
solve_uniq.

rewrite !cons_app_one in *
; rewrite app_assoc in PER; rewrite <-app_nil_l in PER.
forwards EQ: perm_cod_uniq PER; try solve_uniq.
rewrite prop_dual_iff in EQ; apply dual_sym in EQ
; rewrite <-prop_dual_iff in EQ; substs; rewrite <-prop_dual_involutive in *.
apply perm_dom_uniq in PER; [|solve_uniq]; rewrite app_nil_l in PER.
forwards UN1: uniq_perm PER; try solve_uniq.
forwards~ BNDS: Perm_binds x' (? A) PER; analyze_binds_uniq BNDS.
apply binds_env_split in BindsTac; inversion_clear BindsTac as (E1 & E2 & EQ)
; substs~; des_reqs.
rewrite app_assoc in PER; apply perm_dom_uniq in PER; [|solve_uniq].
eapply Permutation_app with (m:=x~? A) in PER; auto.
forwards UN3: uniq_perm PER; try solve_uniq.
apply Permutation_sym in PER; applys ignore_env_order PER.
eapply ignore_env_order; [apply Permutation_app_comm|]; auto.
rewrite <-!app_assoc. apply cp_fwd with (A:=!¬A)(Ω:=E1++E2); auto.
s; rewrite <-prop_dual_involutive; solve_perm.
solve_uniq.

rewrite !cons_app_one in *; eapply Permutation_trans in PER
; [|apply Permutation_app]; [|auto|apply Permutation_app_comm].
rewrite app_assoc in PER; forwards EQ: perm_cod_uniq PER; try solve_uniq.
rewrite <-EQ in *; clear EQ.
apply perm_dom_uniq in PER; [|solve_uniq].
forwards UN1: uniq_perm PER; try solve_uniq.
forwards~ BNDS: Perm_binds x'' (? A) PER; analyze_binds_uniq BNDS.
apply binds_env_split in BindsTac; inversion_clear BindsTac as (E1 & E2 & EQ)
; substs~; des_reqs.
apply Permutation_sym in PER; applys ignore_env_order PER.
eapply ignore_env_order; [apply Permutation_app_head|]
; [apply Permutation_app_comm|].
rewrite <-!app_assoc. apply cp_fwd with (A:=? A)(Ω:=E2++E1); auto.
solve_uniq.

rewrite !cons_app_one in *; eapply Permutation_trans in PER
; [|apply Permutation_app]; [|auto|apply Permutation_app_comm].
rewrite app_assoc in PER; forwards EQ: perm_cod_uniq PER; try solve_uniq.
rewrite <-EQ in *; clear EQ.
apply perm_dom_uniq in PER; [|solve_uniq].
forwards UN1: uniq_perm PER; try solve_uniq.
forwards~ BNDS: Perm_binds x'' (? A) PER; analyze_binds_uniq BNDS.
apply binds_env_split in BindsTac; inversion_clear BindsTac as (E1 & E2 & EQ)
; substs~; des_reqs.
rewrite app_assoc in PER; apply perm_dom_uniq in PER; [|solve_uniq].
eapply Permutation_app with (m:=x~? A) in PER; auto.
forwards UN3: uniq_perm PER; try solve_uniq.
apply Permutation_sym in PER; applys ignore_env_order PER.
rewrite <-!app_assoc; rewrite (app_assoc E1).
eapply ignore_env_order; [apply Permutation_app_head|]
; [apply Permutation_app_comm|].
apply cp_fwd with (A:=? A)(Ω:=E1++E2); auto.
solve_uniq.

rewrite !cons_app_one in *
; rewrite app_assoc in PER; forwards EQ: perm_cod_uniq PER; try solve_uniq.
rewrite <-EQ in *; clear EQ.
apply perm_dom_uniq in PER; [|solve_uniq].
forwards UN1: uniq_perm PER; try solve_uniq.
forwards~ BNDS: Perm_binds x' (? A) PER; analyze_binds_uniq BNDS.
apply binds_env_split in BindsTac; inversion_clear BindsTac as (E1 & E2 & EQ)
; substs~; des_reqs.
rewrite app_assoc in PER; apply perm_dom_uniq in PER; [|solve_uniq].
eapply Permutation_app with (m:=x~? A) in PER; auto.
forwards UN3: uniq_perm PER; try solve_uniq.
apply Permutation_sym in PER; applys ignore_env_order PER.
rewrite <-!app_assoc; rewrite (app_assoc E1).
eapply ignore_env_order; [apply Permutation_app_head|]
; [apply Permutation_app_comm|].
apply cp_fwd with (A:=? A)(Ω:=E1++E2); auto.
solve_uniq.

rewrite !cons_app_one in *.
forwards UN1: uniq_perm PER; try solve_uniq.
forwards~ BNDS: Perm_binds x'' (? A) PER; analyze_binds_uniq BNDS.
apply binds_env_split in BindsTac0
; inversion_clear BindsTac0 as (E1 & E2 & EQ); substs~; des_reqs.
rewrite 3 app_assoc in PER; apply perm_dom_uniq in PER; [|solve_uniq].
rewrite <-!app_assoc in PER.
forwards~ BNDS: Perm_binds x' (? A) PER; analyze_binds_uniq BNDS.
 {
   apply binds_env_split in BindsTac
   ; inversion_clear BindsTac as (E11 & E12 & EQ); substs~; des_reqs.
   rewrite <-!app_assoc in PER; rewrite 2 app_assoc in PER
   ; apply perm_dom_uniq in PER; [|solve_uniq].
   eapply Permutation_app with (m:=x~? A) in PER; auto.
   forwards UN3: uniq_perm PER; try (by applys uniq_perm UN0; solve_perm).
   apply Permutation_sym in PER; applys ignore_env_order PER.
   rewrite <-!app_assoc in *.
   apply cp_fwd with (A:=A0)(Ω:=E11++E12++E2++x~? A); auto.
 }
 {
   apply binds_env_split in BindsTac
   ; inversion_clear BindsTac as (E21 & E22 & EQ); substs~; des_reqs.
   rewrite 3 app_assoc in PER; apply perm_dom_uniq in PER
   ; [|rewrite app_assoc in UN; apply uniq_app_1 in UN; exact UN].
   eapply Permutation_app with (m:=x~? A) in PER; auto.
   forwards UN3: uniq_perm PER; try (by applys uniq_perm UN0; solve_perm).
   apply Permutation_sym in PER; applys ignore_env_order PER.
   rewrite <-!app_assoc in *.
   apply cp_fwd with (A:=A0)(Ω:=E1++E21++E22++x~? A); auto.
 }

Admitted.

Reserved Notation "P '==>cp' Q" (at level 69, right associativity).

Inductive proc_red : proc -> proc -> Prop :=
  | red_axcut : forall P A dA (w x:atom) (DUA: dual_props A dA)
                       (NF: w `notin` fv_proc P),
                  ν A → w ⟷ 0 ‖ P ==>cp (open_proc P w)
where "P '==>cp' Q" := (proc_red P Q) : cp_scope.

Theorem proc_sub_red: forall Γ P Q
    (WT: P ⊢cp Γ)
    (RED: P ==>cp Q),
  Q ⊢cp Γ.
Proof.
  ii; induction RED; subst. inversion WT; subst.
  pick fresh y; destruct_notin; specializes CPP Fr.
  rewrite /open_proc in CPP; simpl in CPP.
  inverts keep CPP; rewrite !cons_app_one in *.
  forwards UN1: uniq_perm PER0 UN0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  forwards EQC: perm_cod_uniq PER0; [solve_uniq|]; substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq].
  eapply Permutation_sym,Permutation_trans in PER0
  ; [|apply Permutation_app_comm].
  forwards~ BNDS: Perm_binds w (¬A0) PER0.
  apply binds_env_split in BNDS.
  inversion_clear BNDS as (E1 & E2 & EQ); substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq].
  apply requests_perm in PER0; auto; des_reqs.

idtac.
forwards~ UN3: uniq_perm PER.
apply Permutation_sym in PER; rewrite !app_assoc in PER
; eapply Permutation_trans in PER
; [|apply Permutation_app]; [|apply Permutation_app|]
; [|apply Permutation_app_comm| |]; auto.
applys ignore_env_order PER; rewrite <-!app_assoc; rewrite (app_assoc E1).
apply~ typing_weaken; [|apply Permutation_sym in PER; applys~ uniq_perm PER].
eapply ignore_env_order; [apply Permutation_app_comm|].
apply typing_rename with (x:=y); try (by destruct_uniq; solve_notin).
eapply ignore_env_order; [apply Permutation_app_comm|].
apply~ CPQ.

Qed.