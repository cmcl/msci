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
  | p_weak: pname -> proc -> proc
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
Notation "'?' '[' ']' x → P" := (p_weak x P) (at level 68,
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
    | ? [] z → P => ? [] (sub z) → (proc_subst x y P)
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
    | ? [] z → P => ? [] (sub z) → (proc_open_rec k x P)
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
    | ? [] z → P => fv z `union` fv_proc P
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
                         (COQ: lc_proc Q),
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
  | lc_p_weak : forall P (x:atom) (COP: lc_proc P), lc_proc (? [] x → P)
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
    et al. tactics.
*)
Inductive cp_rule : proc -> penv -> Prop :=
  | cp_fwd : forall Γ (x w:atom) A
                    (PER: Permutation Γ (w ~ ¬A ++ x ~ A))
                    (UN: uniq Γ),
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
  | cp_weaken : forall P Γ Δ (x:atom) A
                       (PER: Permutation Γ (x ~ ? A ++ Δ))
                       (UN: uniq Γ)
                       (CPP: P ⊢cp Δ),
                  ? [] x → P ⊢cp Γ
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
  | cp_empout : forall (x: atom), x → 0 ⊢cp x ~ pp_one
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

Hint Constructors cp_rule.

Inductive sublist {A:Type} {X:EqDec_eq A}: list A -> list A -> Prop :=
  | sublist_nil: sublist nil nil
  | sublist_cons: forall z xs ys, sublist xs ys -> sublist (z :: xs) (z :: ys)
  | sublist_sub: forall y xs ys, sublist xs ys -> sublist xs (y :: ys).

Hint Constructors sublist.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * prop) => dom x) in
  let D := gather_atoms_with (fun x : proc => fv_proc x) in
  constr:(A `union` B `union` C `union` D).

Section SublistProperties.
  Variable A : Type.
  Variable X : EqDec_eq A.

Lemma sublist_id:
  forall (xs:list A),
    sublist xs xs.
Proof. induction xs; auto. Qed.

Lemma sublist_empty:
  forall (xs:list A),
    sublist nil xs.
Proof. induction xs; auto. Qed.

Lemma sublist_trans:
  forall (xs ys zs: list A)
         (SUB1: sublist xs ys)
         (SUB2: sublist ys zs),
    sublist xs zs.
Proof. ii; gen xs; induction SUB2; ii; inv SUB1; auto. Qed.

Lemma sublist_app:
  forall (xs1 xs2 ys1 ys2: list A)
         (SUB1: sublist xs1 ys1)
         (SUB2: sublist xs2 ys2),
    sublist (xs1++xs2) (ys1++ys2).
Proof. ii; gen xs1; induction ys1; ii; inv SUB1; auto. Qed.

Lemma sublist_app_l:
  forall (xs ys zs: list A)
         (SUB: sublist xs ys),
    sublist xs (ys++zs).
Proof.
  i; rewrite <-(app_nil_r xs); apply sublist_app; auto using sublist_empty.
Qed.

Lemma sublist_app_r:
  forall (xs ys zs: list A)
         (SUB: sublist xs ys),
    sublist xs (zs++ys).
Proof.
  i; rewrite <-(app_nil_l xs); apply sublist_app; auto using sublist_empty.
Qed.

End SublistProperties.

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

Hint Resolve Permutation_length_1_inv.
Lemma ignore_env_order: forall Γ Δ P
    (INB: Permutation Γ Δ)
    (WT: P ⊢cp Γ),
  P ⊢cp Δ.
Proof.
  ii; gen Δ; induction WT; ii; try (by econstructor; ss; eauto).
  apply Permutation_length_1_inv in INB; substs; simpl_env; auto.
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

Ltac analyze_in x :=
  match goal with
    | [H: x `in` dom ?E |- _] =>
      let a := fresh "a" in
      let E1 := fresh "E1" in
      let E2 := fresh "E2" in
      let EQ := fresh "EQ" in
      apply in_env_split in H
      ; inversion_clear H as (a & E1 & E2 & EQ)
      ; substs~; des_reqs
  end.

Fixpoint weakenv (xs:list atom) (P:proc) : proc :=
  match xs with
  | nil => P
  | x :: xs' => ? [] x → (weakenv xs' P)
  end.

Lemma typing_weaken:
  forall Γ Δ E P xs
         (WT: P ⊢cp Γ ++ E) (UN: uniq(Γ ++ Δ ++ E))
         (FVC: forall x, x `in` dom Δ <-> In x xs)
         (NDUP: NoDupA Logic.eq xs)
         (REQS: all_requests Δ),
    weakenv xs P ⊢cp Γ ++ Δ ++ E.
Proof.
  i; gen Γ Δ E P; induction xs as [|x xs]; ii.
  - destruct Δ; auto; destruct p as [y a]; specializes FVC y; des;ss;fsetdec.
  - forwards FVX: FVC x; des; exploit FVX1; auto; ii.
    analyze_in x.
    rewrite <-!app_assoc,app_assoc.
    eapply ignore_env_order
    ; [apply Permutation_app_head; apply Permutation_app_comm|].
    simpl_env in *; inverts REQS2.
    apply cp_weaken with (A:=A)(Δ:=Γ++E1++E2++E)
    ; [solve_perm|applys uniq_perm UN;solve_perm|].
    rewrite (app_assoc E1); apply~ IHxs; [| |solve_uniq]; inv NDUP; auto.
    ii; simpl_env in *; specializes FVC x0; rewrite !dom_app in *; des; ii.
    + destruct_in; analyze_in x0; rewrite !dom_app in *; ss.
      { exploit FVC0; [fsetdec|].
        ii; destruct_in; auto; []
        ; subst; destruct_uniq; solve_notin; solve_uniq. }
      { exploit FVC0; [fsetdec|].
        ii; des; auto; []; subst; destruct_uniq; solve_notin; solve_uniq. }
    + destruct (x == x0); [apply InA_iff_In in H; subst; ss; tryfalse|].
      specialize (FVC1 (or_intror H)); destruct_in; auto; tryfalse.
Qed.

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

Lemma open_fv_proc_1:
  forall x y k P
         (NEQ: x <> y)
         (FV: x `notin` fv_proc P),
    x `notin` fv_proc ({k ~> y}P).
Proof.
  i; gen k; induction P; ii; destruct_all pname; des; destruct_in; eauto.
Qed.

Lemma open_fv_proc_2:
  forall x y k P
         (FV: x `notin` fv_proc ({k ~> y}P)),
    x `notin` fv_proc P.
Proof.
  i; gen k; induction P; ii; destruct_all pname; des; destruct_in; eauto.
Qed.

Hint Resolve open_fv_proc_1 open_fv_proc_2.

Lemma fv_env_proc:
  forall Γ P x
         (FV: x `notin` dom Γ)
         (WT: P ⊢cp Γ),
    x `notin` fv_proc P.
Proof.
  i; induction WT; auto
  ; try (by ii; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER
         ; auto
         ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
         ; s; fsetdec).
  - ii; destruct_in; pick fresh y; destruct_notin. 
    + apply (@open_fv_proc_2 x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; auto.
      apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
    + apply (@open_fv_proc_2 x y 0) in H3; auto.
      ii; apply (H0 y); auto; ii; destruct_in; auto.
      apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_fv_proc_2 x y 0) in H0; auto.
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
    + apply (@open_fv_proc_2 x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; substs~
      ; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_fv_proc_2 x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; substs~
      ; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_fv_proc_2 x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; substs~
      ; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_fv_proc_2 x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; substs~
      ; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_fv_proc_2 x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; substs~
      ; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
Qed.

Lemma cp_implies_lc:
  forall P Γ
         (WT: P ⊢cp Γ),
    lc_proc P.
Proof.
  ii; induction WT; eauto
  ; pick fresh y; destruct_notin; specializes H Fr; eauto.
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

  Lemma open_rec_comm:
    forall t j v i u
           (NEQ: i <> j),
      {i ~> u}({j ~> v} t) = {j ~> v} ({i ~> u}t).
  Proof.
    induction t; ii; destruct_all pname; des; subst
    ; solve [exfalso; auto
            |f_equal; firstorder].
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
    pick fresh y and apply Constructor; auto
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
    forall Γ w x y z A B
           (UNY: uniq (Γ ++ y ~ A))
           (UNX: uniq (Γ ++ z ~ A))
           (PER: Permutation (Γ ++ z ~ A) (w ~ ¬B ++ x ~ B)),
      [z ~> y](w ⟷ x) ⊢cp Γ ++ y ~ A.
  Proof.
    ii; des; substs.
    - apply uniq_perm in PER; auto; []; inv PER; ss; substs; fsetdec.
    - rewrite cons_app_one in PER; rewrite <- app_nil_l in PER
      ; forwards EQ: perm_cod_uniq PER; apply perm_dom_uniq in PER; substs~.
      apply cp_fwd with (A:=B); first [auto|solve_uniq].
      eapply Permutation_trans; [apply Permutation_app|]; [exact PER|auto|].
      solve_perm.
    - rewrite <- app_nil_r in PER. rewrite cons_app_one,<-app_assoc in PER.
      forwards EQ: perm_cod_uniq PER; apply perm_dom_uniq in PER; substs~.
      apply cp_fwd with (A:=B); first [auto|solve_uniq].
    - simpl_env in *; apply Perm_in with (x:=z) in PER; rewrite !dom_app in *
      ; ss; fsetdec.
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
    - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
      forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
      ; forwards~ BNDS: Perm_binds x A0 PER.
      analyze_binds_uniq BNDS; try rewrite !dom_app in *; destruct_notin.
      + s; des; clear H0; rewrite <-app_nil_l in PER
        ; apply perm_dom_uniq in PER; auto; ss
        ; apply cp_weaken with (A:=A)(Δ:=Δ); ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { forwards~ FV: fv_env_proc x0 WT; rewrite~ subst_fresh. }
      + apply binds_env_split in BindsTac
        ; inversion_clear BindsTac as (Γ1 & Γ2 & EQ); substs~.
        rewrite app_assoc in *; apply perm_dom_uniq in PER; auto; ss
        ; obtain atoms L' as LEQ; destruct_notin; destruct (x0 == x)
        ; tryfalse; des_reqs.
        clear n0; apply cp_weaken with (A:=A)(Δ:=Γ1++Γ2++y~A0); ii; substs~
        ; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { rewrite app_assoc.
          apply~ IHWT; rewrite <-!app_assoc; try solve_perm.
          forwards UNX: uniq_perm_app PER NINX; destruct_uniq; solve_uniq. }
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
    - eapply Permutation_sym,Permutation_trans in PER
      ; [|apply Permutation_app_comm]; apply Permutation_sym in PER; ss.
      apply Permutation_length_1_inv in PER; inverts PER; ss.
      des; tryfalse; auto.
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

Section ProcEquiv.

  (* Process equivalence w.r.t typing. *)
  Definition proc_equiv : relation proc :=
    fun P Q => forall Γ, P ⊢cp Γ <-> Q ⊢cp Γ.
  
End ProcEquiv.

Export  AtomSetImpl AtomSetFacts AtomSetProperties.
SearchAbout (elements _).

Lemma fv_proc_NoDup:
  forall P, NoDupA Logic.eq (elements (fv_proc P)).
Proof.
  intro P; generalize (fv_proc P); apply elements_3w.
Qed.

(* Lemma cp_test: *)
(*   forall P x k Γ *)
(*          (NFV: x `notin` fv_proc ({k ~> x}P)) *)
(*          (WT: {k ~> x}P ⊢cp Γ), *)
(*     lc_proc P. *)
(* Proof. *)
(*   i; gen Γ k; induction P; ii; destruct_all pname; des; destruct_in; auto; inverts WT; try solve_notin. pick fresh y and apply lc_p_cut; destruct_notin. *)
(* specializes CPP Fr. *)
(* unfold open_proc in *; rewrite~ open_rec_comm in CPP. *)
(* specialize (IHP1 _ _ NFV CPP). *)

(* inverts WT. apply (uniq_perm _ _ _ PER) in UN. solve_uniq. *)
(* solve_notin. *)
(*   ii; gen k; induction P; destruct_all pname; des; eauto. *)
(*   ii; remember ({k ~> x}P) as P'; gen P k; induction P; ii; eauto. *)
(*   rewrite subst_open_var in HeqP'. *)


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

Lemma perm_l_swap_r:
  forall {A} (xs ys zs xs':list A)
         (PER: Permutation (xs++ys++zs) xs'),
    Permutation (xs++zs++ys) xs'.
Proof.
  ii; eapply Permutation_trans in PER; [|apply Permutation_app_head]
  ; [|apply Permutation_app_comm]; auto.
Qed.

Hint Resolve uniq_remove_last.

Ltac extract_bnd x A :=
  match goal with
    | [H: Permutation (_++x~A) ?F |- _] =>
      let BNDS := fresh "BNDS" in
      forwards~ BNDS: Perm_binds x A H; analyze_binds_uniq BNDS
      ; try (by applys~ uniq_perm H)
      ; try (match goal with
               | [H: binds x A ?E |- _] =>
                 let E1 := fresh "E1" in
                 let E2 := fresh "E2" in
                 let EQ := fresh "EQ" in
                 apply binds_env_split in H
                 ; inversion_clear H as (E1 & E2 & EQ)
                 ; substs~; des_reqs
             end)
  end.
(*
Lemma fv_env_proc_wt:
  forall Γ P x A
         (FV: x `notin` fv_proc P)
         (WT: P ⊢cp Γ ++ x ~ ? A),
    P ⊢cp Γ.
Proof.
  ii; remember (Γ++x~? A) as Γ'
  ; assert (PER: Permutation Γ' (Γ++x~? A)) by substs~.
  clear HeqΓ'; gen A Γ; induction WT; i; ss; destruct_notin; substs~.
  - forwards UN2: uniq_perm PER UN.
    eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
    extract_bnd x (? A0); simpl_env in PER.
    rewrite 2 app_assoc in PER; apply perm_dom_uniq in PER
    ; [|applys uniq_perm PER0 UN].
    apply Permutation_sym in PER; applys ignore_env_order PER.
    rewrite <-!app_assoc; apply cp_fwd with (A:=A)(Ω:=E1++E2); auto.
    solve_uniq.
  - forwards UN2: uniq_perm PER UN.
    eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
    extract_bnd x (? A0); simpl_env in PER.
    {
      apply perm_dom_uniq in PER; [|applys uniq_perm PER0 UN].
      apply Permutation_sym in PER; applys ignore_env_order PER.
      rewrite app_assoc; obtain atoms L' as LEQ
      ; eapply cp_cut with (L:=L')(ΔQ:=ΔQ); ii; destruct_notin; substs~.
      - solve_uniq.
      - apply H with (A1:=A0); auto; try solve_perm.
        apply~ open_fv_proc_1.
    }
Admitted.*)
(*
Lemma cp_strengthen:
  forall P Γ x y A
         (BNDS: binds x (? A) Γ)
         (WT: P ⊢cp Γ ++ y ~ ? A),
    [y ~> x]P ⊢cp Γ.
Proof.
  ii; apply binds_env_split in BNDS; inversion_clear BNDS as (E1 & E2 & EQ)
  ; destruct (x == y); substs~; [apply cp_implies_uniq in WT; solve_uniq|].
  rewrite <-app_assoc in *; eapply ignore_env_order in WT
  ; [|apply Permutation_app_head; apply Permutation_app]
  ; [|apply Permutation_app_comm|auto].
  eapply ignore_env_order
  ; [apply Permutation_app_head; apply Permutation_app_comm|].
  simpl_env in *; rewrite app_assoc in *; revert WT; generalize (E1++E2) as Γ.
  clear E1 E2; i; remember (Γ++x~? A++y~? A) as Γ'
  ; assert (PER: Permutation Γ' (Γ++x~? A++y~? A)) by substs~
  ; clear HeqΓ'.
  gen A Γ; induction WT; ii; substs~; forwards~ UN1: uniq_perm PER0
  ; apply Permutation_sym in PER0; apply (Permutation_trans PER0) in PER
  ; apply Permutation_sym in PER0.
  - des; substs~; try (by rewrite !cons_app_one in *
                       ; forwards: uniq_perm PER UN1; solve_uniq).
    {
      rewrite !cons_app_one in *
      ; rewrite app_assoc in PER; rewrite <-app_nil_l in PER.
      forwards EQ: perm_cod_uniq PER; [simpl_env; auto|].
      rewrite prop_dual_iff in EQ; apply dual_sym in EQ
      ; rewrite <-prop_dual_iff in EQ; substs
      ; rewrite <-prop_dual_involutive in *.
      apply perm_dom_uniq in PER; [|simpl_env; auto];
      rewrite app_nil_l in PER.
      extract_bnd x (? A0).
      (* forwards~ BNDS: Perm_binds x (? A0) PER; analyze_binds_uniq BNDS *)
      (* ; [applys~ uniq_perm PER|]. *)
      (* apply binds_env_split in BindsTac *)
      (* ; inversion_clear BindsTac as (E1 & E2 & EQ) *)
      (* ; substs~; des_reqs. *)
      apply Permutation_sym in PER; applys ignore_env_order PER.
      eapply ignore_env_order; [apply Permutation_app_comm|]; auto.
      rewrite <-!app_assoc; apply cp_fwd with (A:=!¬A0)(Ω:=E1++E2); auto.
      s; rewrite <-prop_dual_involutive. solve_perm.
      solve_uniq.
    }
    {
      rewrite !cons_app_one in *; rewrite app_assoc in PER.
      forwards EQ: perm_cod_uniq PER; [simpl_env; auto|]; substs.
      apply perm_dom_uniq in PER; [|simpl_env; auto].
      extract_bnd x (? A0).
      (* forwards~ BNDS: Perm_binds x (? A0) PER; analyze_binds_uniq BNDS *)
      (* ; [applys~ uniq_perm PER|]. *)
      (* apply binds_env_split in BindsTac *)
      (* ; inversion_clear BindsTac as (E1 & E2 & EQ) *)
      (* ; substs~; des_reqs. *)
      apply Permutation_sym in PER; applys ignore_env_order PER.
      eapply ignore_env_order
      ; [apply Permutation_app_head; apply Permutation_app_comm|].
      apply cp_fwd with (A:=? A0)(Ω:=E2++E1); auto.
      solve_uniq.
    }
    {
      rewrite !cons_app_one in *; rewrite app_assoc in PER.
      extract_bnd y (? A0).
      (* forwards~ BNDS: Perm_binds y (? A0) PER; analyze_binds_uniq BNDS *)
      (* ; [applys~ uniq_perm PER|]. *)
      (* apply binds_env_split in BindsTac0 *)
      (* ; inversion_clear BindsTac0 as (E1 & E2 & EQ); substs~; des_reqs. *)
      rewrite 2 app_assoc in PER; apply perm_dom_uniq in PER
      ; [|simpl_env; auto].
      rewrite <-!app_assoc in PER.
      extract_bnd x (? A0).
      (* forwards~ BNDS: Perm_binds x (? A0) PER; analyze_binds_uniq BNDS. *)
      - rewrite <-app_nil_l in PER; forwards* EQ: perm_cod_uniq PER.
        rewrite prop_dual_iff in EQ; apply dual_sym in EQ
        ; rewrite <-prop_dual_iff in EQ; substs
        ; rewrite <-prop_dual_involutive in *; rewrite app_nil_l in PER.
        apply Permutation_sym in PER; applys ignore_env_order PER.
        apply cp_fwd with (A:=!¬A0)(Ω:=E1++E2); auto.
        s; rewrite <-prop_dual_involutive; solve_perm.
      - apply Permutation_sym in PER; applys ignore_env_order PER.
        apply cp_fwd with (A:=? A0)(Ω:=E1++E2); auto.
      - (* apply binds_env_split in BindsTac *)
        (*;inversion_clear BindsTac as (E11 & E12 & EQ); substs~; des_reqs. *)
        apply Permutation_sym in PER; applys ignore_env_order PER.
        rewrite <-!app_assoc in *.
        apply cp_fwd with (A:=A)(Ω:=E0++x~? A0++E3++E2); auto.
      - (* apply binds_env_split in BindsTac *)
        (*; inversion_clear BindsTac as (E21 & E22 & EQ); substs~; des_reqs.*)
        apply Permutation_sym in PER; applys ignore_env_order PER.
        apply cp_fwd with (A:=A)(Ω:=E1++E0++x~? A0++E3); auto.
    }
  - rewrite !cons_app_one in *; rewrite app_assoc in PER.
    extract_bnd y (? A0).
    (* forwards~ BNDS: Perm_binds y (? A0) PER; analyze_binds_uniq BNDS *)
    (* ; [applys~ uniq_perm PER| |]. *)
    {
      (* apply binds_env_split in BindsTac *)
      (* ; inversion_clear BindsTac as (E1 & E2 & EQ); substs~; des_reqs. *)
      rewrite <-!app_assoc,app_assoc in PER; apply perm_dom_uniq in PER
      ; [|simpl_env; auto].
      apply Permutation_sym in PER; applys ignore_env_order PER.
      rewrite app_assoc.
      obtain atoms L' as LEQ; eapply cp_cut with (L:=L')(ΔQ:=ΔQ)
      ; [apply~ Permutation_app_tail|solve_uniq| |]; ii
      ; substs; destruct_notin; first last.
      - specializes CPQ NL; forwards~ FV: fv_env_proc y CPQ
        ; rewrite* subst_fresh.
      - apply Permutation_sym in PER; extract_bnd x (? A0).
        + rewrite~ subst_open_var; rewrite !cons_app_one,<-!app_assoc.
          rewrite app_assoc; eapply ignore_env_order
          ; [apply Permutation_app_head; apply Permutation_app_comm|].
          rewrite !app_assoc; apply~ H; solve_perm.
        + rewrite~ subst_open_var; rewrite !cons_app_one.
          rewrite 2 app_assoc; eapply ignore_env_order
          ; [apply Permutation_app_head; apply Permutation_app_comm|].
          rewrite !app_assoc; apply~ H; solve_perm.
        + admit.
    }
    {
      admit.
    }
Admitted.*)
(*
Lemma cp_contract:
  forall P Γ x x' x'' A
         (UN: uniq (x ~ ? A ++ Γ))
         (WT: P ⊢cp Γ ++ x' ~ ? A ++ x'' ~ ? A),
    [x'' ~> x]([x' ~> x]P) ⊢cp Γ ++ (x ~ ? A).
Proof.
  ii; destruct (x'' == x); destruct (x' == x); substs~; try rewrite !subst_id.
  - apply cp_implies_uniq in WT; solve_uniq.
  - apply cp_strengthen with (A:=A); auto.
    simpl_env; eapply ignore_env_order; [|exact WT]; []; solve_perm.
  - apply cp_strengthen with (A:=A); auto.
    simpl_env; eapply ignore_env_order; [|exact WT]; []; solve_perm.
  - apply cp_strengthen with (A:=A); auto.
    simpl_env; apply cp_strengthen with (A:=A); auto.
    forwards UN2: cp_implies_uniq WT.
    apply (cp_weaken x A) in WT; [|solve_uniq].
    eapply ignore_env_order; [|exact WT]; []; solve_perm.
Qed.
*)
(*   - *)
(*   ii; rewrite !cons_app_one in *; remember (Γ++x'~? A++x''~? A) as Γ'. *)
(*   gen Γ; induction WT; ii; substs~. *)
(*   - admit. *)
(*   - admit. *)
(*   - des; substs~; rewrite !cons_app_one in * *)
(*     ; try (by apply perm_l_swap_r in PER *)
(*            ; rewrite app_assoc,<-app_nil_l in PER; apply perm_cod_uniq in PER *)
(*            ; [|solve_uniq]; inv PER). *)
(*     rewrite app_assoc,<-app_nil_l in PER; apply perm_cod_uniq in PER *)
(*     ; [|simpl_env; exact UN]; inv PER. *)
(*     forwards UN1: uniq_perm PER; try exact UN. *)
(*     forwards~ BNDS: Perm_binds x'' (? A) PER; analyze_binds_uniq BNDS. *)
(*     apply binds_env_split in BindsTac0 *)
(*     ; inversion_clear BindsTac0 as (E1 & E2 & EQ); substs~; des_reqs. *)
(* rewrite 3 app_assoc in PER; apply perm_dom_uniq in PER; [|solve_uniq]. *)
(* rewrite <-!app_assoc in PER. *)
(* forwards~ BNDS: Perm_binds x' (? A) PER; analyze_binds_uniq BNDS. *)
(*  { *)
(*    apply binds_env_split in BindsTac *)
(*    ; inversion_clear BindsTac as (E11 & E12 & EQ); substs~; des_reqs. *)
(*    rewrite <-!app_assoc in PER; rewrite 2 app_assoc in PER *)
(*    ; apply perm_dom_uniq in PER; [|solve_uniq]. *)
(*    eapply Permutation_app with (m:=x~? A) in PER; auto. *)
(*    forwards UN3: uniq_perm PER; try (by applys uniq_perm UN0; solve_perm). *)
(*    apply Permutation_sym in PER; applys ignore_env_order PER. *)
(*    rewrite <-!app_assoc in *. *)
(*    apply cp_fwd with (A:=A0)(Ω:=E11++E12++E2++x~? A); auto. *)
(*  } *)
(*  { *)
(*    apply binds_env_split in BindsTac *)
(*    ; inversion_clear BindsTac as (E21 & E22 & EQ); substs~; des_reqs. *)
(*    rewrite 3 app_assoc in PER; apply perm_dom_uniq in PER *)
(*    ; [|rewrite app_assoc in UN; apply uniq_app_1 in UN; exact UN]. *)
(*    eapply Permutation_app with (m:=x~? A) in PER; auto. *)
(*    forwards UN3: uniq_perm PER; try (by applys uniq_perm UN0; solve_perm). *)
(*    apply Permutation_sym in PER; applys ignore_env_order PER. *)
(*    rewrite <-!app_assoc in *. *)
(*    apply cp_fwd with (A:=A0)(Ω:=E1++E21++E22++x~? A); auto. *)
(*  } *)






(*   - des; substs~; try (by rewrite !cons_app_one in * *)
(*                        ; forwards: uniq_perm PER UN; solve_uniq). *)
(* rewrite !cons_app_one in *; exfalso; eauto using perm_cod_dual. *)
(* Focus 2. *)
(* rewrite !cons_app_one in *; exfalso; eauto using perm_cod_dual. *)
(* Focus 3. *)
(* rewrite !cons_app_one in *; eapply Permutation_trans in PER *)
(* ; [|apply Permutation_app]; [|auto|apply Permutation_app_comm]. *)
(* apply perm_cod_dual in PER; [|solve_uniq]; tryfalse. *)
(* Focus 3. *)
(* rewrite !cons_app_one in *; eapply Permutation_trans in PER *)
(* ; [|apply Permutation_app]; [|auto|apply Permutation_app_comm]. *)
(* apply perm_cod_dual in PER; [|solve_uniq]; tryfalse. *)

(* rewrite !cons_app_one in *; eapply Permutation_trans in PER *)
(* ; [|apply Permutation_app]; [|auto|apply Permutation_app_comm]. *)
(* rewrite app_assoc in PER; rewrite <-app_nil_l in PER. *)
(* forwards EQ: perm_cod_uniq PER; try solve_uniq. *)
(* rewrite prop_dual_iff in EQ; apply dual_sym in EQ *)
(* ; rewrite <-prop_dual_iff in EQ; substs; rewrite <-prop_dual_involutive in *. *)
(* apply perm_dom_uniq in PER; [|solve_uniq]; rewrite app_nil_l in PER. *)
(* forwards UN1: uniq_perm PER; try solve_uniq. *)
(* forwards~ BNDS: Perm_binds x'' (? A) PER; analyze_binds_uniq BNDS. *)
(* apply binds_env_split in BindsTac; inversion_clear BindsTac as (E1 & E2 & EQ) *)
(* ; substs~; des_reqs. *)
(* apply Permutation_sym in PER; applys ignore_env_order PER. *)
(* rewrite !app_assoc; eapply ignore_env_order; [apply Permutation_app|] *)
(* ; [apply Permutation_app_comm|auto|]. *)
(* rewrite <-!app_assoc. apply cp_fwd with (A:=!¬A)(Ω:=E1++E2); auto. *)
(* s; rewrite <-prop_dual_involutive; solve_perm. *)
(* solve_uniq. *)


(* rewrite !cons_app_one in *; eapply Permutation_trans in PER *)
(* ; [|apply Permutation_app]; [|auto|apply Permutation_app_comm]. *)
(* rewrite app_assoc in PER; rewrite <-app_nil_l in PER. *)
(* forwards EQ: perm_cod_uniq PER; try solve_uniq. *)
(* rewrite prop_dual_iff in EQ; apply dual_sym in EQ *)
(* ; rewrite <-prop_dual_iff in EQ; substs; rewrite <-prop_dual_involutive in *. *)
(* apply perm_dom_uniq in PER; [|solve_uniq]; rewrite app_nil_l in PER. *)
(* forwards UN1: uniq_perm PER; try solve_uniq. *)
(* forwards~ BNDS: Perm_binds x'' (? A) PER; analyze_binds_uniq BNDS. *)
(* apply binds_env_split in BindsTac; inversion_clear BindsTac as (E1 & E2 & EQ) *)
(* ; substs~; des_reqs. *)
(* rewrite app_assoc in PER; apply perm_dom_uniq in PER; [|solve_uniq]. *)
(* eapply Permutation_app with (m:=x~? A) in PER; auto. *)
(* forwards UN3: uniq_perm PER; try solve_uniq. *)
(* apply Permutation_sym in PER; applys ignore_env_order PER. *)
(* eapply ignore_env_order; [apply Permutation_app_comm|]; auto. *)
(* rewrite <-!app_assoc. apply cp_fwd with (A:=!¬A)(Ω:=E1++E2); auto. *)
(* s; rewrite <-prop_dual_involutive; solve_perm. *)
(* solve_uniq. *)

(* rewrite !cons_app_one in * *)
(* ; rewrite app_assoc in PER; rewrite <-app_nil_l in PER. *)
(* forwards EQ: perm_cod_uniq PER; try solve_uniq. *)
(* rewrite prop_dual_iff in EQ; apply dual_sym in EQ *)
(* ; rewrite <-prop_dual_iff in EQ; substs; rewrite <-prop_dual_involutive in *. *)
(* apply perm_dom_uniq in PER; [|solve_uniq]; rewrite app_nil_l in PER. *)
(* forwards UN1: uniq_perm PER; try solve_uniq. *)
(* forwards~ BNDS: Perm_binds x' (? A) PER; analyze_binds_uniq BNDS. *)
(* apply binds_env_split in BindsTac; inversion_clear BindsTac as (E1 & E2 & EQ) *)
(* ; substs~; des_reqs. *)
(* rewrite app_assoc in PER; apply perm_dom_uniq in PER; [|solve_uniq]. *)
(* eapply Permutation_app with (m:=x~? A) in PER; auto. *)
(* forwards UN3: uniq_perm PER; try solve_uniq. *)
(* apply Permutation_sym in PER; applys ignore_env_order PER. *)
(* eapply ignore_env_order; [apply Permutation_app_comm|]; auto. *)
(* rewrite <-!app_assoc. apply cp_fwd with (A:=!¬A)(Ω:=E1++E2); auto. *)
(* s; rewrite <-prop_dual_involutive; solve_perm. *)
(* solve_uniq. *)

(* rewrite !cons_app_one in *; eapply Permutation_trans in PER *)
(* ; [|apply Permutation_app]; [|auto|apply Permutation_app_comm]. *)
(* rewrite app_assoc in PER; forwards EQ: perm_cod_uniq PER; try solve_uniq. *)
(* rewrite <-EQ in *; clear EQ. *)
(* apply perm_dom_uniq in PER; [|solve_uniq]. *)
(* forwards UN1: uniq_perm PER; try solve_uniq. *)
(* forwards~ BNDS: Perm_binds x'' (? A) PER; analyze_binds_uniq BNDS. *)
(* apply binds_env_split in BindsTac; inversion_clear BindsTac as (E1 & E2 & EQ) *)
(* ; substs~; des_reqs. *)
(* apply Permutation_sym in PER; applys ignore_env_order PER. *)
(* eapply ignore_env_order; [apply Permutation_app_head|] *)
(* ; [apply Permutation_app_comm|]. *)
(* rewrite <-!app_assoc. apply cp_fwd with (A:=? A)(Ω:=E2++E1); auto. *)
(* solve_uniq. *)

(* rewrite !cons_app_one in *; eapply Permutation_trans in PER *)
(* ; [|apply Permutation_app]; [|auto|apply Permutation_app_comm]. *)
(* rewrite app_assoc in PER; forwards EQ: perm_cod_uniq PER; try solve_uniq. *)
(* rewrite <-EQ in *; clear EQ. *)
(* apply perm_dom_uniq in PER; [|solve_uniq]. *)
(* forwards UN1: uniq_perm PER; try solve_uniq. *)
(* forwards~ BNDS: Perm_binds x'' (? A) PER; analyze_binds_uniq BNDS. *)
(* apply binds_env_split in BindsTac; inversion_clear BindsTac as (E1 & E2 & EQ) *)
(* ; substs~; des_reqs. *)
(* rewrite app_assoc in PER; apply perm_dom_uniq in PER; [|solve_uniq]. *)
(* eapply Permutation_app with (m:=x~? A) in PER; auto. *)
(* forwards UN3: uniq_perm PER; try solve_uniq. *)
(* apply Permutation_sym in PER; applys ignore_env_order PER. *)
(* rewrite <-!app_assoc; rewrite (app_assoc E1). *)
(* eapply ignore_env_order; [apply Permutation_app_head|] *)
(* ; [apply Permutation_app_comm|]. *)
(* apply cp_fwd with (A:=? A)(Ω:=E1++E2); auto. *)
(* solve_uniq. *)

(* rewrite !cons_app_one in * *)
(* ; rewrite app_assoc in PER; forwards EQ: perm_cod_uniq PER; try solve_uniq. *)
(* rewrite <-EQ in *; clear EQ. *)
(* apply perm_dom_uniq in PER; [|solve_uniq]. *)
(* forwards UN1: uniq_perm PER; try solve_uniq. *)
(* forwards~ BNDS: Perm_binds x' (? A) PER; analyze_binds_uniq BNDS. *)
(* apply binds_env_split in BindsTac; inversion_clear BindsTac as (E1 & E2 & EQ) *)
(* ; substs~; des_reqs. *)
(* rewrite app_assoc in PER; apply perm_dom_uniq in PER; [|solve_uniq]. *)
(* eapply Permutation_app with (m:=x~? A) in PER; auto. *)
(* forwards UN3: uniq_perm PER; try solve_uniq. *)
(* apply Permutation_sym in PER; applys ignore_env_order PER. *)
(* rewrite <-!app_assoc; rewrite (app_assoc E1). *)
(* eapply ignore_env_order; [apply Permutation_app_head|] *)
(* ; [apply Permutation_app_comm|]. *)
(* apply cp_fwd with (A:=? A)(Ω:=E1++E2); auto. *)
(* solve_uniq. *)

Reserved Notation "P '==>cp' Q" (at level 69, right associativity).

Inductive proc_red : proc -> proc -> Prop :=
  | red_axcut :
      forall P A (w x:atom) (NF: w `notin` fv_proc P),
        ν A → w ⟷ 0 ‖ P
      ==>cp
        (open_proc P w)
  | red_multi :
      forall P Q R A dA B (DUA: dual_props A dA),
        ν A ⨂ B → ([A]0 → P ‖ Q) ‖ ⟨dA⟩ 0 → R
      ==>cp
        ν A → P ‖ (ν B → Q ‖ R)
  | red_add :
      forall P Q R A B,
        ν A ⨂ B → (0[inl] → P) ‖ 0 CASE Q OR R
      ==>cp
        ν A → P ‖ Q
  | red_gc :
      forall P Q (y:atom) A B
             (NF: y `notin` fv_proc P),
        ν ! A → ! ⟨B⟩0 → P ‖ ? [] 0 → Q
      ==>cp
        weakenv (elements (remove y (fv_proc (P ^^ y)))) Q
where "P '==>cp' Q" := (proc_red P Q) : cp_scope.

(** Lemmas for proving well-typedness of reduction rules. *)

Lemma reduce_axcut:
  forall P A (w : atom) Γ
         (NFV: w `notin` fv_proc P)
         (WT: ν A → w ⟷ 0 ‖ P ⊢cp Γ),
    P ^^ w ⊢cp Γ.
Proof.
  ii; inversion WT; subst.
  pick fresh y; destruct_notin; specializes CPP Fr.
  rewrite /open_proc in CPP; simpl in CPP.
  inverts keep CPP; rewrite !cons_app_one in *.
  forwards UN1: uniq_perm PER0 UN0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  forwards EQC: perm_cod_uniq PER0; [solve_uniq|]; substs~.
  rewrite <-app_nil_r in PER0; rewrite <-app_assoc in PER0
  ; apply perm_dom_uniq in PER0; [|solve_uniq]; simpl_env in PER0.
  apply Permutation_sym,Permutation_length_1_inv in PER0; substs~; s in PER.
  forwards~ UN3: uniq_perm PER.
  apply Permutation_sym in PER; applys ignore_env_order PER; simpl_env.
  eapply ignore_env_order; [apply Permutation_app_comm|].
  apply typing_rename with (x:=y); try (by destruct_uniq; solve_notin).
  eapply ignore_env_order; [apply Permutation_app_comm|].
  apply~ CPQ.
Qed.

Lemma reduce_multi:
  forall P Q R A dA B Γ
         (DUA: dual_props A dA)
         (WT: ν A ⨂ B → [A]0 → P ‖ Q ‖ ⟨dA ⟩ 0 → R ⊢cp Γ),
    ν A → P ‖ ν B → Q ‖ R ⊢cp Γ.
Proof.
  ii; inversion WT; subst.
  pick fresh y; destruct_notin; specializes CPP Fr.
  rewrite /open_proc in CPP; simpl in CPP.
  inverts keep CPP; rewrite !cons_app_one in *.
  forwards UN1: uniq_perm PER0 UN0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER0; forwards EQC: perm_cod_uniq PER0
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq]; rewrite app_nil_l in PER0.
Admitted.

Lemma reduce_add:
  forall P Q R A B Γ
         (WT: ν A ⨂ B → (0[inl] → P) ‖ 0 CASE Q OR R ⊢cp Γ),
    ν A → P ‖ Q ⊢cp Γ.
Proof.
Admitted.

Lemma reduce_gc:
  forall P Q (y:atom) A B Γ
         (NF: y `notin` fv_proc P)
         (WT: ν ! A → ! ⟨B⟩0 → P ‖ ? [] 0 → Q ⊢cp Γ),
    weakenv (elements (remove y (fv_proc (P ^^ y)))) Q ⊢cp Γ.
Proof.
  ii; forwards LC: cp_implies_lc WT; inversion WT; inverts LC; subst.
  pick fresh z; destruct_notin; specializes CPP Fr.
  rewrite /open_proc in CPP; simpl in CPP.
  inverts keep CPP; rewrite !cons_app_one in *.
  forwards UN1: uniq_perm PER0 UN0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER0; forwards EQC: perm_cod_uniq PER0
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq]; rewrite app_nil_l in PER0.
  eapply Permutation_sym,Permutation_trans in PER
  ; [|apply Permutation_app]; [|apply Permutation_sym;exact PER0|auto].
  applys ignore_env_order PER; eapply ignore_env_order
  ; [apply Permutation_app_comm|].
  apply Permutation_sym in PER; forwards UN2: uniq_perm PER UN.
  rewrite <-app_nil_r,<-app_assoc; apply typing_weaken; simpl_env
  ; try solve_uniq.
Focus 3.
apply elements_3w.
  specializes CPQ Fr; rewrite /open_proc in CPQ; s in CPQ.
  inverts keep CPQ; simpl_env in *.
  forwards UN4: uniq_perm PER1 UN3.
  eapply Permutation_trans in PER1; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER1; forwards EQC: perm_cod_uniq PER1
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER1; [|solve_uniq]; rewrite app_nil_l in PER1.
  apply Permutation_sym in PER1; applys ignore_env_order PER1.
  apply (ignore_env_order PER1) in CPP1.
  specializes COQ NotInTac. inverts COQ.
SearchAbout (_ `notin` _).
Lemma blah:
  forall Γ P k (x:atom)
         (NIN: x `notin` dom Γ)
         (WT: {k ~> x}P ⊢cp Γ),
    P ⊢cp Γ.
Proof.
  i; remember ({k ~> x}P) as P'; gen P k; induction WT; ii.
{
destruct P; try discriminate; inv HeqP'.
destruct_all pname; des; destr_eq H0; destr_eq H1; subst.
 forwards UN1: uniq_perm PER UN; solve_uniq.

 exfalso; apply NIN; apply Permutation_sym in PER.
 applys Perm_in PER; ss; fsetdec.

 exfalso; apply NIN; apply Permutation_sym in PER.
 applys Perm_in PER; ss; fsetdec.

 apply cp_fwd with (A:=A); auto.
}
{
  destruct P0; try discriminate. inv HeqP'.
  pick fresh y and apply cp_cut. exact PER. auto.

  destruct_notin; specializes H Fr.
  apply H with (k0:=S k).
  i; apply NIN; apply Permutation_sym in PER; applys Perm_in PER
  ; rewrite dom_app; fsetdec.
  rewrite /open_proc; rewrite~ open_rec_comm.

  destruct_notin; specializes H0 Fr.
  apply H0 with (k0:=S k).
  i; apply NIN; apply Permutation_sym in PER; applys Perm_in PER
  ; rewrite dom_app; fsetdec.
  rewrite /open_proc; rewrite~ open_rec_comm.
}

Qed.
idtac.
forwards NFV: blah CPQ.
SearchAbout (fv_proc _).
Lemma open_fv_proc_2':
  forall x y k P
         (NFV: x `notin` fv_proc ({k ~> y}P)),
    lc_proc P.
Proof.
  i; gen k; induction P. ii; destruct_all pname; des; destruct_in; eauto.
Qed.
idtac.
SearchAbout (fv_proc _).
Lemma open_fv_proc_2'':
  forall x y k P
         (NFV: x `notin` fv_proc ({k ~> y}P)),
    lc_proc P.
Proof.
  i; gen k; induction P; ii; destruct_all pname; des; destruct_in; eauto.


idtac.
apply open_fv_proc_2' in NFV.

  rewrite~ lc_no_bvar in CPP1.
Admitted.

Hint Resolve reduce_axcut reduce_multi reduce_add.

Theorem proc_sub_red: forall Γ P Q
    (WT: P ⊢cp Γ)
    (RED: P ==>cp Q),
  Q ⊢cp Γ.
Proof. ii; induction RED; subst; eauto. Qed.
