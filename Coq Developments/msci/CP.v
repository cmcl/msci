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

Fixpoint fv_prop (pp:prop) : atoms :=
  match pp with
  | pp_var v
    => match v with
       | pvar_fvar y => singleton y
       | _ => empty
       end
  | pp_dvar v
    => match v with
       | pvar_fvar y => singleton y
       | _ => empty
       end
  | A ⨂ B => fv_prop A `union` fv_prop B
  | A ⅋ B => fv_prop A `union` fv_prop B
  | A ⨁ B => fv_prop A `union` fv_prop B
  | A & B => fv_prop A `union` fv_prop B
  | ! A => fv_prop A
  | ? A => fv_prop A
  | pp_forall A => fv_prop A
  | pp_exists A => fv_prop A
  | _ => empty
  end.

Lemma prop_dual_preserves_subst: forall A B X,
  ¬({{A // X}}B) = {{A // X}}(¬B).
Proof.
  intros; induction B; simpl; f_equal; auto; destruct p; auto
  ; match goal with
    | |- context[?X == ?Y] => destruct (X == Y)
    end; auto using prop_dual_involutive.
Qed.

Lemma prop_dual_preserves_open:
  forall k x A, ¬prop_open_rec k x A = prop_open_rec k x (¬A).
Proof.
  ii; gen k; induction A; ii; f_equal; auto; destruct p; des; auto.
Qed.

Lemma prop_dual_open_prop:
  forall x A, ¬open_prop A x = open_prop (¬A) x.
Proof.
  ii; rewrite /open_prop prop_dual_preserves_open; auto.
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

(** Lifting substitution of a proposition for a propositional variable to
    processes. *)
Fixpoint proc_subst_prop (x:atom) (y:prop) (p: proc) : proc :=
  match p with
  | ν A → P ‖ Q
    => ν {{ y // x}}A → (proc_subst_prop x y P) ‖ (proc_subst_prop x y Q)
  | [A] z → P ‖ Q => [A] z → (proc_subst_prop x y P) ‖ (proc_subst_prop x y Q)
  | ⟨A⟩ z → P => ⟨{{ y // x}}A⟩ z → (proc_subst_prop x y P)
  | z [inl] → P => z [inl] → (proc_subst_prop x y P)
  | z [inr] → P => z [inr] → (proc_subst_prop x y P)
  | z CASE P OR Q => z CASE (proc_subst_prop x y P) OR (proc_subst_prop x y Q)
  | ! ⟨A⟩ z → P => ! ⟨{{ y // x }}A⟩ z → (proc_subst_prop x y P)
  | ? [A] z → P => ? [{{ y // x }}A] z → (proc_subst_prop x y P)
  | ? [] z → P => ? [] z → (proc_subst_prop x y P)
  | p_send z A P => p_send z ({{ y // x }}A) (proc_subst_prop x y P)
  | p_recv z P => p_recv z (proc_subst_prop x y P)
  | ⟨⟩ z → P => ⟨⟩ z → (proc_subst_prop x y P)
  | _ => p
  end.

Notation "[ x ~>p y ] P" := (proc_subst_prop x y P) (at level 68) : cp_scope.

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

(** Lifting opening of a proposition to a process. *)
Fixpoint proc_prop_open_rec (k: nat) (x: atom) (p: proc) :=
  let
    open := fun A => prop_open_rec k x A
  in
    match p with
    | ν A → P ‖ Q
      => ν (open A) → (proc_prop_open_rec k x P) ‖ (proc_prop_open_rec k x Q)
    | [A] z → P ‖ Q
      => [open A] z → (proc_prop_open_rec k x P) ‖ (proc_prop_open_rec k x Q)
    | ⟨A⟩ z → P => ⟨open A⟩ z → (proc_prop_open_rec k x P)
    | z [inl] → P => z [inl] → (proc_prop_open_rec k x P)
    | z [inr] → P => z [inr] → (proc_prop_open_rec k x P)
    | z CASE P OR Q
      => z CASE (proc_prop_open_rec k x P) OR (proc_prop_open_rec k x Q)
    | ! ⟨A⟩ z → P => ! ⟨open A⟩ z → (proc_prop_open_rec k x P)
    | ? [A] z → P => ? [open A] z → (proc_prop_open_rec k x P)
    | ? [] z → P => ? [] z → (proc_prop_open_rec k x P)
    | p_send z A P => p_send z (open A) (proc_prop_open_rec k x P)
    | p_recv z P => p_recv z (proc_prop_open_rec (S k) x P)
    | ⟨⟩ z → P => ⟨⟩ z → (proc_prop_open_rec k x P)
    | _ => p
    end.

Definition open_proc_prop P x := proc_prop_open_rec 0 x P.
Notation "P '^^p' x" := (open_proc_prop P x) (at level 68) : cp_scope.

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

(* Permute binders inside process. *)
Reserved Notation "{ a <~> b } Q" (at level 68).

Fixpoint swap_binders (a b:nat) (Q:proc) : proc :=
  let
    swap := fun x => match x with
                     | p_bn n =>
                       p_bn (if n == a then b else if n == b then a else n)
                     | _ => x
                     end
  in
    match Q with
    | w ⟷ z => swap w ⟷ swap z
    | ν A → P ‖ R
      => ν A → ({S a <~> S b} P) ‖ ({S a <~> S b} R)
    | [A] z → P ‖ R
      => [A] (swap z) → ({S a <~> S b} P) ‖ ({S a <~> S b}R)
    | ⟨A⟩ z → P => ⟨A⟩ (swap z) → ({S a <~> S b} P)
    | z [inl] → P => (swap z) [inl] → ({a <~> b} P)
    | z [inr] → P => (swap z) [inr] → ({a <~> b} P)
    | z CASE P OR R
      => (swap z) CASE ({a <~> b} P) OR ({a <~> b} R)
    | ! ⟨A⟩ z → P => ! ⟨A⟩ (swap z) → ({S a <~> S b} P)
    | ? [A] z → P => ? [A] (swap z) → ({S a <~> S b} P)
    | ? [] z → P => ? [] (swap z) → ({a <~> b} P)
    | p_send z A P => p_send (swap z) A ({a <~> b} P)
    | p_recv z P => p_recv (swap z) ({a <~> b} P)
    | z → 0 => swap z → 0
    | ⟨⟩ z → P => ⟨⟩ (swap z) → ({a <~> b} P)
    | z CASE 0 => (swap z) CASE 0
    end
where "{ a <~> b } P" := (swap_binders a b P).

(** Environments for the process calculus are mappings of atoms to
    propositions. *)
Definition penv := list (atom * prop).

Fixpoint fv_env (xs:penv) : atoms :=
  match xs with
  | nil => empty
  | x :: xs' => let (_,a) := x in fv_prop a `union` fv_env xs'
  end.

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
                     (PER: Permutation Γ ((x ~ A ⨁ B) ++ Δ))
                     (CPP: P ⊢cp (x ~ A) ++ Δ),
                x[inl] → P ⊢cp Γ
  | cp_right : forall P Γ Δ x A B
                      (PER: Permutation Γ ((x ~ A ⨁ B) ++ Δ))
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
  | cp_empcho : forall (x:atom), x CASE 0 ⊢cp x ~ pp_top
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
  let E := gather_atoms_with (fun x : list (atom * prop) => fv_env x) in
  constr:(A `union` B `union` C `union` D `union` E).

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
  - apply Permutation_length_1_inv in INB; substs; simpl_env; auto.
  - apply Permutation_length_1_inv in INB; substs; simpl_env; auto.
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
         (FV: x `in` fv_proc ({k ~> y}P)),
    x `in` fv_proc P.
Proof.
  i; gen k; induction P; ii; destruct_all pname; des; destruct_in; tryfalse
  ; eauto.
Qed.

Lemma open_fv_proc_2:
  forall x y k P
         (FV: x `in` fv_proc P),
    x `in` fv_proc ({k ~> y}P).
Proof.
  i; gen k; induction P; ii; destruct_all pname; des; destruct_in; eauto.
Qed.

Lemma open_nfv_proc_1:
  forall x y k P
         (NEQ: x <> y)
         (NFV: x `notin` fv_proc P),
    x `notin` fv_proc ({k ~> y}P).
Proof.
  i; gen k; induction P; ii; destruct_all pname; des; destruct_in; eauto.
Qed.

Lemma open_nfv_proc_2:
  forall x y k P
         (NFV: x `notin` fv_proc ({k ~> y}P)),
    x `notin` fv_proc P.
Proof.
  i; gen k; induction P; ii; destruct_all pname; des; destruct_in; eauto.
Qed.

Hint Resolve open_fv_proc_1 open_fv_proc_2 open_nfv_proc_1 open_nfv_proc_2.

Lemma nfv_env_proc:
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
    + apply (@open_nfv_proc_2 x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; auto.
      apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
    + apply (@open_nfv_proc_2 x y 0) in H3; auto.
      ii; apply (H0 y); auto; ii; destruct_in; auto.
      apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_nfv_proc_2 x y 0) in H0; auto.
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
    + apply (@open_nfv_proc_2 x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; substs~
      ; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_nfv_proc_2 x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; substs~
      ; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_nfv_proc_2 x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; substs~
      ; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_nfv_proc_2 x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; substs~
      ; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
  - ii; destruct_in; pick fresh y; destruct_notin; substs~.
    + apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; []; s; fsetdec.
    + apply (@open_nfv_proc_2 x y 0) in H2; auto.
      ii; apply (H y); auto; ii; destruct_in; substs~
      ; apply Permutation_sym in PER; apply Perm_in with (x:=x) in PER; auto
      ; try repeat (rewrite !cons_app_one in *||rewrite !dom_app in *)
      ; s; fsetdec.
Qed.

(** Exporting required entities from AtomSetImpl, AtomSetFacts and
    AtomSetProperties. *)
Definition elements := Metatheory.elements.
Definition elements_3w := AtomSetImpl.elements_3w.
Definition elements_iff := AtomSetFacts.elements_iff.
Definition equal_sym := AtomSetProperties.equal_sym.
Definition remove := Metatheory.remove.
Definition remove_iff := AtomSetFacts.remove_iff.
Definition union_2 := AtomSetImpl.union_2.

Lemma remove_union:
  forall x s s',
    remove x (union s s')[=]union (remove x s) (remove x s').
Proof. fsetdec. Qed.

Lemma remove_nfv_proc_eq:
  forall P k (x y:atom)
         (NFX: x `notin` fv_proc P)
         (NFY: y `notin` fv_proc P),
    remove y (fv_proc ({k ~> y}P))[=]remove x (fv_proc ({k ~> x}P)).
Proof.
  induction P; ii; destruct_notin
  ; try (by destruct_all pname; des; destruct_notin; fsetdec).
  - rewrite !remove_union; rewrite~ (IHP1 (S k) x y)
    ; rewrite~ (IHP2 (S k) y x); fsetdec.
  - destruct_all pname; des; destruct_notin; rewrite !remove_union
    ; rewrite~ (IHP1 (S k) x y); rewrite~ (IHP2 (S k) y x); fsetdec.
  - destruct_all pname; des; destruct_notin; rewrite !remove_union
    ; rewrite~ (IHP (S k) x y); fsetdec.
  - destruct_all pname; des; destruct_notin; rewrite !remove_union
    ; rewrite~ (IHP k x y); fsetdec.
  - destruct_all pname; des; destruct_notin; rewrite !remove_union
    ; rewrite~ (IHP k x y); fsetdec.
  - destruct_all pname; des; destruct_notin; rewrite !remove_union
    ; rewrite~ (IHP1 k x y); rewrite~ (IHP2 k y x); fsetdec.
  - destruct_all pname; des; destruct_notin; rewrite !remove_union
    ; rewrite~ (IHP (S k) x y); fsetdec.
  - destruct_all pname; des; destruct_notin; rewrite !remove_union
    ; rewrite~ (IHP (S k) x y); fsetdec.
  - destruct_all pname; des; destruct_notin; rewrite !remove_union
    ; rewrite~ (IHP k x y); fsetdec.
  - destruct_all pname; des; destruct_notin; rewrite !remove_union
    ; rewrite~ (IHP k x y); fsetdec.
  - destruct_all pname; des; destruct_notin; rewrite !remove_union
    ; rewrite~ (IHP k x y); fsetdec.
  - destruct_all pname; des; destruct_notin; rewrite !remove_union
    ; rewrite~ (IHP k x y); fsetdec.
Qed.

Lemma eq_InA_elements:
  forall xs ys x
         (EQ: xs[=]ys)
         (IN: InA Logic.eq x (elements xs)),
    InA Logic.eq x (elements ys).
Proof.
  ii; apply elements_iff in IN; apply elements_iff; fsetdec.
Qed.

Lemma in_env_fv_1:
  forall P Γ x
         (WT: P ⊢cp Γ)
         (IN: x `in` dom Γ),
    x `in` fv_proc P.
Proof.
  ii; induction WT.
  - forwards IN2: Perm_in PER IN; ss; fsetdec.
  - pick fresh y; destruct_notin; specializes H Fr; specializes H0 Fr; s; des.
    forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in.
    + exploit H; [fsetdec|]; []; ii; apply open_fv_proc_1 in H; auto.
    + exploit H0; [fsetdec|]; []; ii; apply open_fv_proc_1 in H0; auto.
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
    exploit H; [fsetdec|]; ii; apply open_fv_proc_1 in H; auto.
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
    exploit H; [fsetdec|]; ii; apply open_fv_proc_1 in H; auto.
  - forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
  - forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
  - forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
    exploit H; [fsetdec|]; ii; apply open_fv_proc_1 in H; auto.
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
    exploit H; [fsetdec|]; ii; apply open_fv_proc_1 in H; auto.
  - forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
  - ss; fsetdec.
  - forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
  - ss; fsetdec.
Qed.

Lemma in_env_fv_2:
  forall P Γ x
         (WT: P ⊢cp Γ)
         (IN: x `in` fv_proc P),
    x `in` dom Γ.
Proof.
  ii; induction WT.
  - apply Permutation_sym in PER; applys Perm_in PER; ss; fsetdec.
  - pick fresh y; destruct_notin; specializes H Fr; specializes H0 Fr; des; i.
    apply Permutation_sym in PER; applys Perm_in PER; ss
    ; rewrite !dom_app in *; destruct_in.
    + apply (open_fv_proc_2 y 0) in IN0; fsetdec.
    + apply (open_fv_proc_2 y 0) in IN1; fsetdec.
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    apply Permutation_sym in PER; applys Perm_in PER; ss
    ; rewrite !dom_app in *; destruct_in; try (by ss; fsetdec).
    apply (open_fv_proc_2 y 0) in IN0; fsetdec.
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
    apply (open_fv_proc_2 y 0) in IN1; fsetdec.
  - apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
  - apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
  - apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
    apply (open_fv_proc_2 y 0) in IN1; fsetdec.
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
    apply (open_fv_proc_2 y 0) in IN1; fsetdec.
  - apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
  - ss; fsetdec.
  - apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
  - ss; fsetdec.
Qed.

Lemma in_env_fv:
  forall P Γ x
         (WT: P ⊢cp Γ),
    x `in` dom Γ <-> x `in` fv_proc P.
Proof. ii; split; eauto using in_env_fv_1,in_env_fv_2. Qed.

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

  Lemma subst_open_rec:
    forall P x y k,
      [y ~> x] ({k ~> y} P) = {k ~> x} ([y ~> x] P).
  Proof.
    ii; gen k; induction P; ii; destruct_all pname; des; tryfalse
    ; f_equal; auto.
  Qed.

  Lemma subst_open_var :
    forall (x y : atom) u t
           (NEQ: y <> x),
      open_proc ([x ~> u] t) y = [x ~> u] (open_proc t y).
  Proof.
    ii; unfold open_proc; auto using lc_open_subst.
  Qed.

  Lemma subst_intro_open_rec:
    forall x u t k
           (NIN: x `notin` (fv_proc t)),
      {k ~> u} t = [x ~> u]({k ~> x} t).
  Proof.
    ii; gen k; induction t; ii; destruct_all pname; des; substs; f_equal
    ; solve [auto|fsetdec].
  Qed.

  Lemma subst_intro :
    forall (x : atom) u t
           (NIN: x `notin` (fv_proc t)),
      open_proc t u = [x ~> u](open_proc t x).
  Proof.
    ii; unfold open_proc; rewrite~ <-subst_intro_open_rec.
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
        { specializes CPQ NL; forwards FV: nfv_env_proc x CPQ; [solve_notin|].
          rewrite* subst_fresh. }
      + eapply cp_cut with (L:=L')(ΔP:=ΔP)(ΔQ:=Γ1++Γ2++y~A0)
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|].
          solve_perm. }
        { specializes CPP NL; forwards FV: nfv_env_proc x CPP; [solve_notin|].
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
        { specializes CPP NL; forwards~ FV: nfv_env_proc x0 CPP
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
        { rewrite~ subst_fresh; forwards~ FV: nfv_env_proc x WT. }
      + apply binds_env_split in BindsTac0
        ; inversion_clear BindsTac0 as (Γ1 & Γ2 & EQ); substs~.
        rewrite 2 app_assoc in *; apply perm_dom_uniq in PER; auto; ss
        ; obtain atoms L' as LEQ; destruct_notin; destruct (x0 == x)
        ; tryfalse.
        clear n0; eapply cp_output with (L:=L')(ΔP:=ΔP)(ΔQ:=Γ1++Γ2++y~A0)
        ; ii; substs~; destruct_notin.
        { eapply Permutation_trans; [apply Permutation_app|]
          ; [exact PER|auto|]; []; solve_perm. }
        { specializes CPP NL; forwards FV: nfv_env_proc x CPP; [solve_notin|].
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
        { specializes CPP NL; forwards~ FV: nfv_env_proc x0 CPP
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
        { specializes CPP NL; forwards~ FV: nfv_env_proc x0 CPP
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
        { forwards~ FV: nfv_env_proc x0 WT; rewrite~ subst_fresh. }
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
        { forwards~ FV: nfv_env_proc x0 WT; rewrite~ subst_fresh. }
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
    - eapply Permutation_sym,Permutation_trans,Permutation_sym in PER
      ; [|apply Permutation_app_comm].
      apply Permutation_length_1_inv in PER; inverts PER; s; des; auto.
  Qed.

  Lemma typing_rename:
    forall Γ P k (x y : atom) A
           (NINX: x `notin` dom Γ `union` fv_proc P)
           (NINY: y `notin` dom Γ `union` fv_proc P)
           (WTX: {k ~> x}P ⊢cp (x ~ A) ++ Γ),
      {k ~> y}P ⊢cp (y ~ A) ++ Γ.
  Proof.
    ii; destruct (x == y); subst; auto; simpl_env in *.
    forwards UN: cp_implies_uniq WTX.
    rewrite (@subst_intro_open_rec x); auto.
    eapply ignore_env_order; [apply Permutation_app_comm|].
    apply typing_subst with (A := A); [solve_uniq|].
    eapply ignore_env_order; [apply Permutation_app_comm|]; auto.
  Qed.

  Lemma swap_binders_id:
    forall P i,
      {i <~> i} P = P.
  Proof.
    intro; induction P; i; ss; destruct_all pname; des; substs; f_equal; auto.
  Qed.

  Lemma swap_binders_fv:
    forall P i j,
      fv_proc ({i <~> j}P) = fv_proc P.
  Proof.
    ii; destruct (i == j); substs; [rewrite~ swap_binders_id|]; gen i j.
    induction P; ii; destruct_all pname; des; substs; tryfalse
    ; repeat (f_equal; auto).
  Qed.

  Lemma swap_binders_open_id:
    forall P x i j,
      {i ~> x}({j ~> x}({i <~> j}P)) = {i ~> x}({j ~> x}P).
  Proof.
    ii; destruct (i == j); substs; [rewrite~ swap_binders_id|].
    gen i j; induction P; ii; destruct_all pname; des; substs; tryfalse
    ; f_equal; auto.
  Qed.

  Lemma swap_binders_open:
    forall P x y i j,
      {i ~> x}({j ~> y}({i <~> j}P)) = {j ~> x}({i ~> y}P).
  Proof.
    ii; destruct (i == j); substs; [rewrite~ swap_binders_id|].
    destruct (x == y); substs
    ; [rewrite swap_binders_open_id; rewrite~ open_rec_comm|].
    gen i j; induction P; ii; destruct_all pname; des; substs; tryfalse
    ; f_equal; auto.
  Qed.

End CPBasicSubstOpenProperties.

Lemma wt_nin_env:
  forall (Γ Δ:penv) (x:atom)
         (NIN: x `notin` dom Γ)
         (IN: x `in` dom Δ)
         (PER: Permutation Γ Δ),
    False.
Proof.
  ii; apply NIN; analyze_in x; apply Permutation_sym in PER
  ; forwards: Perm_in x PER; simpl_env; fsetdec.
Qed.

Lemma wt_nin_proc:
  forall Γ P k (x:atom)
         (NIN: x `notin` dom Γ)
         (WT: {k ~> x}P ⊢cp Γ),
    P ⊢cp Γ.
Proof.
  i; remember ({k ~> x}P) as P'; gen P k; induction WT; ii
  ; match goal with
    | |- context[?P ⊢cp ?Γ] => destruct P; try discriminate; inv HeqP'
    end.
  - forwards UN1: uniq_perm PER UN.
    destruct_all pname; des; destr_eq H0; destr_eq H1; subst
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    apply cp_fwd with (A:=A); auto.
  - pick fresh y and apply cp_cut; destruct_notin
    ; try (solve [eassumption|auto]); specializes H Fr; specializes H0 Fr
    ; first [apply H with (k0:=S k)|apply H0 with (k0:=S k)]
    ; solve [rewrite /open_proc; rewrite~ open_rec_comm
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H1; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    pick fresh y and apply cp_output; destruct_notin; ss
    ; try (solve [eassumption|auto])
    ; first [specializes H Fr; apply H with (k0:=S k)
            |apply IHWT with (k0:=S k)]
    ; solve [reflexivity
            |rewrite /open_proc; rewrite~ open_rec_comm
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H1; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    pick fresh y and apply cp_input; destruct_notin; ss
    ; try (solve [eassumption|auto]); specializes H Fr; apply H with (k0:=S k)
    ; solve [rewrite /open_proc; rewrite~ open_rec_comm
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H; destr_eq H0; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    applys cp_left PER; apply IHWT with (k0:=k); eauto using wt_nin_env.
  - destruct_all pname; des; destr_eq H; destr_eq H0; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    applys cp_right PER; apply IHWT with (k0:=k); eauto using wt_nin_env.
  - destruct_all pname; des; destr_eq H0; destr_eq H1; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    applys cp_choice PER
    ; first [apply IHWT1 with (k0:=k)
            |apply IHWT2 with (k0:=k)]
    ; solve [reflexivity
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H1; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    pick fresh y and apply cp_accept; destruct_notin; ss
    ; try (solve [eassumption|auto]); specializes H Fr; apply H with (k0:=S k)
    ; solve [rewrite /open_proc; rewrite~ open_rec_comm
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H1; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    pick fresh y and apply cp_request; destruct_notin; ss
    ; try (solve [eassumption|auto]); specializes H Fr; apply H with (k0:=S k)
    ; solve [rewrite /open_proc; rewrite~ open_rec_comm
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H1; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    applys~ cp_weaken PER; apply IHWT with (k0:=k)
    ; solve [reflexivity
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H1; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    pick fresh y and apply cp_send; destruct_notin; ss
    ; try (solve [eassumption|auto]); specializes H Fr; apply H with (k0:=k)
    ; solve [reflexivity
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H1; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    pick fresh y and apply cp_recv; destruct_notin; ss
    ; try (solve [eassumption|auto]); specializes H Fr; apply H with (k0:=k)
    ; solve [reflexivity
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H; substs~; fsetdec.
  - destruct_all pname; des; destr_eq H0; destr_eq H; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    applys~ cp_empin PER; apply IHWT with (k0:=k)
    ; solve [reflexivity
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H; substs~; fsetdec.
Qed.

Section ProcEquiv.

  (* Process equivalence w.r.t typing. *)
  Definition proc_equiv : relation proc :=
    fun P Q => forall Γ, P ⊢cp Γ <-> Q ⊢cp Γ.
  
End ProcEquiv.

Lemma fv_proc_NoDup:
  forall P, NoDupA Logic.eq (elements (fv_proc P)).
Proof.
  intro P; generalize (fv_proc P); apply elements_3w.
Qed.

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
        ν A → P ‖ (ν B → {0 <~> 1}Q ‖ {0 <~> 1}R)
  | red_add_inl :
      forall P Q R A B,
        ν A ⨁ B → (0[inl] → P) ‖ 0 CASE Q OR R
      ==>cp
        ν A → P ‖ Q
  | red_add_inr :
      forall P Q R A B,
        ν A ⨁ B → (0[inr] → P) ‖ 0 CASE Q OR R
      ==>cp
        ν B → P ‖ R
  | red_spawn :
      forall P Q A dA (DUA: dual_props A dA),
        ν ! A → ! ⟨A⟩ 0 → P ‖ ? [dA]0 → Q
      ==>cp
        ν A → P ‖ Q
  | red_gc :
      forall P Q (y:atom) A
             (NF: y `notin` fv_proc P),
        ν ! A → ! ⟨A⟩0 → P ‖ ? [] 0 → Q
      ==>cp
        weakenv (elements (remove y (fv_proc (P ^^ y)))) Q
  | red_exp :
      forall P Q A B x
             (NFV: x `notin` fv_proc Q `union` fv_prop B),
        ν B → p_send 0 A P ‖ p_recv 0 Q
      ==>cp
        ν {{ A // x }}(open_prop B x) → P ‖ [x ~>p A](Q ^^p x)
  | red_unit :
      forall P,
        ν pp_one → (0 → 0) ‖ ⟨⟩0 → P
      ==>cp
        P
where "P '==>cp' Q" := (proc_red P Q) : cp_scope.

(* Find co-finitely quantified hypotheses to specialise. *)
Ltac find_specializes :=
  repeat match goal with
         | [H: forall x, x `notin` ?L -> _, H1: ?y `notin` ?L |- _]
           => specializes H H1
         end.

Lemma assoc:
  forall P Q R A B Γ
         (WT: ν A → P ‖ ν B → Q ‖ R ⊢cp Γ),
    ν B → ν A → P ‖ Q ‖ R ⊢cp Γ.
Proof.
  ii; inverts WT.
  pick fresh x; destruct_notin.
  specializes CPP Fr.
  specializes CPQ Fr.
  inverts CPQ.
  pick fresh y; destruct_notin; find_specializes.
  forwards UN1: uniq_perm PER0 UN0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  extract_bnd x (¬A).
  - simpl_env in *; apply perm_dom_uniq in PER0; [|solve_uniq].
    eapply Permutation_sym,Permutation_trans,Permutation_sym in PER
    ; [|apply Permutation_app]; [|auto|apply Permutation_sym; exact PER0].
    rewrite /open_proc in CPQ0; rewrite~ open_rec_comm in CPQ0.
    apply wt_nin_proc in CPQ0; [|simpl_env; solve_notin].
    rewrite !app_assoc in PER.
    forwards UN2: uniq_perm PER UN.
    obtain atoms L' as LEQ; eapply cp_cut with (L:=L'); try exact PER; auto
    ; i; substs; destruct_notin.
    + forwards NIN: Perm_notin PER0 NotInTac1; simpl_env in *.
      apply typing_rename with (x:=y); try by solve_notin.
      rewrite /open_proc; s; simpl_env.
      eapply ignore_env_order; [apply Permutation_app_comm|].
      simpl_env; obtain atoms L' as LEQ; eapply cp_cut with (L:=L'); auto
      ; first solve_uniq; i; substs; destruct_notin
      ; apply typing_rename with (x:=x); try by solve_notin.
      * rewrite /open_proc; rewrite~ open_rec_comm. 
        rewrite lc_no_bvar; eauto using cp_implies_lc.
      * admit (* Not provable... *).
    + apply typing_rename with (x:=y); try solve_notin.
  - admit (* this isn't provable either... *).
Admitted.

(** Lemmas for proving well-typedness of reduction rules. *)

Lemma reduce_axcut:
  forall P A (w : atom) Γ
         (NFV: w `notin` fv_proc P)
         (WT: ν A → w ⟷ 0 ‖ P ⊢cp Γ),
    P ^^ w ⊢cp Γ.
Proof.
  ii; inversion WT; subst.
  pick fresh y; destruct_notin; find_specializes.
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
  unfold open_proc in *.
  apply typing_rename with (x:=y); try (by destruct_uniq; solve_notin).
Qed.

Lemma reduce_multi:
  forall P Q R A dA B Γ
         (DUA: dual_props A dA)
         (WT: ν A ⨂ B → [A]0 → P ‖ Q ‖ ⟨dA ⟩ 0 → R ⊢cp Γ),
    ν A → P ‖ ν B → {0 <~> 1}Q ‖ {0 <~> 1}R ⊢cp Γ.
Proof.
  ii; inversion WT; subst.
  pick fresh y; destruct_notin
  ; repeat match goal with
             | [H: forall x, x `notin` ?L -> _, H1: ?y `notin` ?L |- _]
               => specializes H H1; rewrite /open_proc in H; s in H
                  ; inverts keep H; simpl_env in *
           end.
  pick fresh z; destruct_notin; find_specializes.

  forwards UNP: uniq_perm PER0 UN0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER0; forwards EQC: perm_cod_uniq PER0
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq]; rewrite app_nil_l in PER0.

  forwards UNQ: uniq_perm PER1 UN1.
  eapply Permutation_trans in PER1; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER1; forwards EQC: perm_cod_uniq PER1
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER1; [|solve_uniq]; rewrite app_nil_l in PER1.

  rewrite /open_proc open_rec_comm in CPP1; auto.
  apply wt_nin_proc in CPP1; [|simpl_env; autounfold; i; destruct_in; auto
                               ; applys wt_nin_env NotInTac0 PER1; simpl_env
                               ; fsetdec].
  eapply Permutation_sym,Permutation_trans in PER
  ; [|apply Permutation_app; apply Permutation_sym; eassumption].
  apply Permutation_sym in PER; forwards UNG: uniq_perm PER UN
  ; apply Permutation_sym in PER.
  applys ignore_env_order PER; simpl_env.
  pick fresh w and apply cp_cut; destruct_notin; auto; first solve_uniq
  ; let v := match goal with
               | |- context[P] => z
               | |- context[Q] => y
             end
    in
    apply typing_rename with (x:=v); try (by try (s; rewrite !swap_binders_fv)
                                          ; destruct_uniq; solve_notin)
    ; clears w.
  eapply ignore_env_order; [apply Permutation_app_comm|]; s.
  simpl_env; pick fresh w and apply cp_cut; destruct_notin; auto
  ; first solve_uniq.
  - rewrite /open_proc; rewrite swap_binders_open; rewrite~ open_rec_comm.
    forwards QEQ: subst_fresh y w Q; [solve_notin|].
    forwards OPQ: subst_open_rec Q w y 1; rewrite QEQ in OPQ.
    eapply ignore_env_order in CPQ0; [|apply Permutation_app_comm].
    apply typing_subst with (y:=w) in CPQ0; [|solve_uniq].
    eapply ignore_env_order in CPQ0; [|apply Permutation_app_comm].
    rewrite OPQ in CPQ0.
    forwards LC: cp_implies_lc CPQ0; rewrite~ lc_no_bvar.
  - unfold open_proc in *.
    rewrite swap_binders_open; rewrite~ open_rec_comm; rewrite app_assoc.
    eapply ignore_env_order; [apply Permutation_app_comm|].
    apply typing_rename with (x:=z); try (by destruct_uniq; solve_notin).
    rewrite~ open_rec_comm.
    eapply ignore_env_order; [apply Permutation_app_comm|].
    simpl_env; apply typing_rename with (x:=y)
    ; try (by destruct_uniq; solve_notin).
    rewrite app_assoc.
    eapply ignore_env_order; [apply Permutation_app_comm|].
    rewrite~ open_rec_comm.
Qed.

Lemma reduce_add_inl:
  forall P Q R A B Γ
         (WT: ν A ⨁ B → (0[inl] → P) ‖ 0 CASE Q OR R ⊢cp Γ),
    ν A → P ‖ Q ⊢cp Γ.
Proof.
  ii; inversion WT; subst.
  pick fresh y; destruct_notin
  ; repeat match goal with
             | [H: forall x, x `notin` ?L -> _, H1: ?y `notin` ?L |- _]
               => specializes H H1; rewrite /open_proc in H; s in H
                  ; inverts keep H; simpl_env in *
           end.

  forwards UN0: cp_implies_uniq CPP0.
  apply Permutation_sym in PER0; forwards UNQ: uniq_perm PER0; [solve_uniq|]
  ; apply Permutation_sym in PER0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER0; forwards EQC: perm_cod_uniq PER0
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq]; rewrite app_nil_l in PER0.

  forwards UN1: cp_implies_uniq CPP1.
  apply Permutation_sym in PER1; forwards UNP: uniq_perm PER1; [solve_uniq|]
  ; apply Permutation_sym in PER1.
  eapply Permutation_trans in PER1; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER1; forwards EQC: perm_cod_uniq PER1
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER1; [|solve_uniq]; rewrite app_nil_l in PER1.

  eapply Permutation_sym,Permutation_trans in PER
  ; [|apply Permutation_app; apply Permutation_sym; eassumption].
  applys ignore_env_order PER.
  apply Permutation_sym in PER; apply (uniq_perm _ _ _ PER) in UN.
  forwards NINP: Perm_notin PER1 NotInTac0.
  forwards NINQ: Perm_notin PER0 NotInTac1.
  pick fresh x and apply cp_cut; destruct_notin; auto
  ; apply typing_rename with (x:=y); try (by solve_notin).
Qed.

Lemma reduce_add_inr:
  forall P Q R A B Γ
         (WT: ν A ⨁ B → (0[inr] → P) ‖ 0 CASE Q OR R ⊢cp Γ),
    ν B → P ‖ R ⊢cp Γ.
Proof.
  ii; inversion WT; subst.
  pick fresh y; destruct_notin
  ; repeat match goal with
             | [H: forall x, x `notin` ?L -> _, H1: ?y `notin` ?L |- _]
               => specializes H H1; rewrite /open_proc in H; s in H
                  ; inverts keep H; simpl_env in *
           end.

  forwards UN0: cp_implies_uniq CPP0.
  apply Permutation_sym in PER0; forwards UNQ: uniq_perm PER0; [solve_uniq|]
  ; apply Permutation_sym in PER0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER0; forwards EQC: perm_cod_uniq PER0
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq]; rewrite app_nil_l in PER0.

  forwards UN1: cp_implies_uniq CPP1.
  apply Permutation_sym in PER1; forwards UNP: uniq_perm PER1; [solve_uniq|]
  ; apply Permutation_sym in PER1.
  eapply Permutation_trans in PER1; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER1; forwards EQC: perm_cod_uniq PER1
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER1; [|solve_uniq]; rewrite app_nil_l in PER1.

  eapply Permutation_sym,Permutation_trans in PER
  ; [|apply Permutation_app; apply Permutation_sym; eassumption].
  applys ignore_env_order PER.
  apply Permutation_sym in PER; apply (uniq_perm _ _ _ PER) in UN.
  forwards NINP: Perm_notin PER1 NotInTac0.
  forwards NINQ: Perm_notin PER0 NotInTac1.
  pick fresh x and apply cp_cut; destruct_notin; auto
  ; apply typing_rename with (x:=y); try (by solve_notin).
Qed.

Lemma reduce_spawn:
  forall P Q A dA Γ
         (DUA: dual_props A dA)
         (WT: ν ! A → ! ⟨A⟩ 0 → P ‖ ? [dA]0 → Q ⊢cp Γ),
    ν A → P ‖ Q ⊢cp Γ.
Proof.
  ii; inversion WT; subst.
  pick fresh y; destruct_notin
  ; repeat match goal with
             | [H: forall x, x `notin` ?L -> _, H1: ?y `notin` ?L |- _]
               => specializes H H1; rewrite /open_proc in H; s in H
                  ; inverts keep H; simpl_env in *
           end.
  pick fresh z; destruct_notin; find_specializes.

  forwards UNQ: uniq_perm PER0 UN0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER0; forwards EQC: perm_cod_uniq PER0
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq]; rewrite app_nil_l in PER0.

  forwards UNP: uniq_perm PER1 UN1.
  eapply Permutation_trans in PER1; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER1; forwards EQC: perm_cod_uniq PER1
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER1; [|solve_uniq]; rewrite app_nil_l in PER1.

  rewrite /open_proc open_rec_comm in CPP1; auto.
  apply wt_nin_proc in CPP1; [|simpl_env; autounfold; i; destruct_in; auto
                               ; applys wt_nin_env NotInTac0 PER1; simpl_env
                               ; fsetdec].
  rewrite /open_proc open_rec_comm in CPP0; auto.
  apply wt_nin_proc in CPP0; [|simpl_env; autounfold; i; destruct_in; auto
                               ; applys wt_nin_env NotInTac1 PER0; simpl_env
                               ; fsetdec].
  eapply Permutation_sym,Permutation_trans in PER
  ; [|apply Permutation_app; apply Permutation_sym; eassumption].
  apply Permutation_sym in PER; forwards UNG: uniq_perm PER UN
  ; apply Permutation_sym in PER.
  applys ignore_env_order PER; simpl_env.

  pick fresh w and apply cp_cut; destruct_notin; auto
  ; apply typing_rename with (x:=z); try (by destruct_uniq; solve_notin).
Qed.

Lemma reduce_gc:
  forall P Q (y:atom) A Γ
         (NF: y `notin` fv_proc P)
         (WT: ν ! A → ! ⟨A⟩0 → P ‖ ? [] 0 → Q ⊢cp Γ),
    weakenv (elements (remove y (fv_proc (P ^^ y)))) Q ⊢cp Γ.
Proof.
  ii; forwards LC: cp_implies_lc WT; inversion WT; inverts LC; subst.
  pick fresh z; destruct_notin; find_specializes.
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
  ; try solve_uniq; auto using elements_3w.
  - rewrite /open_proc in CPQ; s in CPQ.
    inverts keep CPQ; simpl_env in *.
    forwards UN4: uniq_perm PER1 UN3.
    eapply Permutation_trans in PER1; [|apply Permutation_app_comm].
    rewrite <-app_nil_l in PER1; forwards EQC: perm_cod_uniq PER1
    ; [solve_uniq|]; inverts EQC; substs~.
    apply perm_dom_uniq in PER1; [|solve_uniq]; rewrite app_nil_l in PER1.
    apply Permutation_sym in PER1; apply (ignore_env_order PER1) in CPP1.
    applys wt_nin_proc NotInTac4 CPP1.
  - pick fresh w; destruct_notin; find_specializes.
    rewrite /open_proc in CPP0; rewrite~ open_rec_comm in CPP0.
    forwards PER1: Permutation_app_head (w~A) PER0.
    apply Permutation_sym in PER1; apply (ignore_env_order PER1) in CPP0.
    apply wt_nin_proc in CPP0; [|ss;fsetdec].
    eapply ignore_env_order in CPP0; [|apply Permutation_app_comm].
    forwards UN3: cp_implies_uniq CPP0.
    forwards EQ: remove_nfv_proc_eq NF NotInTac20.
    split; ii.
    + apply InA_iff_In; applys eq_InA_elements EQ.
      apply Permutation_sym in PER0; forwards IN: Perm_in PER0 H.
      apply elements_iff,remove_iff; destruct (x == w)
      ; [analyze_in x; solve_uniq|].
      split; auto.
      apply open_fv_proc_2.
      apply in_env_fv with (x:=x) in CPP0; des; rewrite !dom_app in *.
      specialize (CPP1 (union_2 _ IN)); apply open_fv_proc_1 in CPP1; auto.
    + apply equal_sym in EQ; apply InA_iff_In,(eq_InA_elements EQ) in H.
      apply elements_iff,remove_iff in H; des.
      apply in_env_fv with (x:=x) in CPP0; des; rewrite !dom_app in *.
      applys Perm_in PER0.
      apply CPP2 in H0; ss; destruct_in; tryfalse; auto.
Qed.

Lemma reduce_exp:
  forall P Q A B Γ x
         (NFV: x `notin` fv_proc Q `union` fv_prop B)
         (WT: ν pp_exists B → p_send 0 A P ‖ p_recv 0 Q ⊢cp Γ),
    ν {{ A // x }}(open_prop B x) → P ‖ [x ~>p A](Q ^^p x) ⊢cp Γ.
Proof.
  ii; inversion WT; subst.
  pick fresh y; destruct_notin
  ; repeat match goal with
             | [H: forall x, x `notin` ?L -> _, H1: ?y `notin` ?L |- _]
               => specializes H H1; rewrite /open_proc in H; s in H
                  ; inverts keep H; simpl_env in *
           end.
  pick fresh z; destruct_notin; find_specializes.

  forwards UNQ: cp_implies_uniq CPQ.
  forwards UNΔ: uniq_perm PER0; [solve_uniq|].
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER0; forwards EQC: perm_cod_uniq PER0
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq]; rewrite app_nil_l in PER0.

  forwards UNP: cp_implies_uniq CPP.
  forwards UNΔ0: uniq_perm PER1; [solve_uniq|].
  eapply Permutation_trans in PER1; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER1; forwards EQC: perm_cod_uniq PER1
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER1; [|solve_uniq]; rewrite app_nil_l in PER1.

  eapply Permutation_sym,Permutation_trans in PER
  ; [|apply Permutation_app; apply Permutation_sym; eassumption].
  apply Permutation_sym in PER; forwards UNG: uniq_perm PER UN
  ; apply Permutation_sym in PER.
  applys ignore_env_order PER; simpl_env.

  forwards NINP: Perm_notin PER1 NotInTac2.
  forwards NINQ: Perm_notin PER0 NotInTac3.
  pick fresh w and apply cp_cut; destruct_notin; auto.
  apply typing_rename with (x:=y); try by solve_notin.
  admit (* Rename x to z in cod of env pair. *).

  apply typing_rename with (x:=y).
  admit (* fv_proc [x ~>p A](Q ^^p x) = ... *).
  admit (* fv_proc [x ~>p A](Q ^^p x) = ... *).
  rewrite prop_dual_preserves_subst; rewrite prop_dual_open_prop.
  admit (* Rename x to z in cod of env pair. *).
Admitted.

Lemma reduce_unit:
  forall P Γ
         (WT: ν pp_one → (0 → 0) ‖ ⟨⟩0 → P ⊢cp Γ),
    P ⊢cp Γ.
Proof.
  ii; inversion WT; subst.
  pick fresh y; destruct_notin
  ; repeat match goal with
             | [H: forall x, x `notin` ?L -> _, H1: ?y `notin` ?L |- _]
               => specializes H H1; rewrite /open_proc in H; s in H
                  ; inverts keep H; simpl_env in *
           end.

  forwards UNP: uniq_perm PER0 UN0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER0; forwards EQC: perm_cod_uniq PER0
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq]; rewrite app_nil_l in PER0.

  forwards NIN: Perm_notin PER0 NotInTac1.
  apply wt_nin_proc in CPP0; auto.
  forwards PER2: Permutation_sym (Permutation_trans PER PER0).
  applys~ ignore_env_order PER2.
Qed.

Hint Resolve reduce_axcut reduce_multi reduce_add_inl reduce_add_inr
     reduce_spawn reduce_gc reduce_exp reduce_unit.

Theorem proc_sub_red: forall Γ P Q
    (WT: P ⊢cp Γ)
    (RED: P ==>cp Q),
  Q ⊢cp Γ.
Proof. ii; induction RED; subst; eauto. Qed.
