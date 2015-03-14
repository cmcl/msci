(** Beginning of the file for CP mechanisation as described in

    Philip Wadler. 2012. Propositions as sessions. In Proceedings of the 17th
    ACM SIGPLAN international conference on Functional programming (ICFP '12).
    ACM, New York, NY, USA, 273-286. DOI=10.1145/2364527.2364568
    http://doi.acm.org/10.1145/2364527.2364568

*)
Require Import Metatheory.Metatheory.
Require Import Coq.Sorting.Permutation.

(** Exporting required entities from AtomSetImpl, AtomSetFacts and
    AtomSetProperties. *)
Definition elements := AtomSetImpl.elements.
Definition elements_3w := AtomSetImpl.elements_3w.
Definition elements_iff := AtomSetFacts.elements_iff.
Definition equal_sym := AtomSetProperties.equal_sym.
Definition remove := Metatheory.remove.
Definition remove_iff := AtomSetFacts.remove_iff.
Definition union_2 := AtomSetImpl.union_2.
Definition union_3 := AtomSetImpl.union_3.

Set Implicit Arguments.

(** Propositional variables are represented as natural numbers (bound) or
    atoms (free).
*)
Inductive pvar :=
  | pvar_bvar : nat -> pvar
  | pvar_fvar : atom -> pvar.

Coercion pvar_bvar : nat >-> pvar.
Coercion pvar_fvar : atom >-> pvar.

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
  | dual_umul : dual_props pp_one pp_bot
  | dual_uadd : dual_props pp_zero pp_top
  | dual_sym : forall P dP (DP: dual_props P dP),
                 dual_props dP P.

Hint Constructors dual_props.

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
  | _ => empty
  end.

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
      => [A] (sub z) → (proc_open_rec (S k) x P) ‖ (proc_open_rec k x Q)
    | ⟨A⟩ z → P => ⟨A⟩ (sub z) → (proc_open_rec (S k) x P)
    | z [inl] → P => (sub z) [inl] → (proc_open_rec k x P)
    | z [inr] → P => (sub z) [inr] → (proc_open_rec k x P)
    | z CASE P OR Q
      => (sub z) CASE (proc_open_rec k x P) OR (proc_open_rec k x Q)
    | ! ⟨A⟩ z → P => ! ⟨A⟩ (sub z) → (proc_open_rec (S k) x P)
    | ? [A] z → P => ? [A] (sub z) → (proc_open_rec (S k) x P)
    | ? [] z → P => ? [] (sub z) → (proc_open_rec k x P)
    | z → 0 => sub z → 0
    | ⟨⟩ z → P => ⟨⟩ (sub z) → (proc_open_rec k x P)
    | z CASE 0 => (sub z) CASE 0
    end.

Notation "{ k ~> u } t" := (proc_open_rec k u t) (at level 68,
                                                  right associativity).

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
    | z → 0 => fv z
    | ⟨⟩ z → P => fv z `union` fv_proc P
    | z CASE 0 => fv z
    end.

(* Permute binders inside process. *)
Reserved Notation "{ a <~> b } Q" (at level 68, right associativity).

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
      => [A] (swap z) → ({S a <~> S b} P) ‖ ({a <~> b}R)
    | ⟨A⟩ z → P => ⟨A⟩ (swap z) → ({S a <~> S b} P)
    | z [inl] → P => (swap z) [inl] → ({a <~> b} P)
    | z [inr] → P => (swap z) [inr] → ({a <~> b} P)
    | z CASE P OR R
      => (swap z) CASE ({a <~> b} P) OR ({a <~> b} R)
    | ! ⟨A⟩ z → P => ! ⟨A⟩ (swap z) → ({S a <~> S b} P)
    | ? [A] z → P => ? [A] (swap z) → ({S a <~> S b} P)
    | ? [] z → P => ? [] (swap z) → ({a <~> b} P)
    | z → 0 => swap z → 0
    | ⟨⟩ z → P => ⟨⟩ (swap z) → ({a <~> b} P)
    | z CASE 0 => (swap z) CASE 0
    end
where "{ a <~> b } P" := (swap_binders a b P) : cp_scope.

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
  | cp_empout : forall (x: atom), x → 0 ⊢cp x ~ pp_one
  | cp_empin : forall P Γ Δ (x:atom)
                      (PER: Permutation Γ (x ~ pp_bot ++ Δ))
                      (UN: uniq Γ)
                      (CPP: P ⊢cp Δ),
                 ⟨⟩ x → P ⊢cp Γ
  | cp_empcho : forall (x:atom), x CASE 0 ⊢cp x ~ pp_top
where "P '⊢cp' Γ" := (cp_rule P Γ) : cp_scope.

Hint Constructors cp_rule.

Fixpoint weakenv (xs:list atom) (P:proc) : proc :=
  match xs with
  | nil => P
  | x :: xs' => ? [] x → (weakenv xs' P)
  end.

Reserved Notation "P '==>cp' Q" (at level 69, right associativity).

(** Principal cut reductions and commuting conversions. *)
Inductive proc_red : proc -> proc -> Prop :=
  (** Principal cut reductions *)
  | red_axcut :
      forall P A (w x:atom) (NF: w `notin` fv_proc P),
        ν A → w ⟷ 0 ‖ P
      ==>cp
        (open_proc P w)
  | red_multi :
      forall P Q R A dA B (DUA: dual_props A dA),
        ν A ⨂ B → ([A]0 → P ‖ Q) ‖ ⟨dA⟩ 0 → R
      ==>cp
        ν A → P ‖ (ν B → Q ‖ {0 <~> 1}R)
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
  | red_unit :
      forall P,
        ν pp_one → (0 → 0) ‖ ⟨⟩0 → P
      ==>cp
        P
  (** Commuting conversions *)
  | red_cc_multi_one:
      forall P Q R (x:atom) A B
             (LCQ: lc_proc Q),
        ν A → ([B] x → P ‖ Q) ‖ R
      ==>cp
        [B] x → (ν A → {0 <~> 1}P ‖ R) ‖ Q
  | red_cc_multi_two:
      forall P Q R (x:atom) A B
             (LCP: forall x, lc_proc (P ^^ x)),
        ν A → ([B] x → P ‖ Q) ‖ R
      ==>cp
        [B] x → P ‖ (ν A → Q ‖ R)
  | red_cc_input:
      forall P Q (x:atom) A B,
        ν A → (⟨B⟩ x → P) ‖ Q
      ==>cp
        ⟨B⟩x → ν A → ({0 <~> 1}P) ‖ Q
  | red_cc_add_inl:
      forall P Q (x:atom) A,
        ν A → (x[inl] → P) ‖ Q
      ==>cp
        x[inl] → (ν A → P ‖ Q)
  | red_cc_add_inr:
      forall P Q (x:atom) A,
        ν A → (x[inr] → P) ‖ Q
      ==>cp
        x[inr] → (ν A → P ‖ Q)
  | red_cc_choice:
      forall P Q R (x:atom) A,
        ν A → (x CASE P OR Q) ‖ R
      ==>cp
        x CASE (ν A → P ‖ R) OR (ν A → Q ‖ R)
  | red_cc_accept:
      forall P Q (x:atom) A B
             (REQS: forall Γ Δ
                           (PER: Permutation Γ (x~! B++Δ))
                           (WT: ν A → (! ⟨B⟩x → P) ‖ Q ⊢cp Γ),
                      all_requests Δ),
        ν A → (! ⟨B⟩x → P) ‖ Q
      ==>cp
        ! ⟨B⟩x → (ν A → {0 <~> 1}P ‖ Q)
  | red_cc_request:
      forall P Q (x:atom) A B,
        ν A → (? [B]x → P) ‖ Q
      ==>cp
        ? [B]x → (ν A → P ‖ Q)
  | red_cc_weaken:
      forall P Q (x:atom) A,
        ν A → (? []x → P) ‖ Q
      ==>cp
        ? []x → (ν A → P ‖ Q)
  | red_cc_empin:
      forall P Q (x:atom) A,
        ν A → (⟨⟩x → P) ‖ Q
      ==>cp
        ⟨⟩x → (ν A → P ‖ Q)
  | red_cc_empcho:
      forall Q (x y:atom) A
           (REQS: forall Γ Δ
                         (PER: Permutation Γ (x~pp_top ++ Δ))
                         (WT: ν A → (? []0 → x CASE 0) ‖ Q ⊢cp Γ),
                    all_requests Δ)
             (NF: y `notin` fv_proc Q),
        ν A → (? []0 → x CASE 0) ‖ Q
      ==>cp
        weakenv (elements (remove y (fv_proc (Q ^^ y)))) (x CASE 0)
where "P '==>cp' Q" := (proc_red P Q) : cp_scope.

Definition is_cut (P:proc) : Prop :=
  match P with
  | ν _ → _ ‖ _ => True
  | _ => False
  end.