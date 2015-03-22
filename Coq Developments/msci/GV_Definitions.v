(** Beginning of the file for GV definitions as described in

    Philip Wadler. 2012. Propositions as sessions. In Proceedings of the 17th
    ACM SIGPLAN international conference on Functional programming (ICFP '12).
    ACM, New York, NY, USA, 273-286. DOI=10.1145/2364527.2364568
    http://doi.acm.org/10.1145/2364527.2364568

    which is based on ``Classic GV'' by Simon Gay and Vasco Vasconcelos in

    Simon J. Gay and Vasco T. Vasconcelos. 2010. Linear type theory for
    asynchronous session types. J. Funct. Program. 20, 1 (January 2010),19-50.
    DOI=10.1017/S0956796809990268 http://dx.doi.org/10.1017/S0956796809990268

*)
Require Import Metatheory Coq.Program.Tactics Program.Equality.
Set Implicit Arguments.

(** The notion of kind is borrowed from

    Karl Mazurak, Jianzhou Zhao, and Steve Zdancewic. 2010. Lightweight linear
    types in system f°. In Proceedings of the 5th ACM SIGPLAN workshop on
    Types in language design and implementation (TLDI '10). ACM, New York, NY,
    USA, 77-88. DOI=10.1145/1708016.1708027
    http://doi.acm.org/10.1145/1708016.1708027

    but there is no subsumption rule here. In other words, kinds are just a
    mechanism by which to classify types. The rationale for including kinds is
    to allow a later extension to a System F-pop inspired language.

    In lemmas and theorems, k is used to range over kinds.
*)
Inductive kind : Set :=
  | lin : kind (* linear *)
  | un : kind (* unlimited *).

(** [typ] is ranged over by T, U and V. It differs slightly from the
    definition given in Wadler's paper in the following ways:

      * Session types are defined within this inductive type rather than
        mutually; a technical convenience since Coq mutually inductive
        types can be tricky to manipulate,
      * Choice and branch are binary; this matches the intuition of tensor
        product which is defined as binary and also maps better to the CP
        with and plus constructs which are also binary
*)
Inductive typ : Set :=
(* Session types section *)
  | typ_soutput : typ -> typ -> typ
  | typ_sinput : typ -> typ -> typ
  | typ_schoice : typ -> typ -> typ
  | typ_sbranch : typ -> typ -> typ
  | typ_oend : typ (* output end *)
  | typ_iend : typ (* input end *)
(* Other non-session GV types *)
  | typ_tensor :  typ -> typ -> typ
  | typ_labs : typ -> typ -> typ
  | typ_abs : typ -> typ -> typ
  | typ_unit : typ (* always unlimited *).

(** The notation for sessions has been altered from the standard presentation
    to fit within allowable notations in Coq.
*)
Notation "'!' T '#' S" := (typ_soutput T S) (at level 68,
                                             right associativity) : gv_scope.
Notation "'?' T '#' S" := (typ_sinput T S) (at level 68, right associativity).
Notation "S1 '<+>' S2" := (typ_schoice S1 S2) (at level 68,
                                               right associativity)
                                              : gv_scope.
Notation "S1 <&> S2" := (typ_sbranch S1 S2) (at level 68,
                                             right associativity) : gv_scope.
Notation "T ⊸ U" := (typ_labs T U) (at level 68, right associativity)
                                   : gv_scope.
Notation "T → U" := (typ_abs T U) (at level 68, right associativity)
                                  : gv_scope.
Notation "T <x> U" := (typ_tensor T U) (at level 68, right associativity)
                                     : gv_scope.
Delimit Scope gv_scope with gv.
Open Scope gv_scope.

(** [ty] as defined above is more general than the types handled by GV; the
    types are considered session types and so could, for example, appear in
    branch or choice constructs (e.g. a regular function type). To prevent
    this, a predicate [is_session] is defined over [typ] constructors to
    restrict where certain constructors may occur.

    S range over session types.
*)
Inductive is_session : typ -> Prop :=
  | is_output : forall (T: typ) S
                       (IS: is_session S),
                  is_session (! T # S)
  | is_input : forall (T: typ) S
                      (IS: is_session S),
                 is_session (? T # S)
  | is_choice : forall S1 S2 (IS1: is_session S1) (IS2: is_session S2),
                  is_session (S1 <+> S2)
  | is_branch : forall S1 S2 (IS1: is_session S1) (IS2: is_session S2),
                  is_session (S1 <&> S2)
  | is_oend : is_session typ_oend
  | is_iend : is_session typ_iend.

Hint Constructors is_session.

(** Well-formed types are types with the correct kind annotations. *)
Inductive wf_typ : typ -> kind -> Prop :=
(* Session types section *)
  | wf_output : forall k T S (WFT: wf_typ T k) (WFS: wf_typ S lin)
                       (IS: is_session S),
                  wf_typ (! T # S) lin
  | wf_input : forall k T S (WFT: wf_typ T k) (WFS: wf_typ S lin)
                      (IS: is_session S),
                 wf_typ (? T # S) lin
  | wf_choice : forall S1 S2 (WFS1: wf_typ S1 lin) (WFS2: wf_typ S2 lin)
                       (IS1: is_session S1) (IS2: is_session S2),
                  wf_typ (S1 <+> S2) lin
  | wf_branch : forall S1 S2 (WFS1: wf_typ S1 lin) (WFS2: wf_typ S2 lin)
                       (IS1: is_session S1) (IS2: is_session S2),
                  wf_typ (S1 <&> S2) lin
  | wf_oend : wf_typ typ_oend lin (* output end *)
  | wf_iend : wf_typ typ_iend lin (* input end *)
(* Other non-session GV types *)
  | wf_tensor : forall kt ku T U (WFT: wf_typ T kt) (WFU: wf_typ U ku),
                  wf_typ (T <x> U) lin
  | wf_labs : forall kt ku T U (WFT: wf_typ T kt) (WFU: wf_typ U ku),
                wf_typ (T ⊸ U) lin
  | wf_abs : forall kt ku T U (WFT: wf_typ T kt) (WFU: wf_typ U ku),
               wf_typ (T → U) un
  | wf_unit : wf_typ typ_unit un.

Hint Constructors wf_typ.

(** Define a duality relation on session types to specify that two session
    types are dual to each other.

    The computational view of duality cannot be used in the well-typed term
    relation because the proof of duality cannot be inferred for an arbitrary
    session type argument.
*)
Inductive are_dual : typ -> typ -> Prop :=
  | output_dual : forall k T (WFT: wf_typ T k) S S' (DU: are_dual S S'),
                    are_dual (! T # S) (? T # S')
  | input_dual : forall k T (WFT: wf_typ T k) S S' (DU: are_dual S S'),
                   are_dual (? T # S) (! T # S')
  | choice_dual : forall S1 S2 S1' S2'
                         (DU1: are_dual S1 S1') (DU2: are_dual S2 S2'),
                    are_dual (S1 <+> S2) (S1' <&> S2')
  | branch_dual : forall S1 S2 S1' S2'
                         (DU1: are_dual S1 S1') (DU2: are_dual S2 S2'),
                    are_dual (S1 <&> S2) (S1' <+> S2')
  | oend_dual : are_dual typ_oend typ_iend
  | iend_dual : are_dual typ_iend typ_oend.

Hint Constructors are_dual.

(** Define a label type for binary branch and choice. *)
Inductive label : Set :=
  | lb_inr : label
  | lb_inl : label.

Inductive var : Set :=
  | bvar : nat -> var
  | fvar : atom -> var.

Coercion bvar : nat >-> var.
Coercion fvar : atom >-> var.

(** Define the terms of GV. We follow the approach in the UPenn Metatheory
    library, defining free variables as atoms and bound variables as de
    Bruijn indices.

*)
Inductive term : Set :=
  | tm_var : var -> term
  | tm_unit : term
  | tm_weak : var -> term -> term
  | tm_abs : typ -> term -> term
  | tm_app : term -> term -> term
  | tm_pair : term -> term -> term
  | tm_let : typ -> typ -> term -> term -> term
  | tm_send : term -> term -> term
  | tm_recv : term -> term
  | tm_select : label -> term -> term
  | tm_case : term -> label -> term -> label -> term -> term
  | tm_connect : typ -> term -> term -> term
  | tm_end : term -> term.

Coercion tm_var : var >-> term.

(** In the style of ``Engineering Formal Metatheory'' we define
    substitution of expressions for atoms and opening of expressions with
    bound variables.
*)


(** The following definition of substitution for a free variable assumes the
    term to be substituted is locally closed.
*)
Fixpoint subst (x: atom) (u: term) (t: term) : term :=
  match t with
  | tm_var (fvar y) => if x == y then u else (tm_var y)
  | tm_weak v m => tm_weak v (subst x u m)
  | tm_abs T b => tm_abs T (subst x u b)
  | tm_app m n => tm_app (subst x u m) (subst x u n)
  | tm_pair p q => tm_pair (subst x u p) (subst x u q)
  | tm_let T U m n => tm_let T U (subst x u m) (subst x u n)
  | tm_send m n => tm_send (subst x u m) (subst x u n)
  | tm_recv m => tm_recv (subst x u m)
  | tm_select l m => tm_select l (subst x u m)
  | tm_case m ll nl lr nr
    => tm_case (subst x u m) ll (subst x u nl) lr (subst x u nr)
  | tm_connect T m n => tm_connect T (subst x u m) (subst x u n)
  | tm_end m => tm_end (subst x u m)
  | _ => t
  end.

Notation "[ x ~> u ] t" := (subst x u t) (at level 68) : gv_scope.

(** Opening a term t is replacing an unbound variable with index k with term
    u. Assume u is locally closed and is only substituted once if it contains
    free variables.
*)
Fixpoint open_rec (k: nat) (u: term) (t: term) :=
  match t with
  | tm_var (bvar n) => if k == n then u else (tm_var n)
  | tm_weak v m => tm_weak v (open_rec k u m)
  | tm_abs T b => tm_abs T (open_rec (S k) u b)
  | tm_app m n => tm_app (open_rec k u m) (open_rec k u n)
  | tm_pair p q => tm_pair (open_rec k u p) (open_rec k u q)
  | tm_let T U m n
    => tm_let T U (open_rec k u m) (open_rec (S (S k)) u n)
  | tm_send m n => tm_send (open_rec k u m) (open_rec k u n)
  | tm_recv m => tm_recv (open_rec k u m)
  | tm_select l m => tm_select l (open_rec k u m)
  | tm_case m ll nl lr nr
    => tm_case (open_rec k u m)
               ll (open_rec (S k) u nl) lr (open_rec (S k) u nr)
  | tm_connect T m n
    => tm_connect T (open_rec (S k) u m) (open_rec (S k) u n)
  | tm_end m => tm_end (open_rec k u m)
  | _ => t
  end.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 68,
                                             right associativity) : gv_scope.

(** Opening a term t is replacing the unbound variable with index 0 with term
    u. Assume u is locally closed and is only substituted once if it contains
    free variables.
*)
Definition open t u := open_rec 0 u t.

Hint Unfold open.

Fixpoint GVFV (t: term) :=
  match t with
  | tm_var (fvar y) => singleton y
  | tm_weak (fvar y) m => singleton y `union` GVFV m
  | tm_weak _ m => GVFV m
  | tm_abs T b => GVFV b
  | tm_app m n => GVFV m `union` GVFV n
  | tm_pair p q => GVFV p `union` GVFV q
  | tm_let T U m n => GVFV m `union` GVFV n
  | tm_send m n => GVFV m `union` GVFV n
  | tm_recv m => GVFV m
  | tm_select l m => GVFV m
  | tm_case m ll nl lr nr => GVFV m `union` GVFV nl `union` GVFV nr
  | tm_connect T m n => GVFV m `union` GVFV n
  | tm_end m => GVFV m
  | _ => empty
  end.

(** A locally closed term has no unbounded variables. Note also using
    cofinite quantification with binding constructs. *)
Inductive lc : term -> Prop :=
  | lc_var : forall (x:atom), lc (tm_var x)
  | lc_unit : lc tm_unit
  | lc_weak : forall (x:atom) M (MLC: lc M), lc (tm_weak x M)
  | lc_abs : forall (L:atoms) k T M
                    (WFT: wf_typ T k)
                    (CO: forall (x:atom), x `notin` L -> lc (open M x)),
               lc (tm_abs T M)
  | lc_app : forall M N (MLC: lc M) (NLC: lc N), lc (tm_app M N)
  | lc_pair : forall M N (MLC: lc M) (NLC: lc N), lc (tm_pair M N)
  | lc_let : forall (L L':atoms) T U M N
                    (WF: wf_typ (T <x> U) lin)
                    (MLC: lc M)
                    (NCO: forall (x y:atom)
                                 (XL: x `notin` L)
                                 (YL: y `notin` L'),
                            lc ({1 ~> x} (open N y))),
               lc (tm_let T U M N)
  | lc_send : forall M N (MLC: lc M) (NLC: lc N), lc (tm_send M N)
  | lc_recv : forall M (MLC: lc M), lc (tm_recv M)
  | lc_select : forall lbl M (LCM: lc M), lc (tm_select lbl M)
  | lc_case : forall (L:atoms) M NL NR (MLC: lc M)
                     (NLCO: forall (x:atom), x `notin` L -> lc (open NL x))
                     (NRCO: forall (x:atom), x `notin` L -> lc (open NR x)),
                lc (tm_case M lb_inl NL lb_inr NR)
  | lc_connect : forall (L:atoms) T M N
                        (WFT: wf_typ T lin)
                        (MCO: forall (x:atom), x `notin` L -> lc (open M x))
                        (NCO: forall (x:atom), x `notin` L -> lc (open N x)),
                   lc (tm_connect T M N)
  | lc_end : forall M (MLC: lc M), lc (tm_end M).

Hint Constructors lc.

(** Typing environments are lists of (atom,typ) pairs. *)
Definition tenv := list (atom * typ).

Definition un_env (G : tenv) : Prop :=
  forall x (IN: x `in` dom G),
    exists T, wf_typ T un /\ binds x T G.

(** To get Coq to accept the '~' notation used here, we need to make sure t
    and T are parsed as identifiers.

    Reserved Notation "G |- t ~ T" (at level 68, t ident, T ident).

    Inductive wt_tm : tenv -> term -> forall k, typ k -> Prop :=
      | wt_tm_unid : forall x T, (x ~ inr T) |- x ~ T
    where "G '|-' t ~ T" := (wt_tm G t T) : gv_scope.

    However, I'm going to adopt the ∈ notation below since it will be easier
    to differentiate between the environment notation.
*)
Reserved Notation "Φ ⊢ t ∈ T" (at level 69).

Inductive wt_tm : tenv -> term -> typ -> Prop :=
  | wt_tm_id : forall k T x (WFT: wf_typ T k), x ~ T ⊢ x ∈ T
  | wt_tm_unit : nil ⊢ tm_unit ∈ typ_unit
  | wt_tm_weaken : forall Φ x N k T U
                          (WFT: wf_typ T un) (WFU: wf_typ U k)
                          (UN: uniq (Φ ++ x ~ T))
                          (WT: Φ ⊢ N ∈ U),
                     Φ ++ x ~ T ⊢ (tm_weak x N) ∈ U
  | wt_tm_labs : forall (L: atoms) Φ T U M
                        (WF: wf_typ (T ⊸ U) lin)
                        (UN: uniq Φ)
                        (WT: forall (x:atom),
                               x `notin` L ->
                               Φ ++ x ~ T ⊢ (open M x) ∈ U),
                   Φ ⊢ tm_abs T M ∈ T ⊸ U
  | wt_tm_lapp : forall Φ Ψ T U M N
                        (WF: wf_typ (T ⊸ U) lin)
                        (UN: uniq (Φ ++ Ψ))
                        (WTM: Φ ⊢ M ∈ T ⊸ U) (WTN: Ψ ⊢ N ∈ T),
                   Φ ++ Ψ ⊢ (tm_app M N) ∈ U
  | wt_tm_abs : forall Φ T U M
                       (WF: wf_typ (T → U) un)
                       (UN: uniq Φ)
                       (WT: Φ ⊢ M ∈ T ⊸ U) (UL: un_env Φ),
                  Φ ⊢ M ∈ T → U
  | wt_tm_app : forall Φ T U M
                       (WF: wf_typ (T ⊸ U) lin)
                       (UN: uniq Φ)
                       (WT: Φ ⊢ M ∈ T → U),
                  Φ ⊢ M ∈ T ⊸ U
  | wt_tm_pair : forall Φ Ψ T U M N
                        (WF: wf_typ (T <x> U) lin)
                        (UN: uniq (Φ ++ Ψ))
                        (WTM: Φ ⊢ M ∈ T) (WTN: Ψ ⊢ N ∈ U),
                   Φ ++ Ψ ⊢ (tm_pair M N) ∈ T <x> U
  | wt_tm_let :
      forall (L L':atoms) Φ Ψ kv T U V M N
             (WF: wf_typ (T <x> U) lin) (WFV: wf_typ V kv)
             (UN: uniq (Φ ++ Ψ))
             (WTM: Φ ⊢ M ∈ T <x> U)
             (WTN: forall (x y:atom)
                          (XL: x `notin` L)
                          (YL: y `notin` L'),
                     Ψ ++ x ~ T ++ y ~ U ⊢ ({1 ~> x} (open N y)) ∈ V),
        Φ ++ Ψ ⊢ (tm_let T U M N) ∈ V
  | wt_tm_send : forall Φ Ψ M T N S
                        (WF: wf_typ (! T # S) lin)
                        (UN: uniq (Φ ++ Ψ))
                        (WTM: Φ ⊢ M ∈ T) (WTN: Ψ ⊢ N ∈ ! T # S),
                   Φ ++ Ψ ⊢ tm_send M N ∈ S
  | wt_tm_recv : forall Φ M T S
                        (WF: wf_typ (? T # S) lin)
                        (UN: uniq Φ)
                        (WT: Φ ⊢ M ∈ ? T # S),
                   Φ ⊢ tm_recv M ∈ typ_tensor T S
  | wt_tm_l_select : forall Φ M S1 S2 (UN: uniq Φ)
                            (WF: wf_typ (S1 <+> S2) lin)
                            (WT: Φ ⊢ M ∈ (S1 <+> S2)),
                       Φ ⊢ tm_select lb_inl M ∈ S1
  | wt_tm_r_select : forall Φ M S1 S2
                            (UN: uniq Φ)
                            (WF: wf_typ (S1 <+> S2) lin)
                            (WT: Φ ⊢ M ∈ (S1 <+> S2)),
                       Φ ⊢ tm_select lb_inr M ∈ S2
  | wt_tm_case : forall (L:atoms) Φ Ψ M NL NR S1 S2 kt T
                        (UN: uniq (Φ ++ Ψ))
                        (WF: wf_typ (S1 <&> S2) lin)
                        (WFT: wf_typ T kt)
                        (WTM: Φ ⊢ M ∈ (S1 <&> S2))
                        (WTNL: forall (x:atom) (NLH: x `notin` L),
                                 Ψ ++ x ~ S1 ⊢ (open NL x) ∈ T)
                        (WTNR: forall (x:atom) (NL: x `notin` L),
                                 Ψ ++ x ~ S2 ⊢ (open NR x) ∈ T),
                   Φ ++ Ψ ⊢ (tm_case M lb_inl NL lb_inr NR) ∈ T
  | wt_tm_connect : forall (L:atoms) Φ Ψ M N S S' kt T
                           (UN: uniq (Φ ++ Ψ))
                           (DU: are_dual S S')
                           (WF: wf_typ T kt)
                           (WTM: forall (x:atom) (NL: x `notin` L),
                                   Φ ++ x ~ S ⊢ (open M x) ∈ typ_oend)
                           (WTN: forall (x:atom) (NL: x `notin` L),
                                   Ψ ++ x ~ S' ⊢ (open N x) ∈ T),
                      Φ ++ Ψ ⊢ (tm_connect S M N) ∈ T
  | wt_tm_end : forall Φ M T
                       (WF: wf_typ (T <x> typ_iend) lin)
                       (UN: uniq Φ)
                       (WT: Φ ⊢ M ∈ typ_tensor T typ_iend),
                  Φ ⊢ tm_end M ∈ T
where "Φ ⊢ t ∈ T" := (wt_tm Φ t T) : gv_scope.

Hint Constructors wt_tm.
