(** Beginning of the file for GV mechanisation as described in

    Philip Wadler. 2012. Propositions as sessions. In Proceedings of the 17th
    ACM SIGPLAN international conference on Functional programming (ICFP '12).
    ACM, New York, NY, USA, 273-286. DOI=10.1145/2364527.2364568
    http://doi.acm.org/10.1145/2364527.2364568

    which is based on ``Classic GV'' by Simon Gay and Vasco Vasconcelos in

    Simon J. Gay and Vasco T. Vasconcelos. 2010. Linear type theory for
    asynchronous session types. J. Funct. Program. 20, 1 (January 2010),19-50.
    DOI=10.1017/S0956796809990268 http://dx.doi.org/10.1017/S0956796809990268

*)
Require Import Metatheory Coq.Program.Tactics.
Require Import ssreflect.
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
      * There is only one end construct (TODO: Check if the proofs will need
        two end terminators).
*)
Inductive typ : kind -> Set :=
(* Session types section *)
  | typ_soutput : forall k, typ k -> typ lin -> typ lin
  | typ_sinput : forall k, typ k -> typ lin -> typ lin
  | typ_schoice : typ lin -> typ lin -> typ lin
  | typ_sbranch : typ lin -> typ lin -> typ lin
  | typ_szero : typ lin (* end is a keyword; use zero as in pi-calculus *)
(* Other non-session GV types *)
  | typ_tensor : forall kt ku, typ kt -> typ ku -> typ lin
  | typ_labs : forall kt ku, typ kt -> typ ku -> typ lin
  | typ_abs : forall kt ku, typ kt -> typ ku -> typ un
  | typ_unit : typ un.

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
Delimit Scope gv_scope with gv.
Open Scope gv_scope.

(** [ty] as defined above is more general than the types handled by GV; the
    types are considered session types and so could, for example, appear in
    branch or choice constructs (e.g. a regular function type). To prevent
    this, a predicate [is_session] is defined over [typ] constructors to
    restrict where certain constructors may occur.

    S range over session types.
*)
Inductive is_session : forall k, typ k -> Prop :=
  | is_output : forall k (T : typ k) S
                       (IS: is_session S),
                  is_session (! T # S)
  | is_input : forall k (T : typ k) S
                      (IS: is_session S),
                 is_session (? T # S)
  | is_choice : forall S1 S2 (IS1: is_session S1) (IS2: is_session S2),
                  is_session (S1 <+> S2)
  | is_branch : forall S1 S2 (IS1: is_session S1) (IS2: is_session S2),
                  is_session (S1 <&> S2)
  | is_end : is_session typ_szero.

(** It's a pity we obscure the definition of session duals here by defining it
    as a proof term. This was recommended by Jonathan (jonikelee@gmail.com) on
    the CoqClub mailing list.
*)
Definition session_duals (S: { T : typ lin | is_session T}) :
  {T : typ lin | is_session T}.
  destruct S as [T P].
  induction T; try (by exfalso; inversion P).
  - assert (IS: is_session T2) by (inversion P; subst; exact IS).
    specialize (IHT2 IS); inversion IHT2 as [S' IS'].
    eapply exist; apply is_input with (T:=T1); exact IS'.
  - assert (IS: is_session T2) by (inversion P; subst; exact IS).
    specialize (IHT2 IS); inversion IHT2 as [S' IS'].
    eapply exist; apply is_output with (T:=T1); exact IS'.
  - assert (IS: is_session T1 /\ is_session T2) by (inversion P; subst; auto).
    destruct IS as [IS1 IS2].
    specialize (IHT1 IS1); clear IS1; inversion_clear IHT1 as [S1 IS1].
    specialize (IHT2 IS2); clear IS2; inversion_clear IHT2 as [S2 IS2].
    eapply exist; apply is_branch; [exact IS1 | exact IS2].
  - assert (IS: is_session T1 /\ is_session T2) by (inversion P; subst; auto).
    destruct IS as [IS1 IS2].
    specialize (IHT1 IS1); clear IS1; inversion_clear IHT1 as [S1 IS1].
    specialize (IHT2 IS2); clear IS2; inversion_clear IHT2 as [S2 IS2].
    eapply exist; apply is_choice; [exact IS1 | exact IS2].
  - eapply exist; apply is_end.
Defined.

Notation "'¬' S" := (session_duals (exist _ S _)) (at level 69,
                                                   right associativity)
                                                  : gv_scope.
(** FIXME: Unfortunately the definition does not prevent placing non-session
    [typ] constructors within the continuation part of a session:

    Eval compute in ¬(! typ_unit # (typ_tensor typ_unit typ_unit)).

    In the inductive hypothesis is it assumed the continuation is a session
    so perhaps if this isn't true we can conclude the dual is a session
    (assume anything from absurdity).

*)

(** Define a label type for binary branch and choice. *)
Inductive label : Set :=
  | lb_inr : label
  | lb_inl : label.

(** Define the terms of GV. We follow the approach in the UPenn Metatheory
    library, defining free variables as atoms and bound variables as de
    Bruijn indices.

*)
Inductive term : Set :=
(* Rule for bound variables *)
  | tm_bvar : nat -> term
(* Rules representing those in the paper: *)
  | tm_id : atom -> term
  | tm_unit : term
  | tm_abs : forall k, typ k -> term -> term
  | tm_app : term -> term -> term
  | tm_pair : term -> term -> term
  | tm_let : forall kt ku, typ kt -> typ ku -> term -> term -> term
  | tm_send : term -> term -> term
  | tm_recv : term -> term
  | tm_select : label -> term -> term
  | tm_case : term -> label -> term -> label -> term -> term
  | tm_connect : typ lin -> term -> term -> term
  | tm_end : term -> term.

Coercion tm_bvar : nat >-> term.
Coercion tm_id : atom >-> term.

(** In the style of ``Engineering Formal Metatheory'' (??) we define
    substitution of expressions for atoms and opening of expressions with
    bound variables.
*)


(** The following definition of substitution for a free variable assumes the
    term to be substituted is locally closed.
*)
Fixpoint subst (x: atom) (u: term) (t: term) : term :=
  match t with
  | tm_id y => if x == y is left _ then u else (tm_id y)
  | tm_abs k T b => tm_abs T (subst x u b)
  | tm_app m n => tm_app (subst x u m) (subst x u n)
  | tm_pair p q => tm_pair (subst x u p) (subst x u q)
  | tm_let kt ku T U m n => tm_let T U (subst x u m) (subst x u n)
  | tm_send m n => tm_send (subst x u m) (subst x u m)
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
  | tm_bvar n => if k == n is left _ then u else (tm_bvar n)
  | tm_abs k' T b => tm_abs T (open_rec (S k) u b)
  | tm_app m n => tm_app (open_rec k u m) (open_rec k u n)
  | tm_pair p q => tm_pair (open_rec k u p) (open_rec k u q)
  | tm_let kt ku T U m n
    => tm_let T U (open_rec k u m) (open_rec (S (S k)) u n)
  | tm_send m n => tm_send (open_rec k u m) (open_rec k u m)
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

Notation "{ k ~> u } t" := (open_rec k u t) (at level 68) : gv_scope.

(** Opening a term t is replacing the unbound variable with index 0 with term
    u. Assume u is locally closed and is only substituted once if it contains
    free variables.
*)
Fixpoint open t u := open_rec 0 u t.

(** A locally closed term has no unbounded variables. *)
(* Inductive lc : term -> Prop :=*)


(** Typing environments are lists of (atom,typ) pairs. *)
Definition tenv := list (atom * (typ lin + typ un)).
Definition un_env (G : tenv) : Prop := forall x (T : typ un)
                                              (IN: x `in` dom G),
                                         binds x (inr T) G.

(** To get Coq to accept the '~' notation used here, we need to make sure t
    and T are parsed as identifiers.

    Reserved Notation "G |- t ~ T" (at level 68, t ident, T ident).

    Inductive wt_tm : tenv -> term -> forall k, typ k -> Prop :=
      | wt_tm_unid : forall x T, (x ~ inr T) |- x ~ T
    where "G '|-' t ~ T" := (wt_tm G t T) : gv_scope.

    However, I'm going to adopt the ∈ notation below since it will be easier
    to differentiate between the environment notation.
*)
Reserved Notation "Φ ⊢ t ∈ T" (at level 30).

Inductive wt_tm : tenv -> term -> forall k, typ k -> Prop :=
  | wt_tm_unid : forall x T, (x ~ inr T) ⊢ x ∈ T
  | wt_tm_lid : forall x T, (x ~ inl T) ⊢ x ∈ T
  | wt_tm_unit : nil ⊢ tm_unit ∈ typ_unit
  | wt_tm_weaken : forall Φ x N k (U: typ k) T (WT: Φ ⊢ N ∈ U),
                     (Φ ++ (x ~ inr T)) ⊢ N ∈ U
(*  | wt_tm_contract : *)
(*  | wt_tm_labs : *)
  | wt_tm_send : forall k Φ Ψ M (T: typ k) N S
                        (IS: is_session S)
                        (WTM: Φ ⊢ M ∈ T) (WTN: Ψ ⊢ N ∈ ! T # S),
                   (Φ ++ Ψ) ⊢ tm_send M N ∈ S
  | wt_tm_recv : forall k Φ M (T: typ k) S
                        (WT: Φ ⊢ M ∈ ? T # S) (IS: is_session S),
                   Φ ⊢ tm_recv M ∈ typ_tensor T S
  | wt_tm_l_select : forall Φ M S1 S2
                            (IS: is_session (S1 <+> S2))
                            (WT: Φ ⊢ M ∈ (S1 <+> S2)),
                       Φ ⊢ tm_select lb_inl M ∈ S1
  | wt_tm_r_select : forall Φ M S1 S2
                            (IS: is_session (S1 <+> S2))
                            (WT: Φ ⊢ M ∈ (S1 <+> S2)),
                       Φ ⊢ tm_select lb_inr M ∈ S2
  | wt_tm_end : forall k Φ M (T: typ k) (WT: Φ ⊢ M ∈ typ_tensor T typ_szero),
                  Φ ⊢ tm_end M ∈ T
where "Φ ⊢ t ∈ T" := (wt_tm Φ t T) : gv_scope.
