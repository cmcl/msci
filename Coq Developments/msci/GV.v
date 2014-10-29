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
Require Import Program.
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

(** Labels are just natural numbers. *)
Definition label := nat.

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
                                             right associativity).
Notation "'?' T '#' S" := (typ_sinput T S) (at level 68, right associativity).
Notation "S1 '<+>' S2" := (typ_schoice S1 S2) (at level 68,
                                               right associativity).
Notation "S1 <&> S2" := (typ_sbranch S1 S2) (at level 68,
                                             right associativity).

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
