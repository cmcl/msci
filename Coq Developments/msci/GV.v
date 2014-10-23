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

(** Session type definition is standard (cf. Wadler's end points).

    S ranges over session types.

    TODO: Check if the proofs will need two end terminators.
*)
Inductive session : Set :=
  | s_output : forall k, typ k -> session -> session
  | s_input : forall k, typ k -> session -> session
  (* choice *)
  (* branch *)
  | s_zero : session (* end is a keyword; use zero as in pi-calculus *)
(** typ is ranged over by T, U and V. It differs slightly from the definition
    given in Wadler's paper in that a base type is added.

*)
with typ : kind -> Set :=
  | typ_ses : session -> typ lin
  | typ_tensor : forall kt ku, typ kt -> typ ku -> typ lin
  | typ_labs : forall kt ku, typ kt -> typ ku -> typ lin
  | typ_abs : forall kt ku, typ kt -> typ ku -> typ un
  | typ_base : forall k, typ k
  | typ_unit : typ un.

(** The notation for sessions has been altered from the standard presentation
    to fit within allowable notations in Coq.
*)
Notation "'!' T '#' S" := (s_output _ T S) (at level 68).
Notation "'?' T '#' S" := (s_input _ T S) (at level 68).

Eval compute in !typ_base un#s_zero.
Eval compute in !typ_base un#? typ_base un#s_zero.