(** Beginning of the file for CP mechanisation as described in

    Philip Wadler. 2012. Propositions as sessions. In Proceedings of the 17th
    ACM SIGPLAN international conference on Functional programming (ICFP '12).
    ACM, New York, NY, USA, 273-286. DOI=10.1145/2364527.2364568
    http://doi.acm.org/10.1145/2364527.2364568

*)
Print LoadPath.
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
  | pp_forall : forall (X: pvar), (pvar -> prop) -> prop
  | pp_exists : forall (X: pvar), (pvar -> prop) -> prop
  | pp_one : prop (* unit for times *)
  | pp_bot : prop (* unit for par *)
  | pp_zero : prop (* unit for plus *)
  | pp_top : prop (* unit for with *).

(** Environments for the process calculus are mappings of atoms to
    propositions. *)
Definition penv := list (atom * prop).

(** Definition of a processes ranged over by P, Q and R. *)
Inductive proc : Set :=
  | p_link : atom -> atom -> proc
  | p_par : atom -> prop -> proc -> proc -> proc
  | p_output : atom -> atom -> proc -> proc
  | p_input : atom -> atom -> proc
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