Require Export Arith.EqNat.
Require Export Arith.Lt.
Require Export Arith.Compare_dec.
Require Export List.
Require Import String.
Open Scope string_scope.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import Process.
Require Import List.
Require Import PrettyPrinter.
Require Import TypeAssignmentPoly.
Require Import ResultBasics.
Require Import ExampleCommon.
Require Import ExampleRecursion.

(* ------------ abp-recv ------------------*)

(*
proc recv_i(err2, out) =
 err2!(1-i);recv_i(err2, out)                  Send ack 1-i (maybe a duplicate)
 +err2?z;[z=(1−i)];err2?y;recv_i(err2, out)    Ignore duplicate message y
 +err2?z;[z=i];err2?x;out!x;recv_{1-i}(err2, out)  New ack i, send x on out & ack
*)

(* err2!(1-i);recv_i(err2, out) *)
Definition abp_recvA_procR (i : bool) : procR :=
(OutputR (var_value_of_string "err2") (token_value_of_bool (negb i))
  (RecurseR ("recv_"++(string_of_bool i))
    ((var_value_of_string "err2") :: (var_value_of_string "out") :: nil))).

(* +err2?z;[z=(1−i)];err2?y;recv_i(err2, out) *)
Definition abp_recvB_procR (i : bool) : procR :=
(InputR (var_value_of_string "err2")
  (IsEqR (ValVariable (Var (Bound 0))) (token_value_of_bool (negb i))
    (InputR (var_value_of_string "err2")
      (RecurseR ("recv_"++(string_of_bool i))
        ((var_value_of_string "err2") :: (var_value_of_string "out")
        :: nil))))).

(* +err2?z;[z=i];err2?x;out!x;recv_{1-i}(err2, out) *)
Definition abp_recvC_procR (i : bool) : procR :=
(InputR (var_value_of_string "err2")
  (IsEqR (ValVariable (Var (Bound 0))) (token_value_of_bool i)
    (InputR (var_value_of_string "err2")
      (OutputR (var_value_of_string "out") (ValVariable (Var (Bound 0)))
        (RecurseR ("recv_"++(string_of_bool (negb i)))
          ((var_value_of_string "err2") :: (var_value_of_string "out")
          :: nil)))))).

(*
  err2!(1-i);recv_i(err2, out)
+ err2?z;[z=(1−i)];err2?y;recv_i(err2, out)
+ err2?z;[z=i];err2?x;out!x;recv_{1-i}(err2, out)
*)
Definition abp_recv_procR (i : bool) : procR :=
  SumR (abp_recvA_procR i) (SumR (abp_recvB_procR i) (abp_recvC_procR i)).

Definition abp_recv err2 out :=
  let mkTriple i :=
    (String.append "recv_" (string_of_bool i), "err2" :: "out" :: nil,
      abp_recv_procR i) in
  createRecProc (map mkTriple (false :: true :: nil)) "recv_false"
    (err2 :: out :: nil).

Definition abp_recv_test : proc :=
  abp_recv (var_value_of_string "qerr2") (var_value_of_string "qout").

(*
Eval compute in abp_recv_test.
*)


