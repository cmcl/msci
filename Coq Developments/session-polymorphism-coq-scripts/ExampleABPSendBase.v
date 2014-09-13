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


(* ------------ abp-send ------------------*)

(*
  proc send_i(x, in, err1) =
   err1!i;err1!x;send_i(x, in, err1)   Send message x (maybe a duplicate)
   +err1?(1 − i);send_i(x, in, err1)   Ignore duplicate ack 1−i
   +err1?i;in?y;send_{1-i}(y, in, err1)  New ack i, send next message y from in
*)

Definition abp_sendA_procR (i : bool) : procR :=
(* err1!i;err1!x;send_i(x, in, err1) *)
(OutputR (var_value_of_string "err1") (token_value_of_bool i)
  (OutputR (var_value_of_string "err1") (var_value_of_string "x")
    (RecurseR ("send_"++(string_of_bool i))
      ((var_value_of_string "x") :: (var_value_of_string "in")
        :: (var_value_of_string "err1") :: nil)))).

Definition abp_sendB_procR (i : bool) : procR :=
(* err1?z;[z=(1 − i)];send_i(x, in, err1) *)
(InputR (var_value_of_string "err1")
  (IsEqR (ValVariable (Var (Bound 0))) (token_value_of_bool (negb i))
    (RecurseR ("send_"++(string_of_bool i)) ((var_value_of_string "x")
      :: (var_value_of_string "in") :: (var_value_of_string "err1") :: nil)))).

Definition abp_sendC_procR (i : bool) : procR :=
(* err1?z;[z=i];in?y;send_{1-i}(y, in, err1) *)
(InputR (var_value_of_string "err1")
  (IsEqR (ValVariable (Var (Bound 0))) (token_value_of_bool i)
    (InputR (var_value_of_string "in")
      (RecurseR ("send_"++(string_of_bool (negb i)))
        ((ValVariable (Var (Bound 0))) :: (var_value_of_string "in")
          :: (var_value_of_string "err1") :: nil))))).


(*
   err1!i;err1!x;send_i(x, in, err1) 
+  err1?z;[z=(1 − i)];send_i(x, in, err1) 
+  err1?z;[z=i];in?y;send_{1-i}(y, in, err1) 
*)
Definition abp_send_procR (i : bool) : procR :=
  SumR (abp_sendA_procR i) (SumR (abp_sendB_procR i) (abp_sendC_procR i)).

Definition abp_send x inp err1 := 
  let mkTriple i := (String.append "send_" (string_of_bool i),
      "x" :: "in" :: "err1" :: nil, abp_send_procR i) in
  createRecProc (map mkTriple (false :: true :: nil)) "send_false"
    (x :: inp :: err1 :: nil).

Definition abp_send_test : proc :=
  abp_send (var_value_of_string "qx") (var_value_of_string "qin")
    (var_value_of_string "qerr1").

(*

NOTES:

Eval compute in abp_send_test.

Eval compute in 
  (undebruijn_proc 50
    ("send_false" % "send_true" % 
      (("xc" % "x" % "xin" % "xerr1" % (("d" % $$) ^^ (("z" % "d" % $$) ^^ ("z" % "y" % "d" % $$)))) ^^ 
        (("xc" % "x" % "xin" % "xerr1" % (("d" % $$) ^^ (("z" % "d" % $$) ^^ ("z" % "y" % "d" % $$)))) ^^ $$) ^^ 
        ("c" % $$))
    )
    abp_send_test
  ).

*)


