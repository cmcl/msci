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

(* ------------ abp-lossy ------------------*)

(* proc lossy(err1, err2) =
  err1?i; err1?x;                     Drop or forward tagged message (i,x)
    (lossy(err1, err2) + err2!i; err2!x; lossy(err1, err2))
  +err2?bit;                          Drop or forward ack bit
    (lossy(err1, err2) + err1!bit;lossy(err1, err2))
*)

(* err1?i; err1?x; (lossy(err1, err2) + err2!i; err2!x; lossy(err1, err2)) *)
Definition abp_lossyA_procR : procR :=
(InputR (var_value_of_string "err1")
  (InputR (var_value_of_string "err1")
    (SumR
      (RecurseR "lossy" ((var_value_of_string "err1")
        :: (var_value_of_string "err2") :: nil))
      (OutputR (var_value_of_string "err2") (ValVariable (Var (Bound 1)))
        (OutputR (var_value_of_string "err2") (ValVariable (Var (Bound 0)))
          (RecurseR "lossy" ((var_value_of_string "err1")
            :: (var_value_of_string "err2") :: nil))))))).

(* +err2?bit; (lossy(err1, err2) + err1!bit;lossy(err1, err2)) *)
Definition abp_lossyB_procR : procR :=
(InputR (var_value_of_string "err2")
  (SumR
    (RecurseR "lossy" ((var_value_of_string "err1")
         :: (var_value_of_string "err2") :: nil))
    (OutputR (var_value_of_string "err1") (ValVariable (Var (Bound 0)))
      (RecurseR "lossy" ((var_value_of_string "err1")
            :: (var_value_of_string "err2") :: nil))))).

(*
  err1?i; err1?x; (lossy(err1, err2) + err2!i; err2!x; lossy(err1, err2))
  +err2?bit; (lossy(err1, err2) + err1!bit;lossy(err1, err2))
*)
Definition abp_lossy_procR : procR := SumR abp_lossyA_procR abp_lossyB_procR.

Definition abp_lossy err1 err2 :=
  let mkTriple := ("lossy", "err1" :: "err2" :: nil, abp_lossy_procR) in
  createRecProc (mkTriple :: nil) "lossy" (err1 :: err2 :: nil).

Definition abp_lossy_test : proc :=
  abp_lossy (var_value_of_string "qerr1") (var_value_of_string "qerr2").

(*

NOTES:
Eval compute in abp_lossy_test.
     = New
         (Nm (Bound 0) ? ;
          (Var (Bound 0) ? ;
           (Var (Bound 1) ? ;
            (Var (Bound 1) ? ;
             (Var (Bound 2) ? ;
              (New
                 (CoNm (Bound 6) ! Nm (Bound 0);
                  (CoNm (Bound 0) ! Var (Bound 4);
                   (CoNm (Bound 0) ! Var (Bound 3); Zero))) +++
               Var (Bound 2) ! Var (Bound 1);
               (Var (Bound 2) ! Var (Bound 0);
                New
                  (CoNm (Bound 6) ! Nm (Bound 0);
                   (CoNm (Bound 0) ! Var (Bound 4);
                    (CoNm (Bound 0) ! Var (Bound 3); Zero)))))) +++
             Var (Bound 0) ? ;
             (New
                (CoNm (Bound 5) ! Nm (Bound 0);
                 (CoNm (Bound 0) ! Var (Bound 3);
                  (CoNm (Bound 0) ! Var (Bound 2); Zero))) +++
              Var (Bound 2) ! Var (Bound 0);
              New
                (CoNm (Bound 5) ! Nm (Bound 0);
                 (CoNm (Bound 0) ! Var (Bound 3);
                  (CoNm (Bound 0) ! Var (Bound 2); Zero))))))) ||| Zero
          ||| New
                (CoNm (Bound 1) ! Nm (Bound 0);
                 (CoNm (Bound 0) ! Var (Free "qerr1");
                  (CoNm (Bound 0) ! Var (Free "qerr2"); Zero))))
     : proc


Eval compute in 
  (undebruijn_proc 50
    ("lossy" %
      (("xc" % "err1" % "err2" % 
        (* abp_lossyA_procR *)
        (("i" % "x" % (("d" % $$) ^^ ("d" % $$)))
        (* abp_lossyB_procR *)
        ^^ ("i" % (("d" % $$) ^^ ("d" % $$)))))
        (* 0 *)
        ^^ ($$))
      (* bootstrap *)
      ^^ ("c" % $$)
    )
    abp_lossy_test
  ).
     = "(new lossy)
         (((%lossy ? $xc. $xc ? $err1. $xc ? $err2.
           (($err1 ? $i. $err1 ? $x.
             (((new d) (%/lossy ! %d. %/d ! $err1. %/d ! $err2. 0))
             + ($err2 ! $i. $err2 ! $x. (new d)
                (%/lossy ! %d. %/d ! $err1. %/d ! $err2. 0))))
           + ($err2 ? $i.
               (((new d) (%/lossy ! %d. %/d ! $err1. %/d ! $err2. 0))
               + ($err1 ! $i. (new d) (%/lossy ! %d. %/d ! $err1. %/d ! $err2. 0)))))
         | 0)
         | (new c) (%/lossy ! %c. %/c ! $qerr1. %/c ! $qerr2. 0)))"
     : string
*)

