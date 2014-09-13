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

(* ------------ utilities ------------------*)
Definition token_value_of_bool (b : bool) := ValToken (token_of_bool b).

Definition var_value_of_string (name : string) : value := ValVariable (Var (Free name)).

(* ------------ recursive procs ------------------*)

Inductive procR : Set :=
| InputR : value -> procR -> procR
| OutputR : value -> value -> procR -> procR
| IsEqR : value -> value -> procR -> procR
| IsNotEqR : value -> value -> procR -> procR
| NewR : procR -> procR
| ParR : procR -> procR -> procR
| SumR : procR -> procR -> procR
| RepR : procR -> procR
| ZeroR : procR
| RecurseR : string -> list value -> procR.

Fixpoint send_args_aux (out : value) (us : list value) : proc :=
  match us with 
    | nil => Zero
    | v::vs => out ! v; (send_args_aux out vs)
  end.

Definition send_args (recipient : string) (us : list value) : proc :=
  let tmp := "tmp" in
  let tmpNm := Nm (Free tmp) in
  let arg_send_proc := send_args_aux (ValName (dual_name tmpNm)) us in
  let channel_send_and_arg_send_proc := (ValName (CoNm (Free recipient))) ! (ValName tmpNm); arg_send_proc in
  New (close_proc tmp 0 channel_send_and_arg_send_proc).

Fixpoint recv_args_aux (inp : value) (params : list string) (P : proc) : proc :=
  match params with 
    | nil => P
    | param::params => inp ?; (close_proc param 0 (recv_args_aux inp params P))
  end.

Definition recv_args (recipient : string) (params : list string) (P : proc) : proc :=
  let tmp := "tmp" in
  let tmpVal := ValVariable (Var (Free tmp)) in
  let arg_recv_proc := recv_args_aux tmpVal params P in
  (ValName (Nm (Free recipient))) ? ; (close_proc tmp 0 arg_recv_proc).

(* 
NOTES

Eval compute in send_args "send_false" ((ValName (Nm (Free "in"))) :: (ValToken (Token "qwerty")) :: nil).
Eval compute in recv_args "send_false" ("in" :: "out" :: nil) ( ValVariable (Var (Free "in")) ! ValVariable (Var (Free "out")) ; Zero ).
*)

Fixpoint transformProcR (P : procR) : proc :=
  match P with
    | InputR u P' => u ? ; transformProcR P'
    | OutputR u v P' => u ! v ; transformProcR P' 
    | IsEqR u v P' => IsEq u v (transformProcR P')
    | IsNotEqR u v P' => IsNotEq u v (transformProcR P')
    | NewR P' => New (transformProcR P')
    | ParR P1 P2 => (transformProcR P1) ||| (transformProcR P2)
    | SumR P1 P2 => (transformProcR P1) +++ (transformProcR P2)
    | RepR P' => ! (transformProcR P')
    | ZeroR => Zero
    | RecurseR name us => send_args name us
  end.

(*
Eval compute in 
  transformProcR (RecurseR "send_false" ((ValName (Nm (Free "in"))) :: (ValToken (Token "qwerty")) :: nil)).
*)

Definition createRecProcOne (triple : string * list string * procR) : proc := 
  match triple with
    | (procName, params, P) => recv_args procName params (transformProcR P)
  end.

Fixpoint parAll (Ps : list proc) : proc := 
  match Ps with
    | nil => Zero
    | P::Ps => P ||| (parAll Ps)
  end.

Fixpoint newAll (procNames : list string) (P : proc) : proc :=
  match procNames with
    | nil => P
    | procName::procNames => New (close_proc procName 0 (newAll procNames P))
  end.

Definition createRecProc (defns : list (string * list string * procR)) (initProcName : string) (initArgs : list value) : proc :=
  let transformedDefns := parAll (map createRecProcOne defns) in
  let initProc := send_args initProcName initArgs in
  let procNames := map (fun triple => fst (fst triple)) defns in
    newAll (procNames) (transformedDefns ||| initProc).


(* ------------ sink ------------------*)

(* proc sink(in,out) = in?x; sink(in) *)
Definition sink_procR : procR :=
  InputR (ValVariable (Var (Bound 1)))
    (RecurseR
      "sink" 
      ((ValVariable (Var (Free "c"))) :: nil)).

Definition sink_recursive :=
  createRecProc (("sink", "c" :: nil, sink_procR) :: nil).

(* ------------ forwarder ------------------*)

(* proc fwd(in, out) = in?z; out!z; fwd(in, out) *)
Definition uni_forwarder_multi_step_procR : procR := 
  InputR
  (ValVariable (Var (Bound 1)))
  (OutputR
    (ValVariable (Var (Bound 1)))
    (ValVariable (Var (Bound 0)))
    (RecurseR
      "forwarder" 
      ((ValVariable (Var (Free "in"))) :: (ValVariable (Var (Free "out"))) :: nil))).

Definition uni_forwarder_multi_step_recursive :=
  createRecProc
    (("forwarder", "in"::"out"::nil, uni_forwarder_multi_step_procR) :: nil). 

(* ----------------- tactics --------------------- *)

Ltac discriminate_w_list :=
 (repeat
   match goal with
     | [ H1: ~ In ?x _ ,  H2 : (?x :: _) = (?x :: _) |- False ] =>
       contradict H1
     | [ H: ~ In ?x _ |- ValName (Nm (Free ?x)) <> _ ] =>
       contradict H; inversion H
     | [ H: ~ In ?x _ |- ValName (CoNm (Free ?x)) <> _ ] =>
       contradict H; inversion H
     | [ H: ~ In ?x _ |- ValVariable (Var (Free ?x)) <> _ ] =>
       contradict H; inversion H
     | [ H: ~ In ?x _ |- _ <> ValVariable (Var (Free ?x)) ] =>
       contradict H; inversion H
     | [ H1: ~ In ?x _ , H2: (ValVariable (Var (Free ?x)),_) = _ |- False ] =>
       contradict H1; inversion H2
     | [ H: ValVariable (Var (Free ?x)) = _ |- In ?x _ ] =>
       inversion H; clear H
     | [ H: _ = ValVariable (Var (Free ?x)) |- In ?x _ ] =>
       inversion H; clear H
     | |- In ?x _ => red
     | |- ?x = ?x \/ _ => left; reflexivity
     | |- ?x = ?y \/ _ => right
   end).
