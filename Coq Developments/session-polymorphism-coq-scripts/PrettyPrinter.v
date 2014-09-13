Require Import String.
Require Import TypeAssignmentPoly.
Require Import ResultBasics.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import List.

Require String. Open Scope string_scope.

Require Import Recdef.

(* ================================================================ *)

Inductive naming_tree : Set := 
| NTFinal : naming_tree
| NTName : free_id -> naming_tree -> naming_tree
| NTBranch : naming_tree -> naming_tree -> naming_tree.

Definition undebruijn_value (v : value) : string :=
  match v with
    | ValName (Nm (Free i)) => "%" ++ i
    | ValName (CoNm (Free i)) => "%/" ++ i
    | ValToken (Token s) => "'" ++ s ++ "'"
    | ValVariable (Var (Free i)) => "$" ++ i
    | _ => "?"
  end.

Fixpoint undebruijn_proc (n : nat) (nt : naming_tree) (P : proc)  : string := 
  match n with
    | 0 => "*"
    | S m =>
      match nt with
        | NTFinal => "@"
        | NTName i nt1 => 
          match P with 
            | u? ; P => 
              (undebruijn_value u) ++ " ? " ++ (undebruijn_value (open_value i 0 (ValVariable (Var (Bound 0))))) ++ 
              ". " ++ (undebruijn_proc m nt1 (open_proc i 0 P))
            | u!v ; P => 
              (undebruijn_value u) ++ " ! " ++ (undebruijn_value v) ++ ". " ++ (undebruijn_proc m nt P)
            | IsEq u v P => "[" ++ (undebruijn_value u) ++ "=" ++ (undebruijn_value v) ++ "]" ++ ". " ++ (undebruijn_proc m nt P)
            | IsNotEq u v P => "[" ++ (undebruijn_value u) ++ "<>" ++ (undebruijn_value v) ++ "]" ++ ". " ++ (undebruijn_proc m nt P)
            | New P => "(new " ++ i ++ ") (" ++ (undebruijn_proc m nt1 (open_proc i 0 P)) ++ ")"
            | ( ! P ) => "rep (" ++ (undebruijn_proc m nt P) ++ "))"
            | Zero => "0"
            | _ => "@"
          end
        | NTBranch nt1 nt2 => 
          match P with 
            | (P ||| Q) => "(" ++ (undebruijn_proc m nt1 P) ++ " | " ++ (undebruijn_proc m nt2 Q) ++ ")"
            | (P +++ Q) => "((" ++ (undebruijn_proc m nt1 P) ++ ") + (" ++ (undebruijn_proc m nt2 Q) ++ "))"
            | _ => "@"
          end
      end
  end.

(* ================================================================ *)

Notation "x % nt" := (NTName x nt) (at level 45, right associativity).
Notation "nt1 ^^ nt2" := (NTBranch nt1 nt2) (at level 40, left associativity).
Notation "$$" := (NTName "unused" NTFinal).

(* ================================================================ *)

(*
Require Import ExampleCommon.
Require Import ExampleUniForwarderMultiStepTyping.

Eval compute in
  (undebruijn_proc 50
    (NTName "c" 
      (NTBranch
        (NTName "d" 
          (NTName "unused" NTFinal))
        (NTName "xd"
          (NTName "xin" 
            (NTName "xout" 
              (NTName "y" 
                (NTName "d2" 
                  (NTName "unused" NTFinal))))))
      )
    )
    (uni_forwarder_multi_step (ValVariable (Var (Free "in"))) (ValVariable (Var (Free "out"))))).

Eval compute in
  (undebruijn_proc 50
    ("c"% (("d" % $$) ^^ ("xd" % "xin" % "xout" % "y" % "d2" % $$)))
    (uni_forwarder_multi_step (ValVariable (Var (Free "in"))) (ValVariable (Var (Free "out"))))).

*)

