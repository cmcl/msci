Require Export Arith.EqNat.
Require Export Arith.Lt.
Require Export Arith.Compare_dec.
Require Export List.
Require Import String.
Require Import TacticsSF.
Require Import TacticsCPDT.

(* ============================================================================= *)

Inductive token : Set := 
| Token : string -> token.

Hint Resolve string_dec.

Lemma token_dec : forall x y : token, {x = y} + {~ (x = y)}.
Proof.
  decide equality.
Qed.

Hint Resolve token_dec.

Definition free_id := string.
Definition bound_id := nat.

Inductive id : Set := 
| Free : free_id -> id
| Bound : bound_id -> id.

Lemma id_dec : forall x y : id, {x = y} + {~ (x = y)}.
Proof.  
  do 2 decide equality.
Qed.

Hint Resolve id_dec.

Inductive name : Set := 
| Nm : id -> name
| CoNm : id -> name.

Lemma name_dec : forall x y : name, {x = y} + {~ (x = y)}.
Proof.
  decide equality.
Qed.

Hint Resolve name_dec.

Inductive variable : Set :=
| Var : id -> variable.

Lemma variable_dec : forall x y : variable, {x = y} + {~ (x = y)}.
Proof.
  decide equality.
Qed.

Inductive value : Set :=
| ValName : name -> value
| ValToken : token -> value
| ValVariable : variable -> value.

Coercion ValName : name >-> value.
Coercion ValToken : token >-> value.
Coercion ValVariable : variable >-> value.

Lemma value_dec : forall x y : value, {x = y} + {~ (x = y)}.
Proof.
  do 2 decide equality.
Qed.

Hint Resolve value_dec.

Definition dual_name (x : name) : name :=
  match x with
  | Nm i => CoNm i
  | CoNm i => Nm i
  end.

(* UNUSED???

Definition beq_name (x y : name) : bool :=
  match (x, y) with
    | (nm m, nm n) => beq_nat m n
    | (nm m, co_nm n) => false
    | (co_nm m, nm n) => false
    | (co_nm m, co_nm n) => beq_nat m n
  end.

Definition beq_variable (x y : variable) : bool :=
  match (x, y) with
    | (var m, var n) => beq_nat m n
  end.

*)

(* UNUSED??? The following definition of "distinct_values" specializes "eq" by
application to type "value".

Definition distinct_values (x y : value) : Prop := ~ (@eq value x y).

 *)

(* ============================================================================= *)

Inductive free_value : value -> Prop := 
| FNm : forall i, free_value (ValName (Nm (Free i)))
| FCoNm : forall i, free_value (ValName (CoNm (Free i)))
| FVariable : forall i, free_value (ValVariable (Var (Free i))).

(* ============================================================================= *)

Inductive proc : Set :=
| Input : value -> proc -> proc
| Output : value -> value -> proc -> proc
| IsEq : value -> value -> proc -> proc
| IsNotEq : value -> value -> proc -> proc
| New : proc -> proc
| Par : proc -> proc -> proc
| Sum : proc -> proc -> proc
| Rep : proc -> proc
| Zero : proc.

Notation "u ? ; P" := (Input u P) (at level 40, left associativity).
Notation "u ! v ; P" := (Output u v P) (at level 40, left associativity).
Notation "P ||| Q" := (Par P Q) (at level 50, left associativity).
Notation "P +++ Q" := (Sum P Q) (at level 50, left associativity).
Notation "! P" := (Rep P) (at level 60, right associativity).

(* ============================================================================= *)

Definition open_id (x : free_id) (n : bound_id) (i : id) : id := 
  match i with
    | Free _ => i
    | Bound m => 
      if (eq_nat_decide m n) 
        then Free x
        else if (le_lt_dec m n)
          then i 
          else Bound (pred m)
  end.

Definition open_name (x : free_id) (n : bound_id) (nm : name) : name := 
  match nm with
    | Nm i => Nm (open_id x n i)
    | CoNm i => CoNm (open_id x n i)
  end.

Definition open_variable (x : free_id) (n : bound_id) (var : variable) : variable := 
  match var with
    | Var i => Var (open_id x n i)
  end.

Definition open_value (x : free_id) (n : bound_id) (u : value) : value := 
  match u with
    | ValName nm => ValName (open_name x n nm)
    | ValToken _ => u
    | ValVariable var => ValVariable (open_variable x n var)
  end.

Fixpoint open_proc (x : free_id) (n : bound_id) (P1 : proc) : proc := 
  match P1 with
    | (u ? ; P) => (open_value x n u) ? ; (open_proc x (S n) P)
    | (u ! v ; P) => (open_value x n u) ! (open_value x n v) ; (open_proc x n P)
    | IsEq u v P => IsEq (open_value x n u) (open_value x n v) (open_proc x n P)
    | IsNotEq u v P => IsNotEq (open_value x n u) (open_value x n v) (open_proc x n P)
    | New P => New (open_proc x (S n) P)
    | (P ||| Q) => (open_proc x n P) ||| (open_proc x n Q) 
    | (P +++ Q) => (open_proc x n P) +++ (open_proc x n Q)
    | ( ! P ) => ! (open_proc x n P)
    | Zero => Zero
  end.

(* ============================================================================= *)

Definition close_id (x : free_id) (n : bound_id) (i : id) : id := 
  match i with
    | Free y => if (string_dec x y) then Bound n else i
    | Bound m => if (le_lt_dec n m) then Bound (S m) else i
  end.

Definition close_name (x : free_id) (n : bound_id) (nm : name) : name := 
  match nm with
    | Nm i => Nm (close_id x n i)
    | CoNm i => CoNm (close_id x n i)
  end.

Definition close_variable (x : free_id) (n : bound_id) (var : variable) : variable := 
  match var with
    | Var i => Var (close_id x n i)
  end.

Definition close_value (x : free_id) (n : bound_id) (u : value) : value := 
  match u with
    | ValName nm => ValName (close_name x n nm)
    | ValToken _ => u
    | ValVariable var => ValVariable (close_variable x n var)
  end.

Fixpoint close_proc (x : free_id) (n : bound_id) (P1 : proc) : proc := 
  match P1 with
    | (u ? ; P) => (close_value x n u) ? ; (close_proc x (S n) P)
    | (u ! v ; P) => (close_value x n u) ! (close_value x n v) ; (close_proc x n P)
    | IsEq u v P => IsEq (close_value x n u) (close_value x n v) (close_proc x n P)
    | IsNotEq u v P => IsNotEq (close_value x n u) (close_value x n v) (close_proc x n P)
    | New P => New (close_proc x (S n) P)
    | (P ||| Q) => (close_proc x n P) ||| (close_proc x n Q) 
    | (P +++ Q) => (close_proc x n P) +++ (close_proc x n Q)
    | ( ! P ) => ! (close_proc x n P)
    | Zero => Zero
  end.

(* ============================================================================= *)

Definition free_values_value (u : value) : list value :=
  match u with
    | ValName (Nm (Free (i)))  => u :: nil
    | ValName (CoNm (Free (i)))  => u :: nil
    | ValVariable (Var (Free i)) => u :: nil
    | _ => nil
  end.

Fixpoint free_values_proc (P : proc) : list value :=
  match P with
    | (u ? ; P) => (free_values_value u) ++ (free_values_proc P)
    | (u ! v ; P) => (free_values_value u) ++ (free_values_value v) ++ (free_values_proc P)
    | IsEq u v P => (free_values_value u) ++ (free_values_value v) ++ (free_values_proc P)
    | IsNotEq u v P => (free_values_value u) ++ (free_values_value v) ++ (free_values_proc P)
    | New P => (free_values_proc P)
    | (P ||| Q) => (free_values_proc P) ++ (free_values_proc Q)
    | (P +++ Q) => (free_values_proc P) ++ (free_values_proc Q)
    | ( ! P ) => (free_values_proc P)
    | Zero => nil
  end.

(* ============================================================================= *)

Definition free_ids_id (i : id) : list free_id :=
  match i with
    | Free s => s :: nil
    | Bound _ => nil
  end.

Definition free_ids_name (nm : name) : list free_id :=
  match nm with
    | Nm i => free_ids_id i
    | CoNm i => free_ids_id i
  end.

Definition free_ids_variable (var : variable) : list free_id :=
  match var with
    | Var i => free_ids_id i
  end.

Definition free_ids_value (u : value) : list free_id :=
  match u with
    | ValName nm => free_ids_name nm
    | ValToken _ => nil
    | ValVariable var => free_ids_variable var
  end.

Fixpoint free_ids_proc (P : proc) : list free_id :=
  match P with
    | (u ? ; P) => (free_ids_value u) ++ (free_ids_proc P)
    | (u ! v ; P) => (free_ids_value u) ++ (free_ids_value v) ++ (free_ids_proc P)
    | IsEq u v P => (free_ids_value u) ++ (free_ids_value v) ++ (free_ids_proc P)
    | IsNotEq u v P => (free_ids_value u) ++ (free_ids_value v) ++ (free_ids_proc P)
    | New P => (free_ids_proc P)
    | (P ||| Q) => (free_ids_proc P) ++ (free_ids_proc Q)
    | (P +++ Q) => (free_ids_proc P) ++ (free_ids_proc Q)
    | ( ! P ) => (free_ids_proc P)
    | Zero => nil
  end.

(* ============================================================================= *)

Definition insert_id (min : bound_id) (i : id) : id := 
  match i with
    | Free _ => i
    | Bound m => 
      if (le_lt_dec min m)
        then Bound (S m)
        else i
  end.

Definition insert_name (min : bound_id) (nm : name) : name := 
  match nm with
    | Nm i => Nm (insert_id min i)
    | CoNm i => CoNm (insert_id min i)
  end.

Definition insert_variable (min : bound_id) (var : variable) : variable := 
  match var with
    | Var i => Var (insert_id min i)
  end.

Definition insert_value (min : bound_id) (u : value) : value := 
  match u with
    | ValName nm => ValName (insert_name min nm)
    | ValToken _ => u
    | ValVariable var => ValVariable (insert_variable min var)
  end.

Fixpoint insert_proc (min : bound_id) (P1 : proc) : proc := 
  match P1 with
    | (u ? ; P) => (insert_value min u) ? ; (insert_proc (S min) P)
    | (u ! v ; P) => (insert_value min u) ! (insert_value min v) ; (insert_proc min P)
    | IsEq u v P => IsEq (insert_value min u) (insert_value min v) (insert_proc min P)
    | IsNotEq u v P => IsNotEq (insert_value min u) (insert_value min v) (insert_proc min P)
    | New P => New (insert_proc (S min) P)
    | (P ||| Q) => (insert_proc min P) ||| (insert_proc min Q) 
    | (P +++ Q) => (insert_proc min P) +++ (insert_proc min Q)
    | ( ! P ) => ! (insert_proc min P)
    | Zero => Zero
  end.

(* ============================================================================= *)

Reserved Notation "P == Q" (no associativity, at level 90).

Inductive struct_equiv : proc -> proc -> Prop := 
| StrRefl : forall P, P == P
| StrSym : forall P Q, P == Q -> Q == P
| StrTrans : forall P Q R, P == Q -> Q == R -> P == R
| StrParZeroRight : forall P, P == (P ||| Zero)
| StrSumZeroRight : forall P, P == (P +++ Zero) 
| StrParComm : forall P Q, (P ||| Q) == (Q ||| P)
| StrSumComm : forall P Q, (P +++ Q) == (Q +++ P)
| StrParAssoc : forall P Q R, ((P ||| Q) ||| R) == (P ||| (Q ||| R))
| StrSumAssoc : forall P Q R, ((P +++ Q) +++ R) == (P +++ (Q +++ R))
| StrRep : forall P, (! P) == (P ||| (! P))
| StrNewParRight : forall P Q, (P ||| (New Q)) == (New ((insert_proc 0 P) ||| Q)) 
| StrNewSumRight : forall P Q, (P +++ (New Q)) == (New ((insert_proc 0 P) +++ Q)) 
| StrParCongRight : forall P Q1 Q2, Q1 == Q2 -> (P ||| Q1) == (P ||| Q2)
| StrSumCongRight : forall P Q1 Q2, Q1 == Q2 -> (P +++ Q1) == (P +++ Q2)
| StrNewCong : forall P Q, 
    (forall i, 
      ~ (In i (free_ids_proc P))
      -> 
      ~ (In i (free_ids_proc Q))
      -> 
      open_proc i 0 P == open_proc i 0 Q)
    -> 
    (New P) == (New Q)
where "P == Q" := (struct_equiv P Q).

(* ============================================================================= *)

Fixpoint subst_value (body : value) (old : value) (new : value) : value := 
  match body with
    | ValVariable (Var (Free i)) => if (value_dec body old) then new else body
    | _ => body
  end.

Fixpoint subst_proc (body : proc) (old : value) (new : value) : proc := 
  match body with
    | (u ? ; P) => (subst_value u old new) ? ; (subst_proc P old new)
    | (u ! v ; P) => (subst_value u old new) ! (subst_value v old new) ; (subst_proc P old new)
    | (IsEq u v P) => (IsEq (subst_value u old new) (subst_value v old new) (subst_proc P old new))
    | (IsNotEq u v P) => (IsNotEq (subst_value u old new) (subst_value v old new) (subst_proc P old new))
    | (P ||| Q) => (subst_proc P old new) ||| (subst_proc Q old new) 
    | (P +++ Q) => (subst_proc P old new) +++ (subst_proc Q old new) 
    | (New P) => (New (subst_proc P old new))
    | (! P) => (! (subst_proc P old new))
    | Zero => Zero
  end.

Definition subst_open_proc (P : proc) (i : free_id) (b : bound_id) (new : value) : proc := 
  subst_proc (open_proc i b P) (Var (Free i)) new.

(* ============================================================================= *)

Definition is_not_token (u : value) : Prop := (forall k : token, u <> ValToken k).

Inductive is_name : value -> Prop :=
| ISNName : forall nm, is_name (ValName nm).

Inductive error : proc -> Prop := 
| EInput : forall u P, ~ is_name u -> error ( u ? ; P )
| EOutput : forall u v P, ~ is_name u -> error ( u ! v ; P )
| EIsEq : forall u v P, (is_not_token u \/ is_not_token v) -> error ( IsEq u v P )
| EIsNotEq : forall u v P, (is_not_token u \/ is_not_token v) -> error ( IsNotEq u v P )
| ESumLeft : forall P Q, error P -> error (P +++ Q)
| ESumRight : forall P Q, error Q -> error (P +++ Q)
| EParLeft : forall P Q, error P -> error (P ||| Q)
| EParRight : forall P Q, error Q -> error (P ||| Q)
| ENew : forall P, error P -> error (New P)
| ERep : forall P, error P -> error (Rep P).

(* ============================================================================= *)

Inductive vis_value : Set :=
| VVChan : vis_value
| VVToken : token -> vis_value.

Inductive vis_dir : Set :=
| VDInp : vis_dir
| VDOut : vis_dir.

Inductive obs : Set :=
| VONone : obs
| VOInteract : vis_dir -> free_id -> vis_value -> obs.

Inductive mk_vis_value : value -> vis_value -> Prop :=
| MVVNm : forall f, mk_vis_value (ValName (Nm f)) VVChan
| MVVCoNm : forall f, mk_vis_value (ValName (CoNm f)) VVChan
| MVVToken : forall k, mk_vis_value (ValToken k) (VVToken k).

Inductive mk_obs : name -> value -> obs -> Prop := 
| MVONm : forall f v vv, mk_vis_value v vv -> mk_obs (Nm (Free f)) v (VOInteract VDInp f vv)
| MVOCoNm : forall f v vv, mk_vis_value v vv -> mk_obs (CoNm (Free f)) v (VOInteract VDOut f vv).

Definition hide_obs (f : free_id) (vo : obs) : obs := 
  match vo with
    | VONone => VONone
    | VOInteract vd f2 vv => if (string_dec f f2) then VONone else vo
  end.

Definition free_ids_obs (vo : obs) : list free_id :=
  match vo with
    | VONone => nil
    | VOInteract vd f vv => f :: nil
  end.

Inductive new_obs_choice : Set :=
| NOCVisObs : obs -> new_obs_choice
| NOCHidden : vis_dir -> vis_value -> new_obs_choice.

Inductive new_obs : list free_id -> obs -> new_obs_choice -> Prop :=
| NOEq : forall l vo, (forall x, In x (free_ids_obs vo) -> In x l) -> new_obs l vo (NOCVisObs vo)
| NOHidden : forall l vd vv, new_obs l VONone (NOCHidden vd vv).  

Definition expand_new_obs_choice (noc : new_obs_choice) (i : free_id) : obs :=
  match noc with
    | NOCVisObs vo => vo
    | NOCHidden vd vv => VOInteract vd i vv
  end.

(* ============================================================================= *)

Inductive reduction : proc -> proc -> obs -> Prop := 
| VRedInteract : forall m vo n i v P1 Q1 P2 Q2, 
    dual_name m = n 
    ->
    ~ (In i (free_ids_proc (((m ? ; P1) +++ P2) ||| ((n ! v; Q1) +++ Q2))))
    ->
    mk_obs m v vo
    ->
    reduction (((m ? ; P1) +++ P2) ||| ((n ! v; Q1) +++ Q2)) ((subst_open_proc P1 i 0 v) ||| Q1) vo 
| VRedStr : forall P1 P2 Q1 Q2 vo, P1 == P2 -> (reduction P2 Q2 vo) -> Q2 == Q1 -> (reduction P1 Q1 vo)
| VRedIsEq : forall k : token, forall P, reduction (IsEq k k P) P VONone
| VRedIsNotEq : forall k1 k2 : token, forall P, k1 <> k2 -> reduction (IsNotEq k1 k2 P) P VONone
| VRedPar : forall P1 P2 Q vo, (reduction P1 P2 vo) -> (reduction (P1 ||| Q) (P2 ||| Q) vo)
| VRedNew : forall P Q L vo noc, 
    new_obs (free_ids_proc P) vo noc
    ->
    (forall i, 
      ~ (In i (L ++ (free_ids_proc P)))
      -> 
      (reduction (open_proc i 0 P) (open_proc i 0 Q) (expand_new_obs_choice noc i)))
    -> 
    (reduction (New P) (New Q) vo).

(* ============================================================================= *)

Inductive reductions : proc -> proc -> list obs -> Prop :=
| VRedsNil : forall P, reductions P P nil
| VRedsCons : forall P1 P2 P3 vo vos, reduction P1 P2 vo -> reductions P2 P3 vos -> reductions P1 P3 (vo :: vos)
.

(* ============================================================================= *)

Definition is_obs_free_id (f : free_id) (vo : obs) : bool := 
  match vo with
    | VONone => false
    | VOInteract _ f' _ => if (string_dec f f') then true else false
  end.

(* ============================================================================= *)

