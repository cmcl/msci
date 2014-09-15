(** This file presents the equivalence of System Fsub with and without contexts.
 - Authors: Jonghyun Park and Jeongbong Seo  *)
Set Implicit Arguments.

Require Import List Arith Max. 
Require Import LibTactics LibNat.

(* *************************************************************** *)
(** * Contents
 - Syntax 
  - [erased_t] and [erased_e]
 - Variables 
 - Parameters
 - Substitution
 - Typing contexts
 - Local closure
 - Well-formed typing contexts
 - Subtyping relation 
   - [sub]: a subtyping relation of System Fsub with contexts
   - [ann_sub]: a subtyping relation of System Fsub without contexts
 - Typing relation 
   - [typing]: a typing relation of System Fsub with contexts
   - [ann_typing]: a typing relation of System Fsub without contexts
 - Unrolling
 - Tactical support
 - Properties of System Fsub with contexts
 - Properties of System Fsub without contexts 
 - Preliminaries
 - The equivalence proof (Theorem 7)
   - Equivalence of [sub] and [ann_sub]
     - Lemma [sub_implies_ann_sub]
     - Lemma [ann_sub_implies_sub]
   - Equivalence of [typing] and [ann_typing]
     - Lemma [typing_implies_ann_typing]
     - Lemma [ann_typing_implies_typing]
 *)
(* *************************************************************** *)

(* *************************************************************** *)
(** * Syntax 
 Both variables and parameters are represented as natural numbers. 
 Since we use locally nameless representation, variables are treated 
 as indices, while parameters are treated as distinct atoms. *)
Notation ltvar     := nat.  (* type variable            *) 
Notation ftvar     := nat.  (* erased type parameter    *)
Notation ann_ftvar := nat.  (* annotated type parameter *)

Notation lvar      := nat.  (* term variable            *)
Notation fvar      := nat.  (* erased term parameter    *)  
Notation ann_fvar  := nat.  (* annotated term parameter *)  

(**
 To prove the equivalence of two systems, we use the following definition
 of types and terms: 
<< 
 types T, U, S := \top | A | X | X <: T | T -> U | \forall A <: T. U 
 terms t, u, s := a | x | x : T | \lambda a : T. t | t u | \Lambda A <: T. t | t [ T ] 
>> 
 Note that the definition allows us to use both parameters with and without 
 annotation. We refer to type parameters without annotation as erased type 
 parameters, and type parameters with annotation as annotated type parameters.

 We use the following notations for variables and parameters:
  - type variables  A, B, C 
  - type parameters X, Y, Z
  - term variables  a, b, c
  - term parameters x, y, z *)
Inductive typ : Set :=
| typ_top       : typ
| typ_ltvar     : ltvar -> typ
| typ_ftvar     : ftvar -> typ
| typ_ann_ftvar : ann_ftvar -> typ -> typ
| typ_arrow     : typ -> typ -> typ
| typ_all       : ltvar -> typ -> typ -> typ.

Inductive tm : Set :=
| tm_lvar     : lvar -> tm
| tm_fvar     : fvar -> tm
| tm_ann_fvar : ann_fvar -> typ -> tm
| tm_abs      : lvar -> typ -> tm -> tm
| tm_app      : tm -> tm -> tm
| tm_tabs     : ltvar -> typ -> tm -> tm
| tm_tapp     : tm -> typ -> tm.

Notation " X ^^ "    := (typ_ftvar X) (at level 65). 
Notation " X ^^ T "  := (typ_ann_ftvar X T) (at level 65). 
Notation " T --> U " := (typ_arrow T U) (at level 65).

Notation " x ** "   := (tm_fvar x) (at level 55).
Notation " x ** T " := (tm_ann_fvar x T) (at level 55).

Lemma typ_dec : forall T U : typ, 
  {T = U} + {T <> U}.
Proof.
  decide equality; apply eq_nat_dec.
Qed.

Lemma ftvar_dec : forall (X Y : ftvar), 
  {X = Y} + {X <> Y}.
Proof.
  decide equality; apply eq_nat_dec.
Qed.

Lemma ann_ftvar_dec : forall (Xt Yt : (ann_ftvar * typ)), 
  {Xt = Yt} + {Xt <> Yt}.
Proof.
  decide equality; [apply typ_dec | apply eq_nat_dec ].
Qed.

Lemma fvar_dec : forall (x y : fvar), 
  {x = y} + {x <> y}.
Proof.
  decide equality; apply eq_nat_dec.
Qed.

Lemma ann_fvar_dec : forall (xt yt : (ann_fvar * typ)), 
  {xt = yt} + {xt <> yt}.
Proof.
  decide equality; [apply typ_dec | apply eq_nat_dec ].
Qed.

Notation "p ==_t q"  := (fvar_dec p q) (at level 70).
Notation "p ==_T q"  := (ftvar_dec p q) (at level 70).
Notation "p ===_t q" := (ann_fvar_dec p q) (at level 70).
Notation "p ===_T q" := (ann_ftvar_dec p q) (at level 70).

(** ** [erased_t] and [erased_e] 
 A type [T] (or a term [t]) is said to be erased if every parameter in it is
 erased. We use [erased_t] and [erased_e] to denote such erased types and 
 terms. *)
Inductive erased_t : typ -> Prop :=
| erased_t_top   : 
  erased_t typ_top
| erased_t_ltvar : forall A, 
  erased_t (typ_ltvar A)
| erased_t_ftvar : forall X, 
  erased_t (X ^^)
| erased_t_arrow : forall T U, 
  erased_t T -> 
  erased_t U -> 
  erased_t (T --> U)
| erased_t_all   : forall A T U, 
  erased_t T -> 
  erased_t U -> 
  erased_t (typ_all A T U).

Inductive erased_e : tm -> Prop :=
| erased_e_lvar : forall a, 
  erased_e (tm_lvar a)
| erased_e_fvar : forall x, 
  erased_e (x **)
| erased_e_abs  : forall a T t, 
  erased_t T -> 
  erased_e t -> erased_e (tm_abs a T t)
| erased_e_app  : forall t t', 
  erased_e t -> 
  erased_e t' -> 
  erased_e (tm_app t t')
| erased_e_tabs : forall A T t, 
  erased_t T -> 
  erased_e t -> 
  erased_e (tm_tabs A T t)
| erased_e_tapp : forall t T, 
  erased_e t -> 
  erased_t T -> 
  erased_e (tm_tapp t T).

Hint Constructors erased_t erased_e.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Variables 
 The function [LV_all_tt], defined below, calculates the set of type
 variables that appear in a type [T]. *)
Fixpoint LV_all_tt (T: typ) : list ltvar :=
  match T with
    | typ_top         => nil
    | typ_ltvar A     => A :: nil
    | X ^^            => nil
    | X ^^ T          => nil
    | T1 --> T2       => LV_all_tt T1 ++ LV_all_tt T2
    | typ_all A T1 T2 => A :: (LV_all_tt T1 ++ LV_all_tt T2)
  end.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Parameters
 ** Type parameters
 The functions [FV_tt] and [FV_te], defined below, calculate 
 the set of erased type parameters in a type and a term, respectively. *)
Fixpoint FV_tt (T:typ) : list ftvar :=
  match T with
    | typ_top         => nil
    | typ_ltvar _     => nil
    | X ^^            => X :: nil
    | X ^^ _          => nil
    | T1 --> T2       => FV_tt T1 ++ FV_tt T2
    | typ_all _ T1 T2 => FV_tt T1 ++ FV_tt T2
  end.

Fixpoint FV_te (t : tm) : list ftvar :=
  match t with
  | tm_lvar _     => nil 
  | _ **          => nil
  | _ ** _        => nil
  | tm_abs _ T t  => FV_tt T ++ FV_te t
  | tm_app t t'   => FV_te t ++ FV_te t'
  | tm_tabs _ T t => FV_tt T ++ FV_te t
  | tm_tapp t T   => FV_te t ++ FV_tt T
end.

(** The functions [ann_FV_tt] and [ann_FV_te], defined below, calculate 
 the set of annotated type parameters in a type and a term, respectively. *)
Fixpoint ann_FV_tt (T:typ) : list ann_ftvar :=
  match T with
    | typ_top         => nil
    | typ_ltvar _     => nil
    | X ^^            => nil
    | X ^^ T          => X :: (ann_FV_tt T)
    | T1 --> T2       => ann_FV_tt T1 ++ ann_FV_tt T2
    | typ_all _ T1 T2 => ann_FV_tt T1 ++ ann_FV_tt T2
  end.

Fixpoint ann_FV_te (t:tm) : list ann_ftvar :=
  match t with
    | tm_lvar _     => nil 
    | _ **          => nil
    | _ ** T        => ann_FV_tt T
    | tm_abs _ T t  => ann_FV_tt T ++ ann_FV_te t
    | tm_app t t'   => ann_FV_te t ++ ann_FV_te t'
    | tm_tabs _ T t => ann_FV_tt T ++ ann_FV_te t 
    | tm_tapp t T   => ann_FV_te t ++ ann_FV_tt T
  end.

(** ** Term parameters
 The function [FV_ee], defined below, calculates the set of erased 
 term parameters in a term, and the function [ann_FV_ee] calculates 
 the set of annotated term parameters in a term. *)
Fixpoint FV_ee (t : tm) : list fvar :=
  match t with
    | tm_lvar _     => nil 
    | x **          => x :: nil
    | _ ** _        => nil
    | tm_abs _ _ t  => FV_ee t
    | tm_app t t'   => FV_ee t ++ FV_ee t'
    | tm_tabs _ _ t => FV_ee t
    | tm_tapp t _   => FV_ee t
  end.

Fixpoint ann_FV_ee (t : tm) : list ann_fvar :=
  match t with
    | tm_lvar _     => nil 
    | x **          => nil
    | x ** _        => x :: nil
    | tm_abs _ _ t  => ann_FV_ee t
    | tm_app t t'   => ann_FV_ee t ++ ann_FV_ee t'
    | tm_tabs _ _ t => ann_FV_ee t
    | tm_tapp t _   => ann_FV_ee t
  end.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Substitution *)
(** ** Type variables 
 The functions [lsubst_tt] and [lsubst_te], defined below, replace
 a type variable with a type for types and terms, respectively.*)
Fixpoint lsubst_tt (B : ltvar) (U : typ) (T : typ) : typ :=
  match T with
    | typ_top         => typ_top
    | typ_ltvar A     => if A == B then U else typ_ltvar A
    | X ^^            => X ^^
    | X ^^ T          => X ^^ T
    | T1 --> T2       => (lsubst_tt B U T1) --> (lsubst_tt B U T2)
    | typ_all A T1 T2 => 
      if A == B then typ_all A (lsubst_tt B U T1) T2
        else typ_all A (lsubst_tt B U T1) (lsubst_tt B U T2)
  end.

Fixpoint lsubst_te (B : ltvar) (U : typ)  (t : tm) : tm :=
  match t with
    | tm_lvar a     => tm_lvar a
    | x **          => x ** 
    | x ** T        => x ** T
    | tm_abs a T t  => tm_abs a (lsubst_tt B U T) (lsubst_te B U t) 
    | tm_app t1 t2  => tm_app (lsubst_te B U t1) (lsubst_te B U t2) 
    | tm_tabs A T t => 
      if A == B then tm_tabs A (lsubst_tt B U T) t 
        else tm_tabs A (lsubst_tt B U T) (lsubst_te B U t) 
    | tm_tapp t T   => tm_tapp (lsubst_te B U t) (lsubst_tt B U T) 
  end.

(** ** Term variables
 The function [lsubst_ee], defined below, replaces a term variable 
 with a term. *)
Fixpoint lsubst_ee (b : lvar) (u : tm) (t : tm) : tm :=
  match t with
    | tm_lvar a     => if a == b then u else tm_lvar a
    | x **          => x **
    | x ** T        => x ** T
    | tm_abs a T t  => 
      if a == b then tm_abs a T t else tm_abs a T (lsubst_ee b u t)
    | tm_app t1 t2  => tm_app (lsubst_ee b u t1) (lsubst_ee b u t2)
    | tm_tabs A T t => tm_tabs A T (lsubst_ee b u t)
    | tm_tapp t T   => tm_tapp (lsubst_ee b u t) T
  end.

(** ** Type parameters 
 The functions [fsubst_tt] and [fsubst_te] replace an erased type 
 parameter with a type. *)
Fixpoint fsubst_tt (Y:ftvar) (U : typ) (T : typ) : typ :=
  match T with
    | typ_top         => typ_top
    | typ_ltvar A     => typ_ltvar A
    | X ^^            => if X == Y then U else X ^^
    | X ^^ T          => X ^^ T
    | T1 --> T2       => (fsubst_tt Y U T1) --> (fsubst_tt Y U T2)
    | typ_all A T1 T2 => typ_all A (fsubst_tt Y U T1) (fsubst_tt Y U T2)
  end.

Fixpoint fsubst_te (Y:ftvar) (U:typ) (t:tm) : tm :=
  match t with
    | tm_lvar a     => tm_lvar a
    | X **          => X **
    | X ** T        => X ** T
    | tm_abs a T t  => tm_abs a (fsubst_tt Y U T) (fsubst_te Y U t)
    | tm_app t1 t2  => tm_app (fsubst_te Y U t1) (fsubst_te Y U t2)
    | tm_tabs A T t => tm_tabs A (fsubst_tt Y U T) (fsubst_te Y U t)
    | tm_tapp t T   => tm_tapp (fsubst_te Y U t) (fsubst_tt Y U T)
  end.

(** The functions [ann_fsubst_tt] and [ann_fsubst_te] 
 replace an annotated type parameter with a type. Note that [ann_fsubst_tt] 
 replaces a type parameter only when both a parameter and its annotated 
 type are matched. *)
Fixpoint ann_fsubst_tt (Y:ann_ftvar) (TY:typ) (U : typ) (T : typ) : typ :=
  match T with
    | typ_top         => typ_top
    | typ_ltvar A     => typ_ltvar A
    | X ^^            => X ^^
    | X ^^ T          => 
      if ann_ftvar_dec (X, T) (Y, TY)
        then U else (X ^^ (ann_fsubst_tt Y TY U T))
    | T1 --> T2       => 
      (ann_fsubst_tt Y TY U T1) --> (ann_fsubst_tt Y TY U T2)
    | typ_all A T1 T2 => 
      typ_all A (ann_fsubst_tt Y TY U T1) (ann_fsubst_tt Y TY U T2)
  end.

Fixpoint ann_fsubst_te (Y : ann_ftvar) (TY:typ) (U:typ) (t:tm) : tm :=
  match t with
    | tm_lvar a     => tm_lvar a
    | x **          => x **
    | x ** T        => x ** (ann_fsubst_tt Y TY U T) 
    | tm_abs A T t  => 
      tm_abs A (ann_fsubst_tt Y TY U T) (ann_fsubst_te Y TY U t)
    | tm_app t1 t2  => 
      tm_app (ann_fsubst_te Y TY U t1) (ann_fsubst_te Y TY U t2)
    | tm_tabs A T t => 
      tm_tabs A (ann_fsubst_tt Y TY U T) (ann_fsubst_te Y TY U t)
    | tm_tapp t T   => 
      tm_tapp (ann_fsubst_te Y TY U t) (ann_fsubst_tt Y TY U T)
  end.

(** ** Term parameters 
 The function [fsubst_ee] replaces an erased term parameter with a term. *)
Fixpoint fsubst_ee (y : fvar) (u t: tm) : tm :=
  match t with
    | tm_lvar a     => tm_lvar a
    | x **          => if x == y then u else tm_fvar x
    | x ** T        => x ** T
    | tm_abs a T t  => tm_abs a T (fsubst_ee y u t)
    | tm_app t1 t2  => tm_app (fsubst_ee y u t1) (fsubst_ee y u t2)
    | tm_tabs A T t => tm_tabs A T (fsubst_ee y u t)
    | tm_tapp t T   => tm_tapp (fsubst_ee y u t) T
  end.

(**  The function [ann_fsubst_tt] replaces an annotated term parameter with
 a term. Note that [ann_fsubst_ee] replaces a term parameter only when 
 both a parameter and its annotated type are matched.*)
Fixpoint ann_fsubst_ee (y : ann_fvar) (Ty:typ) (u t: tm) : tm :=
  match t with
    | tm_lvar a     => tm_lvar a
    | x **          => x **
    | x ** T        => 
      if ann_fvar_dec (x, T) (y, Ty) then u else x ** T
    | tm_abs a T t  => tm_abs a T (ann_fsubst_ee y Ty u t)
    | tm_app t1 t2  => 
      tm_app (ann_fsubst_ee y Ty u t1) (ann_fsubst_ee y Ty u t2)
    | tm_tabs A T t => tm_tabs A T (ann_fsubst_ee y Ty u t)
    | tm_tapp t T   => tm_tapp (ann_fsubst_ee y Ty u t) T
  end.

(** We introduce several notations to simplify the presentation, which
 use the following conventions:
  - { ... } denotes variable substitution.
  - [ ... ] denotes parameter substitution.
  - ~> denotes type substitution over types.
  - :~> denotes type substitution over terms.
  - ::~> denotes term substitution over terms. *)
Notation "{ A ~> U } T" := (lsubst_tt A U T) (at level 67).
Notation "{ A :~> U } t" := (lsubst_te A U t) (at level 67).
Notation "{ a ::~> u } t " := (lsubst_ee a u t) (at level 67).

Notation "[ X ~> U ] T" := (fsubst_tt X U T) (at level 67).
Notation "[ X :~> U ] t " := (fsubst_te X U t) (at level 67).
Notation "[ x ::~> u ] t " := (fsubst_ee x u t) (at level 67).

Notation "[ ( X , TX ) ~> U ] T" := (ann_fsubst_tt X TX U T) (at level 67).
Notation "[ ( X , TX ) :~> U ] t " := (ann_fsubst_te X TX U t) (at level 67).
Notation "[ ( x , Tx ) ::~> u ] t " := (ann_fsubst_ee x Tx u t) (at level 67).
(* *************************************************************** *)

(* *************************************************************** *)
(** * Typing contexts 
 A typing context records specific properties of parameters which 
 eventually originate from binders. We refer to each record as 
 binding. Since there are two kinds of binders, there are two 
 kinds of bindings. *)
Inductive ctxt_bind : Set :=
| ctxt_bind_fvar  : fvar -> typ -> ctxt_bind
| ctxt_bind_ftvar : ftvar -> typ -> ctxt_bind.

(** A typing context is a list of these bindings *)
Notation ctxt := (list ctxt_bind).   

(** X ~<: T denotes a type binding, and x ~: T denotes a term binding. *)
Notation " x ~: T " := (ctxt_bind_fvar x T) (at level 56).
Notation " X ~<: T " := (ctxt_bind_ftvar X T) (at level 56).

(** ** Parameters
 The function [dom_tc], defined below, calculates the set of type 
 parameters bound in a typing context. *)
Fixpoint dom_tc (Gamma : ctxt) : list ftvar :=
  match Gamma with
    | nil => nil 
    | (_ ~: _) :: Gamma' => dom_tc Gamma'
    | (X ~<: _) :: Gamma' => X :: dom_tc Gamma'
  end.

(** In other words, if [X ~<: T] is in [Gamma], [X] is in [dom_tc Gamma]. *)
Lemma ftvar_bind_in_dom_ctxt_t : forall Gamma X T,
  In (X ~<: T) Gamma -> In X (dom_tc Gamma).
Proof.
  induction Gamma; intros.
    Destruct In by auto.
    destruct a; simpl dom_tc; Destruct In by (eauto; congruence).
      inversion H; subst; Destruct In by eauto.
Qed.

Hint Resolve ftvar_bind_in_dom_ctxt_t.

(** The converse is also true. *)
Lemma exists_ftvar_bind : forall X Gamma,
  In X (dom_tc Gamma) -> exists T, In (X ~<: T) Gamma.
Proof.
  intros; induction Gamma as [ | b Gamma'].
  inversion H.
  destruct b.
    destruct (IHGamma' H) as [T' ?]. 
      simpl dom_tc in H. 
      exists T'; Destruct In by eauto.
    simpl dom_tc in H; Destruct In by subst.
      exists t; Destruct In by eauto. 
      destruct (IHGamma' H) as [T' ?]; exists T'; Destruct In by eauto. 
Qed.

(** The function [dom_ec], defined below, calculates the set of term 
 parameters bound in a typing context. *)
Fixpoint dom_ec (Gamma : ctxt) : list fvar :=
  match Gamma with
    | nil => nil 
    | (x ~: _) :: Gamma' => x :: dom_ec Gamma'
    | (_ ~<: _ ) :: Gamma' => dom_ec Gamma'
  end.

(** In other words, if [x ~: T] is in [Gamma], [x] is in [dom_ec Gamma]. *)
Lemma fvar_bind_in_dom_ctxt_e : forall Gamma x T,
  In (x ~: T) Gamma -> In x (dom_ec Gamma).
Proof.
  induction Gamma; intros; [ eauto with v62 | idtac ].
  destruct (in_inv H); subst.
    simpl; eauto. 
    destruct a; simpl dom_ec; Destruct In by eauto.
Qed.

Hint Resolve fvar_bind_in_dom_ctxt_e.

(** The function [FV_tc], defined below, calculates the set of all erased 
 type parameters that appear in a typing context. *)
Fixpoint FV_tc (Gamma : ctxt) : list ftvar :=
  match Gamma with
    | nil => nil 
    | (_ ~: T) :: Gamma' => FV_tt T ++ FV_tc Gamma'
    | (X ~<: T) :: Gamma' => X :: (FV_tt T ++ FV_tc Gamma')
  end.

(** Thus, [FV_tc Gamma] includes all the erased type parameters in 
 [dom_tc Gamma]. *)
Lemma incl_dom_ftvar_ctxt : forall Gamma X,
  In X (dom_tc Gamma) -> In X (FV_tc Gamma).
Proof.
  induction Gamma; intros.
    Destruct In by eauto.
    destruct a; 
      simpl FV_tc; simpl dom_tc in H; 
        Destruct In by (eauto; congruence).
      subst; Destruct In by eauto.
Qed.

Hint Resolve incl_dom_ftvar_ctxt.

(** All of these functions are distributive over [++]. *)
Lemma dom_tc_app_dist : forall Gamma Gamma',
  dom_tc (Gamma ++ Gamma') = dom_tc Gamma ++ dom_tc Gamma'.
Proof.
  induction Gamma; intros; simpl; auto.
    destruct a; simpl; f_equal; auto.
Qed.

Lemma dom_ec_app_dist : forall Gamma Gamma',
  dom_ec (Gamma ++ Gamma') = dom_ec Gamma ++ dom_ec Gamma'.
Proof.
  induction Gamma; intros; simpl; auto.
  destruct a; simpl; f_equal; auto.
Qed.

Lemma FV_tc_app_dist : forall Gamma Gamma',
  FV_tc (Gamma ++ Gamma') = FV_tc Gamma ++ FV_tc Gamma'.
Proof.
  induction Gamma; intros; eauto.
  destruct a; simpl.
    rewrite IHGamma; eauto with v62.
    rewrite IHGamma; f_equal; eauto with v62.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Local closure 
 ** Local closure of types 
 We bring the definition of [lclosed_t] from [lclosed_t] in [Fnamedcontext.v],
 and that of [ann_lclosed_t] from [lclosed_t] in [Fnamed.v]. *)
Inductive lclosed_t : ctxt -> list ltvar -> typ -> Prop :=
| lclosed_t_top   : forall Gamma, 
  lclosed_t Gamma emptyset typ_top
| lclosed_t_ltvar : forall Gamma A, 
  lclosed_t Gamma (A :: emptyset) (typ_ltvar A)
| lclosed_t_ftvar : forall Gamma X,
  In X (dom_tc Gamma) -> 
  lclosed_t Gamma emptyset (X ^^)
| lclosed_t_arrow : forall Gamma I1 I2 (T U : typ),
  lclosed_t Gamma I1 T -> 
  lclosed_t Gamma I2 U -> 
  lclosed_t Gamma (I1 ++ I2) (T --> U)
| lclosed_t_all   : forall Gamma I1 I2 A T U,
  lclosed_t Gamma I1 T ->
  lclosed_t Gamma I2 U -> 
  lclosed_t Gamma (I1 ++ (remove eq_nat_dec A I2)) (typ_all A T U).

Hint Constructors lclosed_t.

Inductive ann_lclosed_t : list ltvar -> typ -> Prop :=
| ann_lclosed_t_top   : 
  ann_lclosed_t emptyset typ_top
| ann_lclosed_t_ltvar : forall A,
  ann_lclosed_t (A :: emptyset) (typ_ltvar A)
| ann_lclosed_t_ftvar : forall X (T : typ),
  ann_lclosed_t emptyset T ->
  ann_lclosed_t emptyset (X ^^ T)
| ann_lclosed_t_arrow : forall I1 I2 (T U : typ),
  ann_lclosed_t I1 T ->
  ann_lclosed_t I2 U ->
  ann_lclosed_t (I1 ++ I2) (T --> U)
| ann_lclosed_t_all   : forall I1 I2 A T U,
  ann_lclosed_t I1 T ->
  ann_lclosed_t I2 U -> 
  ann_lclosed_t (I1 ++ (remove eq_nat_dec A I2)) (typ_all A T U).

Hint Constructors ann_lclosed_t.

(** ** Local closure of terms 
 Similarly, we bring the definition of [lclosed_e] from [lclosed_e] in 
 [Fnamedcontext.v] and that of [ann_lclosed_e] from [lclosed_e] in 
 [Fnamed.v]. *)
Inductive lclosed_e : ctxt -> list ltvar -> list lvar -> tm -> Prop := 
| lclosed_e_lvar : forall Gamma a, 
  lclosed_e Gamma nil (a :: nil) (tm_lvar a)
| lclosed_e_fvar : forall Gamma x, 
  In x (dom_ec Gamma) -> 
  lclosed_e Gamma nil nil (x **)
| lclosed_e_abs  : forall Gamma I1 I2 i a T t, 
  lclosed_t Gamma I1 T -> 
  lclosed_e Gamma I2 i t -> 
  lclosed_e Gamma (I1 ++ I2) (remove eq_nat_dec a i) (tm_abs a T t) 
| lclosed_e_app  : forall Gamma I1 I2 i1 i2 t1 t2,
  lclosed_e Gamma I1 i1 t1 -> 
  lclosed_e Gamma I2 i2 t2 -> 
  lclosed_e Gamma (I1 ++ I2) (i1 ++ i2) (tm_app t1 t2)
| lclosed_e_tabs : forall Gamma I1 I2 i A T t,
  lclosed_t Gamma I1 T -> 
  lclosed_e Gamma I2 i t -> 
  lclosed_e Gamma (I1 ++ (remove eq_nat_dec A I2)) i (tm_tabs A T t)
| lclosed_e_tapp : forall Gamma I1 I2 i t T,
  lclosed_e Gamma I1 i t -> 
  lclosed_t Gamma I2 T -> 
  lclosed_e Gamma (I1 ++ I2) i (tm_tapp t T).

Hint Constructors lclosed_e.

Inductive ann_lclosed_e : list ltvar -> list lvar -> tm -> Prop := 
| ann_lclosed_e_lvar : forall a, 
  ann_lclosed_e nil (a :: nil) (tm_lvar a)
| ann_lclosed_e_fvar : forall x T, 
  ann_lclosed_t emptyset T ->
  ann_lclosed_e emptyset emptyset (x ** T)
| ann_lclosed_e_abs  : forall I1 I2 i a T t, 
  ann_lclosed_t I1 T ->
  ann_lclosed_e I2 i t ->
  ann_lclosed_e (I1 ++ I2) (remove eq_nat_dec a i) (tm_abs a T t) 
| ann_lclosed_e_app  : forall I1 I2 i1 i2 t1 t2,
  ann_lclosed_e I1 i1 t1 ->
  ann_lclosed_e I2 i2 t2 ->
  ann_lclosed_e (I1 ++ I2) (i1 ++ i2) (tm_app t1 t2)
| ann_lclosed_e_tabs : forall I1 I2 i A T t,
  ann_lclosed_t I1 T ->
  ann_lclosed_e I2 i t ->
  ann_lclosed_e (I1 ++ (remove eq_nat_dec A I2)) i (tm_tabs A T t)
| ann_lclosed_e_tapp : forall I1 I2 i t T,
  ann_lclosed_e I1 i t ->
  ann_lclosed_t I2 T ->
  ann_lclosed_e (I1 ++ I2) i (tm_tapp t T).

Hint Constructors ann_lclosed_e.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Well-formed typing contexts 
 We say that a typing context is well-formed if every type contained 
 within are well-formed w.r.t its corresponding typing contexts, and
 every parameter is distinct. Note the use of [lclosed_t] in the
 [ctxt_okay_epar] and [ctxt_okay_tpar] cases. *)
Inductive ctxt_okay : ctxt -> Prop :=
| ctxt_okay_nil : 
  ctxt_okay nil
| ctxt_okay_epar : forall Gamma x T,
  ctxt_okay Gamma ->
  ~ In x (dom_ec Gamma) ->
  lclosed_t Gamma nil T ->
  ctxt_okay (x ~: T :: Gamma)
| ctxt_okay_tpar : forall Gamma X T,
  ctxt_okay Gamma ->
  ~ In X (dom_tc Gamma) ->
  lclosed_t Gamma nil T ->
  ctxt_okay (X ~<: T :: Gamma).

Hint Constructors ctxt_okay.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Subtyping relation 
 We bring the definition of [sub] from [sub] in [Fnamedcontext.v], 
 and that of [ann_sub] from [sub] in [Fnamed.v]. Since out proof 
 necessities induction on the size of [ann_sub] proofs, we also 
 bring the definition of [ann_subLH] from [subLH] in [Fnamed.v]. *)
Inductive sub : ctxt -> typ -> typ -> Prop :=
| sub_top        : forall Gamma T, 
  ctxt_okay Gamma -> 
  lclosed_t Gamma emptyset T -> 
  sub Gamma T typ_top
| sub_refl_tvar  : forall Gamma X,
  ctxt_okay Gamma -> 
  lclosed_t Gamma emptyset (X ^^) ->
  sub Gamma (X ^^) (X ^^)
| sub_trans_tvar : forall Gamma T U X,
  In (X ~<: T) Gamma -> 
  sub Gamma T U -> 
  sub Gamma (X ^^) U
| sub_arrow      : forall Gamma T1 T2 U1 U2,
  sub Gamma U1 T1 ->
  sub Gamma T2 U2 ->
  sub Gamma (T1 --> T2) (U1 --> U2)
| sub_all        : forall Gamma T1 T2 U1 U2 X A B,
  sub Gamma U1 T1 ->
  ~ In X (FV_tc Gamma) ->
  ~ In X (FV_tt T2 ++ FV_tt U2) -> 
  sub (X ~<: U1 :: Gamma) ({A ~> X ^^} T2) ({B ~> X ^^} U2) ->
  sub Gamma (typ_all A T1 T2) (typ_all B U1 U2). 

Hint Constructors sub.

Inductive ann_sub : typ -> typ -> Prop :=
| ann_sub_top        : forall T,
  ann_lclosed_t emptyset T -> 
  ann_sub T typ_top
| ann_sub_refl_tvar  : forall T X,
  ann_lclosed_t emptyset T ->
  ann_sub (X ^^ T) (X ^^ T)
| ann_sub_trans_tvar : forall T U X,
  ann_sub T U ->
  ann_sub (X ^^ T) U
| ann_sub_arrow      : forall T1 T2 U1 U2,
  ann_sub U1 T1 ->
  ann_sub T2 U2 ->
  ann_sub (T1 --> T2) (U1 --> U2)
| ann_sub_all        : forall T1 T2 U1 U2 X A B,
  ann_sub U1 T1 ->
  ~ In X (ann_FV_tt T2) ->
  ~ In X (ann_FV_tt U2) ->
  ~ In X (ann_FV_tt T1) ->
  ~ In X (ann_FV_tt U1) ->
  ann_sub ({A ~> X ^^ U1} T2) ({B ~> X ^^ U1} U2) ->
  ann_sub (typ_all A T1 T2) (typ_all B U1 U2). 
   
Inductive ann_subLH : nat -> typ -> typ -> Prop :=
| ann_subLH_top        : forall T, 
  ann_lclosed_t emptyset T -> 
  ann_subLH O T typ_top
| ann_subLH_refl_tvar  : forall T X,
  ann_lclosed_t emptyset T ->
  ann_subLH O (X ^^ T) (X ^^ T)
| ann_subLH_trans_tvar : forall T U X n,
  ann_subLH n T U ->
  ann_subLH (S n) (X ^^ T) U
| ann_subLH_arrow      : forall T1 T2 U1 U2 n1 n2,
  ann_subLH n1 U1 T1 ->
  ann_subLH n2 T2 U2 ->
  ann_subLH (S (max n1 n2)) (T1 --> T2) (U1 --> U2)
| ann_subLH_all        : forall T1 T2 U1 U2 X n1 n2 A B,
  ann_subLH n1 U1 T1 ->
  ~ In X (ann_FV_tt T2) ->
  ~ In X (ann_FV_tt U2) ->
  ~ In X (ann_FV_tt T1) ->
  ~ In X (ann_FV_tt U1) ->
  ann_subLH n2 ({A ~> X ^^ U1} T2) ({B ~> X ^^ U1} U2) ->
  ann_subLH (S (max n1 n2)) (typ_all A T1 T2) (typ_all B U1 U2). 

Hint Constructors ann_sub ann_subLH.

(** Lemma [ann_sub_subLH] and [ann_subLH_sub] formally state the equivalence 
 between [ann_sub] and [ann_subLH]. *)
Lemma ann_sub_subLH : forall annA annB,
  ann_sub annA annB -> exists n, ann_subLH n annA annB.
Proof.
  induction 1; eauto.
  destruct IHann_sub as [n ?]. 
  exists (S n); eauto.
  destruct IHann_sub1 as [n1 ?].
  destruct IHann_sub2 as [n2 ?].
  exists (S (max n1 n2)); eauto.
  destruct IHann_sub1 as [n1 ?].
  destruct IHann_sub2 as [n2 ?].
  exists (S (max n1 n2)); eauto.
Qed.

Lemma ann_subLH_sub : forall n annA annB,
  ann_subLH n annA annB -> ann_sub annA annB.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve ann_sub_subLH ann_subLH_sub.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Typing relation 
 We bring the definition of [typing] from [typing] in [Fnamedcontext.v], 
 and that of [ann_typing] from [typing] in [Fnamed.v]. Since our proof 
 uses induction on the size of [ann_typing] proofs, we introduce the 
 inductive definition [ann_typingLH]. Note that the definition of 
 [ann_typingLH] is different from that of [typingLH] in [Fnamed.v].
 The size of proofs does not increase for the [ann_typingLH_sub] case. *)
Inductive typing : ctxt -> tm -> typ -> Prop :=
| typing_fvar : forall Gamma x T,
  ctxt_okay Gamma ->
  In (x ~: T) Gamma ->
  typing Gamma (x **) T
| typing_abs  : forall Gamma a T U t x,
  lclosed_t Gamma emptyset T ->
  ~ In x (dom_ec Gamma) -> 
  ~ In x (FV_ee t) ->
  typing (x ~: T :: Gamma) ({a ::~> x **} t) U ->
  typing Gamma (tm_abs a T t) (T --> U)
| typing_app  : forall Gamma t t' T U,
  typing Gamma t (T --> U) -> 
  typing Gamma t' T ->
  typing Gamma (tm_app t t') U
| typing_tabs : forall Gamma A B t T U X,
  lclosed_t Gamma emptyset T -> 
  ~ In X (FV_tc Gamma) ->
  ~ In X (FV_te t ++ FV_tt U) -> 
  typing (X ~<: T :: Gamma) ({A :~> X ^^} t) ({B ~> X ^^} U) 
  -> typing Gamma (tm_tabs A T t) (typ_all B T U)
| typing_tapp : forall Gamma t A T T' U,
  typing Gamma t (typ_all A T' U) -> 
  sub Gamma T T' -> 
  typing Gamma (tm_tapp t T) ({A ~> T} U)
| typing_sub : forall Gamma t T U,
  typing Gamma t T -> 
  sub Gamma T U -> 
  typing Gamma t U.

Hint Constructors typing.

Inductive ann_typing : tm -> typ -> Prop :=
| ann_typing_fvar : forall x T,
  ann_lclosed_t emptyset T ->
  ann_typing (x ** T) T
| ann_typing_abs  : forall a T U t x,
  ann_lclosed_t emptyset T ->
  ~ In x (ann_FV_ee t) ->
  ann_typing ({a ::~> x ** T} t) U ->
  ann_typing (tm_abs a T t) (T --> U)
| ann_typing_app  : forall t t' T U,
  ann_typing t (T --> U) ->
  ann_typing t' T ->
  ann_typing (tm_app t t') U
| ann_typing_tabs : forall A T t B U X,
  ann_lclosed_t emptyset T ->
  ~ In X (ann_FV_te t ++ ann_FV_tt U) ->
  ann_typing ({A :~> X ^^ T} t) ({B ~> X ^^ T} U) ->
  ann_typing (tm_tabs A T t) (typ_all B T U)
| ann_typing_tapp : forall t A T U S,
  ann_typing t (typ_all A U S) ->
  ann_sub T U ->
  ann_typing (tm_tapp t T) ({A ~> T} S)
| ann_typing_sub  : forall t T U,
  ann_typing t T ->
  ann_sub T U ->
  ann_typing t U.

Inductive ann_typingLH : nat -> tm -> typ -> Prop :=
| ann_typingLH_fvar : forall x T,
  ann_lclosed_t emptyset T ->
  ann_typingLH O (x ** T) T
| ann_typingLH_abs  : forall a T U t x k,
  ann_lclosed_t emptyset T ->
  ~ In x (ann_FV_ee t) -> 
  ann_typingLH k ({a ::~> x ** T} t) U -> 
  ann_typingLH (S k) (tm_abs a T t) (T --> U)
| ann_typingLH_app  : forall t t' T U k1 k2,
  ann_typingLH k1 t (T --> U) ->
  ann_typingLH k2 t' T ->
  ann_typingLH (S (max k1 k2)) (tm_app t t') U
| ann_typingLH_tabs : forall A T t B U X k,
  ann_lclosed_t emptyset T ->
  ~ In X (ann_FV_te t ++ ann_FV_tt U) ->
  ann_typingLH k ({A :~> X ^^ T} t) ({B ~> X ^^ T} U) ->
  ann_typingLH (S k) (tm_tabs A T t) (typ_all B T U)
| ann_typingLH_tapp : forall t A T U S k,
  ann_typingLH k t (typ_all A U S) ->
  ann_sub T U -> 
  ann_typingLH (Datatypes.S k) (tm_tapp t T) ({A ~> T} S)
| ann_typingLH_sub  : forall t T U k,
  ann_typingLH k t T ->
  ann_sub T U ->
  ann_typingLH k t U.

(** The proof of the equivalence of [typing] and [ann_typing] 
 exploits properties of [ann_typing] proofs whose last case
 is not the [ann_typingLH_sub] case. We use [ann_pure_typingLH]
 to denote such proofs. *)
Inductive ann_pure_typingLH : nat -> tm -> typ -> Prop :=
| ann_pure_typingLH_fvar : forall x T,
  ann_lclosed_t emptyset T ->
  ann_pure_typingLH O (x ** T) T
| ann_pure_typingLH_abs  : forall a T U t x k,
  ann_lclosed_t emptyset T ->
  ~ In x (ann_FV_ee t) -> 
  ann_typingLH k ({a ::~> x ** T} t) U -> 
  ann_pure_typingLH (S k) (tm_abs a T t) (T --> U)
| ann_pure_typingLH_app  : forall t t' T U k1 k2,
  ann_typingLH k1 t (T --> U) ->
  ann_typingLH k2 t' T ->
  ann_pure_typingLH (S (max k1 k2)) (tm_app t t') U
| ann_pure_typingLH_tabs : forall A T t B U X k,
  ann_lclosed_t emptyset T ->
  ~ In X (ann_FV_te t ++ ann_FV_tt U) ->
  ann_typingLH k ({A :~> X ^^ T} t) ({B ~> X ^^ T} U) ->
  ann_pure_typingLH (S k) (tm_tabs A T t) (typ_all B T U)
| ann_pure_typingLH_tapp : forall t A T U S k,
  ann_typingLH k t (typ_all A U S) ->
  ann_sub T U -> 
  ann_pure_typingLH (Datatypes.S k) (tm_tapp t T) ({A ~> T} S).

Hint Constructors ann_typing ann_typingLH ann_pure_typingLH.

Lemma ann_typing_implies_ann_typingLH : forall ann_e ann_A,
  ann_typing ann_e ann_A ->
  exists n, ann_typingLH n ann_e ann_A.
Proof.
  induction 1; eauto.
  destruct IHann_typing as [n ?]; exists (S n); eauto.
  destruct IHann_typing1 as [n1 ?];
    destruct IHann_typing2 as [n2 ?];
      exists (S (max n1 n2)); eauto.
  destruct IHann_typing as [n ?]; exists (S n); eauto.
  destruct IHann_typing as [n ?]; exists (Datatypes.S n); eauto.
  destruct IHann_typing as [n ?]; exists n; eauto.
Qed.

Lemma ann_pure_typingLH_implies_ann_typingLH : forall n ann_e ann_A,
  ann_pure_typingLH n ann_e ann_A -> ann_typingLH n ann_e ann_A.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve ann_typing_implies_ann_typingLH.
Hint Resolve ann_pure_typingLH_implies_ann_typingLH.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Unrolling 
 We show the equivalence via two bridge functions: [unroll_t] and [unroll_e].
 These functions take a typing context [Gamma] and replace erased parameters 
 with annotated parameters according to the typing context [Gamma]. 

 We refer to an operation that replaces erased parameters with annotated 
 ones as "unrolling". 

 We use [unroll_t Gamma T] to denote a result of unrolling a type 
 [T], and [unroll_e Gamma t] to denote a result of unrolling a term [t]. *)
Fixpoint unroll_t (Gamma : ctxt) (U : typ) : typ :=
  match Gamma with
    | nil => U
    | (x ~: T) :: Gamma' => 
      unroll_t Gamma' U
    | (X ~<: T) :: Gamma' => 
      unroll_t Gamma' ([ X ~> (X ^^ (unroll_t Gamma' T))] U)
  end.

Fixpoint unroll_e (Gamma : ctxt) (u : tm) : tm :=
  match Gamma with
    | nil => u
    | (x ~: T) :: Gamma' => 
      unroll_e Gamma' ([x ::~> (x ** (unroll_t Gamma' T))] u)
    | (X ~<: T) :: Gamma' => 
      unroll_e Gamma' ([ X :~> (X ^^ (unroll_t Gamma' T))] u)
  end.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Tactical support 
 We introduce an automation tactic [Simplify] to simplify the proof.
 [Simplify] attempts to evaluate several fixpoint functions, such as 
 [FV_tt], [ann_FV_tt], as much as possible. This simplification is 
 useful for the following case:
<<
 ...
 H : ~ In X (FV_tt (Gamma_1 ++ Gamma_2 ++ Gamma_3 ++ Gamma_4) )
 ...
 --------------------------------------------------------------
 ~ In X (FV_tt Gamma_4)
>>
 [Simplify by eauto] first decomposes the hypothesis H as follows:
<<
 ...
 ? : ~ In X (FV_tt Gamma_1)
 ? : ~ In X (FV_tt Gamma_2)
 ? : ~ In X (FV_tt Gamma_3)
 ? : ~ In X (FV_tt Gamma_4)
 ...
 --------------------------------------------------------------
 ~ In X (FV_tt Gamma_4)
>>
 Then it applies [eauto] to solve the goal. *)
Ltac simplifyTac tac :=
let rec filter_list l := 
  match l with
    | emptyset => idtac
    | _ :: _ => idtac
    | _ => fail 
  end
with filter_t t :=
  match t with
    | typ_top => idtac
    | typ_ltvar _ => idtac
    | typ_ftvar _  => idtac
    | typ_ann_ftvar _ _ => idtac
    | typ_arrow _ _ => idtac
    | typ_all _ _ _ => idtac
    | _ => fail
  end 
with filter_e e :=
  match e with
    | tm_lvar _ => idtac
    | tm_fvar _ => idtac
    | tm_ann_fvar _ _ => idtac
    | tm_abs _ _ _ => idtac
    | tm_app _ _ => idtac
    | tm_tabs _ _ _ => idtac
    | tm_tapp _ _ => idtac
    | _ => fail
  end 
with filter_b b :=
  match b with
    | _ ~: _ => idtac
    | _ ~<: _ => idtac
    | _ => fail
  end 
with filter_C c :=
  match c with
    | emptyset => idtac
    | emptyset ++ ?l => filter_C l
    | ?b :: _ => filter_b b
    | _ => fail
  end 
with filter_var_t C :=
  lazymatch C with
    | FV_tt => idtac
    | erased_t => fail
    | _ => idtac
  end
with filter_var_e C :=
  lazymatch C with
    | FV_te => idtac
    | FV_ee => idtac
    | erased_e => fail
    | _ => idtac
  end
with filter_var_b C :=
  match C with
    | dom_tc => idtac
    | dom_ec => idtac
    | FV_tc => idtac
    | _ => fail
  end
with filter_lsubst_e S :=
  match S with
    | lsubst_te => idtac
    | lsubst_ee => idtac
    | _ => fail
  end
with filter_fsubst_e S :=
  match S with
    | fsubst_te => idtac
    | fsubst_ee => idtac
    | _ => fail
  end
with filter_ann_fsubst_e S :=
  match S with
    | ann_fsubst_te => idtac
    | ann_fsubst_ee => idtac
    | _ => fail
  end in
  match goal with
    | H: ?X = ?X |- _ => clear H; simplifyTac tac
    | H: ?X <> ?X |- _ => try congruence
    | H: context [?X == ?Y] |- _   => 
      destruct (X == Y); [ try subst X | idtac ]; simplifyTac tac
    | |- context [?X == ?Y]        => 
      destruct (X == Y); [ try subst X | idtac ]; simplifyTac tac
    | H: context [?X ==_t ?Y] |- _ => 
      destruct (X ==_t Y); [ try subst X | idtac ]; simplifyTac tac
    | |- context [?X ==_t ?Y]      => 
      destruct (X ==_t Y); [ try subst X | idtac ]; simplifyTac tac
    | H: context [?X ==_T ?Y] |- _ => 
      destruct (X ==_T Y); [ try subst X | idtac ]; simplifyTac tac
    | |- context [?X ==_T ?Y]      => 
      destruct (X ==_T Y); [ try subst X | idtac ]; simplifyTac tac   
    | H: context [?X ===_t ?Y] |- _ => 
      destruct (X ===_t Y); [ try subst X | idtac ]; simplifyTac tac
    | |- context [?X ===_t ?Y]      => 
      destruct (X ===_t Y); [ try subst X | idtac ]; simplifyTac tac
    | H: context [?X ===_T ?Y] |- _ => 
      destruct (X ===_T Y); [ try subst X | idtac ]; simplifyTac tac
    | |- context [?X ===_T ?Y]      => 
      destruct (X ===_T Y); [ try subst X | idtac ]; simplifyTac tac   
    | H: context[ remove _ _ ?l ] |- _ =>
      filter_list l; simpl remove in H; simplifyTac tac
    | H : context[ ?C (?Gamma ++ ?Gamma') ] |- _ =>
      let filter_var_C := 
        lazymatch C with
          | dom_ec => rewrite (dom_ec_app_dist Gamma Gamma') in H
          | dom_tc => rewrite (dom_tc_app_dist Gamma Gamma') in H
          | FV_tc => rewrite (FV_tc_app_dist Gamma Gamma') in H
          | _ => fail end 
        in filter_var_C; simplifyTac tac
    | H : context[ ?C ?l ] |- _ =>
      filter_var_b C; filter_C l; simpl C in H; simplifyTac tac
    | H : context[ unroll_t ?l _ ] |- _ =>
      filter_C l; simpl unroll_t in H; simplifyTac tac
    | H : context[ unroll_e ?l _ ] |- _ =>
      filter_C l; simpl unroll_e in H; simplifyTac tac
    | H : context[ ?C ?t ] |- _ =>
      filter_var_t C; filter_t t; simpl C in H; simplifyTac tac
    | H : context[ ?C ?e ] |- _ =>
      filter_var_e C; filter_e e; simpl C in H; simplifyTac tac
    | H : context[ lsubst_tt _ _ ?t ] |- _ =>
      filter_t t; simpl lsubst_tt in H; simplifyTac tac
    | H : context[ ?S _ _ ?e ] |- _ =>
      filter_lsubst_e S; filter_e e; simpl S in H; simplifyTac tac
    | H : context[ fsubst_tt _ _ ?t ] |- _ =>
      filter_t t; simpl fsubst_tt in H; simplifyTac tac
    | H : context[ ann_fsubst_tt _ _ _ ?t ] |- _ =>
      filter_t t; simpl ann_fsubst_tt in H; simplifyTac tac
    | H : context[ ?S _ _ ?e ] |- _ =>
      filter_fsubst_e S; filter_e e; simpl S in H; simplifyTac tac
    | H : context[ ?S _ _ _ ?e ] |- _ =>
      filter_ann_fsubst_e S; filter_e e; simpl S in H; simplifyTac tac
    | |- context[ remove _ _ ?l ] =>
      filter_list l; simpl remove; simplifyTac tac
    | |- context[ ?C (?Gamma ++ ?Gamma') ] =>
      let filter_var_C := 
        lazymatch C with
          | dom_ec => rewrite (dom_ec_app_dist Gamma Gamma')
          | dom_tc => rewrite (dom_tc_app_dist Gamma Gamma')
          | FV_tc => rewrite (FV_tc_app_dist Gamma Gamma')
          | _ => fail end 
        in filter_var_C; simplifyTac tac
    | |- context[ ?C ?l ] =>
      filter_var_b C; filter_C l; simpl C; simplifyTac tac
    | |- context[ unroll_t ?l _ ] =>
      filter_C l; simpl unroll_t; simplifyTac tac
    | |- context[ unroll_e ?l _ ] =>
      filter_C l; simpl unroll_e; simplifyTac tac
    | |- context[ ?C ?t ] =>
      filter_var_t C; filter_t t; simpl C; simplifyTac tac
    | |- context[ ?C ?e ] =>
      filter_var_e C; filter_e e; simpl C; simplifyTac tac
    | |- context[ lsubst_tt _ _ ?t ] =>
      filter_t t; simpl lsubst_tt; simplifyTac tac
    | |- context[ ?S _ _ ?e ] =>
      filter_lsubst_e S; filter_e e; simpl S; simplifyTac tac
    | |- context[ fsubst_tt _ _ ?t ] =>
      filter_t t; simpl fsubst_tt; simplifyTac tac
    | |- context[ ann_fsubst_tt _ _ _ ?t ] =>
      filter_t t; simpl ann_fsubst_tt; simplifyTac tac    
    | |- context[ ?S _ _ ?e ] =>
      filter_fsubst_e S; filter_e e; simpl S; simplifyTac tac
    | |- context[ ?S _ _ _ ?e ] =>
      filter_ann_fsubst_e S; filter_e e; simpl S; simplifyTac tac
    | _ => tac
  end.

Tactic Notation "Simplify" "by" tactic(tac) := simplifyTac tac.

(** * Properties of System Fsub with contexts
 This section presents properties of System Fsub with contexts that we use
 in the equivalence proof. Each lemma has the same name as the corresponding
 lemma in [Fnamedcontext.v]. *)

Lemma lclosed_t_ftvar_dom_ctxt_typ : forall T Gamma I X,
  lclosed_t Gamma I T ->
  In X (FV_tt T) ->
  In X (dom_tc Gamma).
Proof.
  induction T; intros; inversion H; try discriminate;
    Simplify by Destruct In by (subst; eauto).
Qed.

Hint Resolve lclosed_t_ftvar_dom_ctxt_typ : incl_param.

Lemma ctxt_okay_app : forall Gamma Delta,
  ctxt_okay (Gamma ++ Delta)->
  ctxt_okay Delta.
Proof.
  induction Gamma; intros; eauto.
  rewrite <- list_cons_cons_move_app in H.
  inversion H; subst; eauto.
Qed.

Lemma lclosed_t_remove_ftvar_bind : forall T U X Gamma I,
  ~ In X (FV_tt T) ->
  lclosed_t (X ~<: U :: Gamma) I T ->
  lclosed_t Gamma I T.
Proof.
  induction T; intros; inversion H0; subst; 
    Simplify by Destruct notIn by eauto.
    econstructor; Destruct In by congruence.
Qed.

Lemma lclosed_t_ltvar_split : forall T Gamma A X U I0,
  ~ In X (FV_tt T) ->
  lclosed_t (X ~<: U :: Gamma) I0 ({A ~> X ^^} T) ->
  (exists I, (lclosed_t Gamma I T /\ remove eq_nat_dec A I = I0)).
Proof.
  induction T; intros ? ? ? ? ? H0 H.
  inversion H; exists (emptyset:list ltvar); simpl; auto.
  Simplify by eauto; inversion H; subst.
    exists (A :: emptyset); Simplify by eauto.
    exists (n :: emptyset); Simplify by eauto.
  Simplify by (Destruct notIn by eauto).
  inversion H; subst; clear H.
  exists (emptyset:list ltvar); simpl; split; eauto.
    econstructor; Simplify by (Destruct In by congruence).   
  Simplify by (Destruct notIn by eauto).
    inversion H.
  inversion H; subst.
  Simplify by (Destruct notIn by eauto).
  destruct (IHT1 _ _ _ _ _ H1 H5) as [I1' [Ha Ha']].
  destruct (IHT2 _ _ _ _ _ H2 H6) as [I2' [Hb Hb']].
  exists (I1' ++ I2'); split; auto.
    rewrite list_remove_app.
    rewrite Ha'; rewrite Hb'; eauto.
  Simplify by (Destruct notIn by eauto); inversion H; subst.
    destruct (IHT1 _ _ _ _ _ H1 H6) as [I1' [Ha Ha']].
    forwards Hb: (lclosed_t_remove_ftvar_bind H2 H8).
    exists (I1' ++ (remove eq_nat_dec A I2)); split; auto.
      rewrite list_remove_app; rewrite list_remove_repeat.
      rewrite Ha'; eauto.
    destruct (IHT1 _ _ _ _ _ H1 H6) as [I1' [Ha Ha']].
    destruct (IHT2 _ _ _ _ _ H2 H8) as [I2' [Hb Hb']].
    exists (I1' ++ (remove eq_nat_dec n I2')); split; auto.
      rewrite list_remove_app; rewrite list_remove_twice.
      rewrite Ha'; rewrite Hb'; eauto.
Qed.

Hint Resolve sym_eq list_remove_in: nochange.

Lemma subst_ftvar_nochange_t : forall T U X,
  ~ In X (FV_tt T) -> [X ~> U] T = T.
Proof.
  induction T; intros; Simplify by (Destruct notIn by eauto).
    f_equal; [apply IHT1 | apply IHT2]; Destruct notIn by auto.
    f_equal; [apply IHT1 | apply IHT2]; Destruct notIn by auto.
Qed.

Hint Resolve subst_ftvar_nochange_t : nochange.

Lemma subst_fvar_nochange_e : forall t t' x,
  ~ In x (FV_ee t) -> [x ::~> t'] t = t.
Proof.
  induction t; intros; Simplify by Destruct notIn by (f_equal; eauto). 
Qed.

Lemma subst_ftvar_nochange_e : forall t X S,
  ~ In X (FV_te t) -> ([ X :~> S ] t) = t.
Proof.
  induction t; intros; 
    Simplify by Destruct notIn by (f_equal; eauto with nochange).
Qed.

Hint Resolve subst_fvar_nochange_e subst_ftvar_nochange_e : nochange.

Lemma sub_ctxt_okay : forall T U Gamma,
  sub Gamma T U -> 
  ctxt_okay Gamma.
Proof.
   induction 1; intros; Simplify by (Destruct notIn by intuition).
Qed.

Lemma sub_lclosed_t : forall T U Gamma,
  sub Gamma T U -> 
  lclosed_t Gamma emptyset T /\ lclosed_t Gamma emptyset U .
Proof.
  induction 1; intros; Simplify by (Destruct notIn by intuition).
  econstructor; Destruct In by eauto.
  unsimpl (emptyset ++ emptyset:list ltvar); eauto.
  unsimpl (emptyset ++ emptyset:list ltvar); eauto.
  destruct (lclosed_t_ltvar_split _ _ H3 H6) as [I1 [Ha' Ha'']].
  replace (emptyset:list ltvar) with (emptyset ++ (remove eq_nat_dec A I1)); 
    eauto.
  destruct (lclosed_t_ltvar_split _ _ H4 H7) as [I2 [Ha' Ha'']].
  replace (emptyset:list ltvar) with (emptyset ++ (remove eq_nat_dec B I2)); 
    eauto.
Qed.

Lemma typing_ctxt_okay : forall Gamma t T,
  typing Gamma t T ->
  ctxt_okay Gamma.
Proof.
  induction 1; eauto.
    inversion IHtyping; eauto.
    inversion IHtyping; eauto.
Qed.

(** * Properties of System Fsub without contexts 
 This section presents properties of System Fsub without contexts that 
 we use in the equivalence proof. Almost every lemma has a different
 name from the corresponding lemma in [Fnamed.v]. We annotate the name 
 of the corresponding lemma as a comment for such lemmas. If there is
 no comment, it means that the lemma has the same name as the corresponding
 lemma. *)

(** [lclosed_t_ltvar_split] from [Fnamed.v] *)
Lemma ann_lclosed_t_ltvar_split : forall T A X U I0,
  ann_lclosed_t I0 ({A ~> X ^^ U} T) ->
  (exists I, (ann_lclosed_t I T /\ remove eq_nat_dec A I = I0)).
Proof.
  induction T; intros; auto.
  inversion H; exists (emptyset:list ltvar); Simplify by eauto.
  Simplify by eauto; inversion H; subst.
    exists (A :: emptyset); Simplify by eauto.
    exists (n :: emptyset); Simplify by eauto.
  Simplify by eauto; inversion H; subst.
  Simplify by eauto; inversion H; subst.
     exists (emptyset : list ltvar); Simplify by eauto.
  Simplify by eauto; inversion H; subst.
  destruct (IHT1 _ _ _ _ H3) as [I1' [Ha Ha']]. 
  destruct (IHT2 _ _ _ _ H4) as [I2' [Hb Hb']].
  exists (I1' ++ I2'); split; Simplify by eauto.
    rewrite list_remove_app; rewrite Ha'; rewrite Hb'; eauto.
  Simplify by eauto; inversion H; clear H.
    destruct (IHT1 _ _ _ _ H3) as [I1' [Ha Ha']]. 
    exists (I1' ++ (remove eq_nat_dec A I2)); split; auto.
      rewrite list_remove_app; rewrite list_remove_repeat.
      rewrite Ha'; eauto.
    destruct (IHT1 _ _ _ _ H3) as [I1' [Ha Ha']].   
    destruct (IHT2 _ _ _ _ H5) as [I2' [Hb Hb']].
    exists (I1' ++ (remove eq_nat_dec n I2')); split; eauto.      
      rewrite list_remove_app; rewrite list_remove_twice.
      rewrite Ha'; rewrite Hb'; eauto.
Qed.

(** [lclosed_t_subst_ltvar] from [Fnamed.v] *)
Lemma ann_lclosed_t_subst_ltvar : forall T U I A,
  ann_lclosed_t emptyset U ->
  ann_lclosed_t I T ->
  ann_lclosed_t (remove eq_nat_dec A I) ({A ~> U} T).
Proof.
  induction T; intros; inversion H0; subst; Simplify by eauto. 
  rewrite list_remove_app; eauto.
  rewrite list_remove_app; rewrite list_remove_repeat; eauto.
  rewrite list_remove_app; rewrite list_remove_twice; eauto.
Qed.

(** [lclosed_t_subst_ftvar] from [Fnamed.v] *)
Lemma ann_lclosed_t_subst_ftvar : forall T U U' X I,
  ann_lclosed_t I T ->
  ann_lclosed_t emptyset U ->
  ann_lclosed_t I ([(X, U') ~> U] T).
Proof.
  induction 1; intros; Simplify by eauto.
Qed.  

Hint Resolve ann_lclosed_t_subst_ftvar : subst_aux.

Lemma subst_ltvar_nochange_t : forall I T,
  ann_lclosed_t I T -> forall A U, ~ In A I -> {A ~> U} T = T.
Proof.
  induction 1; intros; 
    Simplify by Destruct notIn by (f_equal; eauto with nochange). 
Qed.

(** [subst_ftvar_nochange_t] from [Fnamed.v] *)
Lemma subst_ann_ftvar_nochange_t : forall T U S X, 
  ~ In X (ann_FV_tt T) -> [(X, U) ~> S] T = T. 
Proof.
  induction T; intros; 
    Simplify by Destruct notIn by (f_equal; eauto; congruence). 
Qed.  

Hint Resolve subst_ltvar_nochange_t subst_ann_ftvar_nochange_t : nochange.

Fixpoint synsize_t (T:typ) :=
  match T with
    | typ_top       => 0
    | typ_ltvar _   => 0
    | X ^^          => 0
    | X ^^ T        => S (synsize_t T)
    | T --> U       => S (synsize_t T + synsize_t U)
    | typ_all _ T U => S (synsize_t T + synsize_t U)
  end.

(** [lem_subst_ftvar_nochange_t_idemp] from [Fnamed.v] *)
Lemma lem_subst_ann_ftvar_nochange_t_idemp : forall T S,
  synsize_t S <= synsize_t T -> 
  forall X U, [(X, T) ~> U] S = S.
Proof.
  induction S; intros; Simplify by (f_equal; eauto with arith). 
    inversion e; subst; Simplify by firstorder using le_Sn_n.
Qed.

(** [subst_rename_ftvar_ltvar_t] from [Fnamed.v] *)
Lemma subst_rename_ann_ftvar_ltvar_t : forall T U S X Y,
  forall A,
    [(X,U) ~> Y^^U] ({A ~> S} T) = {A ~> [(X,U) ~> Y^^U] S} ([(X,U) ~> Y^^U] T).
Proof.
  induction T; intros; Simplify by (f_equal; eauto; congruence). 
Qed.

(** [subst_ftvar_ltvar_t] from [Fnamed.v] *)
Lemma subst_ann_ftvar_ltvar_t : forall T U S S' X,
  ann_lclosed_t emptyset S ->
  forall A,
    [(X,U) ~> S] ({A ~> S'} T) = {A ~> [(X,U) ~> S] S'} ([(X,U) ~> S] T).
Proof.
  induction T; intros; Simplify by (f_equal; eauto with nochange; congruence). 
Qed.

(** [subst_seq_ftvar_ltvar_t] from [Fnamed.v] *)
Lemma subst_seq_ann_ftvar_ltvar_t : forall T U S X,
  ~ In X (ann_FV_tt T) ->
  forall A,
    [(X,U) ~> S] ({A ~> (X^^U)} T) = {A ~> S} T.
Proof.
  induction T; intros; 
    Simplify by Destruct notIn by (f_equal; eauto with nochange; congruence). 
Qed.

(** [sub_lclosed_t] from [Fnamed.v] *)
Lemma ann_sub_ann_lclosed_t : forall T U, 
  ann_sub T U -> ann_lclosed_t emptyset T /\ ann_lclosed_t emptyset U.
Proof.
  induction 1; intros; firstorder.
  unsimpl (emptyset ++ emptyset:list ltvar); eauto.
  unsimpl (emptyset ++ emptyset:list ltvar); eauto.
  destruct (ann_lclosed_t_ltvar_split _ _ _ _ H7) as [I1 [Ha' Ha'']].
  replace (emptyset:list ltvar) with (emptyset ++ (remove eq_nat_dec A I1)); 
    eauto.
  destruct (ann_lclosed_t_ltvar_split _ _ _ _ H8) as [I2 [Ha' Ha'']].
  replace (emptyset:list ltvar) with (emptyset ++ (remove eq_nat_dec B I2)); 
    eauto.
Qed.

(** [lclosed_t_rename_ftvar] from [Fnamed.v] *)
Lemma ann_lclosed_t_rename_ftvar : forall T U X Y I,
  ann_lclosed_t I T ->
  ann_lclosed_t I ([(X, U) ~> Y ^^ U] T).
Proof.
  induction 1; intros; Simplify by eauto.
    inversion e; subst; eauto.
Qed.

Hint Resolve ann_lclosed_t_rename_ftvar : rename_aux.

(** [sub_rename_ftvar_aux] from [Fnamed.v] *)
Lemma ann_sub_rename_ftvar_aux : forall m n T U,
  n < m ->
  ann_subLH n T U ->
  forall X Y S,
      ann_subLH n ([(X,S) ~> Y^^S] T) 
                  ([(X,S) ~> Y^^S] U).
Proof.
  induction m.
  firstorder using lt_n_O.
  destruct 2; intros; Simplify by eauto with rename_aux. 
  inversion e; subst; eauto.
  inversion e; subst.
    rewrite <- (lem_subst_ann_ftvar_nochange_t_idemp S S) at 1; 
      eauto with arith.
  eauto with arith.
  econstructor; eauto with arith.
  set (L := ann_FV_tt ([(X0, S)~> Y ^^ S]T2) ++
           ann_FV_tt ([(X0, S)~> Y ^^ S]U2) ++ 
           ann_FV_tt ([(X0, S)~> Y ^^ S]T1) ++
           ann_FV_tt ([(X0, S)~> Y ^^ S]U1) ++
           (X0 :: nil)).
  destruct (pick_fresh L) as [Z Hfresh'].
  unfold L in Hfresh'.
  apply ann_subLH_all with Z; Destruct notIn by eauto with arith.
    replace (Z ^^ ([ (X0, S)~> Y ^^ S] U1)) 
      with ([ (X0, S)~> Y ^^ S] (Z ^^ U1)) by Simplify by congruence.
    repeat (rewrite <- (subst_rename_ann_ftvar_ltvar_t) by auto).
    apply IHm; eauto with arith.
      rewrite <- subst_seq_ann_ftvar_ltvar_t 
        with (T := T2) (X := X) (U := U1) by eauto.
      rewrite <- subst_seq_ann_ftvar_ltvar_t 
        with (T := U2) (X := X) (U := U1) by eauto.
      eauto with arith. 
Qed.

Hint Resolve ann_sub_rename_ftvar_aux : rename_aux.

(** [sub_rename_ftvar] from [Fnamed.v] *)
Lemma ann_sub_rename_ftvar : forall T U,
  ann_sub T U ->
  forall X Y S,
      ann_sub ([(X,S) ~> Y^^S] T)
              ([(X,S) ~> Y^^S] U).
Proof.
  intros.
  destruct (ann_sub_subLH H) as [n ?].
  eauto with arith rename_aux.
Qed.

Hint Resolve ann_sub_rename_ftvar : rename_aux.

(** This lemma does not appear in [Fnamed.v], but is easily provable. *)
Lemma ann_subLH_ltvar_subst_rename_ftvar : forall T U,
  forall X, ~ In X (ann_FV_tt T) -> ~ In X (ann_FV_tt U) ->
  forall S A B Y n, 
  ann_subLH n ({A ~> X ^^ S} T) ({B ~> X ^^ S} U) ->
  ann_subLH n ({A ~> Y ^^ S} T) ({B ~> Y ^^ S} U).
Proof.
  intros.
  rewrite <- subst_seq_ann_ftvar_ltvar_t 
    with (A := A) (X := X) (U := S) by eauto.
  rewrite <- subst_seq_ann_ftvar_ltvar_t 
    with (A := B) (X := X) (U := S) by eauto.
  eauto with rename_aux.
Qed. 

Hint Resolve ann_subLH_ltvar_subst_rename_ftvar : rename_aux.

(** [sub_ltvar_subst_rename_ftvar] from [Fnamed.v] *)
Lemma ann_sub_ltvar_subst_rename_ftvar : forall T U,
  forall X, ~ In X (ann_FV_tt T) -> ~ In X (ann_FV_tt U) ->
  forall S A B Y, 
  ann_sub ({A ~> X ^^ S} T) ({B ~> X ^^ S} U) ->
  ann_sub ({A ~> Y ^^ S} T) ({B ~> Y ^^ S} U).
Proof.
  intros.
  destruct (ann_sub_subLH H1) as [n ?].
  eauto with rename_aux.
Qed. 

(** [sub_transitivity_on] from [Fnamed.v] *)
Definition ann_sub_transitivity_on T := forall U S,
  ann_sub U T -> ann_sub T S -> ann_sub U S.

Fixpoint size_t (T : typ) : nat :=
  match T with
    | typ_top         => 0
    | typ_ltvar _     => 0
    | typ_ftvar _     => 0
    | typ_ann_ftvar _ _ => 0
    | typ_arrow T1 T2 => S (size_t T1 + size_t T2)
    | typ_all _ T1 T2 => S (size_t T1 + size_t T2)
  end.

Lemma size_t_nochange_ltvar : forall T A X U,
  size_t ({A ~> X ^^ U} T) = size_t T.
Proof.
  induction T; intros; Simplify by eauto.
Qed.

(** [sub_narrowing_aux] from [Fnamed.v] *)
Lemma ann_sub_narrowing_aux : forall m n T U,
  n < m ->
  ann_subLH n T U ->
  forall S S',
    ann_sub_transitivity_on S ->
    ann_sub S' S ->
    forall X,
      ann_sub ([(X, S) ~> X ^^ S'] T) ([(X, S) ~> X ^^ S'] U).
Proof.
  induction m.
  firstorder using lt_n_O.
  destruct 2; intros.
  destruct (ann_sub_ann_lclosed_t H2) as [? ?]; eauto with subst_aux. 
  destruct (ann_sub_ann_lclosed_t H2) as [? ?].
  Simplify by eauto with subst_aux.
  Simplify by eauto with arith.
    inversion e; subst.
    apply H1; eauto.
    erewrite <- lem_subst_ann_ftvar_nochange_t_idemp at 1; eauto with arith.
  Simplify by idtac.
  econstructor; eauto with arith.
  set (L := X0 :: ann_FV_tt ([ (X0, S)~> X0 ^^ S'] T2) ++
            ann_FV_tt ([ (X0, S)~> X0 ^^ S'] U2) ++ 
            ann_FV_tt ([ (X0, S)~> X0 ^^ S'] T1) ++
            ann_FV_tt ([ (X0, S)~> X0 ^^ S'] U1)).
  destruct (pick_fresh L) as [Y HfreshL].
  unfold L in HfreshL.
  Simplify by (Destruct notIn by eauto).
  constructor 5 with Y; eauto with arith.
    destruct (ann_sub_ann_lclosed_t H5) as [? ?].
    destruct (ann_sub_ann_lclosed_t (ann_subLH_sub H0_)) as [? ?].
    replace (Y ^^ ([ (X0, S)~> X0 ^^ S'] U1)) 
      with ([ (X0, S)~> X0 ^^ S' ] (Y ^^ U1)) by Simplify by congruence.
    repeat rewrite <- subst_ann_ftvar_ltvar_t by eauto.
    forwards Hdelta : (ann_sub_rename_ftvar_aux (lt_n_Sn n2) H0_0 X Y U1).
    eapply IHm with n2; eauto with arith.
    rewrite <- subst_seq_ann_ftvar_ltvar_t with (T := T2) (X := X) (U := U1);
      eauto.
    rewrite <- subst_seq_ann_ftvar_ltvar_t with (T := U2) (X := X) (U := U1);
      eauto.
Qed.

(** [sub_narrowing] from [Fnamed.v] *)
Lemma ann_sub_narrowing : forall T U,
  ann_sub T U ->
  forall S S',
    ann_sub_transitivity_on S ->
    ann_sub S' S ->
    forall X,
      ann_sub ([(X, S) ~> X ^^ S'] T)
          ([(X, S) ~> X ^^ S'] U).
Proof.
  intros.
  destruct (ann_sub_subLH H) as [n ?].
  eauto using ann_sub_narrowing_aux.
Qed.

(** [sub_trans_ftvar_aux] from [Fnamed.v] *)
Lemma ann_sub_trans_ftvar_aux : forall A S U X,
  ann_sub A S ->
  S = (X ^^ U) ->
  forall S', ann_sub S S' -> ann_sub A S'.
Proof.
  induction 1; intros; try discriminate; eauto.
Qed.

(** [sub_trans_fun_aux] from [Fnamed.v] *)
Lemma ann_sub_trans_fun_aux : forall T U U1 U2 S,
  ann_sub_transitivity_on U1 ->
  ann_sub_transitivity_on U2 ->
  ann_sub T U ->
  ann_sub U S ->
  U = U1 --> U2 ->
  ann_sub T S.
Proof.
  induction 3; intros; try discriminate; Simplify by eauto.
  inversion H2; subst; clear H2.
    destruct (ann_sub_ann_lclosed_t H1_) as [? ?].
    destruct (ann_sub_ann_lclosed_t H1_0) as [? ?].
    inversion H1; subst; econstructor; eauto.
      unsimpl (emptyset ++ emptyset:list ltvar); eauto.
Qed.

(** [sub_trans_forall_aux] from [Fnamed.v] *)
Lemma ann_sub_trans_forall_aux : forall T U U1 U2 S A,
  (forall S, size_t S < size_t U -> ann_sub_transitivity_on S) ->
  ann_sub T U ->
  U = typ_all A U1 U2 ->
  ann_sub U S ->
  ann_sub T S.
Proof.
  intros until 2. 
  induction H0; intros; try discriminate; eauto.
  clear IHann_sub1 IHann_sub2.
  inversion H4; subst; clear H4.
  inversion H5 as [ B | | | | ? ? S1 S2 Y]; subst.
  econstructor.
    destruct (ann_sub_ann_lclosed_t H0_0) as [H' _].
    destruct (ann_sub_ann_lclosed_t H0_) as  [_ H''].
    destruct (ann_lclosed_t_ltvar_split _ _ _ _ H') as [I [Ha Hb]].
    replace (emptyset :list ltvar) 
      with (emptyset ++ (remove eq_nat_dec A0 I)) by Simplify by congruence.
    econstructor; eauto.
  set (L := ann_FV_tt T2 ++ ann_FV_tt U2 ++ 
            ann_FV_tt S2 ++ ann_FV_tt T1 ++ 
            ann_FV_tt S1).
  destruct (pick_fresh L) as [Z Hfresh].
  unfold L in Hfresh.
  assert (ann_sub ({A0 ~> Z^^U1}T2) ({A ~> Z^^U1}U2)).
    eapply ann_sub_ltvar_subst_rename_ftvar; eauto.
  assert (ann_sub ({A0 ~> Z^^S1}T2) ({A ~> Z^^S1}U2)).
    Destruct notIn by idtac.
    rewrite <- (subst_seq_ann_ftvar_ltvar_t T2 U1 (Z^^S1) Z) by eauto.
    rewrite <- (subst_seq_ann_ftvar_ltvar_t U2 U1 (Z^^S1) Z) by eauto.
    eapply ann_sub_narrowing; Simplify by eauto with arith.
  assert (ann_sub ({A ~> Z^^S1} U2) ({B ~> Z^^S1}S2)).
    eapply ann_sub_ltvar_subst_rename_ftvar; eauto.
  assert (ann_sub_transitivity_on ({A ~> Z^^S1} U2)).
    apply H; Simplify by idtac.
    rewrite size_t_nochange_ltvar; eauto with arith.
  assert (ann_sub ({A0 ~> Z^^S1} T2) ({B ~> Z^^S1} S2)) by auto.
  assert (ann_sub_transitivity_on U1).
    apply H; Simplify by eauto with arith.
  assert (ann_sub S1 T1) by eauto.
  Destruct notIn by eauto.
Qed.

(** [sub_transitivity_aux] from [Fnamed.v] *)
Lemma ann_sub_transitivity_aux : forall n T,
  size_t T < n -> ann_sub_transitivity_on T.
Proof.
  induction n; intros.
  firstorder using lt_n_O. 
  destruct T; unfold ann_sub_transitivity_on; intros.
  inversion H1; assumption.
  inversion H1; inversion H2; eauto.
  inversion H1; inversion H2.
  eauto using ann_sub_trans_ftvar_aux.
  Simplify by idtac.
  assert (size_t T1 < n) by eauto with arith.
  assert (size_t T2 < n) by eauto with arith.
  eauto using ann_sub_trans_fun_aux.
  Simplify by idtac.
  assert (forall S, 
    size_t S < size_t (typ_all n0 T1 T2) -> 
    ann_sub_transitivity_on S) by eauto with arith.
  eauto using ann_sub_trans_forall_aux.
Qed.

(** [sub_transitivity] from [Fnamed.v] *)
Lemma ann_sub_transitivity : forall T U S, 
  ann_sub T U -> 
  ann_sub U S -> 
  ann_sub T S.
Proof.
  intros.
  forwards Ha : ann_sub_transitivity_aux (Datatypes.S (size_t U)) U; 
  eauto with arith.
Qed.

(** [sub_reflexivity_aux] from [Fnamed.v] *)
Lemma ann_sub_reflexivity_aux : forall n T,
  size_t T < n -> ann_lclosed_t emptyset T -> ann_sub T T.
Proof.
  induction n. 
  intros; firstorder using lt_n_O.
  destruct T; intros H' H; inversion H; Simplify by eauto.
  assert (size_t T1 < n) by eauto with arith.  
  assert (size_t T2 < n) by eauto with arith.
  assert (I1 = emptyset) by firstorder using app_eq_nil.
  assert (I2 = emptyset) by firstorder using app_eq_nil.
  subst; eauto.
  set (L := ann_FV_tt T1 ++ ann_FV_tt T2).
  destruct (pick_fresh L) as [X Hfresh].
  unfold L in Hfresh.
  assert (I1 = emptyset) by firstorder using app_eq_nil; subst I1.
  assert (remove eq_nat_dec A I2 = emptyset) by firstorder using app_eq_nil.
  constructor 5 with (X := X); Destruct notIn by eauto.
    apply IHn; eauto with arith.     
    apply IHn; subst.
      rewrite size_t_nochange_ltvar; eauto with arith.
      replace (emptyset : list ltvar) with (remove eq_nat_dec n0 I2).
      eauto using ann_lclosed_t_subst_ltvar.
Qed.

(** This lemma also does not appear in [Fnamed.v], but it is easily provable. 
*)
Lemma ann_sub_reflexivity : forall T,
  ann_lclosed_t emptyset T -> 
  ann_sub T T.
Proof.
  intros. 
  eapply ann_sub_reflexivity_aux with (n := S (size_t T)); eauto with arith.
Qed.

Hint Resolve ann_sub_transitivity ann_sub_reflexivity : equiv_aux.

(** [subst_ftvar_nochange_e] from [Fnamed.v] *)
Lemma subst_ann_ftvar_nochange_e : forall t X T U, 
  ~ In X (ann_FV_te t) -> ([ ( X , T ) :~> U ] t) = t.
Proof.
  induction t; intros; 
    Simplify by Destruct notIn by (f_equal; eauto with nochange). 
Qed.

Hint Resolve subst_ann_ftvar_nochange_e : nochange.

Lemma subst_lvar_lvar_e : forall t a x T b y U,
  a <> b -> 
{b ::~> y ** U}({a ::~> x ** T} t) = {a ::~> x ** T}({b ::~> y ** U} t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto).
Qed.

Lemma subst_ltvar_lvar_e : forall t A X a x T U ,
  {A :~> X ^^ T} ({a ::~> x ** U} t) = {a ::~> x ** U} ({A :~> X^^T} t).
Proof.
  induction t; intros; Simplify by congruence.
Qed.

(** [subst_ftvar_lvar_e] from [Fnamed.v] *)
Lemma subst_ann_ftvar_lvar_e : forall t u X T U a,
  [(X, T) :~> U]({a ::~> u} t) = {a ::~> ([(X, T) :~> U] u)}([ (X, T) :~> U] t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto).
Qed.

(** [subst_rename_ftvar_ltvar_e] from [Fnamed.v] *)
Lemma subst_rename_ann_ftvar_ltvar_e : forall t A X Y T U,
  [(X, T) :~> (Y^^T)] ({A :~> U} t) = 
    {A :~> [(X, T)~>(Y^^T)] U} ([(X, T) :~> (Y^^T)] t).
Proof.
  induction t; intros; 
    Simplify by 
    (f_equal; eauto using subst_rename_ann_ftvar_ltvar_t).
Qed.

(** [subst_seq_ftvar_ltvar_e] from [Fnamed.v] *)
Lemma subst_seq_ann_ftvar_ltvar_e : forall t T U X,
  ~ In X (ann_FV_te t) ->
  forall A,
    [(X,T) :~> U] ({A :~> (X^^T)} t) = {A :~> U} t.
Proof.
  induction t; intros; 
    Simplify by 
    Destruct notIn by 
    (f_equal; eauto using subst_seq_ann_ftvar_ltvar_t with nochange).
Qed.

(** [FV_te_nochange_lvar] from [Fnamed.v] *)
Lemma ann_FV_te_nochange_lvar : forall t a x y T,
  ann_FV_te ({a ::~> x ** T} t) = ann_FV_te ({a ::~> y ** T} t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto).
Qed.

(** [FV_ee_nochange_ftvar] from [Fnamed.v] *)
Lemma ann_FV_ee_nochange_ftvar : forall t X T Y U,
  ann_FV_ee ([(X, T) :~> Y^^U] t) = ann_FV_ee t.
Proof.
  induction t; intros; Simplify by eauto.
    rewrite IHt1; rewrite IHt2; eauto.
Qed.

Hint Resolve ann_FV_te_nochange_lvar ann_FV_ee_nochange_ftvar : nochange.

Fixpoint size_e (t : tm) : nat :=
  match t with
    | tm_lvar _       => 0
    | tm_fvar _       => 0
    | tm_ann_fvar _ _ => 0
    | tm_abs _ _ t    => S (size_e t)
    | tm_app t1 t2    => S (size_e t1 + size_e t2)
    | tm_tabs _ _ t   => S (size_e t)
    | tm_tapp t _     => S (size_e t)
  end.

Lemma size_e_nochange_lvar : forall a x T t,
  size_e ({a ::~> x ** T} t) = size_e t.
Proof.
  induction t; Simplify by eauto. 
Qed.

Lemma size_e_nochange_ltvar : forall A X T t,
  size_e ({ A :~> X ^^ T} t) = size_e t.
Proof.
  induction t; Simplify by eauto.
Qed.

Hint Resolve size_e_nochange_lvar size_e_nochange_ltvar : nochange.

(** [typingLH_subst_lvar_rename_fvar] from [Fnamed.v] *)
Lemma ann_typingLH_subst_lvar_rename_fvar_aux : forall k t u a x y T U n,
  n + size_e t < k -> 
  ann_typingLH n u T -> 
  u = {a ::~> x ** U} t -> 
  ann_typingLH n ({a ::~> y ** U} t) T.
Proof.
  induction k.
  firstorder using lt_n_O.
  induction 2; intro; Simplify by try congruence.
  destruct t; Simplify by try discriminate; inversion H1; subst; eauto.
  destruct t; Simplify by try discriminate; inversion H3; subst; eauto.
    set (L := ann_FV_ee ({a ::~> y ** U} t1)).
    destruct (pick_fresh L) as [x' Hfresh].
    unfold L in Hfresh.
    constructor 2 with (x := x'); auto.
    assert ( k0 + size_e ({a ::~> y ** U}t1) < k ).
      rewrite size_e_nochange_lvar; eauto with arith.
    assert ( k0 + size_e ({n ::~> x0 ** t}t1) < k ).
      rewrite size_e_nochange_lvar; eauto with arith.
    eapply IHk with (u := {n ::~> x0 ** t}({ a ::~> y ** U } t1)); eauto.
    rewrite subst_lvar_lvar_e by congruence.
    eapply IHk with (u := {a ::~> x ** U}({ n ::~> x0 ** t } t1)); eauto.
    rewrite subst_lvar_lvar_e by congruence; eauto.
  destruct t; Simplify by try discriminate; inversion H0; subst.
  simpl in H; rewrite <- plus_Snm_nSm in H. 
  assert (k1 < S (max k1 k2)) by eauto with arith.
  assert (k2 < S (max k1 k2)) by eauto with arith.
  assert (size_e t1 <= size_e t1 + size_e t2) by eauto with arith.
  assert (size_e t2 <= size_e t1 + size_e t2) by eauto with arith.
  assert (k1 + size_e t1 < S (max k1 k2) + (size_e t1 + size_e t2)) by
    auto using plus_lt_le_compat with arith.
  assert (k2 + size_e t2 < S (max k1 k2) + (size_e t1 + size_e t2)) by
    auto using plus_lt_le_compat with arith.
  assert ( k1 + size_e t1 < k ) by eauto with arith.
  assert ( k2 + size_e t2 < k ) by eauto with arith.
  constructor 3 with (T := T); eauto.
  destruct t; Simplify by try discriminate.
    inversion H3; subst.
    constructor 4 with (X := X); Destruct notIn by eauto.
      erewrite ann_FV_te_nochange_lvar; eassumption.
      simpl in H; rewrite <- plus_Snm_nSm in H.
      assert ( k0 + size_e ({n :~> X ^^ t}t1) < k ).
        rewrite size_e_nochange_ltvar; eauto with arith.
      rewrite subst_ltvar_lvar_e.
      eapply IHk with (u := {a ::~> x** U}({n:~> X ^^ t} t1)); eauto.
      rewrite <- subst_ltvar_lvar_e; eauto.
  destruct t; Simplify by try discriminate.
    inversion H2; subst; clear H2.
    assert (k0 + size_e t < k) by eauto with arith; eauto.
  eauto.
Qed.

(** This lemma does not appear in [Fnamed.v]. Note that this lemma is
 a corollary of Lemma [ann_typingLH_subst_lvar_rename_fvar_aux]. *)
Lemma ann_typingLH_subst_lvar_rename_fvar : forall n t a x y T U,
  ann_typingLH n ({a ::~> x ** U} t) T -> 
  ann_typingLH n ({a ::~> y ** U} t) T.
Proof.
  intros.
  eauto using ann_typingLH_subst_lvar_rename_fvar_aux.
Qed.

(** [typing_rename_ftvar_aux] from [Fnamed.v] *)
Lemma ann_typingLH_rename_ftvar : forall m n t T,
  n < m -> 
  ann_typingLH n t T ->  
  forall X Y U,
  ann_typingLH n ([(X, U) :~> Y ^^ U] t) ([(X, U) ~> Y ^^ U] T).
Proof.
  induction m.
  firstorder using lt_n_O. 
  induction 2; intros; Simplify by eauto with rename_aux. 
  constructor 2 with (x := x); eauto with rename_aux.
    rewrite ann_FV_ee_nochange_ftvar; eauto.
    unsimpl ([ (X, U0) :~> Y ^^ U0](x ** T)).
    erewrite <- subst_ann_ftvar_lvar_e; eauto with arith.
  econstructor; eauto with arith.
    unsimpl ([(X, U0)~> Y^^U0](T --> U)); eauto with arith.
  set (L := X0 :: ann_FV_te t ++ 
                  ann_FV_te ([(X0, U0):~>Y^^U0] t) ++ 
                  ann_FV_tt U ++ 
                  ann_FV_tt ([(X0, U0)~>Y^^U0] U)).
  destruct (pick_fresh L) as [Z HfreshL].
  unfold L in HfreshL.
  constructor 4 with (X := Z); Destruct notIn by eauto with rename_aux. 
  repeat replace (Z ^^ ([ (X0, U0)~> Y ^^ U0]T))
    with ([ (X0, U0) ~> Y ^^ U0 ] (Z ^^ T )) by Simplify by congruence.
  rewrite <- subst_rename_ann_ftvar_ltvar_t.
  rewrite <- subst_rename_ann_ftvar_ltvar_e.
  eapply IHm; eauto with arith.
  erewrite <- subst_seq_ann_ftvar_ltvar_t with (X := X) by eauto.
  erewrite <- subst_seq_ann_ftvar_ltvar_e with (X := X) by eauto.
  eapply IHm; eauto with arith.
  rewrite subst_rename_ann_ftvar_ltvar_t.
  econstructor 5 with (U := [(X, U0) ~> Y ^^ U0] U); eauto with rename_aux.  
    unsimpl ([ (X, U0) ~> Y ^^ U0 ] (typ_all A U S)); eauto with arith.
Qed.

(** [typingLH_subst_ltvar_rename_ftvar] from [Fnamed.v] *)
Lemma ann_typingLH_subst_ltvar_rename_ftvar : forall m t T,
  forall X, ~ In X (ann_FV_te t) -> ~ In X (ann_FV_tt T) ->
  forall U Y A B ,
  ann_typingLH m ({A :~> X ^^ U} t) ({B ~> X ^^ U} T) ->
  ann_typingLH m ({A :~> Y ^^ U} t) ({B ~> Y ^^ U} T).
Proof.
  intros.
  erewrite <- subst_seq_ann_ftvar_ltvar_t with (X := X) by eauto.
  erewrite <- subst_seq_ann_ftvar_ltvar_e with (X := X) by eauto.
  eauto using ann_typingLH_rename_ftvar with arith.
Qed.

(** [sub_subst_ftvar_aux] from [Fnamed.v] *)
Lemma ann_sub_subst_ftvar_aux : forall m n T U,
  n < m -> 
  ann_subLH n T U -> 
  forall X S S', 
    ann_sub S' S ->
    ann_sub ([(X, S) ~> S'] T) ([(X, S) ~> S'] U).
Proof.
  induction m.
  firstorder using lt_n_O.
  destruct 2; intros.
  Simplify by firstorder using ann_sub_ann_lclosed_t with subst_aux.
  destruct (ann_sub_ann_lclosed_t H1) as [? ?].
  Simplify by eauto using ann_sub_reflexivity with subst_aux arith.
  assert (n < m) by eauto with arith.
  Simplify by eauto.
    inversion e; subst; clear e.
    forwards IHsub' : IHm H2 H0 H1.
    erewrite lem_subst_ann_ftvar_nochange_t_idemp in IHsub'; 
    eauto using ann_sub_transitivity.
  assert (n1 < m) by eauto with arith.
  assert (n2 < m) by eauto with arith.
  Simplify by eauto.
  set (L := X0 :: 
    ann_FV_tt ([(X0, S)~> S'] T2) ++ ann_FV_tt ([(X0, S) ~> S'] U2) ++
    ann_FV_tt ([(X0, S)~> S'] T1) ++ ann_FV_tt ([(X0, S)~> S'] U1)).
  destruct (pick_fresh L) as [Y Hfresh'].
  unfold L in Hfresh'.
  Simplify by eauto.
  constructor 5 with (X := Y); Destruct notIn by eauto with arith.
  assert (n2 < m) by eauto with arith.
  assert (n2 < Datatypes.S n2) by eauto with arith.
  destruct (ann_sub_ann_lclosed_t H4) as [? ?].
  forwards Ha : (ann_sub_rename_ftvar_aux H9 H0_0 X Y U1).
  repeat rewrite subst_seq_ann_ftvar_ltvar_t in Ha by assumption.
  forwards Hb : (IHm n2 _ _ H9 Ha X0 _ _ H4).
  repeat rewrite subst_ann_ftvar_ltvar_t in Hb by assumption.
  Simplify by eauto.
    inversion e; congruence.
Qed.

(** [sub_subst_ftvar] from [Fnamed.v] *)
Lemma ann_sub_subst_ftvar : forall T U,
  ann_sub T U -> 
  forall X S S', 
    ann_sub S' S -> 
    ann_sub ([(X,S) ~> S'] T) ([(X,S) ~> S'] U).
Proof.
  intros.
  destruct (ann_sub_subLH H) as [n H']; eauto using ann_sub_subst_ftvar_aux.
Qed.

(** * Preliminaries 
 ** Properties of substitution 
 We use [unroll_t] and [unroll_e] to show the equivalence, and these functions
 replace erased parameters with annotated parameters. Note that such 
 substitution does not appear when we deal with either [typing] or [ann_typing].
 
 This section presents properties of such substitution that appears only when
 we use [unroll_t] and [unroll_e]. *)

(** We may swap variable and parameter substitution. *)
Lemma swap_fsubst_tt_lsubst_tt : forall T A X U U',
  [X ~> X ^^ U'] ({A ~> U} T) = 
  {A ~> [X ~> X ^^ U'] U} ([X ~> X ^^ U'] T).
Proof.
  induction T; intros; Simplify by (f_equal; eauto). 
Qed.

Lemma swap_fsubst_te_lsubst_te : forall t X Y A T U,
  [Y :~> Y ^^ U] ({A :~> X ^^ T} t) = 
  {A :~> X ^^ T} ([Y :~> Y ^^ U] t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto);
    rewrite swap_fsubst_tt_lsubst_tt; eauto. 
Qed.

Lemma swap_fsubst_ee_lsubst_ee : forall t x x' T T' a,
  [x' ::~> x' ** T'] ({a ::~> x ** T} t) = 
  {a ::~> x ** T} ([x' ::~> x' ** T'] t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto). 
Qed.

Lemma swap_fsubst_ee_lsubst_te : forall t x X A T T',
  [x ::~> x ** T'] ({A :~> X ^^ T} t) = 
  {A :~> X ^^ T} ([x ::~> x ** T'] t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto). 
Qed.

Lemma swap_fsubst_te_lsubst_ee : forall t x X T T' a,
  [X :~> X ^^ T'] ({a ::~> x ** T} t) = 
  {a ::~> x ** T} ([X :~> X ^^ T'] t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto). 
Qed.

Hint Rewrite swap_fsubst_tt_lsubst_tt : swap_subst.
Hint Rewrite swap_fsubst_te_lsubst_te swap_fsubst_ee_lsubst_ee : swap_subst. 
Hint Rewrite swap_fsubst_te_lsubst_ee swap_fsubst_ee_lsubst_te : swap_subst.

(** We may replace a type variable with a fresh erased type parameter, 
 and then replace the erased type parameter with a given annotated type
 parameter instead of directly replacing the type variable with the 
 annotated type parameter . *)
Lemma fsubst_tt_lsubst_tt_seq : forall T U A X,
  ~ In X (FV_tt T) ->
  [ X ~> (X ^^ U) ] ({A ~> X ^^} T) = {A ~> X ^^ U} T.
Proof.
  induction T; intros; 
    Simplify by 
    Destruct notIn by (f_equal; eauto with nochange). 
Qed.

Lemma fsubst_te_lsubst_te_seq : forall t A X T,
  ~ In X (FV_te t) ->
  [ X :~> (X ^^ T) ] ({A :~> X ^^} t) = {A :~> X ^^ T} t.
Proof.
  induction t; intros;
    Simplify by 
    Destruct notIn by
    (f_equal; eauto using fsubst_tt_lsubst_tt_seq with nochange).
Qed.

Lemma fsubst_ee_lsubst_ee_seq : forall t a x T,
  ~ In x (FV_ee t) ->
  [ x ::~> x ** T ] ({ a ::~> x **} t) = { a ::~> x ** T } t.
Proof.
  induction t; intros; 
    Simplify by 
    Destruct notIn by 
    (f_equal; eauto with nochange). 
Qed.

(** ** Properties of [erased_t] and [erased_e] *)

(** [erased_t] and [erased_e] are stable under substitution. *)
Lemma erased_t_lsubst_tt_safe : forall T A U,
  erased_t ({A ~> U} T) -> erased_t T.
Proof.
  induction T; intros; Simplify by eauto; inversion H; eauto.
Qed.

Lemma erased_t_lsubst_tt_safe_inv : forall T U A,
  erased_t T -> erased_t U -> erased_t ({A ~> U} T).
Proof.
  induction T; intros; Simplify by eauto; inversion H; eauto. 
Qed.

Hint Resolve erased_t_lsubst_tt_safe     : safe_aux.
Hint Resolve erased_t_lsubst_tt_safe_inv : safe_inv_aux.

Lemma erased_e_lsubst_te_safe : forall t A X,
  erased_e ({A :~> X ^^} t) -> 
  erased_e t.
Proof.
  induction t; intros;
    Simplify by (inversion H; subst; eauto with safe_aux).
Qed.

Lemma erased_e_lsubst_te_safe_inv : forall t A T,
  erased_e t -> 
  erased_t T -> 
  erased_e ({A :~> T} t).
Proof.
  induction t; intros; 
    Simplify by (inversion H; subst; eauto with safe_inv_aux). 
Qed.

Hint Resolve erased_e_lsubst_te_safe     : safe_aux.
Hint Resolve erased_e_lsubst_te_safe_inv : safe_inv_aux.

Lemma erased_e_lsubst_ee_safe : forall t a u,
  erased_e ({a ::~> u} t) -> erased_e t.
Proof.
  induction t; intros; Simplify by (inversion H; subst; eauto). 
Qed.

Lemma erased_e_lsubst_ee_safe_inv : forall t a u,
  erased_e t -> erased_e u -> erased_e ({a ::~> u} t).
Proof.
  induction t; intros; Simplify by (inversion H; eauto).
Qed.

Hint Resolve erased_e_lsubst_ee_safe     : safe_aux.
Hint Resolve erased_e_lsubst_ee_safe_inv : safe_inv_aux.

(** An erased type (or term) does not include annotated parameters *)
Lemma erased_t_implies_not_in_ann_FV_tt : forall X T,
  erased_t T -> ~ In X (ann_FV_tt T).
Proof.
  induction T; intros Herased; inversion Herased; subst;
    Simplify by (Destruct notIn by eauto).
Qed.

Lemma erased_e_implies_not_in_ann_FV_te : forall X t,
  erased_e t -> ~ In X (ann_FV_te t).
Proof.
  induction t; intros Herased; inversion Herased; subst; 
    Simplify by 
    Destruct notIn by 
    eauto using erased_t_implies_not_in_ann_FV_tt.
Qed.

Lemma erased_e_implies_not_in_ann_FV_ee : forall x t,
  erased_e t -> ~ In x (ann_FV_ee t).
Proof.
  induction t; intros Herased; inversion Herased; subst; 
    Simplify by 
    Destruct notIn by 
    eauto. 
Qed.

Hint Resolve erased_t_implies_not_in_ann_FV_tt : incl_param.
Hint Resolve erased_e_implies_not_in_ann_FV_te : incl_param.
Hint Resolve erased_e_implies_not_in_ann_FV_ee : incl_param.

(** ** Basic properties of [lclosed_t], [sub], and [typing]. *)

(** [lclosed_t] deals with erased types only. *)
Lemma lclosed_t_implies_erased_t : forall Gamma I T,
  lclosed_t Gamma I T -> erased_t T.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve lclosed_t_implies_erased_t : erased_aux.

(** [sub] deals with erased types only. *)
Lemma sub_implies_erased_t : forall Gamma A B,
  sub Gamma A B -> erased_t A /\ erased_t B.
Proof.
  induction 1; Simplify by firstorder using erased_t_lsubst_tt_safe.
   eauto with erased_aux.
Qed.

Hint Resolve sub_implies_erased_t : erased_aux.

(** [typing] deals with erased types and terms only. *)
Lemma typing_implies_erased_t : forall T Gamma t,
  typing Gamma t T -> 
  erased_t T.
Proof.
  induction 1;
  Simplify by eauto with erased_aux safe_aux. 
  destruct (in_split _ _ H0) as [Gamma1 [Gamma2 ?]]; subst; clear H0.
  forwards Hokay : ctxt_okay_app H. 
  inversion Hokay; subst; eauto with erased_aux. 
  inversion IHtyping1; eauto.
  destruct (sub_implies_erased_t H0) as [? _].
  inversion IHtyping; subst; eauto with safe_inv_aux. 
  destruct (sub_implies_erased_t H0) as [_ ?]; eauto.
Qed.

Lemma typing_implies_erased_e : forall Gamma t T,
  typing Gamma t T -> erased_e t.
Proof.
  induction 1; Simplify by eauto with erased_aux safe_aux.
  destruct (sub_implies_erased_t H0) as [? ?]; eauto with erased_aux. 
Qed.

Hint Resolve typing_implies_erased_t typing_implies_erased_e : erased_aux.

(** ** Basic properties of [unroll_t] and [unroll_e] 
 [unroll_t] and [unroll_e] lie at the heart of the equivalence proof. This
 section presents their basic properties that we will use in the equivalence
 proof. Most of proofs proceed by induction on the size of typing contexts,
 which is defined as follows: *)
Fixpoint size_ctxt (Gamma : ctxt) : nat :=
  match Gamma with
    | nil         => 0
    | _ :: Gamma' => 1 + size_ctxt Gamma'
  end.

(** [size_ctxt] is distributive over [++] *)
Lemma size_ctxt_app : forall Gamma Delta,
  size_ctxt (Gamma ++ Delta) = (size_ctxt Gamma) + (size_ctxt Delta).
Proof.
  induction Gamma as [| b' Gamma1']; intros; eauto.
    simpl; f_equal; eauto.
Qed.

(** *** Properties of [unroll_t] 
 We first show that if [T] has a specific form, then [unroll_t Gamma T] 
 also has a specific form, accordingly. *)
Lemma unroll_t_top : forall Gamma, 
  unroll_t Gamma typ_top = typ_top.
Proof.
  induction Gamma; eauto.
    destruct a; simpl; eauto.
Qed.

Lemma unroll_t_ltvar : forall Gamma A, 
  unroll_t Gamma (typ_ltvar A) = typ_ltvar A.
Proof.
  induction Gamma; eauto.
    destruct a; simpl; eauto.
Qed.

Lemma unroll_t_ann_ftvar : forall Gamma X T, 
  unroll_t Gamma (X ^^ T) = X ^^ T.
Proof.
  induction Gamma; eauto.
    destruct a; simpl; eauto.
Qed.

Lemma unroll_t_ftvar : forall Gamma Gamma_1 Gamma_2 X T,
  ctxt_okay Gamma ->
  Gamma = Gamma_1 ++ (X ~<: T :: Gamma_2) ->
  unroll_t Gamma (X ^^) = X ^^ (unroll_t Gamma_2 T).
Proof.
  intros Gamma Gamma_1. 
  generalize dependent Gamma.
  induction Gamma_1 as [| a Gamma_1']; intros; subst; 
    Simplify by eauto using unroll_t_ann_ftvar. 
  inversion H; clear H; subst. 
    simpl; eauto.
    simpl; Simplify by Destruct notIn by eauto.
Qed.

Lemma unroll_t_ftvar_inv : forall Gamma X,
  ctxt_okay Gamma ->
  (unroll_t Gamma (X ^^) = X ^^) \/ 
  exists T', (unroll_t Gamma (X ^^) = X ^^ T').
Proof.
  induction 1; intros; simpl.
    left; reflexivity.
    intuition.
    Simplify by eauto.
      right. exists (unroll_t Gamma T); eauto using unroll_t_ann_ftvar.
Qed.

Lemma unroll_t_fun : forall Gamma T U, 
  unroll_t Gamma (T --> U) = (unroll_t Gamma T) --> (unroll_t Gamma U).
Proof.
  induction Gamma; intros; eauto.
    destruct a; simpl; eauto.
Qed.

Lemma unroll_t_all : forall Gamma A T U, 
  unroll_t Gamma (typ_all A T U) = 
  typ_all A (unroll_t Gamma T) (unroll_t Gamma U).
Proof.
  induction Gamma; intros; eauto.
    destruct a; simpl; eauto.
Qed.

(** We then show that the converse is also true: if [unroll_t Gamma T] has 
 a specific form, then [T] also has a specific form, accordingly. *)
Lemma inv_unroll_t_top : forall T Gamma, 
  ctxt_okay Gamma -> 
  erased_t T -> 
  typ_top = unroll_t Gamma T -> 
  typ_top = T.
Proof.
  destruct 2; intros.
  reflexivity.
  rewrite unroll_t_ltvar in H0; inversion H0.
  destruct (unroll_t_ftvar_inv X H); [ | destruct H1]; congruence.
  rewrite unroll_t_fun in H0; inversion H0.
  rewrite unroll_t_all in H0; inversion H0.
Qed.

Lemma inv_unroll_t_ltvar : forall T Gamma A, 
  ctxt_okay Gamma -> 
  erased_t T ->
  typ_ltvar A = unroll_t Gamma T -> 
  typ_ltvar A = T.
Proof.
  destruct 2; intros.
  rewrite unroll_t_top in H0; inversion H0.
  rewrite unroll_t_ltvar in H0; assumption.
  destruct (unroll_t_ftvar_inv X H); [ | destruct H1]; congruence.
  rewrite unroll_t_fun in H0; inversion H0.
  rewrite unroll_t_all in H0; inversion H0.
Qed.

Lemma inv_unroll_t_ftvar : forall T Gamma X ann_U,
  ctxt_okay Gamma -> 
  erased_t T -> 
  X ^^ ann_U = unroll_t Gamma T ->
  exists Gamma_1 Gamma_2 U,
    (T = X ^^) /\ 
    (Gamma = Gamma_1 ++ X ~<: U :: Gamma_2) /\ 
    (ann_U = unroll_t Gamma_2 U).
Proof.
  destruct 2; intros.
  rewrite unroll_t_top in H0; inversion H0.
  rewrite unroll_t_ltvar in H0; inversion H0.
    generalize dependent ann_U. 
    induction H; intros.
    inversion H0.
    simpl in H2. destruct (IHctxt_okay _ H2) as [Gamma_1 [Gamma_2 [U ?]]].
    exists ((x ~: T)::Gamma_1) (Gamma_2) U.
    intuition; subst; reflexivity.
    simpl in H2; Simplify by eauto.
      exists (emptyset:ctxt) Gamma T.
      rewrite unroll_t_ann_ftvar in H2; inversion H2; subst.
      intuition.
      destruct (IHctxt_okay _ H2) as [Gamma_1 [Gamma_2 [U ?]]].
      exists (X1 ~<: T :: Gamma_1) Gamma_2 U.
      intuition; subst; reflexivity.
  rewrite unroll_t_fun in H0; inversion H0.
  rewrite unroll_t_all in H0; inversion H0.
Qed.

Lemma inv_unroll_t_ftvar_nochange : forall X T Gamma,
  ctxt_okay Gamma -> 
  erased_t T ->
  X ^^ = unroll_t Gamma T -> 
  X ^^ = T.
Proof.
  destruct 2; intros.
  rewrite unroll_t_top in H0; inversion H0.
  rewrite unroll_t_ltvar in H0; assumption.
  destruct (unroll_t_ftvar_inv X0 H); [ | destruct H1]; congruence.
  rewrite unroll_t_fun in H0; inversion H0.
  rewrite unroll_t_all in H0; inversion H0.
Qed.

Lemma inv_unroll_t_fun : forall T Gamma ann_U ann_S,
  ctxt_okay Gamma -> 
  erased_t T -> 
  (ann_U --> ann_S) = unroll_t Gamma T -> 
  exists U S, 
    (T = U --> S) /\ 
    (ann_U = (unroll_t Gamma U)) /\ 
    (ann_S = (unroll_t Gamma S)).
Proof.
  destruct 2; intros.
  rewrite unroll_t_top in H0; inversion H0.
  rewrite unroll_t_ltvar in H0; inversion H0.
  destruct (unroll_t_ftvar_inv X H); [ | destruct H1]; congruence.
  rewrite unroll_t_fun in H0; inversion H0; eauto.
  rewrite unroll_t_all in H0; inversion H0.
Qed.

Lemma inv_unroll_t_all : forall T Gamma A ann_U ann_S,
  ctxt_okay Gamma -> 
  erased_t T -> 
  (typ_all A ann_U ann_S) = unroll_t Gamma T -> 
  exists U S, 
    (T = typ_all A U S) /\ 
    (ann_U = (unroll_t Gamma U)) /\ 
    (ann_S = (unroll_t Gamma S)).
Proof.
  destruct 2; intros.
  rewrite unroll_t_top in H0; inversion H0.
  rewrite unroll_t_ltvar in H0; inversion H0.
  destruct (unroll_t_ftvar_inv X H); [ | destruct H1]; congruence.
  rewrite unroll_t_fun in H0; inversion H0.
  rewrite unroll_t_all in H0; inversion H0. eauto.
Qed.

(** We may swap [unroll_t] and type variable substitution. *)
Lemma unroll_t_lsubst_tt : forall Gamma A U T,
  unroll_t Gamma ({A ~> U} T) = {A ~> unroll_t Gamma U} (unroll_t Gamma T).
Proof. 
  induction Gamma; intros; eauto.
    destruct a; Simplify by (simpl; eauto). 
      rewrite swap_fsubst_tt_lsubst_tt; eauto.
Qed.

(** If [T] is erased and [Gamma2] contains all the parameters of [T], then
 [unroll_t (Gamma_1 ++ Gamma_2) T] results in the same result as 
 [unroll_t Gamma2 T] as long as [ctxt_okay (Gamma1 ++ Gamma2)] holds. *)
Lemma unroll_t_weakening : forall Gamma1 Gamma2 T,
  ctxt_okay (Gamma1 ++ Gamma2) ->
  lclosed_t Gamma2 emptyset T ->
  unroll_t Gamma2 T = unroll_t (Gamma1 ++ Gamma2) T.
Proof.
  induction Gamma1 as [| b Gamma1']; intros; Simplify by eauto.
  inversion H; subst.
    simpl; eauto.
    simpl; Simplify by Destruct notIn by idtac.
    assert ( ~ In X (FV_tt T) ) by eauto with incl_param.
    rewrite subst_ftvar_nochange_t; eauto.
Qed.

(** [unroll_t] is invertible. *)
Lemma unroll_t_inv : forall T U Gamma,
  erased_t T ->
  erased_t U ->
  ctxt_okay Gamma ->
  unroll_t Gamma T = unroll_t Gamma U ->
  T = U.
Proof.
  intros.
  generalize dependent Gamma.
  generalize dependent U.
  induction H; intros.
  rewrite  unroll_t_top in H2.
  eauto using inv_unroll_t_top.
  rewrite unroll_t_ltvar in H2.
  eauto using inv_unroll_t_ltvar.
  destruct (unroll_t_ftvar_inv X H1).
    rewrite H in H2; eauto using inv_unroll_t_ftvar_nochange. 
    destruct H as [C H]; rewrite H in H2.
    destruct (inv_unroll_t_ftvar H1 H0 H2) as [Gamma1 [Gamma2 [C' [HA _]]]]; 
      congruence.
  rewrite unroll_t_fun in H3.
  destruct (inv_unroll_t_fun H2 H1 H3) as [T' [U' [HT [HT' HU']]]]; subst. 
  inversion H1; f_equal; eauto.
  rewrite unroll_t_all in H3.
  destruct (inv_unroll_t_all H2 H1 H3) as [T' [U' [HT [HT' HU']]]]; subst. 
  inversion H1; f_equal; eauto.
Qed.

(** *** Properties of [unroll_e] 
 Similarly, this section shows properties of [unroll_e]. 

 First of all,  as [unroll_t], we first show that if [t] has a specific 
 form, then [unroll_e Gamma t] also has a specific form, accordingly. *)
Lemma unroll_e_lvar : forall Gamma a,
  unroll_e Gamma (tm_lvar a) = tm_lvar a.
Proof.
  induction Gamma; intros; eauto.
    destruct a; simpl; eauto.
Qed.

Lemma unroll_e_ann_fvar : forall Gamma x T,
  unroll_e Gamma (x ** T) = x ** T.
Proof.
  induction Gamma; intros; eauto.
    destruct a; simpl; eauto.
Qed.

Lemma unroll_e_fvar : forall Gamma Gamma_1 Gamma_2 x T,
  ctxt_okay Gamma ->
  Gamma = Gamma_1 ++ (x ~: T :: Gamma_2) ->
  unroll_e Gamma (x **) = x ** (unroll_t Gamma_2 T).
Proof.
  intros Gamma Gamma_1. generalize dependent Gamma.
  induction Gamma_1 as [| a Gamma_1']; intros; subst; 
    Simplify by eauto using unroll_e_ann_fvar.  
  inversion H; clear H; subst. 
    simpl; Simplify by Destruct notIn by eauto.
    simpl; Simplify by eauto.
Qed.

Lemma unroll_e_fvar_inv : forall Gamma x,
  ctxt_okay Gamma ->
  (unroll_e Gamma ( x ** ) = x ** ) \/ 
  exists T, (unroll_e Gamma (x ** ) = x ** T).
Proof.
  induction 1; intros; Simplify by eauto.
  simpl; Simplify by eauto.
    right; exists (unroll_t Gamma T); eauto using unroll_e_ann_fvar.
Qed.

Lemma unroll_e_abs : forall Gamma a T t, 
  unroll_e Gamma (tm_abs a T t) = 
  tm_abs a (unroll_t Gamma T) (unroll_e Gamma t).
Proof.
  induction Gamma; intros; eauto.
    destruct a; simpl; eauto.
Qed.

Lemma unroll_e_app : forall Gamma t t', 
  unroll_e Gamma (tm_app t t') = tm_app (unroll_e Gamma t) (unroll_e Gamma t').
Proof.
  induction Gamma; intros; eauto.
    destruct a; simpl; eauto.
Qed.

Lemma unroll_e_tabs : forall Gamma A T t,
  unroll_e Gamma (tm_tabs A T t) = 
  tm_tabs A (unroll_t Gamma T) (unroll_e Gamma t).
Proof.
  induction Gamma; intros; eauto.
    destruct a; simpl; eauto.
Qed.

Lemma unroll_e_tapp : forall Gamma t T, 
  unroll_e Gamma (tm_tapp t T) = tm_tapp (unroll_e Gamma t) (unroll_t Gamma T).
Proof.
  induction Gamma; intros; eauto.
    destruct a; simpl; eauto.
Qed.

(** We then show that its converse is also true: if [unroll_e Gamma t] has 
 a specific form, then [t] also has a specific form, accordingly. *)
Lemma inv_unroll_e_fvar : forall t Gamma x ann_T,
  ctxt_okay Gamma -> 
  erased_e t -> 
  x ** ann_T = unroll_e Gamma t ->
  exists Gamma_1 Gamma_2 T,
    (t = x **) /\ 
    (Gamma = Gamma_1 ++ x ~: T :: Gamma_2) /\ 
    (ann_T = unroll_t Gamma_2 T).
Proof.
  destruct 2; intros.
  rewrite unroll_e_lvar in H0; inversion H0.
    generalize dependent ann_T.
    induction H; intros.
    inversion H0.
    simpl in H2; Simplify by eauto.
      exists (emptyset:ctxt) Gamma T.
      rewrite unroll_e_ann_fvar in H2; inversion H2; subst; intuition.
      destruct (IHctxt_okay _ H2) as [Gamma_1 [Gamma_2 [T' ?]]].
      exists (x1 ~: T :: Gamma_1) Gamma_2 T'; intuition.
        subst; eauto.
    simpl in H2. 
    destruct (IHctxt_okay _ H2) as [Gamma_1 [Gamma_2 [T' ?]]].
    exists ((X ~<: T)::Gamma_1) (Gamma_2) T'; intuition.
      subst; eauto.
  rewrite unroll_e_abs in H2; inversion H2.
  rewrite unroll_e_app in H0; inversion H0.
  rewrite unroll_e_tabs in H2; inversion H2.
  rewrite unroll_e_tapp in H2; inversion H2.
Qed.

Lemma inv_unroll_e_abs : forall Gamma t a ann_T ann_t',
  ctxt_okay Gamma -> 
  erased_e t ->
  tm_abs a ann_T ann_t' = unroll_e Gamma t ->
  exists T t', 
    (t = tm_abs a T t') /\ 
    (ann_T = (unroll_t Gamma T)) /\
    (ann_t' = (unroll_e Gamma t')).
Proof.
  destruct 2; intros.
  rewrite unroll_e_lvar in H0; inversion H0.
  destruct (unroll_e_fvar_inv x H); [ | destruct H1]; congruence.
  rewrite unroll_e_abs in H2; inversion H2; eauto.
  rewrite unroll_e_app in H0; inversion H0; eauto.
  rewrite unroll_e_tabs in H2; inversion H2; eauto.
  rewrite unroll_e_tapp in H2; inversion H2.
Qed.

Lemma inv_unroll_e_app : forall Gamma t ann_t1 ann_t2,
  ctxt_okay Gamma -> 
  erased_e t ->
  tm_app ann_t1 ann_t2 = unroll_e Gamma t ->
  exists t1 t2, 
    (t = tm_app t1 t2) /\ 
    (ann_t1 = unroll_e Gamma t1) /\ 
    (ann_t2 = unroll_e Gamma t2).
Proof.
  destruct 2; intros.
  rewrite unroll_e_lvar in H0; inversion H0.
  destruct (unroll_e_fvar_inv x H); [ | destruct H1]; congruence.
  rewrite unroll_e_abs in H2; inversion H2.
  rewrite unroll_e_app in H0; inversion H0; eauto.
  rewrite unroll_e_tabs in H2; inversion H2.
  rewrite unroll_e_tapp in H2; inversion H2.
Qed.

Lemma inv_unroll_e_tabs : forall Gamma t A ann_T ann_t',
  ctxt_okay Gamma -> 
  erased_e t ->
  tm_tabs A ann_T ann_t' = unroll_e Gamma t ->
  exists T t', 
    (t = tm_tabs A T t') /\ 
    (ann_T = (unroll_t Gamma T)) /\ 
    (ann_t' = (unroll_e Gamma t')).
Proof.
  destruct 2; intros.
  rewrite unroll_e_lvar in H0; inversion H0.
  destruct (unroll_e_fvar_inv x H); [ | destruct H1]; congruence.
  rewrite unroll_e_abs in H2; inversion H2.
  rewrite unroll_e_app in H0; inversion H0.
  rewrite unroll_e_tabs in H2; inversion H2; eauto.
  rewrite unroll_e_tapp in H2; inversion H2.
Qed.

Lemma inv_unroll_e_tapp : forall Gamma t ann_t' ann_T,
  ctxt_okay Gamma -> 
  erased_e t ->
  tm_tapp ann_t' ann_T = unroll_e Gamma t ->
  exists t' T, 
    (t = tm_tapp t' T) /\ 
    (ann_t' = unroll_e Gamma t') /\ 
    (ann_T = unroll_t Gamma T).
Proof.
  destruct 2; intros.
  rewrite unroll_e_lvar in H0; inversion H0.
  destruct (unroll_e_fvar_inv x H); [ | destruct H1]; congruence.
  rewrite unroll_e_abs in H2; inversion H2.
  rewrite unroll_e_app in H0; inversion H0.
  rewrite unroll_e_tabs in H2; inversion H2.
  rewrite unroll_e_tapp in H2; inversion H2. eauto.
Qed.

(** We may swap [unroll_e] and variable substitution. *)
Lemma swap_unroll_e_lsubst_te : forall Gamma A X T t,
  unroll_e Gamma ({A :~> X ^^ T} t) = {A :~> X ^^ T} (unroll_e Gamma t).
Proof.
  induction Gamma; intros; eauto.
    destruct a; simpl; autorewrite with swap_subst using eauto.
Qed.

Lemma swap_unroll_e_lsubst_ee : forall Gamma x X A e,
  unroll_e Gamma ({x ::~> X ** A} e) = {x ::~> X ** A} (unroll_e Gamma e).
Proof.
  induction Gamma; intros; eauto.
    destruct a; simpl; autorewrite with swap_subst using eauto.
Qed.

(** ** Properties of [ann_FV_tt], [ann_FV_te], and [ann_FV_ee] *)
Lemma not_in_ann_FV_tt_nochange_fsubst_tt : forall T X Y U,
  ~ In X (ann_FV_tt T) -> 
  ~ In X (ann_FV_tt U) -> 
  X <> Y ->
  ~ In X (ann_FV_tt ([Y ~> Y ^^ U] T)).
Proof.
  induction T; intros; Simplify by Destruct notIn by eauto. 
Qed.

Hint Resolve not_in_ann_FV_tt_nochange_fsubst_tt : incl_param.

Lemma not_in_ann_FV_te_nochange_fsubst_te : forall t X Y T,
  ~ In X (ann_FV_te t) -> 
  ~ In X (ann_FV_tt T) -> 
  X <> Y ->
  ~ In X (ann_FV_te ([Y :~> Y ^^ T] t)).
Proof.
  induction t; intros; Simplify by Destruct notIn by eauto with incl_param.
Qed.

Hint Resolve not_in_ann_FV_te_nochange_fsubst_te : incl_param.

Lemma not_in_ann_FV_te_nochange_fsubst_ee : forall t T x X,
  ~ In X (ann_FV_te t) -> 
  ~ In X (ann_FV_tt T) -> 
  ~ In X (ann_FV_te ([ x ::~> x ** T] t)).
Proof.
  induction t; intros; Simplify by Destruct notIn by eauto. 
Qed.

Hint Resolve not_in_ann_FV_te_nochange_fsubst_ee : incl_param.
 
Lemma not_in_ann_FV_ee_nochange_fsubst_te : forall t x X T,
  ~ In x (ann_FV_ee t) -> 
  ~ In x (ann_FV_ee ([X :~> T] t)).
Proof.
  induction t; intros; Simplify by Destruct notIn by eauto. 
Qed.

Hint Resolve not_in_ann_FV_ee_nochange_fsubst_te : incl_param.

Lemma not_in_ann_FV_ee_nochange_fsubst_ee : forall t x y u,
  ~ In x (ann_FV_ee t) -> 
  ~ In x (ann_FV_ee u) -> 
  ~ In x (ann_FV_ee ([ y ::~> u ] t)).
Proof.
  induction t; intros; Simplify by Destruct notIn by eauto. 
Qed.

Hint Resolve not_in_ann_FV_ee_nochange_fsubst_ee : incl_param.

Lemma not_in_FV_tc_not_in_FV_tt_not_in_ann_FV_tt : forall Gamma X T,
  ctxt_okay Gamma ->
  erased_t T ->
  ~ In X (FV_tc Gamma) ->
  ~ In X (FV_tt T) ->
  ~ In X (ann_FV_tt (unroll_t Gamma T)).
Proof.
  intros Gamma X T H.
  generalize dependent T.
  generalize dependent X.
  induction H; intros.
  simpl; clear H0 H1.
  induction H; Simplify by (Destruct notIn by eauto).
  simpl; Simplify by Destruct notIn by eauto. 
  induction T0; intros; Simplify by eauto.
    rewrite unroll_t_top; auto.
    rewrite unroll_t_ltvar; auto.
      rewrite unroll_t_ann_ftvar.
      Simplify by Destruct notIn by eauto with erased_aux.
      apply IHctxt_okay; Simplify by Destruct notIn by eauto.
    simpl; apply IHctxt_okay; Simplify by Destruct notIn by eauto.
    inversion H2; subst; clear H2.
    rewrite unroll_t_fun.
    simpl; Simplify by Destruct notIn by eauto. 
    inversion H2; subst; clear H2.
    rewrite unroll_t_all. 
    simpl; Simplify by Destruct notIn by eauto. 
Qed.

Hint Resolve not_in_FV_tc_not_in_FV_tt_not_in_ann_FV_tt : incl_param.

Lemma not_in_ann_FV_te_not_in_FV_tc_not_in_ann_FV_te : forall Gamma X t,
  ctxt_okay Gamma ->
  ~ In X (ann_FV_te t) ->
  ~ In X (FV_tc Gamma) ->
  ~ In X (ann_FV_te (unroll_e Gamma t)).
Proof.
  intros Gamma X t H.
  generalize dependent t.
  generalize dependent X.
  induction H; intros; 
    Simplify by Destruct notIn by eauto with erased_aux incl_param.
Qed.

Hint Resolve not_in_ann_FV_te_not_in_FV_tc_not_in_ann_FV_te : incl_param.

Lemma not_in_ann_FV_ee_not_in_dom_ec_not_in_ann_FV_ee : forall Gamma x t,
  ctxt_okay Gamma ->
  ~ In x (ann_FV_ee t) ->
  ~ In x (dom_ec Gamma) ->
  ~ In x (ann_FV_ee (unroll_e Gamma t)).
Proof.
  intros Gamma x t H.
  generalize dependent t.
  generalize dependent x.
  induction H; intros; Simplify by Destruct notIn by eauto with incl_param.
  apply IHctxt_okay; eauto.
    eapply not_in_ann_FV_ee_nochange_fsubst_ee;
      Simplify by Destruct notIn by eauto.
Qed.

Hint Resolve not_in_ann_FV_ee_not_in_dom_ec_not_in_ann_FV_ee : incl_param.

(** * The equivalence proof 
 To prove the equivalence of two systems, we first need to show the 
 equivalence of [lclosed_t] and [ann_lclosed_t]. 

 We prove the equivalence of [lclosed_t] and [ann_lclosed_t] by showing that
 [lclosed_t Gamma I T] holds if and only if 
 [ann_lclosed_t I (unroll_t Gamma T)] holds.

 This equivalence holds only when a typing context [Gamma] is well-formed.
 Suppose that [Gamma] is [X ~<: X]. Definitely, [lclosed_t Gamma emptyset X]
 holds, but [unroll_t Gamma X] is [X], and thus [ann_lclosed_t emptyset X] does
 not hold.

 We first prove Lemma [lclosed_t_implies_ann_lclosed_t] which states the 
 only if part of the equivalence. The proof proceeds by two lemmas whose 
 proof proceeds by induction on the structure of [lclosed_t] proofs, and 
 on the size of typing contexts, respectively.

 We first prove Lemma [lclosed_t_implies_ann_lclosed_t_size_aux] which states 
 that the only if part holds for a given typing context [Gamma] when we assume 
 that the only if part holds for all typing contexts whose size is less than 
 that of [Gamma]. Note that we use [lclosed_t_size_IH_on] for that purpose.

 Using Lemma [lclosed_t_implies_ann_lclosed_t_size_aux], we then prove Lemma 
 [lclosed_t_implies_ann_lclosed_t_aux]. The proof proceeds by induction on the
 size of typing contexts. *)
Definition lclosed_t_size_IH_on n := forall Gamma T I,
  ctxt_okay Gamma ->
  size_ctxt Gamma < n ->
  lclosed_t Gamma I T ->
  ann_lclosed_t I (unroll_t Gamma T).

Lemma lclosed_t_implies_ann_lclosed_t_size_aux : forall Gamma T I,
  lclosed_t_size_IH_on (size_ctxt Gamma) ->
  ctxt_okay Gamma ->
  lclosed_t Gamma I T ->
  ann_lclosed_t I (unroll_t Gamma T).
Proof.
  induction 3; intros.
  rewrite unroll_t_top; eauto.
  rewrite unroll_t_ltvar; eauto.
  destruct (exists_ftvar_bind _ _ H1) as [T ?].
  destruct (In_split _ _  H2) as [Gamma_1 [Gamma_2 ?]].
  rewrite (unroll_t_ftvar _ _ _ _ H0 H3); subst.
  forwards Hokay : ctxt_okay_app H0.
  inversion Hokay; clear Hokay; subst.
  econstructor.
  apply H; Simplify by eauto.
    rewrite size_ctxt_app; Simplify by eauto with arith.
  rewrite unroll_t_fun; eauto.
  rewrite unroll_t_all; eauto.
Qed.

Lemma lclosed_t_implies_ann_lclosed_t_aux : forall m Gamma I T,
  size_ctxt Gamma < m ->
  ctxt_okay Gamma ->
  lclosed_t Gamma I T ->
  ann_lclosed_t I (unroll_t Gamma T).
Proof.
  induction m; intros.
  firstorder using lt_n_O.
  eapply lclosed_t_implies_ann_lclosed_t_size_aux; eauto.
    unfold lclosed_t_size_IH_on; eauto with arith.
Qed.

Lemma lclosed_t_implies_ann_lclosed_t : forall Gamma A T,
  ctxt_okay Gamma ->
  lclosed_t Gamma T A ->
  ann_lclosed_t T (unroll_t Gamma A).
Proof.
  intros; eauto using lclosed_t_implies_ann_lclosed_t_aux with arith.
Qed.

(** We then prove Lemma [ann_lclosed_t_implies_lclosed_t] which states the 
 if part of the equivalence. The proof proceeds by induction on the structure 
 of [ann_lclosed_t] proofs. *)
Lemma ann_lclosed_t_implies_lclosed_t : forall ann_T I,
  ann_lclosed_t I ann_T -> 
  forall Gamma T,
    ctxt_okay Gamma -> 
    erased_t T -> 
    ann_T = unroll_t Gamma T -> 
    lclosed_t Gamma I T.
Proof.
  induction 1; intros; Simplify by eauto. 
  erewrite <- inv_unroll_t_top; eauto.
  erewrite <- inv_unroll_t_ltvar; eauto.
  edestruct inv_unroll_t_ftvar with (T := T0) 
    as [Gamma_1 [Gamma_2 [U [HT [HGamma HU]]]]]; eauto.
  subst; econstructor. 
    Simplify by Destruct In by eauto.
  edestruct inv_unroll_t_fun with (T := T0) 
    as [T'' [U'' [HT [HU HS]]]]; eauto.
  subst; inversion H2; eauto.
  edestruct inv_unroll_t_all with (T := T0) 
    as [U' [S' [HT [HU HS]]]]; eauto.
  subst; inversion H2; eauto.
Qed.

Hint Resolve lclosed_t_implies_ann_lclosed_t : equiv_aux.
Hint Resolve ann_lclosed_t_implies_lclosed_t : equiv_aux.

(** ** Equivalence of [sub] and [ann_sub] 
 Now, we present the equivalence of [sub] and [ann_sub]. We prove 
 the equivalence by showing that [sub Gamma T U] holds if and only 
 if [ann_sub (unroll_t Gamma T) (unroll_t Gamma U)] holds. 

 We first prove Lemma [sub_implies_ann_sub] which states the only 
 if part of the equivalence. The proof proceeds by induction on 
 the structure of [sub] proofs. *)
Lemma sub_implies_ann_sub : forall Gamma T U,
  sub Gamma T U -> ann_sub (unroll_t Gamma T) (unroll_t Gamma U).
Proof.
  induction 1; intros; Simplify by eauto.
  rewrite unroll_t_top; eauto with equiv_aux. 
  inversion H0; clear H0; subst.
  destruct (exists_ftvar_bind _ _ H3) as [T ?].
  destruct (In_split _ _ H0) as [Gamma1 [Gamma2 ?]].
  rewrite (unroll_t_ftvar _ _ _ _ H H1); subst.
  forwards Hokay : ctxt_okay_app H.
  inversion Hokay; subst.
  constructor; eauto with equiv_aux. 
  destruct (In_split _ _ H) as [Gamma1 [Gamma2 ?]].
  forwards Hokay : sub_ctxt_okay H0.
  rewrite (unroll_t_ftvar _ _ _ _ Hokay H1).
  constructor; subst.
    forwards Hokay' : ctxt_okay_app Hokay.
    inversion Hokay'; subst.
    erewrite unroll_t_weakening 
      with (Gamma1 := (Gamma1 ++ (X ~<: T) :: emptyset));
        repeat rewrite <- list_cons_move_app; eauto.
  repeat (rewrite unroll_t_fun); eauto.
  repeat (rewrite unroll_t_all); eauto.
  set (L := FV_tt T2 ++ FV_tt U2 ++ 
    ann_FV_tt (unroll_t Gamma T1) ++ ann_FV_tt (unroll_t Gamma T2) ++ 
    ann_FV_tt (unroll_t Gamma U1) ++ ann_FV_tt (unroll_t Gamma U2)).
  destruct (pick_fresh L) as [Y Hfresh].
  unfold L in Hfresh.
  econstructor 5 with (X := Y); Destruct notIn by eauto.
  destruct (sub_implies_erased_t H2).
  forwards Hokay : sub_ctxt_okay H.
  destruct (ann_sub_subLH IHsub2) as [n ?]; eapply ann_subLH_sub.
  eapply ann_subLH_ltvar_subst_rename_ftvar with (X := X); 
    Destruct notIn by eauto with incl_param safe_aux. 
    rewrite <- unroll_t_ann_ftvar with (Gamma := Gamma). 
    repeat rewrite <- unroll_t_lsubst_tt.
    repeat (rewrite <- fsubst_tt_lsubst_tt_seq by eauto). 
    unsimpl (unroll_t (X ~<: U1 :: Gamma) ({A ~> X ^^}T2)); 
    unsimpl (unroll_t (X ~<: U1 :: Gamma) ({B ~> X ^^}U2)); 
    eauto.
Qed.

(** We then prove Lemma [ann_sub_implies_sub] which states the  
 if part of the equivalence. The proof proceeds by induction on 
 the size of [ann_sub] proofs. Note the use of the renaming lemma
 for the [ann_sub_all] case. *)
Lemma ann_sub_implies_sub_aux : forall m n ann_T ann_U,
  n < m ->
  ann_subLH n ann_T ann_U ->
  forall Gamma T U,
    ctxt_okay Gamma ->
    erased_t T ->
    erased_t U ->
    ann_T = unroll_t Gamma T ->
    ann_U = unroll_t Gamma U ->
    sub Gamma T U.
Proof.
  induction m; intros.
  firstorder using lt_n_O. 
  destruct H0; subst; Simplify by eauto. 
    rewrite <- (inv_unroll_t_top H1 H3); eauto with equiv_aux. 
    destruct (inv_unroll_t_ftvar H1 H2 H4) 
      as [Gamma1 [Gamma2 [S [? [? ?]]]]]; subst.
    destruct (inv_unroll_t_ftvar H1 H3 H5) 
      as [? [? [S' [? [? ?]]]]]; subst.
    eauto with equiv_aux. 
    destruct (inv_unroll_t_ftvar H1 H2 H4) 
      as [Gamma1 [Gamma2 [S [? [? ?]]]]]; subst.
    constructor 3 with S.
      Destruct In by eauto.
      forwards Hokay : ctxt_okay_app H1.
      inversion Hokay; subst.
      eapply IHm;  eauto with erased_aux arith.
      rewrite -> list_cons_move_app. 
        apply unroll_t_weakening; eauto.
          rewrite <- list_cons_move_app; eauto.
    edestruct inv_unroll_t_fun with (T := T) 
      as [T1' [T2' [HT [HT1' HT2']]]]; subst; eauto.
    edestruct inv_unroll_t_fun with (T := U) 
      as [U1' [U2' [HU [HU1' HU2']]]]; subst; eauto. 
    inversion H2; inversion H3; subst.
    econstructor; eauto with arith.
    edestruct inv_unroll_t_all with (T := T) 
      as [T1' [T2' [HT [HT1' HT2']]]]; eauto. 
      subst.
    edestruct inv_unroll_t_all with (T := U) 
      as [U1' [U2' [HU [HU1' HU2']]]]; eauto.
      subst.
    inversion H2; inversion H3; subst.
    set (L := dom_tc Gamma ++ FV_tc Gamma ++ FV_tt T2' ++ FV_tt U2').
    destruct (pick_fresh L) as [Y Hfresh].
    unfold L in Hfresh.
    eapply sub_all with (X := Y); Destruct notIn by eauto. 
      eapply IHm with (n := n1); eauto with arith.
      eapply IHm with (n := n2)
        (ann_T := unroll_t (Y ~<: U1' :: Gamma) ({ A ~> Y ^^} T2')) 
        (ann_U := unroll_t (Y ~<: U1' :: Gamma) ({ B ~> Y ^^} U2')); 
       eauto  with safe_inv_aux arith; simpl.
       repeat (rewrite fsubst_tt_lsubst_tt_seq by eauto).
       repeat rewrite unroll_t_lsubst_tt.
       repeat rewrite unroll_t_ann_ftvar. 
       eapply ann_subLH_ltvar_subst_rename_ftvar; eauto.
      econstructor; Destruct notIn by eauto.
        eapply sub_lclosed_t with (T := U1') (U := T1'); eauto with arith.
Qed.

Lemma ann_sub_implies_sub : forall Gamma T U,
  ctxt_okay Gamma ->
  erased_t T ->
  erased_t U ->
  ann_sub (unroll_t Gamma T) (unroll_t Gamma U) ->
  sub Gamma T U.
Proof.
  intros.
  destruct (ann_sub_subLH H2) as [n Hsub].
  eauto using ann_sub_implies_sub_aux.
Qed.

Hint Resolve sub_implies_ann_sub : equiv_aux.
Hint Resolve ann_sub_implies_sub : equiv_aux.

(** ** Equivalence of [typing] and [ann_typing] 
 This section presents the equivalence of [typing] and [ann_typing]. 
 We prove the equivalence by showing that [typing Gamma t T] holds if 
 and only if [ann_typing (unroll_e Gamma t) (unroll_t Gamma T)] holds.

 It is straightforward to prove the only if part. 
 
 Lemma [typing_implies_ann_typing] states the only if part of the 
 equivalence. Its proof proceeds by simple induction on the structure 
 of [typing] proofs. *)
Lemma typing_implies_ann_typing : forall Gamma t T,
  typing Gamma t T ->
  ann_typing (unroll_e Gamma t) (unroll_t Gamma T).
Proof.
  induction 1; intros; Simplify by eauto.
    destruct (in_split _ _ H0) as [Gamma1 [Gamma2 ?]]; subst.
    rewrite unroll_e_fvar with _ Gamma1 Gamma2 _ T; eauto.
    forwards Hokay : ctxt_okay_app H.
    inversion Hokay; subst.
    rewrite -> list_cons_move_app.
    rewrite <- unroll_t_weakening; eauto.
    econstructor; eauto with equiv_aux. 
      rewrite <- list_cons_move_app; eauto.
    rewrite unroll_e_abs; rewrite unroll_t_fun.
    forwards Hokay : typing_ctxt_okay H2.
    inversion Hokay; subst.
    forwards Herased : erased_e_lsubst_ee_safe (typing_implies_erased_e H2).
    econstructor 2 with (x := x); eauto with equiv_aux. 
      eauto with incl_param.
      rewrite <- swap_unroll_e_lsubst_ee; eauto.
      rewrite <- fsubst_ee_lsubst_ee_seq; eauto.      
    repeat (rewrite unroll_e_app); eauto.
    eapply ann_typing_app with (T := unroll_t Gamma T); eauto.
    replace (unroll_t Gamma T --> unroll_t Gamma U) 
      with (unroll_t Gamma (T --> U)); eauto using unroll_t_fun.
    rewrite unroll_e_tabs; rewrite unroll_t_all.
    forwards Hokay : typing_ctxt_okay H2.
    inversion Hokay; subst.
    forwards He : erased_e_lsubst_te_safe (typing_implies_erased_e H2).
    forwards Ht : erased_t_lsubst_tt_safe (typing_implies_erased_t H2).
    econstructor 4 with (X := X); 
      Destruct notIn by eauto with equiv_aux incl_param. 
      rewrite <- swap_unroll_e_lsubst_te by eauto.
      rewrite <- unroll_t_ann_ftvar 
        with (Gamma := Gamma) (T := unroll_t Gamma T). 
      repeat rewrite <- unroll_t_lsubst_tt.
      rewrite unroll_t_ann_ftvar with (T := unroll_t Gamma T).
      rewrite <- fsubst_tt_lsubst_tt_seq by eauto. 
      rewrite <- fsubst_te_lsubst_te_seq by eauto. 
      eauto with incl_param. 
    rewrite unroll_e_tapp; rewrite unroll_t_lsubst_tt.
    eapply ann_typing_tapp with (U := unroll_t Gamma T'); 
      eauto with equiv_aux. 
    replace (typ_all A (unroll_t Gamma T') (unroll_t Gamma U)) 
      with (unroll_t Gamma (typ_all A T' U)); eauto using unroll_t_all.
    eapply ann_typing_sub with (T := unroll_t Gamma T); 
      eauto with equiv_aux. 
Qed.

(** Unlike the only if part, the proof of the if part is challenging.
 The main technical challenge is to deal with the [typing_app], 
 [typing_tapp], and [typing_sub] cases that may introduce incompatible 
 annotated types in their premise. We say that an annotated type [T]
 is incompatible under a typing context [Gamma] when for any erased 
 types [T'], [T = unroll_t Gamma T'] does not hold. We similarly
 define the incompatible annotated term. To complete the proof, we
 need to deal with these incompatible types and terms.

 To deal with incompatible types and terms, we first prove Lemma 
 [ann_typingLH_implies_ann_pure_typingLH]. It states that if any 
 compatible term has a type [T], then there exists a compatible 
 type which is a super type of [T]. *)
Lemma typ_decompose : forall T A X,
  ~ In A (LV_all_tt T) ->
  exists T', T = {A ~> X ^^} T' /\ ~ In X (FV_tt T').
Proof.
  induction T; intros. 
  exists typ_top; eauto.
  exists (typ_ltvar n); Simplify by Destruct notIn by eauto. 
  destruct (n == X); subst.
    exists (typ_ltvar A); Simplify by eauto.
    exists (n ^^); split; Simplify by Destruct notIn by eauto.  
  exists (n ^^ T); Simplify by eauto. 
  Simplify by Destruct notIn by eauto.
  destruct IHT1 with (A := A) (X := X) as [T1' [? ?]]; eauto. 
  destruct IHT2 with (A := A) (X := X) as [T2' [? ?]]; eauto.
  exists (T1' --> T2'); split; 
    Simplify by Destruct notIn by (f_equal; eauto).
  Simplify by Destruct notIn by eauto.
  destruct IHT1 with (A := A) (X := X) as [T1' [? ?]]; eauto. 
  destruct IHT2 with (A := A) (X := X) as [T2' [? ?]]; eauto.
  exists (typ_all n T1' T2'); split; 
    Simplify by Destruct notIn by (f_equal; eauto).
Qed.

Lemma sub_unroll_t_fun : forall ann_T ann_T',
  ann_sub ann_T ann_T' ->
  forall Gamma ann_U ann_U' T,
  ctxt_okay Gamma -> 
  erased_t T ->
  ann_T = unroll_t Gamma T ->
  ann_T' = ann_U --> ann_U' ->
  exists U U',
    erased_t U /\ 
    erased_t U' /\
    ann_sub ann_T ((unroll_t Gamma U) --> (unroll_t Gamma U')) /\
    ann_sub ((unroll_t Gamma U) --> (unroll_t Gamma U')) ann_T'.
Proof.
  induction 1; intros; subst; Simplify by try congruence. 
  edestruct inv_unroll_t_ftvar 
    with (Gamma := Gamma) (T := T0) 
      as [Gamma_1 [Gamma_2 [T' [HT [HGamma HT']]]]];
        eauto. 
  subst.
  forwards Hokay : ctxt_okay_app H0.
  inversion Hokay.
  edestruct IHann_sub 
    with (Gamma := Gamma_1 ++ X ~<: T' :: Gamma_2) (T := T')
      as [S [S' [HS [HS' [Hsub1 Hsub2]]]]]; 
        eauto with erased_aux.
    subst. 
    rewrite list_cons_move_app; rewrite <- unroll_t_weakening; eauto.
      rewrite <- list_cons_move_app; eauto.
  exists S S'; eauto.
  edestruct inv_unroll_t_fun 
    with (T := T) as [T1' [T2' [HT [HT1' HT2']]]]; eauto; subst.
  inversion H2; subst.
  destruct (ann_sub_ann_lclosed_t H) as [_ ?]. 
  destruct (ann_sub_ann_lclosed_t H0) as [? _]. 
  exists T1' T2'; repeat split; eauto with equiv_aux. 
Qed.

Lemma sub_unroll_t_all : forall ann_T ann_T',
  ann_sub ann_T ann_T' ->
  forall Gamma ann_U ann_U' A T,
  ctxt_okay Gamma -> 
  erased_t T ->
  ann_T = unroll_t Gamma T ->
  ann_T' = typ_all A ann_U ann_U' ->
  exists B U U',
    erased_t U /\ erased_t U' /\
    ann_sub ann_T (typ_all B (unroll_t Gamma U) (unroll_t Gamma U')) /\
    ann_sub (typ_all B (unroll_t Gamma U) (unroll_t Gamma U')) ann_T'.
Proof.
  induction 1; intros; subst; Simplify by try congruence. 
  edestruct inv_unroll_t_ftvar 
    with (Gamma := Gamma) (T := T0) 
      as [Gamma_1 [Gamma_2 [T' [HT [HGamma HT']]]]];
        eauto.
  subst.
  forwards Hokay : ctxt_okay_app H0; inversion Hokay; subst.
  edestruct IHann_sub with (Gamma := Gamma_1 ++ X ~<: T' :: Gamma_2) (T := T')
    as [B [S [S' [HS [HS' [Hsub1 Hsub2]]]]]]; eauto with erased_aux; subst. 
    rewrite list_cons_move_app; rewrite <- unroll_t_weakening; eauto.
      rewrite <- list_cons_move_app; eauto.
  exists B S S'; eauto.
  edestruct inv_unroll_t_all 
    with (T := T) as [S [S' [HT [HS HS']]]]; eauto.
  subst.
  inversion H6; subst.
  destruct (ann_sub_ann_lclosed_t H) as [_ ?].
  assert 
    (ann_lclosed_t emptyset ({A ~> X ^^ unroll_t Gamma S}unroll_t Gamma S')).
    destruct (ann_sub_ann_lclosed_t H4) as [? _].
    destruct (ann_lclosed_t_ltvar_split _ _ _ _ H10) as [I [? ?]].
    rewrite <- H14; eauto using ann_lclosed_t_subst_ltvar.
  exists A S S'; repeat split; eauto with equiv_aux. 
Qed.

Definition ann_typingLH_implies_ann_pure_typing_on n :=
  forall m ann_t ann_T, 
    m < n ->
    ann_typingLH m ann_t ann_T -> 
    forall Gamma t,
      ctxt_okay Gamma -> 
      erased_e t -> 
      ann_t = unroll_e Gamma t -> 
      exists T,
        erased_t T /\ 
        ann_pure_typingLH m (unroll_e Gamma t) (unroll_t Gamma T) /\ 
        ann_sub (unroll_t Gamma T) ann_T.

Lemma ann_pure_typingLH_implies_ann_pure_typingLH : forall m ann_t ann_T,
  ann_typingLH_implies_ann_pure_typing_on m ->
  ann_pure_typingLH m ann_t ann_T ->
  forall Gamma t,
    ctxt_okay Gamma ->
    erased_e t ->
    ann_t = unroll_e Gamma t ->
    exists T, 
      erased_t T /\ 
      ann_pure_typingLH m (unroll_e Gamma t) (unroll_t Gamma T) /\ 
      ann_sub (unroll_t Gamma T) ann_T.
Proof.
  destruct 2; intros.
  destruct (inv_unroll_e_fvar H1 H2 H3) 
    as [Gamma1 [Gamma2 [T' [He [HGamma HT']]]]]; subst.
  forwards Hokay' : ctxt_okay_app H1.
  inversion Hokay'; subst.
  exists T'. 
    repeat split; eauto with erased_aux. 
    erewrite unroll_e_fvar with (x := x); eauto.
    rewrite -> list_cons_move_app; rewrite <- unroll_t_weakening; eauto.
      rewrite <- list_cons_move_app; auto.
    rewrite -> list_cons_move_app.
    rewrite <- unroll_t_weakening; eauto with equiv_aux. 
      rewrite <- list_cons_move_app; eauto.
  edestruct inv_unroll_e_abs 
    with (t := t0) (ann_T := T) (ann_t' := t) 
      as [T' [t' [Ht0 [HT' Ht']]]]; eauto.
  subst.
  inversion H4; subst.
  set (L := dom_ec Gamma ++ FV_ee t' ++ ann_FV_ee (unroll_e Gamma t')).
  destruct (pick_fresh L) as [y Hfresh].
  unfold L in Hfresh.
  destruct H 
    with (m := k) (ann_t := unroll_e (y ~: T' :: Gamma) ({a ::~> y **} t')) 
      (ann_T := U) (Gamma := y ~: T' :: Gamma) (t := {a ::~> y **} t')
      as [U' [HU' [Htyping Hsub]]]; 
        Simplify by Destruct notIn by eauto with equiv_aux safe_inv_aux. 
    rewrite fsubst_ee_lsubst_ee_seq by eauto.
    rewrite swap_unroll_e_lsubst_ee by eauto. 
    eapply ann_typingLH_subst_lvar_rename_fvar; eauto. 
    exists (T' --> U'); repeat split; eauto.
      rewrite unroll_t_fun; rewrite unroll_e_abs.
      apply ann_pure_typingLH_abs with (x := y); eauto.
      rewrite <- swap_unroll_e_lsubst_ee. 
      rewrite <- fsubst_ee_lsubst_ee_seq; eauto.
      rewrite unroll_t_fun; eauto with equiv_aux. 
  edestruct inv_unroll_e_app 
    with (t := t0) 
      as [t1 [t2 [Ht [Ht1 Ht2]]]]; eauto; subst.
  inversion H3; subst.
  edestruct H 
    with (m := k2) (ann_t := unroll_e Gamma t2) (ann_T := T) (t := t2) 
      as [T' [HT' [HtypingT' HsubT']]]; eauto. 
    eauto with arith.
  edestruct H 
    with (m := k1) (ann_t := unroll_e Gamma t1) (ann_T := T --> U) (t := t1) 
      as [TU' [HTU' [HtypingTU' HsubTU']]]; eauto. 
    eauto with arith.
  edestruct sub_unroll_t_fun 
    with (ann_T := unroll_t Gamma TU') (ann_T' := T --> U) 
      as [T'' [U'' [HT'' [HU'' [Hsub1 Hsub2]]]]]; eauto. 
  inversion Hsub2; subst.
  exists U''; repeat split; eauto.
    rewrite unroll_e_app. 
    econstructor 3 with (T := unroll_t Gamma T'');
      eauto with equiv_aux. 
  edestruct inv_unroll_e_tabs 
    with (A := A) (t := t0) (ann_T := T) (ann_t' := t) 
      as [T' [t' [Ht [HT Ht']]]]; eauto.
  subst.
  inversion H4; subst.  
  set (L := dom_tc Gamma ++ FV_tc Gamma ++ ann_FV_tt (unroll_t Gamma T') ++ 
    ann_FV_te (unroll_e Gamma t') ++ ann_FV_tt U ++ FV_te t').
  destruct (pick_fresh L) as [Y Hfresh].
  unfold L in Hfresh.
  edestruct H 
    with (m := k) (ann_t := unroll_e (Y ~<: T' :: Gamma) ({A :~> Y ^^ } t'))
      (ann_T := {B ~> Y ^^ (unroll_t Gamma T')} U) (Gamma := Y ~<: T' :: Gamma)
      (t := { A :~> Y ^^ } t') as [U' [HU' [HU'typing HU'sub]]]; 
    Simplify by Destruct notIn by eauto with equiv_aux safe_inv_aux.
    rewrite fsubst_te_lsubst_te_seq by eauto. 
    rewrite swap_unroll_e_lsubst_te by eauto.
    apply ann_typingLH_subst_ltvar_rename_ftvar with (X := X); eauto. 
    set (L' := LV_all_tt U' ++ LV_all_tt U).
    destruct (pick_fresh L') as [C HfreshC].
    unfold L' in HfreshC.
    Destruct notIn by idtac.
    destruct typ_decompose 
      with (T := U') (A := C) (X := Y) 
        as [U'' [HU'' Hfresh']]; [eauto | subst].
    forwards HerasedU'' : erased_t_lsubst_tt_safe HU'.
    exists (typ_all C T' U''); repeat split; eauto.
      rewrite unroll_e_tabs; rewrite unroll_t_all.
      econstructor 4 with (X := Y); 
        Destruct notIn by eauto with incl_param. 
      rewrite <- swap_unroll_e_lsubst_te.
      rewrite <- unroll_t_ann_ftvar with (Gamma := Gamma) at 2.
      rewrite <- unroll_t_lsubst_tt.      
      erewrite <- fsubst_te_lsubst_te_seq with (A := A); eauto. 
      erewrite <- fsubst_tt_lsubst_tt_seq with (A := C); eauto.  
      rewrite unroll_t_all.
      econstructor 5 with (X := Y); 
        Destruct notIn by eauto with equiv_aux incl_param.
      rewrite <- unroll_t_ann_ftvar with (Gamma := Gamma) at 1.
      rewrite <- unroll_t_lsubst_tt.      
      rewrite <- fsubst_tt_lsubst_tt_seq with (A := C); eauto.
  edestruct inv_unroll_e_tapp with (t := t0) 
    as [t' [T' [Ht [Ht' HT']]]]; eauto; subst.
  inversion H3; subst.
  edestruct H 
    with (m := k) (ann_t := unroll_e Gamma t') 
      (ann_T := typ_all A U S) (t := t') 
      as [US' [HUS' [HtypingUS' HsubUS']]]; eauto.
  edestruct sub_unroll_t_all 
    with (ann_T := unroll_t Gamma US') (ann_T' := typ_all A U S)
      as [B [U' [S' [HU' [HS' [Hsub1 Hsub2]]]]]]; eauto.
  inversion Hsub2; subst.
  exists ({B ~> T'} S'); repeat split; eauto with safe_inv_aux. 
    rewrite unroll_e_tapp; rewrite unroll_t_lsubst_tt.
    apply ann_pure_typingLH_tapp with (U := (unroll_t Gamma U')).
      apply ann_typingLH_sub with (T := unroll_t Gamma US'); eauto. 
      apply ann_sub_transitivity with (U := U); eauto.
    rewrite unroll_t_lsubst_tt.
    rewrite <- subst_seq_ann_ftvar_ltvar_t 
      with (A := A) (X := X) (U := U) by eauto.
    rewrite <- subst_seq_ann_ftvar_ltvar_t 
      with (A := B) (X := X) (U := U) by eauto.
    eapply ann_sub_subst_ftvar; eauto.
Qed.

Hint Resolve ann_pure_typingLH_implies_ann_pure_typingLH : equiv_aux.

Lemma ann_typingLH_implies_ann_pure_typingLH_aux : forall m ann_t ann_T,
  ann_typingLH_implies_ann_pure_typing_on m ->
  ann_typingLH m ann_t ann_T ->
  forall Gamma t,
    ctxt_okay Gamma ->
    erased_e t ->
    ann_t = unroll_e Gamma t ->
    exists T,
      erased_t T /\ 
      ann_pure_typingLH m (unroll_e Gamma t) (unroll_t Gamma T) /\ 
      ann_sub (unroll_t Gamma T) ann_T.
Proof.
  induction 2; intros; eauto with equiv_aux. 
  edestruct IHann_typingLH 
    with (Gamma := Gamma) (t0 := t0) as [T' [HT' [Htyping Hsub]]]; eauto.
    exists T'; eauto with equiv_aux. 
Qed.

Lemma ann_typingLH_implies_ann_pure_typingLH_ind : forall n m ann_t ann_T,
  m < n -> 
  ann_typingLH m ann_t ann_T ->
  forall Gamma t,
    ctxt_okay Gamma -> 
    erased_e t -> 
    ann_t = unroll_e Gamma t ->
    exists T,
      erased_t T /\ 
      ann_pure_typingLH m (unroll_e Gamma t) (unroll_t Gamma T) /\ 
      ann_sub (unroll_t Gamma T) ann_T.
Proof.
  induction n; intros.
  firstorder using lt_n_O.
  eapply ann_typingLH_implies_ann_pure_typingLH_aux; eauto.
    unfold ann_typingLH_implies_ann_pure_typing_on; eauto with arith.
Qed.

Hint Resolve ann_typingLH_implies_ann_pure_typingLH_ind : equiv_aux.

Lemma ann_typingLH_implies_ann_pure_typingLH : forall m ann_t ann_T,
  ann_typingLH m ann_t ann_T ->
  forall Gamma t,
    ctxt_okay Gamma -> 
    erased_e t-> 
    ann_t = unroll_e Gamma t ->
    exists T,
      erased_t T /\ 
      ann_pure_typingLH m (unroll_e Gamma t) (unroll_t Gamma T) /\ 
      ann_sub (unroll_t Gamma T) ann_T.
Proof.
  eauto with equiv_aux. 
Qed.

(** We then prove Lemma [ann_typing_implies_typing] which states the 
 if part of the equivalence statement. 

 Lemma [ann_typingLH_implies_ann_pure_typingLH] allows us to deal with
 incompatible types since we can use their compatible super type. *)
Definition ann_typingLH_implies_typing_on n :=
  forall m ann_t ann_T,
    m < n -> 
    ann_typingLH m ann_t ann_T ->
    forall Gamma t T,
      ctxt_okay Gamma -> 
      erased_e t -> 
      erased_t T ->
      ann_t = unroll_e Gamma t ->
      ann_T = unroll_t Gamma T ->
      typing Gamma t T.

Lemma ann_pure_typingLH_implies_typing : forall n ann_t ann_T,
  ann_typingLH_implies_typing_on n ->
  ann_pure_typingLH n ann_t ann_T ->
  forall Gamma t T,
    ctxt_okay Gamma -> 
    erased_e t -> 
    erased_t T ->
    ann_t = unroll_e Gamma t ->
    ann_T = unroll_t Gamma T ->
    typing Gamma t T.
Proof.
  destruct 2; intros; subst.
  destruct (inv_unroll_e_fvar H1 H2 H4) 
    as [Gamma1 [Gamma2 [T' [Ht [HGamma HT']]]]]; subst.
  forwards Hokay' : ctxt_okay_app H1.
  inversion Hokay'; subst.
  assert (T0 = T'); [ | subst].
    eapply unroll_t_inv with (Gamma := Gamma1 ++ x ~: T' :: Gamma2); 
      eauto with erased_aux. 
    erewrite list_cons_move_app with (l := Gamma1) at 2.
    erewrite <- unroll_t_weakening 
      with (Gamma1 := Gamma1 ++ x ~: T' :: emptyset); eauto.
      rewrite <- list_cons_move_app; eauto. 
  econstructor; Destruct In by eauto.
  edestruct inv_unroll_t_fun with (T := T0) as [T' [U' [HT [HT' HU']]]]; 
    eauto; subst.
  edestruct inv_unroll_e_abs with (t := t0) as [T'' [t' [Ht0 [HT'' Ht']]]]; 
    eauto. 
  subst.
  inversion H4; inversion H5; subst.
  assert (T' = T'') by eauto using unroll_t_inv; subst.  
  destruct (pick_fresh (dom_ec Gamma ++ FV_ee t')) as [y Hfresh].
  econstructor 2 with (x := y); 
    Destruct notIn by eauto with equiv_aux. 
  eapply H with (m := k) 
    (ann_t := unroll_e (y ~: T'' :: Gamma) ({ a ::~> y ** } t'))
    (t := { a ::~> y **} t') (T := U'); 
    simple; eauto with equiv_aux safe_inv_aux arith. 
    rewrite fsubst_ee_lsubst_ee_seq by eauto.
    rewrite swap_unroll_e_lsubst_ee.
    eapply ann_typingLH_subst_lvar_rename_fvar; eauto.
  edestruct inv_unroll_e_app 
    with (t := t0) as [t1 [t2 [Ht [Ht1 Ht2]]]]; eauto; subst.
  inversion H3; subst.
  edestruct ann_typingLH_implies_ann_pure_typingLH
    with (m := k1) (ann_t := unroll_e Gamma t1) 
      (ann_T := T --> unroll_t Gamma T0) (t := t1)
      as [TU [HTU [HTUtyping HTUsub]]]; eauto.
  edestruct sub_unroll_t_fun 
    with (ann_T := unroll_t Gamma TU) (ann_T' := T --> unroll_t Gamma T0)
      as [T' [U' [HT' [HU' [Hsub1 Hsub2]]]]]; eauto.
  edestruct ann_typingLH_implies_ann_pure_typingLH
    with (m := k2) (ann_t := unroll_e Gamma t2) (ann_T := T) (t := t2)
      as [T'' [HT'' [HT''typing HT''sub]]]; eauto.
  inversion Hsub2; subst.
  apply typing_sub with (T := U'); eauto with equiv_aux. 
  apply typing_app with (T := T').
    eapply H with (m := k1) (ann_t := unroll_e Gamma t1) 
      (ann_T := unroll_t Gamma T' --> unroll_t Gamma U'); eauto with arith.
      rewrite unroll_t_fun; eauto.
    apply typing_sub with (T := T''); eauto with equiv_aux.
    eapply H with (m := k2) 
      (ann_t := unroll_e Gamma t2) (ann_T := unroll_t Gamma T'');
      eauto with arith. 
  edestruct inv_unroll_t_all 
    with (T := T0) as [T' [U' [HT [HT' HU']]]]; eauto.
  subst.
  edestruct inv_unroll_e_tabs 
    with (t := t0) as [T'' [t' [Ht0 [HT'' Ht']]]]; eauto.
  subst.
  inversion H4; subst.
  inversion H5; subst.
  assert (T' = T'') by eauto using unroll_t_inv; subst.
  set (L := dom_tc Gamma ++ FV_tc Gamma ++ FV_te t' ++ FV_tt U').
  destruct (pick_fresh L) as [Y Hfresh].
  unfold L in Hfresh.
  apply typing_tabs with (X := Y); Destruct notIn by eauto with equiv_aux. 
  eapply H 
    with (m := k) (ann_t := unroll_e (Y ~<: T'' :: Gamma) ({A :~> Y ^^} t')) 
      (ann_T := unroll_t (Y ~<: T'' :: Gamma) ({B ~> Y ^^} U')); 
    simpl; eauto with safe_inv_aux equiv_aux arith.
    rewrite fsubst_te_lsubst_te_seq by eauto.
    rewrite fsubst_tt_lsubst_tt_seq by eauto.
    rewrite swap_unroll_e_lsubst_te.
    rewrite unroll_t_lsubst_tt.      
    rewrite unroll_t_ann_ftvar.
    eapply ann_typingLH_subst_ltvar_rename_ftvar with (X := X); eauto.
  edestruct inv_unroll_e_tapp 
    with (t := t0) as [t' [T' [Ht [Ht' HT']]]]; eauto; subst.
  inversion H3; subst.
  edestruct ann_typingLH_implies_ann_pure_typingLH
    with (m := k) (ann_t := unroll_e Gamma t') (ann_T := typ_all A U S) 
      as [US [HUS [HUStyping HUSsub]]]; eauto.
  edestruct sub_unroll_t_all 
    with (ann_T := unroll_t Gamma US) (ann_T' := typ_all A U S)
      as [B [U' [S' [HU' [HS' [Hsub1 Hsub2]]]]]]; eauto.
  inversion Hsub2; subst.
  apply typing_sub with (T := {B ~> T'} S').
    apply typing_tapp with (T' := U'); eauto with equiv_aux.
      eapply H with (m := k) (ann_t := unroll_e Gamma t') 
        (ann_T := typ_all B (unroll_t Gamma U') (unroll_t Gamma S')); eauto.
        rewrite unroll_t_all; eauto.
    apply ann_sub_implies_sub; eauto with safe_inv_aux. 
      rewrite unroll_t_lsubst_tt; rewrite <- H6.
      set (L := ann_FV_tt (unroll_t Gamma S') ++ ann_FV_tt S ++ 
                 FV_tc Gamma ++ FV_tt T' ++ FV_tt S').
      destruct (pick_fresh L) as [Y Hfresh].
      unfold L in Hfresh.
      Destruct notIn by idtac.
      rewrite <- subst_seq_ann_ftvar_ltvar_t 
        with (A := A) (X := Y) (U := U) by eauto.
      rewrite <- subst_seq_ann_ftvar_ltvar_t 
        with (A := B) (X := Y) (U := U) by eauto.
      apply ann_sub_subst_ftvar; eauto.
      apply ann_sub_ltvar_subst_rename_ftvar with (X := X); eauto.
Qed.

Lemma ann_typingLH_implies_typing : forall n m ann_t ann_T,
  m < n -> 
  ann_typingLH m ann_t ann_T ->
  forall Gamma t T,
    ctxt_okay Gamma -> 
    erased_e t -> 
    erased_t T ->
    ann_t = unroll_e Gamma t ->
    ann_T = unroll_t Gamma T ->
    typing Gamma t T.
Proof.
  induction n; intros; subst.
  firstorder using lt_n_O.
  destruct (ann_typingLH_implies_ann_pure_typingLH H0 H1 H2) 
    as [T' [Herased [Htyping Hsub]]]; eauto.
  apply typing_sub with (T := T'); eauto with equiv_aux. 
  eapply ann_pure_typingLH_implies_typing 
    with (n := m) (ann_t := (unroll_e Gamma t)) 
      (ann_T := (unroll_t Gamma T')); eauto.
  unfold ann_typingLH_implies_typing_on; intros. 
  eapply IHn; eauto with arith.
Qed.
  
Lemma ann_typing_implies_typing : forall Gamma t T,
  ctxt_okay Gamma -> 
  erased_e t -> 
  erased_t T ->
  ann_typing (unroll_e Gamma t) (unroll_t Gamma T) ->
  typing Gamma t T.
Proof.
  intros.
  destruct (ann_typing_implies_ann_typingLH H2) as [n Htyping].
  eapply ann_typingLH_implies_typing with (n := S n) (m := n); 
    eauto with arith.
Qed.
