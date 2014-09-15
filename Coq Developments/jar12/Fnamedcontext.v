(** This file presents an exist-fresh style mechanization of System Fsub 
 with contexts using locally named representation. 
 - Authors: Jonghyun Park, Sungwoo Park, and Gyesik Lee *)

Set Implicit Arguments.

(** We import a number of definitions from libraries *)
Require Import List Arith Max. 
Require Import LibTactics LibNat.

(* *************************************************************** *)
(** * Contents
 - Syntax 
 - Parameters
 - Substitution
 - Typing contexts
 - Local closure
 - Well-formed typing contexts
 - Subtyping relation
 - Typing relation
 - Values and evaluation
 - Tactical support
 - Challenge 1A: Transitivity of Subtyping
 - Challenge 2A: Type Safety
 *)
(* *************************************************************** *)

(* *************************************************************** *)
(** * Syntax 
 Both variables and parameters are represented as natural numbers. 
 Since we use locally named representation, they are treated as 
 distinct atoms. *)
Notation ltvar := nat.   (* type variable *) 
Notation ftvar := nat.   (* type parameter *)

Notation lvar := nat.    (* term variable *)
Notation fvar := nat.    (* term parameter *)  

(**  We use the following definition of types and terms:
<< 
 types T, U, S := \top | A | X <: T | T -> U | \forall A <: T. U 
 terms t, u, s := a | x : T | \lambda a : T. t | t u | \Lambda A <: T. t | t [ T ] 
>> 
 We use the following notations for variables and parameters:
  - type variables  A, B, C 
  - type parameters X, Y, Z
  - term variables  a, b, c
  - term parameters x, y, z *)
Inductive typ : Set :=
| typ_top   : typ
| typ_ltvar : ltvar -> typ
| typ_ftvar : ftvar -> typ
| typ_arrow : typ -> typ -> typ
| typ_all   : ltvar -> typ -> typ -> typ.

Inductive tm : Set :=
| tm_lvar : lvar -> tm
| tm_fvar : fvar -> tm
| tm_abs  : lvar -> typ -> tm -> tm
| tm_app  : tm -> tm -> tm
| tm_tabs : ltvar -> typ -> tm -> tm
| tm_tapp : tm -> typ -> tm.

Notation " X ^^ " := (typ_ftvar X) (at level 65). 
Notation " T --> U " := (typ_arrow T U) (at level 65).

Notation " x ** " := (tm_fvar x) (at level 55).
(* *************************************************************** *)

(* *************************************************************** *)
(** * Parameters
 ** Type parameters
 The functions [FV_tt] and [FV_te], defined below, calculate 
 the set of type parameters in a type and a term, respectively. 
 Locally named representation makes the [typ_all] case for [FV_tt] 
 and the [tm_tabs] case for [FV_te] simple because variables and 
 parameters are syntactically distinct. *)
Fixpoint FV_tt (T:typ) : list ftvar :=
  match T with
    | typ_top       => nil
    | typ_ltvar _   => nil
    | X ^^          => X :: nil
    | T --> U       => FV_tt T ++ FV_tt U
    | typ_all _ T U => FV_tt T ++ FV_tt U
  end.

Fixpoint FV_te (t : tm) : list ftvar :=
  match t with
    | tm_lvar _     => nil 
    | tm_fvar _     => nil
    | tm_abs _ T t  => FV_tt T ++ FV_te t
    | tm_app t t'   => FV_te t ++ FV_te t'
    | tm_tabs _ T t => FV_tt T ++ FV_te t 
    | tm_tapp t T   => FV_te t ++ FV_tt T
  end.

(** ** Term parameters
 The function [FV_ee], defined below, calculates the set of term 
 parameters in a term. Locally named representation also makes 
 the [tm_abs] case simple for the same reason. *)
Fixpoint FV_ee (t : tm) : list fvar :=
  match t with
    | tm_lvar _     => nil 
    | tm_fvar X     => X :: nil
    | tm_abs _ T t  => FV_ee t
    | tm_app t t'   => FV_ee t ++ FV_ee t'
    | tm_tabs _ _ t => FV_ee t
    | tm_tapp t _   => FV_ee t
  end.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Substitution *)
(** ** Type variables 
 The functions [lsubst_tt] and [lsubst_te], defined below, replace
 a type variable with a type for types and terms, respectively. 
 Since we use names to represent a type variables, these functions
 check the equality between variables for the [typ_all] case 
 (for [lsubst_tt]) and the [tm_tabs] case (for [lsubst_te]). *)
Fixpoint lsubst_tt (B : ltvar) (U : typ) (T : typ) {struct T} : typ :=
  match T with
    | typ_top         => typ_top
    | typ_ltvar A     => if A == B then U else typ_ltvar A
    | X ^^            => X ^^
    | T1 --> T2       => typ_arrow (lsubst_tt B U T1) (lsubst_tt B U T2)
    | typ_all A T1 T2 => 
      if A == B then typ_all A (lsubst_tt B U T1) T2 
        else typ_all A (lsubst_tt B U T1) (lsubst_tt B U T2)
  end.

Fixpoint lsubst_te (B : ltvar) (U : typ)  (t : tm) {struct t} : tm :=
  match t with
    | tm_lvar a     => tm_lvar a
    | tm_fvar X     => tm_fvar X 
    | tm_abs a T t  => tm_abs a (lsubst_tt B U T) (lsubst_te B U t) 
    | tm_app t1 t2  => tm_app (lsubst_te B U t1) (lsubst_te B U t2) 
    | tm_tabs A T t => 
      if A == B then tm_tabs A (lsubst_tt B U T) t
        else tm_tabs A (lsubst_tt B U T) (lsubst_te B U t) 
    | tm_tapp t T   => tm_tapp (lsubst_te B U t) (lsubst_tt B U T) 
  end.

(** ** Term variables
 The function [lsubst_ee], defined below, replaces a term variable 
 with a term. Note that the [tm_abs] case also checks the equality
 between variables. *)
Fixpoint lsubst_ee (b : lvar) (u : tm) (t : tm) {struct t} : tm :=
  match t with
    | tm_lvar a     => if a == b then u else tm_lvar a
    | tm_fvar X     => tm_fvar X
    | tm_abs a T t  => 
      if a == b then tm_abs a T t else tm_abs a T (lsubst_ee b u t)
    | tm_app t1 t2  => tm_app (lsubst_ee b u t1) (lsubst_ee b u t2)
    | tm_tabs A T t => tm_tabs A T (lsubst_ee b u t)
    | tm_tapp t T   => tm_tapp (lsubst_ee b u t) T
  end.

(** ** Type parameters 
 The functions [fsubst_tt] and [fsubst_te], defined below, replace
 a type parameter with a type. Note that locally named representation
 makes the [typ_all] case (for [fsubst_tt]) and the [tm_tabs] case
 (for [fsubst_te]) simple. *)
Fixpoint fsubst_tt (Y:ftvar) (U : typ) (T : typ) {struct T} : typ :=
  match T with
    | typ_top         => typ_top
    | typ_ltvar A     => typ_ltvar A
    | X ^^            => if X == Y then U else X ^^
    | T1 --> T2       => (fsubst_tt Y U T1) --> (fsubst_tt Y U T2)
    | typ_all A T1 T2 => typ_all A (fsubst_tt Y U T1) (fsubst_tt Y U T2)
  end.

Fixpoint fsubst_te (Y:ftvar) (U:typ) (t:tm) {struct t} : tm :=
  match t with
    | tm_lvar a     => tm_lvar a
    | tm_fvar X     => tm_fvar X
    | tm_abs a T t  => tm_abs a (fsubst_tt Y U T) (fsubst_te Y U t)
    | tm_app t1 t2  => tm_app (fsubst_te Y U t1) (fsubst_te Y U t2)
    | tm_tabs A T t => tm_tabs A (fsubst_tt Y U T) (fsubst_te Y U t)
    | tm_tapp t T   => tm_tapp (fsubst_te Y U t) (fsubst_tt Y U T)
  end.

(** ** Term parameters
 The function [fsubst_ee], defined below, replaces a type parameter 
 with a term. Locally named representation makes the [tm_abs] case 
 simple. *)
Fixpoint fsubst_ee (y : fvar) (u t: tm) {struct t} : tm :=
  match t with
    | tm_lvar a     => tm_lvar a
    | tm_fvar x     => if x == y then u else tm_fvar x
    | tm_abs a T t  => tm_abs a T (fsubst_ee y u t)
    | tm_app t1 t2  => tm_app (fsubst_ee y u t1) (fsubst_ee y u t2)
    | tm_tabs A T t => tm_tabs A T (fsubst_ee y u t)
    | tm_tapp t T   => tm_tapp (fsubst_ee y u t) T
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
(* *************************************************************** *)

(* *************************************************************** *)
(** * Typing contexts 
 A typing context records specific properties of parameters which 
 eventually originate from binders. We refer to each record as 
 binding. Since there are two kinds of binders, there are two 
 kinds of bindings. *)
Inductive ctxt_bind : Set :=
| ctxt_bind_fvar : fvar -> typ -> ctxt_bind
| ctxt_bind_ftvar : ftvar -> typ -> ctxt_bind.

(** A typing context is a list of these bindings *)
Notation ctxt := (list ctxt_bind).   

(** X ~<: T denotes a type binding, and x ~: T denotes a term binding. *)
Notation " X ~<: T " := (ctxt_bind_ftvar X T) (at level 56).
Notation " x ~: T " := (ctxt_bind_fvar x T) (at level 56).

(** ** Parameters
 The function [dom_tc], defined below, calculates the set of type 
 parameters bound in a typing context. *)
Fixpoint dom_tc (Gamma : ctxt) : list ftvar :=
  match Gamma with
  | nil                            => nil 
  | (ctxt_bind_fvar x T) :: Gamma  => dom_tc Gamma
  | (ctxt_bind_ftvar X T) :: Gamma => X :: dom_tc Gamma
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

(** The function [dom_ec], defined below, calculates the set of term 
 parameters bound in a typing context. *)
Fixpoint dom_ec (Gamma : ctxt) : list fvar :=
  match Gamma with
  | nil                            => nil 
  | (ctxt_bind_fvar x T) :: Gamma  => x :: dom_ec Gamma
  | (ctxt_bind_ftvar X T) :: Gamma => dom_ec Gamma
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

(** The function [FV_tc], defined below, calculates the set of all type 
 parameters that appear in a typing context. *)
Fixpoint FV_tc (Gamma : ctxt) : list ftvar :=
  match Gamma with
  | nil                            => nil 
  | (ctxt_bind_fvar x T) :: Gamma  => FV_tt T ++ FV_tc Gamma
  | (ctxt_bind_ftvar X T) :: Gamma => X :: (FV_tt T ++ FV_tc Gamma)
end.

(** Thus, [FV_tc Gamma] includes all the type parameters in [dom_tc Gamma]. *)
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
(** ** Renaming & Substitution
 There are two operations on typing contexts
  - Renaming 
  - Substitution
 We refer to an operation on typing contexts that replaces all the occurrence 
 of a specific (either type or term) parameter with another parameter of the 
 same kind as "renaming", and an operation on typing contexts that replaces 
 all the occurrence of a specific parameter in the type of each typing binding 
 with a type as "substitution".

 Note the difference between renaming and substitution. Renaming [X] into
 [Y] on [[X ~<: Y ^^; Y ~<: X ^^]] results in [[Y ~<: Y ^^; Y ~<: X ^^]], 
 while substituting [X] into [Y ^^] on the same typing context results in 
 [[X ~<: Y ^^; Y ~<: Y ^^]].

 *** Type parameter renaming
 [ctxt_ftvar_rename_map X Y Gamma] denotes a renaming of a type parameter [X]
 into another type parameter [Y] on a typing context [Gamma]. *)
Definition ctxt_ftvar_rename Y Z (bind:ctxt_bind) :=
  match bind with
    | ctxt_bind_fvar x T => ctxt_bind_fvar x ([Y ~> Z ^^] T)
    | ctxt_bind_ftvar X T =>
      if X == Y then ctxt_bind_ftvar Z ([Y ~> Z ^^] T) 
        else ctxt_bind_ftvar X ([Y ~> Z ^^] T)
  end.

Definition ctxt_ftvar_rename_map Gamma X Y := 
  map (ctxt_ftvar_rename X Y) Gamma.

Notation "[ X => Y ] Gamma " := 
  (ctxt_ftvar_rename_map Gamma X Y) (at level 67).

(** *** Term parameter renaming
 [ctxt_fvar_rename_map x y Gamma] denotes a renaming of a term parameter [x]
 into another term parameter [y] on a typing context [Gamma]. *)
Definition ctxt_fvar_rename y z (bind:ctxt_bind) :=
  match bind with
    | ctxt_bind_fvar x T  => 
      if x == y then ctxt_bind_fvar z T else ctxt_bind_fvar x T
    | ctxt_bind_ftvar X T => ctxt_bind_ftvar X T
  end.

Definition ctxt_fvar_rename_map Gamma x y := 
  map (ctxt_fvar_rename x y) Gamma.

Notation "[ x ::=> y ] Gamma " :=
  (ctxt_fvar_rename_map Gamma x y) (at level 67).

(** *** Type parameter substitution
 [ctxt_ftvar_subst_map X T Gamma] denotes a substitution of a type parameter 
 [X] into a type [T] on a typing context [Gamma]. *)
Definition ctxt_ftvar_subst Y U (bind:ctxt_bind) :=
  match bind with
    | ctxt_bind_fvar  x T => ctxt_bind_fvar  x ([Y ~> U] T)
    | ctxt_bind_ftvar X T => ctxt_bind_ftvar X ([Y ~> U] T)
  end.

Definition ctxt_ftvar_subst_map Gamma X T := 
  map (ctxt_ftvar_subst X T) Gamma.

Notation "[ X ==> T ] Gamma " :=
  (ctxt_ftvar_subst_map Gamma X T) (at level 67).
(* *************************************************************** *)

(* *************************************************************** *)
(** * Local closure
 A type (or term) is said to be locally closed if every type (and term) 
 variable has a corresponding binder. To formalize local closure of types 
 and terms, we introduce two inductive definitions [lclosed_t] and 
 [lclosed_e] for types and terms, respectively. 

 ** Local closure of types
 For a typing context [Gamma] and a type variable set [I], 
 [lclosed_t Gamma I T] holds if [I] is a set of all the unbounded type 
 variable in [T], and every type parameter is bound in [Gamma]. Thus, 
 a type [T] is locally closed if it has a typing context [Gamma] such 
 that [lclosed_t Gamma emptyset T] holds. *)
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

(** ** Local closure of terms
 For a typing context [Gamma], a type variable set [I], a term variable set [i],
 [lclosed_e Gamma I i t] holds if [I] and [i] are sets of all the unbound
 type and term variable in [t], respectively, and every parameter is bound in 
 [Gamma]. Thus, a term [t] is locally closed if it has a typing context [Gamma] 
 such that [lclosed_e Gamma emptyset emptyset t] holds. *)
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
(* *************************************************************** *)

(* *************************************************************** *)
(** * Well-formed typing contexts 
 We say that a typing context is well-formed if every type contained 
 within are well-formed w.r.t its corresponding typing contexts, and
 every parameter is distinct. *)
Inductive ctxt_okay : ctxt -> Prop :=
| ctxt_okay_nil  : ctxt_okay nil 
| ctxt_okay_epar : forall Gamma x T,
  ctxt_okay Gamma ->
  ~ In x (dom_ec Gamma) ->
  lclosed_t Gamma emptyset T ->
  ctxt_okay (x ~: T :: Gamma)
| ctxt_okay_tpar : forall Gamma X T, 
  ctxt_okay Gamma ->
  ~ In X (dom_tc Gamma) ->
  lclosed_t Gamma emptyset T ->
  ctxt_okay (X ~<: T :: Gamma).

Hint Constructors ctxt_okay.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Subtyping relation 
 It is straightforward to define the subtyping relation. The [sub_top] 
 and [sub_refl_tvar] cases require types to be locally closed, and
 typing contexts to be well-formed. This implies that the subtyping 
 relation holds only for locally closed types under well-formed typing 
 contexts. Note the use of the exist-fresh style in the [sub_all] case. *)
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

(** ** Subtyping relation with sizes 
 We formally define the size of proofs using the inductive definition 
 [subLH]. If [subLH n Gamma T U] holds, it means that there is a proof of 
 [sub Gamma T U] whose size is [n]. Note that the definition of [subLH] is 
 the same as [sub] except the annotated size.

 Lemma [sub_subLH] and [subLH_sub] formally state the equivalence 
 between [sub] and [subLH]. *)
Inductive subLH : nat -> ctxt -> typ -> typ -> Prop :=
| subLH_top        : forall Gamma T, 
  ctxt_okay Gamma -> 
  lclosed_t Gamma emptyset T -> 
  subLH O Gamma T typ_top
| subLH_refl_tvar  : forall Gamma X,
  ctxt_okay Gamma -> 
  lclosed_t Gamma emptyset (X ^^) ->
  subLH O Gamma (X ^^) (X ^^)
| subLH_trans_tvar : forall Gamma T U X n,
  In (X ~<: T) Gamma -> 
  subLH n Gamma T U -> 
  subLH (S n) Gamma (X ^^) U
| subLH_arrow      : forall Gamma T1 T2 U1 U2 n1 n2,
  subLH n1 Gamma U1 T1 ->
  subLH n2 Gamma T2 U2 ->
  subLH (S (max n1 n2)) Gamma (T1 --> T2) (U1 --> U2)
| subLH_all        : forall Gamma T1 T2 U1 U2 X A B n1 n2,
  subLH n1 Gamma U1 T1 ->
  ~ In X (FV_tc Gamma) ->
  ~ In X (FV_tt T2 ++ FV_tt U2) -> 
  subLH n2 (X ~<: U1 :: Gamma) ({A ~> X ^^} T2) ({B ~> X ^^} U2) ->
  subLH (S (max n1 n2)) Gamma (typ_all A T1 T2) (typ_all B U1 U2). 

Hint Constructors subLH.

Lemma sub_subLH : forall T U Gamma,
  sub Gamma T U -> 
  exists n, subLH n Gamma T U.
Proof.
  induction 1; eauto.
  inversion IHsub as [k ?].
  exists (S k); eauto.
  inversion IHsub1 as [n1 ?]; inversion IHsub2 as [n2 ?].
  exists (S (max n1 n2)); eauto.
  inversion IHsub1 as [n1 ?]; inversion IHsub2 as [n2 ?].
  exists (S (max n1 n2)); eauto.
Qed.

Lemma subLH_sub : forall T U n Gamma,
  subLH n Gamma T U -> sub Gamma T U.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve sub_subLH subLH_sub.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Typing relation 
 It is also straightforward to define the typing relation. The 
 [typing_fvar] case requires typing contexts to be well-formed,
 which implies that the typing relation holds only for well-formed 
 typing contexts. The [typing_fvar] case also requires term binding
 [x ~: T] to be in a well-formed typing context, which implies the
 typing relation holds only for locally closed types (We will formally 
 prove this later). Note the use of the exist-fresh 
 style in the [typing_abs] and [typing_tabs] cases. *)
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
  typing (X ~<: T :: Gamma) ({A :~> X ^^} t) ({B ~> X ^^} U) -> 
  typing Gamma (tm_tabs A T t) (typ_all B T U)
| typing_tapp : forall Gamma t A T T' U,
  typing Gamma t (typ_all A T' U) -> 
  sub Gamma T T' -> 
  typing Gamma (tm_tapp t T) ({A ~> T} U)
| typing_sub : forall Gamma t T U,
  typing Gamma t T -> 
  sub Gamma T U -> 
  typing Gamma t U.

Hint Constructors typing.

(** ** Typing relation with sizes 
 We formally define the size of proofs using the inductive definition 
 [typingLH]. If [typingLH n Gamma t T] holds, it means that there is a 
 proof of [typing Gamma t T] whose size is [n]. Note that the definition 
 of [typingLH] is the same as [typing] except the annotated size.

 Lemma [typing_typingLH] and [typingLH_typing] formally state the equivalence 
 between [typing] and [typingLH]. *)
Inductive typingLH : nat -> ctxt -> tm -> typ -> Prop :=
| typing_fvarLH : forall Gamma x T,
  ctxt_okay Gamma ->
  In (x ~: T) Gamma ->
  typingLH O Gamma (x **) T
| typing_absLH  : forall Gamma x T U t a k,
  lclosed_t Gamma emptyset T ->
  ~ In x (dom_ec Gamma) -> 
  ~ In x (FV_ee t) ->
  typingLH k (x ~: T :: Gamma) ({a ::~> x **} t) U ->
  typingLH (S k) Gamma (tm_abs a T t) (T --> U)
| typing_appLH  : forall Gamma t t' T U k1 k2,
  typingLH k1 Gamma t (T --> U) -> 
  typingLH k2 Gamma t' T -> 
  typingLH (S (max k1 k2)) Gamma (tm_app t t') U
| typing_tabsLH : forall Gamma A T t B U X k,
  lclosed_t Gamma emptyset T -> 
  ~ In X (FV_tc Gamma) -> 
  ~ In X (FV_te t ++ FV_tt U) -> 
  typingLH k (X ~<: T :: Gamma) ({A :~> X ^^} t) ({B ~> X ^^} U) -> 
  typingLH (S k) Gamma (tm_tabs A T t) (typ_all B T U)
| typing_tappLH : forall Gamma t A T U S k,
  typingLH k Gamma t (typ_all A U S) -> 
  sub Gamma T U -> 
  typingLH (Datatypes.S k) Gamma (tm_tapp t T) ({A ~> T} S)
| typing_subLH  : forall Gamma t T U k,
  typingLH k Gamma t T 
  -> sub Gamma T U
  -> typingLH (S k) Gamma t U.

Hint Constructors typingLH.

Lemma typing_typingLH : forall t T Gamma,
  typing Gamma t T -> 
  exists n, typingLH n Gamma t T.
Proof.
  induction 1; eauto.
  inversion IHtyping as [k ?].
  exists (S k); eauto.
  inversion IHtyping1 as [k1 ?]; inversion IHtyping2 as [k2 ?].
  exists (S (max k1 k2)); eauto.
  inversion IHtyping as [k ?].
  exists (S k); eauto.
  inversion IHtyping as [k ?].
  exists (S k); eauto.
  inversion IHtyping as [k ?].
  exists (S k); eauto.
Qed.

Lemma typingLH_typing : forall t T n Gamma,
  typingLH n Gamma t T -> 
  typing Gamma t T.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve typing_typingLH typingLH_typing.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Values and evaluation 
 To state the preservation lemma, we first need to define values 
 and the small-step evaluation relation. These inductive relations 
 are straightforward to define. *)
Inductive value : tm -> Prop :=
| value_abs  : forall a T t, value (tm_abs a T t)
| value_tabs : forall A T t, value (tm_tabs A T t).

Inductive red : tm -> tm -> Prop :=
| red_app_1 : forall t1 t1' t2,
  red t1 t1' ->
    red (tm_app t1 t2) (tm_app t1' t2)
| red_app_2 : forall t1 t2 t2',
  value t1 ->
  red t2 t2' ->
    red (tm_app t1 t2) (tm_app t1 t2')
| red_abs   : forall a T t u,
  value u -> 
  red (tm_app (tm_abs a T t) u) ({a ::~> u} t)
| red_tapp  : forall t t' T,
  red t t' ->
    red (tm_tapp t T) (tm_tapp t' T)
| red_tabs  : forall A T U t,
  red (tm_tapp (tm_tabs A T t) U) ({A :~> U} t).

Hint Constructors red.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Tactical support 
 We introduce an automation tactic [Simplify] to simplify the proof.
 [Simplify] attempts to evaluate several fixpoint functions, such as 
 [FV_tt] and [lsubst_tt], as much as possible. This simplification is 
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
    | typ_arrow _ _ => idtac
    | typ_all _ _ _ => idtac
    | _ => fail
  end 
with filter_e e :=
  match e with
    | tm_lvar _ => idtac
    | tm_fvar _ => idtac
    | tm_abs _ _ _ => idtac
    | tm_app _ _ => idtac
    | tm_tabs _ _ _ => idtac
    | tm_tapp _ _ => idtac
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
    | ?b :: _ => filter_b b
    | _ => fail
  end 
with filter_var_t C :=
  match C with
    | FV_tt => idtac
    | _ => idtac
  end
with filter_var_e C :=
  match C with
    | FV_te => idtac
    | FV_ee => idtac
    | _ => idtac
  end
with filter_var_b C :=
  match C with
    | dom_tc => idtac
    | dom_ec => idtac
    | FV_tc => idtac
    | _ => fail
  end
with filter_subst_t S :=
  match S with
    | lsubst_tt => idtac
    | fsubst_tt => idtac
    | _ => fail
  end
with filter_subst_e S :=
  match S with
    | lsubst_te => idtac
    | lsubst_ee => idtac
    | fsubst_te => idtac
    | fsubst_ee => idtac
    | _ => fail
  end
with filter_subst_m S :=
  match S with
    | ctxt_ftvar_rename_map => idtac
    | ctxt_fvar_rename_map => idtac
    | ctxt_ftvar_subst_map => idtac
    | _ => fail
  end
with filter_subst_b S :=
  match S with
    | ctxt_ftvar_rename => idtac
    | ctxt_fvar_rename => idtac
    | ctxt_ftvar_subst => idtac
    | _ => fail
  end in
  match goal with
    | H: ?X = ?X |- _ => clear H; simplifyTac tac
    | H: ?X <> ?X |- _ => try congruence
    | H: context [?X == ?Y] |- _ => 
      destruct (X == Y); [ try subst X | idtac ]; simplifyTac tac
    | |- context [?X == ?Y]      => 
      destruct (X == Y); [ try subst X | idtac ]; simplifyTac tac
    | H: context[ remove _ _ ?l ] |- _ =>
      filter_list l; simpl remove in H; simplifyTac tac
    | H: context[ ?m ?Gamma _ _ ] |- _ =>
      filter_subst_m m; filter_C Gamma; simpl m in H; simplifyTac tac
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
    | H : context[ ?C ?t ] |- _ =>
      filter_var_t C; filter_t t; simpl C in H; simplifyTac tac
    | H : context[ ?C ?e ] |- _ =>
      filter_var_e C; filter_e e; simpl C in H; simplifyTac tac
    | H : context[ ?S _ _ ?t ] |- _ =>
      filter_subst_t S; filter_t t; simpl S in H; simplifyTac tac
    | H : context[ ?S _ _ ?e ] |- _ =>
      filter_subst_e S; filter_e e; simpl S in H; simplifyTac tac
    | H : context[ ?S _ _ ?b ] |- _ =>
      filter_subst_b S; filter_b b; simpl S in H; simplifyTac tac
    | |- context[ remove _ _ ?l ] =>
      filter_list l; simpl remove; simplifyTac tac
    | |- context[ ?m ?Gamma _ _ ] =>
      filter_subst_m m; filter_C Gamma; simpl m; simplifyTac tac
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
    | |- context[ ?C ?t ] =>
      filter_var_t C; filter_t t; simpl C; simplifyTac tac
    | |- context[ ?C ?e ] =>
      filter_var_e C; filter_e e; simpl C; simplifyTac tac
    | |- context[ ?S _ _ ?t ] =>
      filter_subst_t S; filter_t t; simpl S; simplifyTac tac
    | |- context[ ?S _ _ ?e ] =>
      filter_subst_e S; filter_e e; simpl S; simplifyTac tac
    | |- context[ ?S _ _ ?b ] =>
      filter_subst_b S; filter_b b; simpl S; simplifyTac tac
    | _ => tac
  end.

Tactic Notation "Simplify" "by" tactic(tac) := simplifyTac tac.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Challenge 1A: Transitivity of Subtyping 
 This section presents our solution to the POPLmark Challenge 1A. *)

(* *************************************************************** *)
(** ** Properties of [lclosed_t]
 Note that [sub] uses [lclosed_t] in its definition. To reason about 
 [sub], therefore, we need the properties of [lclosed_t]. Here we 
 present several properties of [lclosed_t] that we use in our solution. *)
 
(* Every type parameter in [T] should be bound in [Gamma] if 
 [lclosed_t Gamma I T] holds. *)
Lemma lclosed_t_ftvar_dom_ctxt_typ : forall T Gamma I X,
  lclosed_t Gamma I T ->
  In X (FV_tt T) ->
  In X (dom_tc Gamma).
Proof.
  induction T; intros; inversion H;
    Simplify by (Destruct In by (subst; eauto)).
Qed.

Hint Resolve lclosed_t_ftvar_dom_ctxt_typ : incl_param.

(** [lclosed_t Gamma I T] holds as long as [Gamma] contains all the parameters
 that appear in [T]. *)
Lemma lclosed_t_incl : forall Gamma Gamma' I T,
  incl (dom_tc Gamma) (dom_tc Gamma') ->
  lclosed_t Gamma I T ->
  lclosed_t Gamma' I T.
Proof.
  induction 2; intros; Simplify by auto.
Qed.

Lemma lclosed_t_remove_ftvar_bind : forall T U X Gamma I,
  ~ In X (FV_tt T) ->
  lclosed_t (X ~<: U :: Gamma) I T ->
  lclosed_t Gamma I T.
Proof.
  induction T; intros; inversion H0; Simplify by (Destruct notIn by eauto).
    econstructor; Destruct In by congruence.
Qed.

(** [lclosed_t] is invertible. *)
Lemma lclosed_t_ltvar_split : forall T Gamma A X U I0,
  ~ In X (FV_tt T) ->
  lclosed_t (X ~<: U :: Gamma) I0 ({A ~> X ^^} T) ->
  (exists I, (lclosed_t Gamma I T /\ remove eq_nat_dec A I = I0)).
Proof.
  induction T; intros ? ? ? ? ? H0 H.
  inversion H; exists (emptyset:list ltvar); auto.
  Simplify by eauto; inversion H; subst.
    exists (A :: emptyset); Simplify by eauto.
    exists (n :: emptyset); Simplify by eauto.
  Simplify by (Destruct notIn by eauto).
  inversion H; subst; clear H.
  exists (emptyset:list ltvar); split; Simplify by eauto.
    econstructor; Simplify by (Destruct In by congruence).
  Simplify by (Destruct notIn by eauto).
  inversion H; subst.
  destruct (IHT1 _ _ _ _ _ H1 H6) as [I1' [Ha Ha']].
  destruct (IHT2 _ _ _ _ _ H2 H7) as [I2' [Hb Hb']].
  exists (I1' ++ I2'); split; auto.
    rewrite list_remove_app.
    rewrite Ha'; rewrite Hb'; auto.
  Simplify by (Destruct notIn by eauto); inversion H; subst.
    destruct (IHT1 _ _ _ _ _ H1 H6) as [I1' [Ha Ha']].
    forwards Hb: (lclosed_t_remove_ftvar_bind H2 H8).
    exists (I1' ++ (remove eq_nat_dec A I2)); split; auto.
      rewrite list_remove_app; rewrite list_remove_repeat.
      rewrite Ha'; auto.
    destruct (IHT1 _ _ _ _ _ H1 H6) as [I1' [Ha Ha']].
    destruct (IHT2 _ _ _ _ _ H2 H8) as [I2' [Hb Hb']].
    exists (I1' ++ (remove eq_nat_dec n I2')); split; auto.
      rewrite list_remove_app; rewrite list_remove_twice.
      rewrite Ha'; rewrite Hb'; auto.
Qed.

(** [lclosed_t] is stable under type variable substitution. *)
Lemma lclosed_t_subst_ltvar : forall T Gamma U I A,
  lclosed_t Gamma emptyset U ->
  lclosed_t Gamma I T ->
  lclosed_t Gamma (remove eq_nat_dec A I) ({A ~> U} T).
Proof.
  induction T; intros; inversion H0; subst; Simplify by eauto.
    rewrite list_remove_app; eauto.
    rewrite list_remove_app; rewrite list_remove_repeat; eauto.
    rewrite list_remove_app; rewrite list_remove_twice; eauto.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Properties of [ctxt_okay]
 [sub] and [typing] uses [ctxt_okay] in their definition, and thus
 we need to reason about [ctxt_okay] in order to reason about [sub]
 and [typing]. This section presents such properties of [ctxt_okay]. *)
Lemma ctxt_okay_app : forall Gamma Delta,
  ctxt_okay (Gamma ++ Delta)->
  ctxt_okay Delta.
Proof.
  induction Gamma; intros; eauto.
  rewrite <- list_cons_cons_move_app in H.
  inversion H; subst; eauto.
Qed.

(** Every parameter in [Gamma] is distinct if [ctxt_okay Gamma] holds. *)
Lemma ctxt_okay_unique_ftvar : forall Gamma X T,
  ctxt_okay (X ~<: T :: Gamma) ->
  ~ In X (FV_tc Gamma).
Proof.
  induction Gamma; intros; Simplify by eauto.
  destruct a; inversion H; inversion H3; 
    subst; Simplify by (Destruct notIn by eauto with incl_param).
Qed.

Lemma ctxt_okay_unique_fvar_bind : forall Gamma x T U,
  ctxt_okay Gamma ->
  In (x ~: T) Gamma ->
  In (x ~: U) Gamma ->
  T = U.
Proof.
  induction Gamma; intros.
    Destruct In by eauto.
    destruct a; inversion H; subst.
      destruct (in_inv H0); destruct (in_inv H1); subst; eauto.
        inversion H2; inversion H3; subst t; eauto.
        inversion H2; subst; elim H6; eauto.
        inversion H3; subst; elim H6; eauto.
      destruct (in_inv H0); destruct (in_inv H1); subst; 
        eauto; discriminate. 
Qed.

Lemma ctxt_okay_unique_ftvar_bind : forall Gamma X T U,
  ctxt_okay Gamma ->
  In (X ~<: T) Gamma ->
  In (X ~<: U) Gamma ->
  T = U.
Proof.
  induction Gamma; intros.
    Destruct In by eauto.
    destruct a; inversion H; subst.
      destruct (in_inv H0); destruct (in_inv H1); subst; 
        eauto; discriminate.
      destruct (in_inv H0); destruct (in_inv H1); subst; eauto.
        inversion H2; inversion H3; subst t; eauto.
        inversion H2; subst; elim H6; eauto.
        inversion H3; subst; elim H6; eauto.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Properties of substitution over types 
 Our solution exploits several properties of substitution over types. *)
Hint Resolve sym_eq list_remove_in : nochange.

(** Type variable substitution over types has no effect if they do not 
 include such a type variable. *)
Lemma subst_ltvar_nochange_t : forall I T Gamma,
  lclosed_t Gamma I T -> 
  forall A U, 
    ~ In A I -> {A ~> U} T = T.
Proof.
  induction 1; intros; 
    Destruct notIn by (Simplify by (f_equal; eauto with nochange)).
Qed.

(** Type parameter substitution over types also has no effect if they 
 do not include such a type parameter. *)
Lemma subst_ftvar_nochange_t : forall T U X,
  ~ In X (FV_tt T) -> [X ~> U] T = T.
Proof.
  induction T; intros; Simplify by (f_equal; Destruct notIn by eauto).
Qed.

Hint Resolve subst_ltvar_nochange_t subst_ftvar_nochange_t : nochange.

(** We may swap variable and parameter substitutions. *)
Lemma subst_ftvar_rename_ltvar_t : forall T U X Y A,
  [X ~> Y ^^] ({A ~> U} T) = {A ~> [X ~> Y ^^] U} ([X ~> Y ^^] T).
Proof.
  induction T; intros; Simplify by (f_equal; eauto). 
Qed.

Lemma subst_ftvar_ltvar_t : forall T U S X Gamma,
  lclosed_t Gamma emptyset U ->
  forall A,
    [X ~> U] ({A ~> S} T) = {A ~> [X ~> U] S} ([X ~> U] T).
Proof.
  induction T; intros; Simplify by (f_equal; eauto with nochange).
Qed.

(** We may replace a type variable with a fresh type parameter, and then 
 replace the type parameter with a given type instead of directly replacing 
 the type variable with the given type. *)
Lemma subst_seq_ftvar_ltvar_t : forall T U X,
  ~ In X (FV_tt T) ->
  forall A,
    [X ~> U] ({A ~> X ^^} T) = {A ~> U} T.
Proof.
  induction T; intros; 
    Simplify by (f_equal; Destruct notIn by eauto with nochange).
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Basic properties of [sub] *)

(** [sub] deals with well-formed contexts only. *)
Lemma sub_ctxt_okay : forall T U Gamma,
  sub Gamma T U -> ctxt_okay Gamma.
Proof.
   induction 1; intros; Simplify by (Destruct notIn by intuition).
Qed.

(** [sub] deals with locally closed types only. *)
Lemma sub_lclosed_t : forall T U Gamma,
  sub Gamma T U -> lclosed_t Gamma emptyset T /\ lclosed_t Gamma emptyset U .
Proof.
  induction 1; intros; Simplify by (Destruct notIn by intuition).
  econstructor; Destruct In by eauto.
  unsimpl (emptyset ++ emptyset:list ltvar); eauto.
  unsimpl (emptyset ++ emptyset:list ltvar); eauto.
  destruct (lclosed_t_ltvar_split _ _ H3 H6) as [I1 [Ha' Ha'']].
  replace (emptyset : list ltvar) with (emptyset ++ remove eq_nat_dec A I1).
    eauto.
  destruct (lclosed_t_ltvar_split _ _ H4 H7) as [I2 [Ha' Ha'']].
  replace (emptyset:list ltvar) with (emptyset ++ remove eq_nat_dec B I2). 
    eauto.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Renaming property of [sub].
 As is well-known in the literature, the exists-fresh style necessitates 
 various renaming properties. This section present the proof of Lemma 
 [sub_rename_ftvar] which formally states the renaming property of [sub].

 *** Auxiliary lemmas
 This section presents several auxiliary lemmas that the proof of Lemma 
 [sub_rename_ftvar] uses. *)
Lemma ftvar_rename_ctxt_bind_in : forall Gamma bind X Y,
  In bind Gamma ->
  In (ctxt_ftvar_rename X Y bind) ([X => Y] Gamma).
Proof.
  induction Gamma; intros; eauto.
    destruct (in_inv H); subst; Simplify by Destruct In by firstorder.
Qed.

Lemma ftvar_rename_ctxt_nochange : forall Gamma X Y,
  ~ In X (FV_tc Gamma) ->
  [X => Y] Gamma = Gamma.
Proof.
  induction Gamma; intros; eauto.
  destruct a; Simplify by Destruct notIn by 
    (repeat f_equal; eauto with nochange).
Qed.

Lemma ftvar_rename_ctxt_dom_tc_eq : forall X Y Gamma,
  In X (dom_tc Gamma) ->
  In Y (dom_tc ([X => Y] Gamma)).
Proof.
  induction Gamma; intros; Simplify by auto.
  destruct a; Simplify by (Destruct In by (eauto; congruence)). 
Qed.

Lemma ftvar_rename_ctxt_dom_tc_neq : forall X Y Z Gamma,
  In X (dom_tc Gamma) ->
  X <> Y ->
  In X (dom_tc ([Y => Z] Gamma)).
Proof.
  induction Gamma; intros; Simplify by eauto.
  destruct a; Simplify by (subst; Destruct In by (eauto; congruence)).
    subst; Destruct In by eauto.
Qed.

Lemma ftvar_rename_ctxt_dom_tc_nochange : forall Gamma X Y,
  ~ In X (dom_tc Gamma) ->
  dom_tc Gamma = dom_tc ([X => Y] Gamma).
Proof.
  induction Gamma; intros; Simplify by eauto.
    destruct a; Simplify by (Destruct notIn by eauto).
      f_equal; eauto.
Qed.

Lemma ftvar_rename_ctxt_preserve_not_in_dom_tc : forall Gamma X,
  ~ In X (dom_tc Gamma) ->
  forall Y Z,
    X <> Z ->
    ~ In X (dom_tc ([Y => Z] Gamma)).
Proof.
  induction Gamma; intros; eauto.
  destruct a; Simplify by (Destruct notIn by eauto).
Qed.

Lemma ftvar_rename_ctxt_dom_ec_nochange : forall Gamma X Y,
  dom_ec ([X => Y] Gamma) = dom_ec Gamma.
Proof.
  induction Gamma; intros; Simplify by auto.
    destruct a; Simplify by eauto; rewrite IHGamma; auto.
Qed.

Hint Resolve ftvar_rename_ctxt_preserve_not_in_dom_tc : rename_aux.
Hint Resolve ftvar_rename_ctxt_dom_tc_eq              : rename_aux.
Hint Resolve ftvar_rename_ctxt_dom_tc_neq             : rename_aux.

(** ** Type parameter renaming
 Here we present the main result of this section. Lemma [sub_rename_ftvar] 
 states the renaming property of the subtyping relation. Note that Lemma 
 [sub_rename_ftvar] requires the variable [Y] not to be in [dom_tc Gamma],
 which is necessary to maintain the well-formedness of typing contexts. 

 The proof proceeds by induction on the proof size, and uses Lemma 
 [lclosed_t_rename_ftvar] and [ctxt_okay_rename_ftvar]. *)
Lemma lclosed_t_rename_ftvar : forall T X Y I Gamma,
  lclosed_t Gamma I T ->
  lclosed_t ([X => Y] Gamma) I ([X ~> Y ^^] T).
Proof.
  induction T; intros; inversion H; subst; 
    Simplify by eauto with rename_aux.
Qed.

Hint Resolve lclosed_t_rename_ftvar : rename_aux.

Lemma ctxt_okay_rename_ftvar : forall Gamma X Y,
  ctxt_okay Gamma ->
  ~ In Y (dom_tc Gamma) ->
  ctxt_okay ([X => Y] Gamma).
Proof.
  induction Gamma; intros; eauto.
  destruct a.
  inversion H; subst; Simplify by eauto.
  constructor; eauto with rename_aux.
    rewrite ftvar_rename_ctxt_dom_ec_nochange; eauto. 
  inversion H; subst; Simplify by Destruct notIn by eauto. 
    constructor; eauto with rename_aux.
      rewrite <- ftvar_rename_ctxt_dom_tc_nochange; 
        Destruct notIn by eauto.
    constructor; eauto with rename_aux.
Qed.

Hint Resolve ctxt_okay_rename_ftvar : rename_aux.

Lemma sub_rename_ftvar_aux : forall m n T U Gamma,
  n < m ->
  subLH n Gamma T U ->
  forall Y Z,
      ~ In Z (dom_tc Gamma) ->
      subLH n ([Y => Z] Gamma) ([Y ~> Z^^] T) ([Y ~> Z^^] U).
Proof.
  induction m.
  firstorder using lt_n_O.
  destruct 2; intros.
  eauto with rename_aux.
  Simplify by eauto with rename_aux.
    inversion H1; subst; 
      eauto with rename_aux.
    econstructor; eauto with rename_aux.
      replace (X ^^) with ([Y ~> Z ^^] (X ^^)) by (Simplify by congruence).
      eauto with rename_aux.
  assert (n < m) by auto with arith.
  Simplify by idtac.
    constructor 3 with (T := [Y ~> Z ^^] T).
      replace (Z ~<: ([Y ~> Z ^^]T)) with (ctxt_ftvar_rename Y Z (Y ~<: T)).
        eapply in_map; eauto.
        Simplify by eauto.
    eapply IHm; eauto with arith.
    constructor 3 with (T := [Y ~> Z ^^] T); eauto with arith.
       replace (X ~<: ([Y ~> Z ^^]T)) with (ctxt_ftvar_rename Y Z (X ~<: T)).
         eapply in_map; eauto.
         Simplify by eauto with arith.
  econstructor; apply IHm; eauto with arith.
  set (L := FV_tc ([Y => Z]Gamma) ++
           (FV_tt ([Y ~> Z^^] T2) ++
           FV_tt ([Y ~> Z^^] U2)) ++
           (FV_tt ([Y ~> Z^^] T1) ++
           FV_tt ([Y ~> Z^^] U1)) ++
           FV_tc Gamma ++
           dom_tc Gamma ++
           (X :: Y :: Z :: nil)).
  destruct (pick_fresh L) as [W Hfresh'].
  unfold L in Hfresh'.
  destruct (sub_lclosed_t (subLH_sub H0_)) as [? ?].
  Simplify by Destruct notIn by eauto.
  apply subLH_all with W; Destruct notIn by eauto.  
    apply IHm; eauto with arith.
    replace (W ^^) with ([ Y ~> Z ^^] (W ^^)) by (Simplify by congruence).
    repeat (rewrite <- subst_ftvar_rename_ltvar_t).
    replace (W ~<: ([Y ~> Z ^^] U1) :: ([Y => Z]Gamma))
      with ([Y => Z] ((W ~<: U1) :: Gamma)) by (Simplify by eauto).
    apply IHm; Simplify by (Destruct notIn by (eauto with arith)).
      rewrite <- subst_seq_ftvar_ltvar_t with (T := T2) (X := X) by eauto.
      rewrite <- subst_seq_ftvar_ltvar_t with (T := U2) (X := X) by eauto.
      replace (W ~<: U1 :: Gamma) with ([X => W] (X ~<: U1 :: Gamma)).
      apply IHm; Simplify by (Destruct notIn by eauto with arith).
      Simplify by eauto.
        rewrite subst_ftvar_nochange_t by (eauto with incl_param).
        rewrite ftvar_rename_ctxt_nochange; eauto.
Qed.

Lemma sub_rename_ftvar : forall Gamma T U,
  sub Gamma T U ->
  forall X Y,
    ~ In Y (dom_tc Gamma) ->
    sub ([X => Y] Gamma) ([X ~> Y^^] T) ([X ~> Y^^] U).
Proof.
  intros.
  forwards HsubLH : sub_subLH H.
  inversion HsubLH as [n HsubLH'].
  apply subLH_sub with n.
  apply sub_rename_ftvar_aux with (S n); auto.
Qed.

Hint Resolve sub_rename_ftvar : rename_aux.

Lemma sub_ltvar_subst_rename_ftvar : forall T U,
  forall X, ~ In X (FV_tt T) -> ~ In X (FV_tt U) ->
  forall Gamma A B Y,
    ~ In Y (dom_tc Gamma) ->
    sub Gamma ({A ~> X^^} T) ({B ~> X^^} U) ->
    sub ([X => Y] Gamma) ({A ~> Y^^} T) ({B ~> Y^^} U).
Proof.
  intros.
  rewrite <- subst_seq_ftvar_ltvar_t with (T := T) (X := X) by auto.
  rewrite <- subst_seq_ftvar_ltvar_t with (T := U) (X := X) by auto.
  eauto with rename_aux.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Structural properties of [sub] 
 *** Permutation 
 This section proves Lemma [permuting_subLH] which states the permutation 
 property of [sub]. *)
Hint Resolve list_permuting_in_app_cons_cons : permuting_aux.

(** We first prove Lemma [permuting_lclosed_t] which is an auxiliary lemma 
 for Lemma [permuting_lclosed_t]. *)
Lemma permuting_lclosed_t : forall Gamma0 Gamma Delta bind bind' T I,
  lclosed_t Gamma0 I T ->
  Gamma0 = (Delta ++ (bind :: bind' :: Gamma)) ->
  lclosed_t (Delta ++ (bind' :: bind :: Gamma)) I T.
Proof.
  induction 1; intro; subst; Simplify by eauto.
    econstructor; Simplify by eauto.
    destruct bind; destruct bind'; Simplify by eauto with v62.
      destruct (n == X); destruct (n0 == X); subst; Destruct In by congruence.
Qed.

Hint Resolve permuting_lclosed_t : permuting_aux.

(** We then prove Lemma [permuting_subLH] using Lemma [permuting_lclosed_t].
 Note that Lemma [permuting_subLH], unlike Lemma [permuting_lclosed_t], 
 requires the typing context to be well-formed after the permutation. *)
Lemma permuting_subLH : forall Gamma0 T U n,
  subLH n Gamma0 T U ->
  forall Gamma Delta bind bind',
  Gamma0 = (Delta ++ (bind :: bind' :: Gamma)) ->
  ctxt_okay (Delta ++ (bind' :: bind :: Gamma)) ->
  subLH n (Delta ++ (bind' :: bind :: Gamma)) T U.
Proof.
  induction 1; intros; subst Gamma; eauto with permuting_aux.
  constructor 5 with (X := X); Simplify by (Destruct notIn by eauto).
    destruct bind; destruct bind'; Simplify by (Destruct notIn by eauto).
    destruct (sub_lclosed_t (subLH_sub H)) as [? ?].
    rewrite list_cons_cons_move_app.
      eapply IHsubLH2; eauto.  
      rewrite <- list_cons_cons_move_app.
      econstructor; eauto with permuting_aux.
        destruct bind; destruct bind'; Simplify by (Destruct notIn by eauto).
Qed.

Hint Resolve permuting_subLH : permuting_aux.

(** *** Weakening 
 This section proves Lemma [weakening_sub_cons] and [weakening_sub_concat]
 which state the weakening property of [sub]. 
 
 We first prove Lemma [weakening_sub_cons] by induction on the size of 
 [sub] proofs (See Lemma [weakening_subLH_cons] for details). *)
Lemma weakening_subLH_cons : forall m n Gamma T U,
  n < m ->
  subLH n Gamma T U ->
  forall bind,
    ctxt_okay (bind :: Gamma) ->
    subLH n (bind :: Gamma) T U.
Proof.
  induction m.
  firstorder using lt_n_O. 
  destruct 2; intros.
  constructor 1; auto.
    apply lclosed_t_incl with (Gamma := Gamma);
      destruct bind; Simplify by eauto with v62.
  constructor 2; auto.
    inversion H1; subst.
    constructor 3; destruct bind; Simplify by Destruct In by auto.
  assert (n < m) by auto with arith.
  constructor 3 with (T := T); Destruct In by auto.
  assert (n1 < m) by eauto with arith.
  assert (n2 < m) by eauto with arith.
  auto.
  assert (n1 < m) by eauto with arith.
  assert (n2 < m) by eauto with arith.
  set (L := FV_tc Gamma ++
            (FV_tt T2 ++ FV_tt U2) ++
            (dom_tc (X ~<: U1 :: Gamma)) ++
            (FV_tc (bind :: Gamma))).
  destruct (pick_fresh L) as [Y HfreshL].
  unfold L in HfreshL.
  assert (~ In Y (dom_tc (X ~<: U1 :: Gamma))).
    Simplify by (Destruct notIn by auto).
  assert (~ In Y (FV_tc (bind :: Gamma))).
    Simplify by (Destruct notIn by auto).
  forwards Ha : (sub_rename_ftvar_aux H4 H0_0 X Y H5).
  rewrite subst_seq_ftvar_ltvar_t in Ha by Destruct notIn by auto.
  rewrite subst_seq_ftvar_ltvar_t in Ha by Destruct notIn by auto.
  Simplify by eauto.
  assert (~ In X (FV_tt U1)).
    destruct (sub_lclosed_t (subLH_sub H0_)) as [? ?].
    eauto with incl_param.
  rewrite subst_ftvar_nochange_t in Ha; auto.
  rewrite ftvar_rename_ctxt_nochange in Ha; auto.
  constructor 5 with Y; eauto.
  Destruct notIn by auto.
  clear H0 H1 H0_0.
  destruct (sub_lclosed_t (subLH_sub H0_)) as [? ?].
  assert (ctxt_okay Gamma) by (inversion H2; auto).
  assert (ctxt_okay (Y ~<: U1 :: Gamma)).
    constructor; Destruct notIn by eauto.
  assert (ctxt_okay (Y ~<: U1 :: bind :: Gamma)).
    constructor; Destruct notIn by eauto.
    apply lclosed_t_incl with (Gamma := Gamma);
      destruct bind;
        Simplify by (eauto with v62).
  assert (ctxt_okay (bind :: Y ~<: U1 :: Gamma)).
    destruct bind.
      inversion H2; subst.
      constructor; Simplify by Destruct notIn by eauto.
      apply lclosed_t_incl with (Gamma := Gamma);
        Simplify by (eauto with v62).
      inversion H10; subst.
      inversion H14; subst.
      constructor; Simplify by (Destruct notIn by eauto).
      apply lclosed_t_incl with (Gamma := Gamma); Simplify by eauto with v62.
  forwards Hb : IHm H4 Ha bind H11.
  replace (bind :: Y ~<: U1 :: Gamma)
    with (nil ++ (bind :: Y ~<: U1 :: Gamma)) in Hb by eauto.
  replace (Y ~<: U1 :: bind :: Gamma)
    with (nil ++ (Y ~<: U1 :: bind :: Gamma)) by eauto.
  eauto using permuting_subLH. 
Qed.

Lemma weakening_sub_cons : forall Gamma T U,
  sub Gamma T U ->
  forall bind,
    ctxt_okay (bind :: Gamma) ->
    sub (bind :: Gamma) T U.
Proof.
  intros.
  destruct (sub_subLH H) as [n H'].
  eauto using weakening_subLH_cons, subLH_sub.
Qed.

(** We then prove Lemma [weakening_sub_concat] using Lemma [weakening_sub_cons] 
 by induction on the structure of typing contexts. *)
Lemma weakening_sub_concat : forall Gamma T U,
  sub Gamma T U ->
  forall Gamma',
    ctxt_okay (Gamma' ++ Gamma) ->
    sub (Gamma' ++ Gamma) T U.
Proof.
  intros; induction Gamma'; Simplify by eauto.
  rewrite <- list_cons_cons_move_app.
  rewrite <- list_cons_cons_move_app in H0.
  forwards Ha : weakening_sub_cons IHGamma' a; auto.
    inversion H0; subst; auto.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Transitivity of [sub]
 Finally, we present the major result of this section: the transitivity 
 of [sub]. The proof is challenging because we need to prove the 
 transitivity and the narrowing property simultaneously. *)

(** *** Narrowing property of subtyping 
 To simplify the proof, we first prove the narrowing property under 
 the assumption that the transitivity of [sub] holds for a specific 
 type. 

 We use [sub_transitivity_on T] to state the assumption that the 
 transitivity of [sub] holds for a specific type [T]. *)
Definition sub_transitivity_on T := forall Gamma U S,
  sub Gamma U T -> sub Gamma T S -> sub Gamma U S.

Lemma ctxt_okay_subst_cons : forall Gamma0,
  ctxt_okay Gamma0 ->
  forall Gamma X T U,
    Gamma0 = X ~<: T :: Gamma ->
    lclosed_t Gamma emptyset U ->
    ctxt_okay (X ~<: U :: Gamma).
Proof.
  induction 1; intros; try discriminate.
  inversion H2; subst. clear H2.
  eauto.
Qed.

Lemma ctxt_okay_subst_concat : forall Gamma' Gamma X T U,
  ctxt_okay (Gamma' ++ X ~<: T :: Gamma) ->
  lclosed_t Gamma emptyset U ->
  ctxt_okay (Gamma' ++ X ~<: U :: Gamma).
Proof.
  induction Gamma'; simpl; intros; subst.
    eauto using ctxt_okay_subst_cons.
    inversion H; subst.
      constructor; Simplify by eauto.
      apply lclosed_t_incl with (Gamma := (Gamma' ++ X ~<: T :: Gamma));
        Simplify by (eauto with v62).
      constructor; Simplify by eauto.
      apply lclosed_t_incl with (Gamma := (Gamma' ++ X ~<: T :: Gamma));
        Simplify by (eauto with v62).
Qed.

Hint Resolve ctxt_okay_subst_cons ctxt_okay_subst_concat : narrowing_aux.

Lemma sub_narrowing_aux : forall m n T U S X Gamma Gamma' Gamma0,
  n < m ->
  subLH n Gamma0 T U ->
  Gamma0 = Gamma' ++ (X ~<: S :: Gamma) ->
  forall S',
    sub_transitivity_on S ->
    sub Gamma S' S ->
      sub (Gamma' ++ (X ~<: S' :: Gamma)) T U.
Proof.
  induction m.
  firstorder using lt_n_O. 
  destruct 2; intros; subst Gamma0.
  constructor 1.
    destruct (sub_lclosed_t H4) as [? ?]; eauto with narrowing_aux.
    apply lclosed_t_incl with (Gamma := Gamma' ++ X ~<: S :: Gamma);
      Simplify by (eauto with v62).
  constructor 2.
    destruct (sub_lclosed_t H4) as [? ?]; eauto with narrowing_aux.
    apply lclosed_t_incl with (Gamma := Gamma' ++ X ~<: S :: Gamma);
      Simplify by (eauto with v62).
  destruct (X == X0); subst.
    assert (T = S).
      forwards Hokay : sub_ctxt_okay (subLH_sub H1).
      eapply ctxt_okay_unique_ftvar_bind 
        with (X := X0) (Gamma := Gamma' ++ X0 ~<: S :: Gamma); eauto.
        Destruct In by eauto.
      subst.
    constructor 3 with (T := S'); auto with v62.
      apply H3.
        rewrite list_cons_move_app.
        eapply weakening_sub_concat; eauto.
          forwards Hokay : (sub_ctxt_okay (subLH_sub H1)).
          destruct (sub_lclosed_t H4) as [? ?].
          rewrite <- list_cons_move_app; eauto with narrowing_aux.
      eapply IHm; eauto with arith.
    constructor 3 with (T := T); auto with v62.
      Destruct In by eauto.
        inversion H0; congruence.
      eapply IHm; eauto with arith.
  assert (n1 < m) by eauto with arith.
  assert (n2 < m) by eauto with arith.
  constructor 4; eauto.
  set (L := (X :: nil) ++ (X0 :: nil)
         ++ (dom_tc Gamma) ++ (dom_tc Gamma')
         ++ (FV_tc (Gamma' ++ X ~<: S' :: Gamma))
         ++ (FV_tt T2 ++ FV_tt U2)).
  destruct (pick_fresh L) as [Z HfreshL].
  unfold L in HfreshL.
  constructor 5 with Z; Destruct notIn by auto.
    assert (n1 < m) by eauto with arith; eauto.
    rewrite list_cons_cons_move_app in H0_0.
    rewrite list_cons_cons_move_app.
    forwards Hdelta : (sub_rename_ftvar_aux (lt_n_Sn n2) H0_0 X0 Z).
      Simplify by (Destruct notIn by auto).
    assert (~ In X0 (FV_tt T2)) by (Destruct notIn by auto).
    rewrite <- subst_seq_ftvar_ltvar_t with (T := T2) (X := X0) by eauto.
    rewrite <- subst_seq_ftvar_ltvar_t with (T := U2) (X := X0) by eauto.
    assert (~ In X0 (FV_tt U1)).
      destruct (sub_lclosed_t (subLH_sub H0_)) as [? ?].
      Destruct notIn by (firstorder using lclosed_t_ftvar_dom_ctxt_typ).    
    Simplify by idtac.
    rewrite ftvar_rename_ctxt_nochange in Hdelta 
      by Simplify by (Destruct notIn by eauto).
    rewrite subst_ftvar_nochange_t in Hdelta by eauto.
    rewrite list_cons_cons_move_app in Hdelta.
    assert (n2 < m) by eauto with arith.
    eapply IHm with (n:=n2) (S := S); eauto.
Qed.

Lemma sub_narrowing : forall T U X S Gamma Gamma' ,
  sub (Gamma' ++ X ~<: S :: Gamma) T U ->
  forall S',
    sub_transitivity_on S ->
    sub Gamma S' S ->
      sub (Gamma' ++ X ~<: S' :: Gamma) T U.
Proof.
  intros.
  destruct (sub_subLH H) as [n ?].
  eapply sub_narrowing_aux with (m:= Datatypes.S n) (n:=n); eauto.
Qed.

(* *************************************************************** *)
(** *** Transitivity 
 We then prove the transitivity of [sub] by induction on the size 
 of types. The size of types is defined by function [size_t]. *)
Fixpoint size_t (T : typ) : nat :=
  match T with
  | typ_top         => 0
  | typ_ltvar _     => 0
  | typ_ftvar _     => 0
  | typ_arrow T1 T2 => S (size_t T1 + size_t T2)
  | typ_all _ T1 T2 => S (size_t T1 + size_t T2)
  end.

Lemma size_t_nochange_ltvar : forall T A X,
  size_t ({A ~> X ^^} T) = size_t T.
Proof.
  induction T; intros; Simplify by eauto.
Qed.

(** Lemma [sub_trans_ftvar_aux] deals with the [typ_ftvar] case. *)
Lemma sub_trans_ftvar_aux : forall T U X Gamma,
  sub Gamma T U ->
  U = (X ^^) ->
  forall S, sub Gamma U S -> sub Gamma T S.
Proof.
  induction 1; intros; try discriminate; subst; eauto.
Qed.

(** Lemma [sub_trans_fun_aux] deals with the [typ_arrow] case. *)
Lemma sub_trans_fun_aux : forall T U U1 U2 S Gamma,
  sub_transitivity_on U1 -> 
  sub_transitivity_on U2 ->
  sub Gamma T U -> 
  sub Gamma U S ->
  U = U1 --> U2 -> 
  sub Gamma T S.
Proof.
  induction 3; intros; try discriminate; eauto.
  inversion H2; subst; clear H2.
    destruct (sub_lclosed_t H1_).
    destruct (sub_lclosed_t H1_0). 
    inversion H1; subst; econstructor; eauto.
      unsimpl (emptyset ++ emptyset:list ltvar); eauto. 
Qed.

(** Lemma [sub_trans_forall_aux] deals with the [typ_all] case. *) 
Lemma sub_trans_forall_aux : forall T U U1 U2 S A,
  (forall S', size_t S' < size_t U -> sub_transitivity_on S') ->
  forall Gamma,
    sub Gamma T U ->
    U = typ_all A U1 U2 ->
    sub Gamma U S ->
    sub Gamma T S.
Proof.
  intros until 2.
  induction H0; intros; try discriminate.
  econstructor; eauto.
  clear IHsub1 IHsub2.
  inversion H2; subst; clear H2.
  destruct (sub_lclosed_t H0_).
  destruct (sub_lclosed_t H0_0).  
  Destruct notIn by auto.
  inversion H3 as [ ? U | | | | ? ? ? S1 S2]; subst.
  econstructor; eauto.
    destruct (lclosed_t_ltvar_split _ _ H7 H5) as [I [Ha Hb]].
    replace (emptyset:list ltvar) with (emptyset ++ (remove eq_nat_dec A0 I));
      eauto.
  destruct (sub_lclosed_t H11).
  destruct (sub_lclosed_t H16).
  set (L := X :: X0 :: FV_tc Gamma ++ dom_tc Gamma ++ 
            FV_tt T2 ++ FV_tt S2).
  destruct (pick_fresh L) as [Y Hfresh].
  unfold L in Hfresh.
  assert (~ In X (FV_tt U1)) by (Destruct notIn by eauto with incl_param).
  assert (~ In X0 (FV_tt S1)) by (Destruct notIn by eauto with incl_param).
  assert (~ In Y (dom_tc (X ~<: U1 :: Gamma))).
    Simplify by (Destruct notIn by eauto).
  assert (~ In Y (dom_tc (X0 ~<: U1 :: Gamma))).
    Simplify by (Destruct notIn by eauto).
  Destruct notIn by idtac.
  forwards Ha : (@sub_ltvar_subst_rename_ftvar T2 U2 X H7 H8 _ A0 A Y H18 H0_0).
    Simplify by eauto. 
    rewrite ftvar_rename_ctxt_nochange in Ha; auto.
    rewrite subst_ftvar_nochange_t in Ha; auto.
    forwards Hb : (@sub_ltvar_subst_rename_ftvar U2 S2 _ H25 H27 
      (X0 ~<: S1 :: Gamma) A B Y H19 H16).
    Simplify by eauto.
    rewrite ftvar_rename_ctxt_nochange in Hb; auto.
    rewrite subst_ftvar_nochange_t in Hb; auto.
  assert (size_t U1 < size_t (typ_all A U1 U2)) by (simpl; auto with arith).
  assert (sub_transitivity_on U1) by auto.
  Simplify by eauto.
  assert (sub_transitivity_on ({A ~> Y ^^}U2)). 
    apply H; rewrite size_t_nochange_ltvar; simpl; auto with arith. 
  constructor 5 with (X := Y); Destruct notIn by auto.
  unsimpl (emptyset ++ Y ~<: S1 :: Gamma).
  eauto using sub_narrowing.
Qed.

(** Using these lemmas, we may complete the proof of the transitivity. *)
Lemma sub_transitivity_aux : forall n T,
  size_t T < n -> sub_transitivity_on T.
Proof.
  induction n. 
  firstorder using lt_n_O. 
  destruct T; unfold sub_transitivity_on; intros.
  inversion H1; assumption.
  inversion H1; subst. 
  inversion H3; firstorder using lt_n_O. 
  eauto using sub_trans_ftvar_aux.
  Simplify by idtac.
  assert (size_t T1 < n) by eauto with arith.
  assert (size_t T2 < n) by eauto with arith.
  eauto using sub_trans_fun_aux.
  Simplify by idtac.
  assert (forall S', 
    size_t S' < size_t (typ_all n0 T1 T2) -> 
    sub_transitivity_on S').
    eauto with arith.
  eauto using sub_trans_forall_aux.
Qed.

Lemma sub_transitivity : forall T T' U Gamma, 
  sub Gamma T U -> 
  sub Gamma U T' -> 
  sub Gamma T T'.
Proof.
  intros. 
  forwards Ha : sub_transitivity_aux (S (size_t U)) U; eauto with arith.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Reflexivity of [sub]
 Reflexivity of [sub] is straightforward to prove. The proof proceeds
 by induction on the size of types.*)
Lemma sub_reflexivity_aux : forall n T Gamma,
  size_t T < n -> 
  ctxt_okay Gamma -> 
  lclosed_t Gamma emptyset T -> 
  sub Gamma T T.
Proof.
  induction n. 
  firstorder using lt_n_O.
  destruct T; intros Gamma H' Hokay H; inversion H; Simplify by eauto. 
  assert (size_t T1 < n) by eauto with arith.  
  assert (size_t T2 < n) by eauto with arith.
  assert (I1 = emptyset) by firstorder using app_eq_nil.
  assert (I2 = emptyset) by firstorder using app_eq_nil.
  subst; auto.
  set (L := dom_tc Gamma ++ FV_tc Gamma ++ FV_tt T2 ++ FV_tt T2).
  destruct (pick_fresh L) as [X Hfresh].
  unfold L in Hfresh; subst.
  assert (I1 = emptyset) by firstorder using app_eq_nil; subst I1.
  assert (remove eq_nat_dec n0 I2 = emptyset) by firstorder using app_eq_nil.
  constructor 5 with (X := X); Destruct notIn by eauto.
    apply IHn; eauto with arith.
    apply IHn.
      rewrite size_t_nochange_ltvar; eauto with arith.
      constructor; eauto using in_or_app.
      replace (emptyset : list ltvar) with (remove eq_nat_dec n0 I2); auto.
      apply lclosed_t_subst_ltvar; auto.
      constructor 3.
      simpl; auto.
      apply lclosed_t_incl with (Gamma:=Gamma); Simplify by (eauto with v62).
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Challenge 2A: Type Safety 
 This section presents our solution to the POPLmark Challenge 2A. *)
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Strengthening properties 
 For any relation based on typing contexts, if the relation is stable 
 under the removal of irrelevant bindings, we say that the relation
 has the  strengthening property. This section presents the strengthening
 property of various relations, such as [lclosed_t]. *)
Lemma strengthen_lclosed_t_fvar_app_aux : forall Gamma0 x T Gamma Delta I U,
  lclosed_t Gamma0 I U ->
  Gamma0 = Gamma ++ (x ~: T) :: Delta ->
  lclosed_t (Gamma ++ Delta) I U.
Proof.
  induction 1; intros; subst; eauto.
  constructor 3; Simplify by auto.
Qed.

Lemma strengthen_lclosed_t_ftvar_aux : forall Gamma0 Gamma X T I U,
  ~ In X (FV_tt U) ->
  lclosed_t Gamma0 I U ->
  Gamma0 = X ~<: T :: Gamma ->
  lclosed_t Gamma I U.
Proof.
  induction 2; intros; subst; Simplify by eauto.
    econstructor; Destruct In by (subst; Destruct notIn by eauto).
    econstructor; [eapply IHlclosed_t1 | eapply IHlclosed_t2 ]; 
      Destruct notIn by eauto.
    econstructor; [eapply IHlclosed_t1 | eapply IHlclosed_t2 ]; 
      Destruct notIn by eauto.
Qed.

Hint Resolve strengthen_lclosed_t_fvar_app_aux : strengthen_aux.
Hint Resolve strengthen_lclosed_t_ftvar_aux    : strengthen_aux.

Lemma strengthen_lclosed_e_fvar_aux : forall Gamma0 Gamma x T I i t,
  ~ In x (FV_ee t) ->
  lclosed_e Gamma0 I i t ->
  Gamma0 = x ~: T :: Gamma ->
  lclosed_e Gamma I i t.
Proof.
  induction 2; intros; subst; auto.
  Simplify by (firstorder; congruence).
  constructor 3; eauto.
    replace Gamma with (emptyset ++ Gamma); eauto.
    eapply strengthen_lclosed_t_fvar_app_aux; Simplify by (simpl; eauto).
  Simplify by Destruct notIn by eauto.
  constructor 5; eauto.
  unsimpl (emptyset ++ Gamma).
  eapply strengthen_lclosed_t_fvar_app_aux;  
    Simplify by Destruct notIn by (simpl; eauto).
  constructor 6; eauto.
  unsimpl (emptyset ++ Gamma).
  eapply strengthen_lclosed_t_fvar_app_aux;
    Simplify by Destruct notIn by (simpl; eauto).
Qed.

Lemma strengthen_lclosed_e_ftvar_aux : forall Gamma0 Gamma X T I i t,
  ~ In X (FV_te t) ->
  lclosed_e Gamma0 I i t ->
  Gamma0 = X ~<: T :: Gamma ->
  lclosed_e Gamma I i t.
Proof.
  induction 2; intros; subst; 
    Simplify by Destruct notIn by eauto with strengthen_aux.
Qed.

Hint Resolve strengthen_lclosed_e_fvar_aux : strengthen_aux.
Hint Resolve strengthen_lclosed_e_ftvar_aux : strengthen_aux.
  
Lemma strengthen_ctxt_okay : forall Gamma Delta Gamma0 x T ,
  ctxt_okay Gamma0 ->
  Gamma0 = Gamma ++ x ~: T :: Delta ->
  ctxt_okay (Gamma ++ Delta).
Proof.
  induction Gamma; intros; subst; inversion H; eauto.
    simpl; econstructor; 
      Simplify by Destruct notIn by eauto with strengthen_aux.
    simpl; econstructor; 
      Simplify by Destruct notIn by eauto with strengthen_aux.
Qed.

Hint Resolve strengthen_ctxt_okay : strengthen_aux.

Lemma strengthen_subLH : forall m n,
  n < m ->
  forall U S Gamma0 Gamma x T Delta,
  subLH n Gamma0 U S ->
  Gamma0 = Gamma ++ x ~: T :: Delta ->
  subLH n (Gamma ++ Delta) U S.
Proof.
  induction m.
  firstorder using lt_n_O.
  destruct 2; intros; subst; eauto with strengthen_aux.
  econstructor; Destruct In by (try discriminate; eauto with arith).
  econstructor; eauto with arith.
  econstructor; Simplify by Destruct notIn by eauto with arith.
    rewrite list_cons_cons_move_app.
    eapply IHm; simpl; eauto with arith.
Qed.

Lemma strengthen_sub : forall Gamma x T Delta U U',
  sub (Gamma ++ x ~: T :: Delta) U U' ->
  sub (Gamma ++ Delta) U U'.
Proof.
  intros.
  destruct (sub_subLH H) as [n ?].
  apply subLH_sub with (n := n).
  eapply strengthen_subLH; eauto with arith.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Properties of [lclosed_e]
 Unlike [sub] which uses [lclosed_t] only, [typing] uses both [lclosed_t]
 and [lclosed_e]. This section presents properties of [lclosed_e] that 
 we will use in the rest. *)

(** [lclosed_e] is also invertible. *)
Lemma lclosed_e_lvar_split : forall Gamma t I i' a x T,
  ~ In x (FV_ee t) ->
  lclosed_e ((x ~: T) :: Gamma) I i' ({a ::~> x **} t) ->
    (exists i, lclosed_e Gamma I i t /\ remove eq_nat_dec a i = i').
Proof.
  induction t; intros.
  Simplify by subst.
    inversion H0; subst.
    exists (a :: emptyset); split; auto.
      Simplify by eauto. 
    inversion H0; subst.
    exists (n :: emptyset); split; auto.
      Simplify by eauto. 
  inversion H0; subst.
    exists (emptyset:list lvar); split; auto.
    destruct H5; auto.
    subst; firstorder.
  Simplify by eauto. 
    inversion H0; subst; exists (remove eq_nat_dec a i); 
      split; auto using list_remove_repeat.
    assert (~ In x (FV_ee (tm_abs a t t0))) by (simpl; auto).
    constructor 3.
    replace Gamma with (emptyset ++ Gamma); eauto.
    eapply strengthen_lclosed_t_fvar_app_aux; eauto.
    simpl; eauto.
    eauto using strengthen_lclosed_e_fvar_aux.
    inversion H0; subst.
      forwards Ha : (IHt _ _ _ _ _ H H8).
      destruct Ha as [S0 [Hb Hc]].
      exists (remove eq_nat_dec n S0).
      split.
        constructor 3; eauto.
        replace Gamma with (emptyset ++ Gamma); eauto.
        eapply strengthen_lclosed_t_fvar_app_aux; eauto; firstorder.
        rewrite <- Hc; auto using list_remove_twice.
  inversion H0; subst.
    Simplify by Destruct notIn by eauto.
    forwards Ha : (IHt1 _ _ _ _ _ H1 H6); destruct Ha as [ia [? ?]].
    forwards Hb : (IHt2 _ _ _ _ _ H2 H7); destruct Hb as [ib [? ?]].
    subst; exists (ia ++ ib); split; auto using list_remove_app.
  inversion H0; subst.
    forwards Ha : (IHt _ _ _ _ _ H H8); destruct Ha as [ia [? ?]].
    exists ia.
    split; auto.
    constructor; eauto.
    replace Gamma with (emptyset ++ Gamma); eauto.
    eapply strengthen_lclosed_t_fvar_app_aux; eauto; firstorder.
  inversion H0; subst.
    forwards Ha : (IHt _ _ _ _ _ H H6); destruct Ha as [Ia [? ?]].
    exists Ia.
    split; auto.
    constructor; eauto.
    replace Gamma with (emptyset ++ Gamma); eauto.
    eapply strengthen_lclosed_t_fvar_app_aux; eauto; firstorder.
Qed.

Lemma lclosed_e_ltvar_split : forall Gamma t I' i A X T,
  ~ In X (FV_te t) ->
  lclosed_e (X ~<: T :: Gamma) I' i ({A :~> X ^^} t) ->
    (exists I, lclosed_e Gamma I i t /\ remove eq_nat_dec A I = I').
Proof.
  induction t; intros; Simplify by eauto.
  inversion H0; subst;
    exists (emptyset:list ltvar); split; eauto. 
  inversion H0; subst.
    exists (emptyset:list ltvar); split; eauto. 
  inversion H0; subst.
    assert (~ In X (FV_tt t)) by Destruct notIn by auto.
    assert (~ In X (FV_te t0)) by Destruct notIn by auto.
    forwards Ha : (IHt _ _ _ _ _ H2 H8); destruct Ha as [Ia [? ?]].
    forwards Hb : (lclosed_t_ltvar_split _ _ H1 H6); destruct Hb as [Ib [? ?]].
    exists (Ib ++ Ia).
    subst; split; auto using list_remove_app.
  inversion H0; subst.
    assert (~ In X (FV_te t1)) by (Destruct notIn by auto).
    assert (~ In X (FV_te t2)) by (Destruct notIn by auto).
    forwards Ha : (IHt1 _ _ _ _ _ H1 H6); destruct Ha as [Ia [? ?]]; clear IHt1.
    forwards Hb : (IHt2 _ _ _ _ _ H2 H7); destruct Hb as [Ib [? ?]]; clear IHt2.
    exists (Ia ++ Ib).
    split; subst; auto using list_remove_app.
  assert (~ In X (FV_tt t)) by (Destruct notIn by auto).
  assert (~ In X (FV_te t0)) by (Destruct notIn by auto).
  inversion H0; subst.
  apply lclosed_t_ltvar_split in H8; [destruct H8 as [I0 [? ?]] | auto].
  exists (I0 ++ (remove eq_nat_dec A I2)).
  subst; split.
    constructor 5; eauto using strengthen_lclosed_e_ftvar_aux.
    rewrite list_remove_app; rewrite list_remove_repeat; auto.
  assert (~ In X (FV_tt t)) by (Destruct notIn by auto).
  assert (~ In X (FV_te t0)) by (Destruct notIn by auto).
  inversion H0; subst.
    forwards Ha : (IHt _ _ _ _ _ H2 H10); destruct Ha as [Ia [? ?]].
    forwards Hb : (lclosed_t_ltvar_split _ _ H1 H8); destruct Hb as [I0 [? ?]].
    exists (I0 ++ (remove eq_nat_dec n Ia)).
    subst; split.
      constructor 5; eauto using strengthen_lclosed_t_ftvar_aux.
      rewrite list_remove_app; rewrite list_remove_twice; auto.
  assert (~ In X (FV_te t)) by (Destruct notIn by auto).
  assert (~ In X (FV_tt t0)) by (Destruct notIn by auto).
  inversion H0; subst.
    forwards Ha : (IHt _ _ _ _ _ H1 H8); destruct Ha as [Ia [? ?]]; clear IHt.
    forwards Hb : (lclosed_t_ltvar_split _ _ H2 H9); destruct Hb as [Ib [? ?]].
    exists (Ia ++ Ib).
    subst; split; auto using list_remove_app.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Properties of substitution over terms.  
 For the proof of type safety, we deal with not only substitution over 
 types but also substitution over terms, and thus we will present its 
 properties in this section. *)

(** Variable substitution over terms has no effect if they do not 
 include such a variable. *)
Lemma subst_lvar_nochange_e : forall t Gamma I i x t',
  lclosed_e Gamma I i t ->
  ~ In x i ->
  {x ::~> t'} t = t.
Proof.
  induction t; intros; 
    Simplify by (inversion H; subst); f_equal; 
    Destruct notIn by eauto with nochange.
Qed.

Lemma subst_ltvar_nochange_e : forall t Gamma I i A S,
  lclosed_e Gamma I i t ->
  ~ In A I ->
  {A :~> S} t = t.
Proof.
  induction t; intros; inversion H; subst;
    Simplify by (f_equal; Destruct notIn by eauto with nochange).
Qed.

(** Parameter substitution over terms also has no effect on terms 
 if they do not include such a parameter. *)
Lemma subst_fvar_nochange_e : forall t t' x,
  ~ In x (FV_ee t) -> [x ::~> t'] t = t.
Proof.
  induction t; intros; Simplify by (f_equal; firstorder).
Qed.

Lemma subst_ftvar_nochange_e : forall t X S,
  ~ In X (FV_te t) -> ([ X :~> S ] t) = t.
Proof.
  induction t; intros; 
    Simplify by Destruct notIn by (f_equal; eauto with nochange).
Qed.

Hint Resolve subst_lvar_nochange_e subst_ltvar_nochange_e : nochange.
Hint Resolve subst_fvar_nochange_e subst_ftvar_nochange_e : nochange.

(** We may swap variable and parameter substitutions. *) 
Lemma subst_fvar_lvar_e : forall Gamma t t' a x y I,
  lclosed_e Gamma I emptyset t' ->
  x <> y ->
  [y ::~> t']({a ::~> x **} t) = {a ::~> x **}([y ::~> t']t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto with nochange).
Qed.

Lemma subst_lvar_rename_fvar_e : forall t a x y z,
  x <> z ->
  {a ::~> z **} ([x ::~> y **] t) = [x ::~> y **] ({a ::~> z **} t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto).
Qed.

Lemma subst_ltvar_fvar_e : forall t A X x t' Gamma I,
  lclosed_e Gamma emptyset I t' ->
  {A :~> X ^^}([x ::~> t'] t) = [x ::~> t']({A :~> X ^^} t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto with nochange). 
Qed.

Lemma subst_ltvar_rename_fvar_e : forall t A X x y,
  {A :~> X ^^} ([x ::~> y **] t) = [x ::~> y **] ({A :~> X ^^} t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto). 
Qed.

Lemma subst_ftvar_lvar_e : forall t t' X U x,
  [X :~> U]({x ::~> t'} t) = {x ::~> ([X :~> U] t')}([X :~> U] t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto).
Qed.

Lemma subst_ftvar_ltvar_e : forall t A X S S' Gamma,
  lclosed_t Gamma emptyset S ->
  [X :~> S] ({A :~> S'} t) = {A :~> [X ~> S] S'} ([X :~> S] t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto using subst_ftvar_ltvar_t).
Qed.

Lemma subst_ftvar_rename_ltvar_e : forall t A X Y S',
  [X :~> (Y ^^)] ({A :~> S'} t) = {A :~> [X ~>(Y^^)] S'} ([X :~> (Y^^)] t).
Proof.
  induction t; intros; 
    Simplify by (f_equal; eauto using subst_ftvar_rename_ltvar_t).
Qed.

(** We may replace a variable with a fresh parameter, and then replace 
 the parameter with a given type (or term) instead of directly replacing 
 the variable with the given type (or term). *)
Lemma subst_seq_fvar_lvar_e : forall t t' a x,
  ~ In x (FV_ee t) ->
  [x ::~> t']({a ::~> x **} t) = {a ::~> t'} t.
Proof.
  induction t; intros; 
    Simplify by (Destruct notIn by (f_equal; eauto with nochange)).   
Qed.

Lemma subst_seq_ftvar_ltvar_e : forall t S X,
  ~ In X (FV_te t) ->
  forall A,
    [X :~> S] ({A :~> (X ^^)} t) = {A :~> S} t.
Proof.
  induction t; intros; Simplify by f_equal;
    Destruct notIn by (eauto using subst_seq_ftvar_ltvar_t with nochange).
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Additional properties of [ctxt_okay]
 While presenting our solution to Challenge 1A, we already present some 
 properties of [ctxt_okay] related with type bindings. This section other 
 properties of [ctxt_okay] related with term bindings. *)
Lemma ctxt_okay_fvar_bind_lclosed_t : forall Gamma x T,
  ctxt_okay Gamma ->
  In (x ~: T) Gamma ->
  lclosed_t Gamma emptyset T.
Proof.
  induction Gamma; intros; eauto.
  inversion H0.
  destruct a.
    inversion H; subst.
    destruct (in_inv H0); [inversion H1; subst | ].
      unsimpl ((x ~: T :: emptyset) ++ Gamma).
      eapply lclosed_t_incl; Simplify by eauto with v62. 
      unsimpl ((n ~: t :: emptyset) ++ Gamma).
      eapply lclosed_t_incl; Simplify by eauto with v62. 
    inversion H; subst.
    destruct (in_inv H0); [inversion H1; subst | ].
      unsimpl ((n ~<: t :: emptyset) ++ Gamma).
      eapply lclosed_t_incl; Simplify by eauto with v62. 
Qed.

Lemma ctxt_okay_ftvar_bind_lclosed_t : forall Gamma x T,
  ctxt_okay Gamma ->
  In (x ~<: T) Gamma ->
  lclosed_t Gamma emptyset T.
Proof.
  induction Gamma; intros; eauto.
  inversion H0.
  destruct a.
    inversion H; subst.
    destruct (in_inv H0); [inversion H1; subst | ].
      unsimpl ((n ~: t :: emptyset) ++ Gamma).
      eapply lclosed_t_incl; Simplify by eauto with v62. 
    inversion H; subst.
    destruct (in_inv H0); [inversion H1; subst | ].
      unsimpl ((x ~<: T :: emptyset) ++ Gamma).
      eapply lclosed_t_incl; Simplify by eauto with v62. 
      unsimpl ((n ~<: t :: emptyset) ++ Gamma).
      eapply lclosed_t_incl; Simplify by eauto with v62. 
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Properties of [FV_tt], [FV_te], [FV_ee], and [FV_tc] *)
Lemma ftvar_bind_in_ctxt_preserve_not_in : forall Gamma T X Y,
  In (X ~<: T) Gamma
  -> ~ In Y (FV_tc Gamma)
  -> ~ In Y (FV_tt T).
Proof.
  induction Gamma; intros; eauto.
  destruct a; Simplify by eauto.
  destruct (in_inv H); [inversion H1; subst | ]; Destruct notIn by eauto.
  destruct (in_inv H); [inversion H1; subst | ]; Destruct notIn by eauto.
Qed.

Hint Resolve ftvar_bind_in_ctxt_preserve_not_in : incl_param.

Lemma not_in_FV_tt_dist_fsubst_tt : forall T X0 X U,
  ~ In X0 (FV_tt U)
  -> ~ In X0 (FV_tt T)
  -> ~ In X0 (FV_tt ([X ~> U] T)).
Proof.
  induction T; intros; Simplify by (Destruct notIn by eauto). 
Qed.

Hint Resolve not_in_FV_tt_dist_fsubst_tt : incl_param.

Lemma FV_te_rename_fvar_nochange : forall t x y,
  FV_te ([x ::~> y **] t) = FV_te t.
Proof.
  induction t; intros; Simplify by (f_equal; eauto). 
Qed.

Hint Resolve FV_te_rename_fvar_nochange : nochange.

Lemma not_in_FV_te_dist_fsubst_te : forall t X0 X T,
  ~ In X0 (FV_tt T)
  -> ~ In X0 (FV_te t)
  -> ~ In X0 (FV_te ([X :~> T] t)).
Proof.
  induction t; intros; 
    Simplify by (Destruct notIn by eauto with incl_param).
Qed.

Hint Resolve not_in_FV_te_dist_fsubst_te : incl_param.

Lemma FV_ee_subst_ftvar_nochange : forall t X T,
  FV_ee ([X :~> T] t) = FV_ee t.
Proof.
  induction t; intros; simpl; Simplify by eauto.
    f_equal; eauto.
Qed.

Hint Resolve FV_ee_subst_ftvar_nochange : nochange.

Lemma not_in_FV_tc_dist_ctxt_subst_ftvar_map : forall Gamma X0 X T,
  ~ In X0 (FV_tc Gamma)
  -> ~ In X0 (FV_tt T)
  -> ~ In X0 (FV_tc ([X ==> T] Gamma)).
Proof.
  induction Gamma; intros; eauto.
  destruct a; simpl ctxt_ftvar_subst_map; 
    Simplify by (Destruct notIn by eauto with incl_param).
Qed.

Hint Resolve not_in_FV_tc_dist_ctxt_subst_ftvar_map : incl_param.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Basic properties of [typing] *)

(** [typing] deals with well-formed contexts. *) 
Lemma typing_ctxt_okay : forall Gamma t T,
  typing Gamma t T ->
  ctxt_okay Gamma.
Proof.
  induction 1; eauto.
    inversion IHtyping; eauto.
    inversion IHtyping; eauto.
Qed.

(** [typing] deals with locally closed types only. *) 
Lemma typing_lclosed_t : forall Gamma t T,
  typing Gamma t T ->
  lclosed_t Gamma emptyset T.
Proof.
  induction 1; Destruct notIn by idtac.
    eauto using ctxt_okay_fvar_bind_lclosed_t.
    rewrite <- emptyset_plus; econstructor; eauto.
      unsimpl (emptyset ++ Gamma).
      eapply strengthen_lclosed_t_fvar_app_aux; simpl; eauto.
    inversion IHtyping1; subst; eauto with v62.
      destruct (app_eq_nil _ _ H1) as [? ?]; subst; eauto.
    destruct (lclosed_t_ltvar_split _ _ H4 IHtyping) as [I [? ?]].
    replace (emptyset : list ltvar) 
      with (emptyset ++ (remove eq_nat_dec B I)).
    econstructor; eauto.
    inversion IHtyping; subst.
      destruct (sub_lclosed_t H0) as  [? ?].
      destruct (app_eq_nil _ _ H1) as [? ?]; subst. 
      simpl; eauto using lclosed_t_subst_ltvar.
    destruct (sub_lclosed_t H0) as [? ?]; eauto.
Qed.

(** [typing] deals with locally closed terms only. *) 
Lemma typing_lclosed_e : forall Gamma t T,
  typing Gamma t T ->
  lclosed_e Gamma emptyset emptyset t.
Proof.
  induction 1; intros; eauto.
  destruct (lclosed_e_lvar_split _ _ H1 IHtyping) as [i [? ?]].
  rewrite <- H4 at 2; rewrite <- emptyset_plus; eauto.
  rewrite <- emptyset_plus; eauto.
  Destruct notIn by idtac.
  destruct (lclosed_e_ltvar_split _ _  H3 IHtyping) as [I [? Hsplit]].
  rewrite <- Hsplit at 1.
  unsimpl (emptyset ++ remove eq_nat_dec A I); eauto.
  destruct (sub_lclosed_t H0) as [? ?].
  rewrite <- emptyset_plus; eauto.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Renaming property of [typing] 
 As is well-known in the literature, the exists-fresh style mechanization
 necessitates various renaming properties. This section proves two lemmas 
 which states the renaming property of [typing] for term and type parameters, 
 respectively. 
 
 *** Auxiliary lemmas 
 This section presents several auxiliary lemmas that the proof of the renaming
 lemmas uses. *)
Lemma fvar_rename_ctxt_bind_in : forall Gamma bind x y,
  In bind Gamma -> In (ctxt_fvar_rename x y bind) ([x ::=> y] Gamma).
Proof.
  induction Gamma; simpl; intros; Simplify by eauto.
    destruct (in_inv H); subst; Destruct In by eauto.
Qed.

Lemma fvar_rename_ctxt_nochange : forall Gamma x y,
  ~ In x (dom_ec Gamma)
  -> [x ::=> y] Gamma = Gamma.
Proof.
  induction Gamma; intros; Simplify by eauto.
  destruct a; simpl; Simplify by (Destruct notIn by eauto). 
    rewrite IHGamma; eauto.
    rewrite IHGamma; eauto.
Qed.

Hint Resolve fvar_rename_ctxt_nochange : nochange.

Lemma fvar_rename_ctxt_preserve_not_in_dom_ec : forall Gamma x,
  ~ In x (dom_ec Gamma) ->
  forall y z,
    x <> z ->
    ~ In x (dom_ec ([y ::=> z] Gamma)).
Proof.
  induction Gamma; intros; eauto.
  destruct a; simpl; Simplify by (Destruct notIn by eauto).
Qed.

Lemma fvar_rename_ctxt_dom_tc_nochange : forall Gamma x y,
  dom_tc ([x ::=> y] Gamma) = dom_tc Gamma.
Proof.
  induction Gamma; eauto; intros.
  destruct a; simpl; Simplify by eauto.
    f_equal; eauto. 
Qed.

Hint Resolve fvar_rename_ctxt_nochange : nochange.

Lemma fvar_rename_ctxt_FV_tc_nochange : forall Gamma x y,
  FV_tc ([x ::=> y] Gamma) = FV_tc Gamma.
Proof.
  induction Gamma; intros; Simplify by eauto.
  destruct a; simpl; Simplify by eauto; rewrite IHGamma; auto.
Qed.

Hint Resolve fvar_rename_ctxt_nochange : nochange.

(** *** Term parameter renaming 
 This section presents the proof of Lemma [typingLH_subst_lvar_rename_fvar]
 which states the term parameter renaming property of [typing]. The proof
 proceeds by induction on the size of [typing] proofs. *)
Lemma ctxt_okay_rename_fvar : forall Gamma x y,
  ctxt_okay Gamma ->
  ~ In y (dom_ec Gamma) ->
  ctxt_okay ([x ::=> y] Gamma).
Proof.
  induction Gamma; intros; auto.
  destruct a; simpl; Simplify by eauto.
  inversion H; subst.
  constructor; Destruct notIn by eauto. 
    rewrite fvar_rename_ctxt_nochange; auto.
    eapply lclosed_t_incl with (Gamma := Gamma); eauto.
      rewrite fvar_rename_ctxt_dom_tc_nochange; eauto with v62.
  inversion H; subst.
  constructor; Destruct notIn by eauto.
    eapply fvar_rename_ctxt_preserve_not_in_dom_ec; eauto.
    eapply lclosed_t_incl with (Gamma := Gamma); eauto.
      rewrite fvar_rename_ctxt_dom_tc_nochange; eauto with v62.
  inversion H; subst.
  constructor; Destruct notIn by eauto.
    rewrite fvar_rename_ctxt_dom_tc_nochange; eauto.
    eapply lclosed_t_incl with (Gamma := Gamma); eauto.
      rewrite fvar_rename_ctxt_dom_tc_nochange; eauto with v62.
Qed.

Hint Resolve ctxt_okay_rename_fvar : rename_aux.

Lemma sub_rename_fvar : forall Gamma T U x y,
  sub Gamma T U
  -> ~ In y (dom_ec Gamma)
  -> sub ([ x ::=> y ] Gamma) T U.
Proof.
  induction 1; intros; eauto.
  econstructor; eauto with rename_aux.
    apply lclosed_t_incl with (Gamma := Gamma); eauto.
      rewrite fvar_rename_ctxt_dom_tc_nochange; eauto using incl_refl.
  econstructor; eauto with rename_aux.
    apply lclosed_t_incl with (Gamma := Gamma); eauto.
      rewrite fvar_rename_ctxt_dom_tc_nochange; eauto using incl_refl.
  econstructor; eauto.
    replace (X ~<: T) with (ctxt_fvar_rename x y (X ~<: T)) by auto.
    eauto using fvar_rename_ctxt_bind_in.
  simpl in IHsub2.
  econstructor; eauto.
    rewrite fvar_rename_ctxt_FV_tc_nochange; eauto.
Qed.

Hint Resolve sub_rename_fvar : rename_aux.

Lemma typingLH_rename_fvar : forall m n Gamma t T x y,
  n < m
  -> typingLH n Gamma t T
  -> ~ In y (dom_ec Gamma)
  -> typingLH n ([ x ::=> y ] Gamma) ([ x ::~> y ** ] t) T.
Proof.
  induction m.
  firstorder using lt_n_O.
  destruct 2; intros; subst.
  Simplify by (econstructor; eauto with rename_aux).
    replace (y ~: T) with (ctxt_fvar_rename x y  (x ~: T)) 
      by (simpl; Simplify by eauto);
      eauto using fvar_rename_ctxt_bind_in.
    replace (x0 ~: T) with (ctxt_fvar_rename x y  (x0 ~: T)) 
      by (simpl; Simplify by eauto);
      eauto using fvar_rename_ctxt_bind_in.
  set (L := x :: x0 :: y :: dom_ec Gamma ++ 
              dom_ec ([x ::=> y] Gamma) ++ FV_ee ([ x ::~> y **] t)).
  destruct (pick_fresh L) as [x' Hfresh].
  unfold L in Hfresh.
  constructor 2 with (x := x'); Destruct notIn by eauto.
    eapply lclosed_t_incl; eauto.
      rewrite fvar_rename_ctxt_dom_tc_nochange; eauto using incl_refl.
    rewrite subst_lvar_rename_fvar_e; auto.
    replace (x' ~: T :: ([x ::=> y]Gamma)) 
      with ([x ::=> y] (x' ~: T :: Gamma))
      by (simpl; Simplify by (f_equal; eauto with nochange)). 
    eapply IHm; Simplify by (Destruct notIn by eauto with arith).
    rewrite <- subst_seq_fvar_lvar_e with (x := x0); eauto.
    replace (x' ~: T :: Gamma) with ([x0 ::=> x'] (x0 ~: T :: Gamma))
      by (simpl; Simplify by (f_equal; eauto with nochange)).
    apply IHm; Simplify by (Destruct notIn by eauto with arith).
  econstructor; eapply IHm; eauto with arith.
  econstructor.
    eapply lclosed_t_incl; eauto.
      rewrite fvar_rename_ctxt_dom_tc_nochange; eauto using incl_refl.
    rewrite fvar_rename_ctxt_FV_tc_nochange; eauto.
    rewrite FV_te_rename_fvar_nochange; auto.
    replace (X ~<: T :: ([x ::=> y] Gamma)) 
      with ([x ::=> y] (X ~<: T :: Gamma)) by auto.
    rewrite subst_ltvar_rename_fvar_e.
    eapply IHm; eauto with arith.
  econstructor; eauto using sub_rename_fvar with arith.
  econstructor; eauto using sub_rename_fvar with arith.
Qed.

Hint Resolve typingLH_rename_fvar : rename_aux.

Lemma typingLH_subst_lvar_rename_fvar : forall t a y z T U n Gamma,
  typingLH n (y ~: T :: Gamma) ({a ::~> y**} t) U
  -> ~ In y (FV_ee t)      
  -> ~ In z (dom_ec Gamma)
  -> typingLH n (z ~: T :: Gamma) ({a ::~> z**} t) U.
Proof.
  intros.
  destruct (y == z); subst; eauto.
  rewrite <- subst_seq_fvar_lvar_e with (x := y); eauto.
  replace (z ~: T :: Gamma) with ([y ::=> z] (y ~: T :: Gamma)).
  apply typingLH_rename_fvar with (m := S n);
    Simplify by (Destruct notIn by eauto with arith).
  forwards Hokay : (typing_ctxt_okay (typingLH_typing H)).
  inversion Hokay; subst.
  simpl; Simplify by (f_equal; eauto with nochange).
Qed.

(** *** Type parameter renaming 
 This section presents the proof of Lemma [typingLH_subst_ltvar_rename_ftvar]
 which states the type parameter renaming property of [typing]. The proof
 proceeds by induction on the size of [typing] proofs. *)
Lemma typingLH_rename_ftvar : forall m n Gamma t T X Y,
  n < m
  -> typingLH n Gamma t T
  -> ~ In Y (dom_tc Gamma)
  -> typingLH n ([ X => Y ] Gamma) ([ X :~> Y ^^ ] t) ([ X ~> Y ^^] T).
Proof.
  induction m.
  firstorder using lt_n_O.
  destruct 2; intros; subst; simpl.
  econstructor; eauto with rename_aux.
    replace (x ~: ([X ~> Y ^^] T)) 
      with (ctxt_ftvar_rename X Y (x ~: T)) 
      by auto; eauto using ftvar_rename_ctxt_bind_in.
  constructor 2 with (x := x); Simplify by (eauto with rename_aux).
    rewrite ftvar_rename_ctxt_dom_ec_nochange; auto.
    rewrite FV_ee_subst_ftvar_nochange; auto.
    replace (x ~: ([X ~> Y ^^] T) :: ([X => Y] Gamma)) 
      with ([X => Y] (x ~: T :: Gamma)) by auto.
    unsimpl ([X :~> Y ^^] x ** ).
    rewrite <- subst_ftvar_lvar_e.
    eapply IHm; eauto with arith.
  constructor 3 with (T := [X ~> Y ^^] T).
    replace (([X ~> Y ^^] T) --> ([X ~> Y ^^] U)) 
      with ([X ~> Y ^^] (T --> U)) by auto.
    eapply IHm; eauto with arith.
    eapply IHm; eauto with arith.
  set (L := X :: Y :: X0 :: dom_tc Gamma ++ 
            FV_tc ([X => Y] Gamma) ++ 
            FV_te ([X :~> Y ^^] t) ++ FV_tt ([X ~> Y ^^] U)).
  destruct (pick_fresh L) as [X' Hfresh].
  unfold L in Hfresh.
  constructor 4 with (X := X'); 
    Destruct notIn by (eauto with rename_aux).
    replace (X' ~<: ([X ~> Y ^^] T) :: ([X => Y] Gamma)) 
      with ([X => Y] (X' ~<: T :: Gamma)) by (simpl; Simplify by eauto).
    replace (X' ^^) 
      with ([X ~> Y ^^] X' ^^) by (Simplify by eauto). 
    rewrite <- subst_ftvar_rename_ltvar_e.
    rewrite <- subst_ftvar_rename_ltvar_t.
    eapply IHm; Simplify by (Destruct notIn by (eauto with arith)).
    replace (X' ~<: T :: Gamma) with ([X0 => X'] X0 ~<: T :: Gamma).
    rewrite <- subst_seq_ftvar_ltvar_e with (X := X0)
      by Destruct notIn by eauto.
    rewrite <- subst_seq_ftvar_ltvar_t with (X := X0)
      by Destruct notIn by eauto.
    eapply IHm; Simplify by (Destruct notIn by (eauto with arith)).
    simpl; Simplify by eauto. 
    rewrite subst_ftvar_nochange_t; eauto with incl_param.
    rewrite ftvar_rename_ctxt_nochange; eauto.
  rewrite subst_ftvar_ltvar_t with (Gamma := Y ~<: S :: nil);
    [ idtac | econstructor; Simplify by (Destruct In by eauto) ].
  constructor 5 with (U := [X ~> Y ^^] U); eauto with rename_aux.
    replace (typ_all A ([X ~> Y ^^] U) ([X ~> Y ^^] S)) 
      with ([X ~> Y ^^] (typ_all A U S)) by auto.
    eapply IHm; eauto with arith.
  constructor 6 with (T := [X ~> Y ^^] T); eauto with arith rename_aux.
Qed.

Hint Resolve typingLH_rename_ftvar : rename_aux.

Lemma typingLH_subst_ltvar_rename_ftvar : forall n Gamma A B X T t U Y,
  typingLH n (X ~<: T :: Gamma) ({ A :~> X ^^ } t) ({ B ~> X ^^ } U)
  -> ~ In X (FV_te t)
  -> ~ In X (FV_tt U)
  -> ~ In Y (dom_tc Gamma)
  -> typingLH n (Y ~<: T :: Gamma) ({ A :~> Y^^} t) ({ B ~> Y^^} U).
Proof.
  intros; destruct (X == Y); subst; eauto.
  forwards Hokay : typing_ctxt_okay (typingLH_typing H).
  inversion Hokay; subst.
  rewrite <- subst_seq_ftvar_ltvar_t with (X := X); eauto.
  rewrite <- subst_seq_ftvar_ltvar_e with (X := X); eauto.
  replace (Y ~<: T :: Gamma) with ([X => Y] (X ~<: T :: Gamma)).
  eapply typingLH_rename_ftvar with (m := S n); 
    Simplify by (Destruct notIn by eauto).
  simpl; Simplify by eauto. 
    rewrite subst_ftvar_nochange_t; [ | eauto with incl_param ].
    rewrite ftvar_rename_ctxt_nochange; eauto using ctxt_okay_unique_ftvar.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Structural properties of [typing]
 *** Permutation 
 This section proves Lemma [permuting_typingLH] which states the permutation 
 property of [typing]. *)
Lemma permuting_typingLH : forall m n,
  n < m ->
  forall Gamma0 bind bind' Gamma Delta t T,
    typingLH n Gamma0 t T
    -> Gamma0 = Gamma ++ bind :: bind' :: Delta
    -> ctxt_okay (Gamma ++ bind' :: bind :: Delta)
    -> typingLH n (Gamma ++ bind' :: bind :: Delta) t T.
Proof.
  induction m.
  firstorder using lt_n_O. 
  destruct 2; intros; subst.
  econstructor; eauto with permuting_aux.
  set (L := dom_ec Gamma ++ dom_ec (bind' :: bind :: Delta) ++ FV_ee t).
  destruct (pick_fresh L) as [x' Hfresh].
  unfold L in Hfresh.
  constructor 2 with (x := x'); 
    Simplify by (Destruct notIn by eauto with permuting_aux).
    rewrite list_cons_cons_move_app.
      eapply IHm; eauto.
        eauto with arith.
      rewrite <- list_cons_cons_move_app.
      eapply typingLH_subst_lvar_rename_fvar with (y := x); eauto.
          destruct bind; destruct bind'; Simplify by (Destruct notIn by eauto).
      rewrite <- list_cons_cons_move_app; econstructor;
        Simplify by (Destruct notIn by (eauto with permuting_aux)).
  econstructor; eapply IHm; eauto with arith.
  set (L := FV_tc Gamma ++ FV_tc (bind' :: bind :: Delta) ++ 
            FV_te t ++ FV_tt U).
  destruct (pick_fresh L) as [X' Hfresh].
  unfold L in Hfresh.
  constructor 4 with (X := X'); 
    Simplify by (Destruct notIn by (eauto with permuting_aux)).
    rewrite list_cons_cons_move_app.
      eapply IHm; eauto.
        eauto with arith.
        rewrite <- list_cons_cons_move_app. 
        eapply typingLH_subst_ltvar_rename_ftvar with (X := X); eauto.
        forwards Hokay : typing_ctxt_okay (typingLH_typing H3).
          inversion Hokay; subst; eauto with incl_param.
        destruct bind; destruct bind'; Simplify by (Destruct notIn by eauto).
      rewrite <- list_cons_cons_move_app; econstructor;
        Simplify by (Destruct notIn by (eauto with permuting_aux)).
  destruct (sub_subLH H1) as [k' ?].
  econstructor; eauto with permuting_aux arith.
  destruct (sub_subLH H1) as [k' ?].
  econstructor; eauto with permuting_aux arith.
Qed.
 
Hint Resolve permuting_typingLH : permuting_aux.

(** *** Weakening 
 This section proves Lemma [weakening_typing] which states the weakening 
 property of [typing]. The proof proceeds by induction on the size of 
 [typing] proofs. (See Lemma [weakening_typingLH] for details) *)
Lemma weakening_typingLH : forall m n,
  n < m ->
  forall Gamma t T bind,
    typingLH n Gamma t T
    -> ctxt_okay (bind :: Gamma)
    -> typingLH n (bind :: Gamma) t T.
Proof.
  induction m.
  firstorder using lt_n_O.
  destruct 2; intros; subst.
  econstructor; eauto with v62.
  set (L := x :: (dom_ec Gamma ++ dom_ec (bind :: Gamma) ++ FV_ee t)).
  destruct (pick_fresh L) as [x' Hfresh].
  unfold L in Hfresh.
  assert (lclosed_t (bind :: Gamma) emptyset T).
    eapply lclosed_t_incl with (Gamma := Gamma); eauto.
      destruct bind; Simplify by eauto with v62.
  constructor 2 with (x := x'); Simplify by (Destruct notIn by eauto).
    unsimpl (emptyset ++ x' ~: T :: bind :: Gamma).
      eapply permuting_typingLH; simpl; eauto.
      eapply IHm; eauto.
        eauto with arith.
        eapply typingLH_subst_lvar_rename_fvar with (y := x); eauto.
        destruct bind; eauto;
          inversion H4; subst; econstructor;
            Simplify by (Destruct notIn by eauto);
            eapply lclosed_t_incl with (Gamma := Gamma);
              Simplify by eauto with v62.
  econstructor; eauto with arith.
  set (L := dom_tc Gamma ++ FV_tc (bind :: Gamma) ++ 
            (FV_te t ++ FV_tt U) ++ FV_tt T).
  destruct (pick_fresh L) as [X' Hfresh].
  unfold L in Hfresh.
  assert (lclosed_t (bind :: Gamma) emptyset T).
    eapply lclosed_t_incl with (Gamma := Gamma); eauto.
      destruct bind; Simplify by eauto with v62.
  constructor 4 with (X := X'); Simplify by (Destruct notIn by eauto).
    unsimpl (emptyset ++ X' ~<: T :: bind :: Gamma).
      eapply permuting_typingLH; simpl; eauto.
      eapply IHm; eauto.
        eauto with arith.
        eapply typingLH_subst_ltvar_rename_ftvar with (X := X); 
          eauto with incl_param.
        destruct bind; eauto;
          inversion H4; subst; econstructor; 
            Simplify by (Destruct notIn by eauto);
            eapply lclosed_t_incl with (Gamma := Gamma); 
              Simplify by eauto with v62.
  econstructor; eauto using weakening_sub_cons with arith.
  econstructor; eauto using weakening_sub_cons with arith.
Qed.

Lemma weakening_typing : forall Gamma t T bind,
    typing Gamma t T
    -> ctxt_okay (bind :: Gamma)
    -> typing (bind :: Gamma) t T.
Proof.
  intros.
  forwards Ha : typing_typingLH H.
  destruct Ha as [n H'].
  eauto using weakening_typingLH.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Substitution lemma 
 This section presents the main result: [typing] is stable under type
 and term parameter substitution.  

 *** Auxiliary lemmas 
 This section presents several auxiliary lemmas that we use in the rest 
 of proofs. *)
Lemma ftvar_subst_ctxt_bind_in : forall Gamma X T bind,
  In bind Gamma ->
  In (ctxt_ftvar_subst X T bind) ([X ==> T]Gamma).
Proof.
  induction Gamma; intros; Simplify by eauto.
    destruct (in_inv H); subst.
      left; eauto.
      right; eauto.
Qed.

Lemma ftvar_subst_ctxt_dom_tc_nochange : forall X T Gamma,
  dom_tc ([X ==> T] Gamma) = dom_tc Gamma.
Proof.
  induction Gamma; intros; eauto.
  destruct a; Simplify by eauto.
    f_equal; auto.
Qed.

Hint Resolve ftvar_subst_ctxt_dom_tc_nochange : nochange.

Lemma ftvar_subst_ctxt_dom_ec_nochange : forall Gamma X T,
  dom_ec ([X ==> T] Gamma) = dom_ec Gamma.
Proof.
  induction Gamma; intros; eauto.
  destruct a; Simplify by eauto. 
    f_equal; eauto. 
Qed.

Hint Resolve ftvar_subst_ctxt_dom_ec_nochange : nochange.

Lemma ftvar_subst_ctxt_nochange : forall Gamma X T,
  ~ In X (FV_tc Gamma)
  -> Gamma = [X ==> T] Gamma.
Proof.
  induction Gamma; intros; eauto.
  destruct a; Simplify by simpl.
  rewrite subst_ftvar_nochange_t; Destruct notIn by eauto.
  rewrite <- IHGamma; Destruct notIn by eauto.
  rewrite subst_ftvar_nochange_t; Destruct notIn by eauto.
  rewrite <- IHGamma; Destruct notIn by eauto.
Qed.

Hint Resolve ftvar_subst_ctxt_nochange : nochange.

(** *** Type parameter substitution lemma
 We first prove Lemma [typing_subst_ftvar] which shows that [typing] 
 is stable under type parameter substitution. The proof proceeds by 
 induction on the size of [typing] proofs. Note the use of the renaming 
 lemmas in the [typing_tabs] cases. Since the term binding does not 
 conflict with the type parameter, the renaming lemma is not used in 
 the [typing_abs] case. *)
Lemma lclosed_t_subst_ftvar_remove : forall T U X S I Gamma Delta Gamma0,
  lclosed_t Gamma0 I U ->
  Gamma0 = (Gamma ++ (X~<: T) :: Delta) ->
  lclosed_t Delta emptyset S ->
  lclosed_t (([X ==> S] Gamma) ++ Delta) I ([X ~> S] U).
Proof.
  induction 1; intros; subst; Simplify by eauto.
  eapply lclosed_t_incl; Simplify by eauto.
    eauto with v62.
  econstructor; Simplify by auto.
    rewrite ftvar_subst_ctxt_dom_tc_nochange; Destruct In by (try congruence).
Qed.

Hint Resolve lclosed_t_subst_ftvar_remove : subst_aux.

Lemma lclosed_t_subst_ftvar : forall Gamma0 I T Gamma X U Delta,
  lclosed_t Gamma0 I T -> 
  Gamma0 = Gamma ++ (X ~<: U :: Delta) -> 
  forall U',
    sub Delta U' U ->  
    lclosed_t (([X ==> U'] Gamma) ++ Delta) I ([X ~> U'] T).
Proof.
  induction 1; intros; simpl; Simplify by eauto. 
  destruct (sub_lclosed_t H1) as [? _].
    eapply lclosed_t_incl with (Gamma := Delta); Simplify by eauto with v62.
  econstructor; subst; Simplify by idtac; 
    rewrite ftvar_subst_ctxt_dom_tc_nochange; 
      Destruct In by (eauto; congruence).
Qed.

Hint Resolve lclosed_t_subst_ftvar : subst_aux.

Lemma ctxt_okay_subst_ftvar : forall Gamma X T Delta,
  ctxt_okay (Gamma ++ (X ~<: T :: Delta))
  -> forall U,
    sub Delta U T
    -> ctxt_okay (([X ==> U] Gamma) ++ Delta).
Proof.
  induction Gamma; intros.
  simpl in H; simpl; inversion H; eauto.
  rewrite <- list_cons_cons_move_app in H.
  destruct a; simpl; Simplify by eauto.
    inversion H; subst. 
    econstructor; Simplify by eauto using lclosed_t_subst_ftvar.
      rewrite ftvar_subst_ctxt_dom_ec_nochange; Destruct notIn by eauto.
    inversion H; subst.
    econstructor; Simplify by eauto using lclosed_t_subst_ftvar.
      rewrite ftvar_subst_ctxt_dom_tc_nochange; Destruct notIn by eauto.
Qed.

Hint Resolve ctxt_okay_subst_ftvar : subst_aux.

Lemma sub_subst_ftvar_aux : forall m n U' U X T Gamma0 Gamma Delta,
  n < m
  -> subLH n Gamma0 U' U
  -> Gamma0 = (Gamma ++ (X ~<: T :: Delta))
  -> forall S',
    sub Delta S' T
    -> sub (([X ==> S'] Gamma) ++ Delta) ([X ~> S'] U') ([X ~> S'] U).
Proof.
  induction m.
  firstorder using lt_n_O.
  destruct 2; intros; subst.
  simpl; econstructor; eauto using ctxt_okay_subst_ftvar.
    destruct (sub_lclosed_t H3) as [? ?]. 
    eapply lclosed_t_subst_ftvar_remove with (T := T); eauto.
  destruct (sub_lclosed_t H3) as [? ?]; eauto.
  simpl; Simplify by eauto.
    eapply sub_reflexivity_aux; eauto using ctxt_okay_subst_ftvar.
    eapply lclosed_t_incl with (Gamma := Delta); Simplify by eauto with v62.
    eapply sub_reflexivity_aux; eauto using ctxt_okay_subst_ftvar.
      replace (X0 ^^) with ([X ~> S'] X0^^) by Simplify by eauto.
      eauto using lclosed_t_subst_ftvar_remove.
  assert (n < m) by auto with arith.
  forwards Hokay : (sub_ctxt_okay (subLH_sub H1)).
  assert (ctxt_okay (([X ==> S']Gamma) ++ Delta)).
    eauto using ctxt_okay_subst_ftvar.
  simpl; Simplify by eauto.
  forwards IHsub : IHm H2 H1 H3; eauto.
  apply sub_transitivity with (U := [X ~> S'] T0); auto.
  assert (T0 = T).
    eapply ctxt_okay_unique_ftvar_bind 
      with (Gamma := Gamma ++ X ~<: T :: Delta); eauto.
      Destruct In by eauto.
  subst T.
  destruct (sub_lclosed_t H3) as [? ?].
  assert (~ In X (FV_tt T0)).
    forwards Hokay' : ctxt_okay_app Hokay.
    inversion Hokay'; eauto with incl_param.
  rewrite -> subst_ftvar_nochange_t by eauto.
  eauto using weakening_sub_concat.
  Destruct In by auto.
  constructor 3 with (T := [X ~> S'] T0); eauto.
  forwards Ha : ftvar_subst_ctxt_bind_in Gamma X S' H0.
  simpl in Ha; Destruct In by eauto.
  inversion H0; subst; congruence.
  constructor 3 with (T := T0); Destruct In by eauto.
  replace T0 with ([X ~> S'] T0); eauto.
  apply subst_ftvar_nochange_t; Destruct notIn by (eauto with incl_param).
    forwards Hokay' : ctxt_okay_app Hokay.
    inversion Hokay'; subst.
    forwards Hclosed : ctxt_okay_ftvar_bind_lclosed_t H8 H0.
    eauto with incl_param.
  assert (n1 < m) by eauto with arith.
  assert (n2 < m) by eauto with arith.
  econstructor; eauto.
  set (L := X :: (FV_tc (([X ==> S']Gamma) ++ Delta)) ++
            (FV_tt ([X ~> S'] T2)) ++ (FV_tt ([X ~> S'] U2)) ++
            (dom_tc ((X0 ~<: U1 :: Gamma) ++ X ~<: T :: Delta))).
  destruct (pick_fresh L) as [Y Hfresh'].
  unfold L in Hfresh'.
  assert (n1 < m) by eauto with arith.
  assert (n2 < m) by eauto with arith.
  simpl; constructor 5 with (X := Y); eauto.
    Simplify by (Destruct notIn by eauto).
    Simplify by (Destruct notIn by eauto).
    replace (Y ~<: ([X ~> S']U1) :: ([X ==> S']Gamma) ++ Delta) 
      with (([X ==> S'] (Y ~<: U1 :: Gamma)) ++ Delta); 
      [ | simpl; rewrite list_cons_cons_move_app; eauto ].
    replace (Y ^^) with ([X ~> S'] (Y ^^));
      [ | simpl; Simplify by (Destruct notIn by eauto) ].
    destruct (sub_lclosed_t H3) as [? ?].
    repeat erewrite <- subst_ftvar_ltvar_t; eauto.
    eapply IHm; eauto with arith.
    rewrite <- subst_seq_ftvar_ltvar_t with (A := A) (X := X0) 
      by Destruct notIn by eauto.
    rewrite <- subst_seq_ftvar_ltvar_t with (A := B) (X := X0) 
      by Destruct notIn by eauto.
    replace ((Y ~<: U1 :: Gamma) ++ X ~<: T :: Delta) 
      with ([X0 => Y ] (((X0 ~<: U1 :: Gamma) ++ X ~<: T :: Delta)));
      [ | simpl; Simplify by eauto ].
    eapply sub_rename_ftvar_aux; Destruct notIn by (eauto with arith).
    forwards Hokay : (sub_ctxt_okay (subLH_sub H0_0)).
    inversion Hokay; subst.
    rewrite subst_ftvar_nochange_t by (eauto with incl_param).
    rewrite ftvar_rename_ctxt_nochange; Simplify by (Destruct notIn by eauto).
Qed.

Lemma sub_subst_ftvar : forall U' U Gamma X T Delta,
  sub (Gamma ++ X ~<: T :: Delta) U' U
  -> forall T',
    sub Delta T' T
    -> sub (([X ==> T'] Gamma) ++ Delta) ([X ~> T'] U') ([X ~> T'] U).
Proof.
  intros.
  forwards Ha : sub_subLH H.
  destruct Ha as [n H'].
  eauto using sub_subst_ftvar_aux.
Qed.

Hint Resolve sub_subst_ftvar : subst_aux.

Lemma typing_subst_ftvar_aux : forall m n Gamma0 t T Gamma X U U' Delta,
  n < m
  -> typingLH n Gamma0 t T
  -> Gamma0 = Gamma ++ X ~<: U :: Delta
  -> sub Delta U' U
  -> typingLH n (([X ==> U']Gamma) ++ Delta) ([X :~> U'] t) ([X ~> U'] T).
Proof.
  induction m.
  firstorder using lt_n_O.
  destruct 2; intros; subst.
  simpl; econstructor; eauto with subst_aux.
    replace (x ~: ([X ~> U'] T)) with (ctxt_ftvar_subst X U' (x ~: T)) by auto.
    assert (~ In X (FV_tc Delta)).
      forwards Hokay : ctxt_okay_app H0.
      eauto using ctxt_okay_unique_ftvar.
    rewrite ftvar_subst_ctxt_nochange 
      with (Gamma := Delta) (X := X) (T := U') by auto.
    unfold ctxt_ftvar_subst_map; rewrite <- map_app.
    eapply ftvar_subst_ctxt_bind_in.
    Destruct In by eauto.
    inversion H1.
  destruct (sub_lclosed_t H5) as  [? ?].
  simpl; constructor 2 with (x := x).
    eapply lclosed_t_subst_ftvar_remove; eauto.
    Simplify by 
    (rewrite ftvar_subst_ctxt_dom_ec_nochange; Destruct notIn by eauto).
    Simplify by 
    (rewrite FV_ee_subst_ftvar_nochange; Destruct notIn by eauto).
    unsimpl ([X :~> U'] x ** ).
    rewrite <- subst_ftvar_lvar_e; rewrite list_cons_cons_move_app.
    replace (x ~: ([X ~> U'] T) :: ([X ==> U'] Gamma)) 
      with ([X ==> U'] (x ~: T :: Gamma)) by auto.
    eapply IHm; eauto with arith.
    rewrite <- list_cons_cons_move_app; eauto.
  simpl; constructor 3 with (T := [X ~> U'] T).
  unsimpl ([X ~> U'] (T --> U0)).
  eapply IHm; eauto with arith.
  eapply IHm; eauto with arith.
  destruct (sub_lclosed_t H5) as [? ?].
  simpl; constructor 4 with (X := X0).
  eapply lclosed_t_subst_ftvar_remove; Simplify by eauto.
  Simplify by (Destruct notIn by eauto 7 with incl_param). 
  Simplify by (Destruct notIn by eauto 7 with incl_param).
  replace (X0 ^^) with ([X ~> U'] X0 ^^);
    [ idtac | simpl; Simplify by (Destruct notIn by congruence) ].
  rewrite <- subst_ftvar_ltvar_e with (Gamma := Delta) by auto.
  rewrite <- subst_ftvar_ltvar_t with (Gamma := Delta) by auto.
  rewrite list_cons_cons_move_app.
  replace (X0 ~<: ([X ~> U'] T) :: ([X ==> U'] Gamma)) 
    with ([X ==> U'] (X0 ~<: T :: Gamma)) by auto.
  eapply IHm; Simplify by (Destruct notIn by (eauto with arith)).
  rewrite <- list_cons_cons_move_app; auto.
  destruct (sub_lclosed_t H3) as [? ?].
  rewrite subst_ftvar_ltvar_t with (Gamma := Delta); auto.
  simpl; constructor 5 with (U := [X ~> U'] U0).
  unsimpl ([X ~> U'] (typ_all A U0 S)).
  eapply IHm; eauto with arith.
  eapply sub_subst_ftvar; eauto.
  destruct (sub_lclosed_t H3) as [? ?].
  simpl; constructor 6 with (T := [X ~> U'] T).
  eapply IHm; eauto with arith.
  eapply sub_subst_ftvar; eauto.
Qed.

Lemma typing_subst_ftvar : forall t X U T U' Gamma,
  typing (X ~<: U :: Gamma) t T
  -> sub Gamma U' U
  -> typing Gamma ([X :~> U'] t) ([X ~> U'] T).
Proof.
  intros.
  destruct (typing_typingLH H) as [n ?].
  unsimpl (([X ==> U'] emptyset) ++ Gamma).
  eapply typingLH_typing with (n := n).
  eapply typing_subst_ftvar_aux; simpl; eauto with arith.
Qed.

Lemma typing_subst_ltvar : forall X U Gamma A B t T U',
  typing (X ~<: U :: Gamma) ({A :~> X ^^} t) ({B ~> X ^^} T)
  -> sub Gamma U' U
  -> ~ In X (FV_te t)     
  -> ~ In X (FV_tt T)
  -> typing Gamma ({A :~> U'} t) ({B ~> U'} T).
Proof.
  intros.
  destruct (sub_lclosed_t H0) as [? ?].
  rewrite <- subst_seq_ftvar_ltvar_t with (X := X); Destruct notIn by eauto.
  rewrite <- subst_seq_ftvar_ltvar_e with (X := X); Destruct notIn by eauto.
  eapply typing_subst_ftvar; eauto.
Qed.

(** *** Term parameter substitution lemma
 We then prove Lemma [typing_subst_fvar] which shows that [typing] is stable
 under term parameter substitution. The proof also proceeds by induction on
 the size of [typing] proofs. Note the use of the renaming lemmas in the 
 [typing_abs] and [typing_tabs] cases. *)
Lemma typing_subst_fvar_aux : forall m n t T Gamma0 Gamma x U Delta u,
  n < m -> 
  typingLH n Gamma0 t T -> 
  Gamma0 = Gamma ++ x ~: U :: Delta -> 
  typing (Gamma ++ Delta) u U -> 
  typing (Gamma ++ Delta) ([x ::~> u] t) T.
Proof.
  induction m.
  firstorder using lt_n_O.
  destruct 2; intros; subst; Simplify by eauto.
  assert (T = U). 
    eapply ctxt_okay_unique_fvar_bind; Destruct In by eauto.
      inversion H1; subst; eauto with v62.
  subst; eauto.
  econstructor; eauto with strengthen_aux.
    Destruct In by congruence.
  set (L := x :: dom_ec (Gamma ++ Delta) ++ FV_ee ([x ::~> u] t) ++ 
                 dom_ec (x ~: U :: Gamma) ++ FV_ee t).
  destruct (pick_fresh L) as [x' Hfresh].
  unfold L in Hfresh.
  constructor 2 with (x := x'); 
    Simplify by Destruct notIn by eauto with strengthen_aux.
    forwards Hokay : typing_ctxt_okay H5.
    forwards Hclosed_e : typing_lclosed_e H5.
    rewrite <- subst_fvar_lvar_e 
      with (Gamma := Gamma ++ Delta) (I := emptyset) by eauto.
    rewrite list_cons_cons_move_app.
    eapply IHm with (Gamma0 := (x' ~: T :: Gamma) ++ x ~: U :: Delta);
      eauto with arith.
    rewrite <- list_cons_cons_move_app.
    eapply typingLH_subst_lvar_rename_fvar; 
      Simplify by Destruct notIn by eauto.
    rewrite <- list_cons_cons_move_app.
    eapply weakening_typing; eauto.
    econstructor; Simplify by Destruct notIn by eauto.
    eapply lclosed_t_incl with (Gamma := Gamma ++ x ~: U :: Delta); 
      Simplify by (eauto with v62).
  constructor 3 with (T := T).
  eapply IHm with (n := k1); eauto with arith.
  eapply IHm with (n := k2); eauto with arith.
  set (L := FV_tc (Gamma ++ Delta) ++ FV_te ([x ::~> u] t) ++ FV_tt U0).
  destruct (pick_fresh L) as [X' Hfresh].
  unfold L in Hfresh.
  constructor 4 with (X := X'); 
    Simplify by Destruct notIn by eauto with strengthen_aux.
    forwards Hokay : typing_ctxt_okay H5.
    forwards Hclosed_e : typing_lclosed_e H5.
    erewrite subst_ltvar_fvar_e with (Gamma := Gamma ++ Delta) by eauto.
    rewrite list_cons_cons_move_app.
    eapply IHm with (Gamma0 := (X' ~<: T :: Gamma) ++ x ~: U :: Delta);
      eauto with arith.
    rewrite <- list_cons_cons_move_app.
    eapply typingLH_subst_ltvar_rename_ftvar;
      Simplify by (Destruct notIn by eauto).
    rewrite <- list_cons_cons_move_app.
    eapply weakening_typing; eauto.
    econstructor; Simplify by Destruct notIn by eauto.
    eapply lclosed_t_incl with (Gamma := Gamma ++ x ~: U :: Delta); 
      Simplify by (eauto with v62).
  econstructor; [eapply IHm | idtac ]; eauto using strengthen_sub with arith.
  econstructor; [eapply IHm | idtac ]; eauto using strengthen_sub with arith.
Qed.

Lemma typing_subst_fvar : forall t T u U Gamma x,
  typing (x ~: U :: Gamma) t T
  -> typing Gamma u U
  -> typing Gamma ([ x ::~> u ] t) T.
Proof.
  intros.
  apply typing_typingLH in H; destruct H as [k ?].
  unsimpl (emptyset ++ Gamma).  
  eapply typing_subst_fvar_aux with (n := k) (m := S k); 
    simpl; eauto with arith.
Qed.

Lemma typing_subst_lvar : forall x U Gamma a t u T,
  typing (x ~: U :: Gamma) ({a ::~> x **} t) T-> 
  typing Gamma u U ->
  ~ In x (FV_ee t) ->
  typing Gamma ({a ::~> u} t) T.
Proof.
  intros.
  rewrite <- subst_seq_fvar_lvar_e with (x := x) by eauto.
  eauto using typing_subst_fvar. 
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Preservation 
 Preservation is straightforward to prove once we prove the substitution 
 lemmas. Lemma [app_red_preservation] deals with the [red_abs] case, and
 Lemma [tapp_red_preservation] deals with the [red_tabs] case. *)
Lemma app_red_preservation : forall Gamma t0 T a T0 t U1 U2 u,
  typing Gamma t0 T
  -> t0 = tm_abs a T0 t
  -> sub Gamma T (U1 --> U2)
  -> typing Gamma u U1
  -> typing Gamma ({a ::~> u} t) U2.
Proof.
  induction 1; simpl; intros He0 Hsub He'; inversion He0; subst.
  inversion Hsub; subst.
  eauto using typing_subst_lvar.
  eauto using sub_transitivity.
Qed.

Lemma tapp_red_preservation : forall Gamma t0 A T B T0 t U1 U2 R,
  typing Gamma t0 T0
  -> t0 = tm_tabs A T t
  -> sub Gamma T0 (typ_all B U1 U2)
  -> sub Gamma R U1
  -> typing Gamma ({A :~> R} t) ({B ~> R} U2).
Proof.
  induction 1; simpl; intros He HsubD HsubA; inversion He; subst.
  clear IHtyping He.
  inversion HsubD; subst.
  constructor 6 with (T := ({B0 ~> R} U)).
  eapply typing_subst_ltvar; Simplify by 
    (Destruct notIn by eauto using sub_transitivity with incl_param).
  unsimpl (([X0 ==> R] emptyset) ++ Gamma).
  rewrite <- subst_seq_ftvar_ltvar_t with (X := X0) (A := B0) 
    by (Destruct notIn by eauto).
  rewrite <- subst_seq_ftvar_ltvar_t with (X := X0) (A := B) 
    by (Destruct notIn by eauto).
  destruct (sub_lclosed_t H9) as [? ?].
  forwards Hokay : (sub_ctxt_okay H9).
  eapply sub_subst_ftvar; simpl; eauto with incl_param.
  eauto using sub_transitivity.
Qed.

Lemma preservation : forall t T Gamma, 
  typing Gamma t T -> 
  forall t', red t t' -> typing Gamma t' T.
Proof.
  induction 1; intros t0 Ha; inversion Ha; subst; eauto.
    clear IHtyping1 IHtyping2 Ha.
    forwards Hokay : typing_ctxt_okay H.
    forwards Hclosed : typing_lclosed_t H.
    inversion H; subst; 
      eapply app_red_preservation; eauto using sub_reflexivity_aux.
    clear IHtyping Ha.
    forwards Hokay : typing_ctxt_okay H.
    forwards Hclosed : typing_lclosed_t H.
    eapply tapp_red_preservation; eauto using sub_reflexivity_aux.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Progress 
 Progress is also straightforward to prove. *)
Hint Constructors value.

(** We first show that there are canonical types for type and term 
 abstraction. *)
Lemma abs_subtype_form : forall T1 T2 T Gamma,
  sub Gamma (T1 --> T2) T
  -> T = typ_top \/ exists T1' T2', T = T1' --> T2'.
Proof.
  intros; inversion H; auto.
  right; exists U1 U2; auto.
Qed.

Lemma abs_typing_form : forall t a t0 T T0 Gamma, 
  typing Gamma t T
  -> t = tm_abs a T0 t0
  -> T = typ_top \/ exists T1 T2, T = T1 --> T2.
Proof.
  intros; induction H; try congruence.
  right; exists T U; auto.
  intuition.
  left; subst; inversion H1; auto.
  destruct H3 as [T1 [T2 Ha]]; subst.
  forwards Ha : abs_subtype_form H1.
  auto.
Qed.

Lemma tabs_subtype_form : forall A T1 T2 T Gamma,
  sub Gamma (typ_all A T1 T2) T
  -> T = typ_top \/ exists B T1' T2', T = typ_all B T1' T2'.
Proof.
  intros; inversion H; auto.
  right; exists B U1 U2; auto.
Qed.

Lemma tabs_typing_form : forall t A T0 t0 T Gamma, 
  typing Gamma t T
  -> t = tm_tabs A T0 t0
  -> T = typ_top \/ exists B T0' T1', T = typ_all B T0' T1'.
Proof.
  intros; induction H; try congruence.
  right; exists B T U; auto.
  intuition.
  left; subst; inversion H1; auto.
  destruct H3 as [A0 [T0' [T1' Ha]]]; subst.
  forwards Ha : tabs_subtype_form H1.
  auto.
Qed.

(** We then show that there are canonical values for arrow and all types *)
Lemma canonical_form_abs : forall t T U Gamma,
  value t 
  -> typing Gamma t (T --> U)
  -> exists a T0 t0, t = tm_abs a T0 t0.
Proof.
  induction 1; simpl; intros; eauto.
  inversion H. 
  assert (tm_tabs A T0 t = tm_tabs A T0 t) by auto.
  forwards Ha : (tabs_typing_form H0 H5).
  destruct Ha.
  subst; inversion H1.
  destruct H6 as [B [T0' [T1' Hb]]]; subst.
  inversion H1.
Qed.

Lemma canonical_form_tabs : forall t A T U Gamma,
  value t 
  -> typing Gamma t (typ_all A T U)
  -> exists A0 T0 t0, t = tm_tabs A0 T0 t0.
Proof.
  induction 1; simpl; intros; eauto.
  inversion H. 
  assert (tm_abs a T0 t = tm_abs a T0 t) by auto.
  forwards Ha : (abs_typing_form H0 H5).
  destruct Ha.
  subst; inversion H1.
  destruct H6 as [T2 [T3 Hb]]; subst.
  inversion H1.
Qed.

(** Finally, we show that a well-typed term is never stuck: either it is 
 a value, or it can reduce. The proof proceeds by simple induction on the
 typing relation, and exploits the canonical forms of values for arrow and
 all types. *)
Lemma progress : forall t T Gamma,
  typing Gamma t T 
  -> Gamma = emptyset
  -> value t \/ exists t', red t t'.
Proof.
  induction 1; intros; simpl; assert (Gamma = Gamma) by auto; subst; eauto. 
  inversion H0. 
  destruct (IHtyping1 H2).
  destruct (IHtyping2 H2).
  forwards Ha : canonical_form_abs H1 H.
  destruct Ha as [x [T0 [t0 ?]]]; subst.
  right; eauto.
  destruct H3 as [t'0 ?]. 
  right; eauto.
  destruct H1 as [t'' ?].
  right; eauto.
  destruct (IHtyping H2).
  forwards Ha : canonical_form_tabs H1 H.
  destruct Ha as [A0 [T0 [t0 ?]]]; subst.
  right; eauto.
  destruct H1 as [e' ?].
  right; eauto.
Qed.
(* *************************************************************** *)
