(** This file presents an exist-fresh style mechanization of System Fsub 
 without contexts using locally nameless representation. 
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
 - Local closure
 - Subtyping relation
 - Typing relation
 - Values and evaluation
 - Tactical support
 - Challenge 1A: Transitivity of Subtyping
 - Challenge 2A: Type Safety *)
(* *************************************************************** *)

(* *************************************************************** *)
(** * Syntax 
 Both variables and parameters are represented as natural numbers. 
 Since we use locally nameless representation, variables are treated 
 as indices, while parameters are treated as distinct atoms. *)
Notation ltvar := nat.   (* type variable *) 
Notation ftvar := nat.   (* type parameter *)

Notation lvar := nat.    (* term variable *)
Notation fvar := nat.    (* term parameter *)  

(**  We use the following definition of types and terms:
<< 
 types T, U, S := \top | A | X <: T | T -> U | \forall <: T. U 
 terms t, u, s := a | x : T | \lambda : T. t | t u | \Lambda <: T. t | t [ T ] 
>> 
 We use the following notations for variables and parameters:
  - type variables  A, B, C 
  - type parameters X, Y, Z
  - term variables  a, b, c
  - term parameters x, y, z *)
Inductive typ : Set :=
| typ_top   : typ
| typ_ltvar : ltvar -> typ
| typ_ftvar : ftvar -> typ -> typ
| typ_arrow : typ -> typ -> typ
| typ_all   : typ -> typ -> typ.

Inductive tm : Set :=
| tm_lvar : lvar -> tm
| tm_fvar : fvar -> typ -> tm
| tm_abs  : typ -> tm -> tm
| tm_app  : tm -> tm -> tm
| tm_tabs : typ -> tm -> tm
| tm_tapp : tm -> typ -> tm.

Notation " X ^^ T " := (typ_ftvar X T) (at level 65). 
Notation " T --> U " := (typ_arrow T U) (at level 65).

Notation " x ** T " := (tm_fvar x T) (at level 65).

Lemma typ_dec : forall T U : typ, {T = U} + {T <> U}.
Proof.
  decide equality; apply eq_nat_dec.
Qed.

Lemma fvar_dec : forall (x y : (fvar * typ)), {x = y} + {x <> y}.
Proof.
  decide equality; [apply typ_dec | apply eq_nat_dec ].
Qed.

Lemma ftvar_dec : forall (X Y : (ftvar * typ)), {X = Y} + {X <> Y}.
Proof.
  decide equality; [apply typ_dec | apply eq_nat_dec ].
Qed.

Notation "p ==_t q" := (fvar_dec p q) (at level 70).
Notation "p ==_T q" := (ftvar_dec p q) (at level 70).
(* *************************************************************** *)

(* *************************************************************** *)
(** * Parameters
 ** Type parameters
 The functions [FV_tt] and [FV_te], defined below, calculate 
 the set of type parameters in a type and a term, respectively. 
 Locally nameless representation makes the [typ_all] case for 
 [FV_tt] and the [tm_tabs] case for [FV_te] simple because 
 variables and parameters are syntactically distinct. *)
Fixpoint FV_tt (T:typ) : list ftvar :=
  match T with
    | typ_top     => nil
    | typ_ltvar _ => nil
    | alpha ^^ T  => alpha :: FV_tt T
    | T --> U     => FV_tt T ++ FV_tt U
    | typ_all T U => FV_tt T ++ FV_tt U
  end.

Fixpoint FV_te (t:tm) : list ftvar :=
  match t with
    | tm_lvar _   => nil 
    | tm_fvar _ T => FV_tt T
    | tm_abs T t  => FV_tt T ++ FV_te t
    | tm_app t t' => FV_te t ++ FV_te t'
    | tm_tabs T t => FV_tt T ++ FV_te t 
    | tm_tapp t T => FV_te t ++ FV_tt T 
end.

(** ** Term parameters
 The function [FV_ee], defined below, calculates the set of term 
 parameters in a term. Locally nameless representation also makes 
 the [tm_abs] case simple for the same reason. *)
Fixpoint FV_ee (t:tm) : list fvar :=
  match t with
    | tm_lvar _   => nil 
    | tm_fvar x _ => x :: nil
    | tm_abs _ t  => FV_ee t
    | tm_app t t' => FV_ee t ++ FV_ee t'
    | tm_tabs _ t => FV_ee t
    | tm_tapp t _ => FV_ee t
  end.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Substitution *)
(** ** Type variables 
 The functions [lsubst_tt] and [lsubst_te], defined below, replace
 a type variable with a type for types and terms, respectively. 
 Note that the use of locally nameless representation eliminates
 the equality checking between variables for the [typ_all] case 
 (for [lsubst_tt]) and the [tm_tabs] case (for [lsubst_te]). *)
Fixpoint lsubst_tt (B : ltvar) (U : typ) (T : typ) {struct T} : typ :=
  match T with
    | typ_top       => typ_top
    | typ_ltvar A   => if A == B then U else typ_ltvar A
    | X ^^ T        => X ^^ T
    | T1 --> T2     => typ_arrow (lsubst_tt B U T1) (lsubst_tt B U T2)
    | typ_all T1 T2 => typ_all (lsubst_tt B U T1) (lsubst_tt (S B) U T2)
  end.

Fixpoint lsubst_te (B : ltvar) (U : typ)  (t : tm) {struct t} : tm :=
  match t with
    | tm_lvar a    => tm_lvar a
    | tm_fvar x T  => tm_fvar x T
    | tm_abs T t   => tm_abs (lsubst_tt B U T) (lsubst_te B U t) 
    | tm_app t1 t2 => tm_app (lsubst_te B U t1) (lsubst_te B U t2) 
    | tm_tabs T t  => tm_tabs (lsubst_tt B U T) (lsubst_te (S B) U t) 
    | tm_tapp t T  => tm_tapp (lsubst_te B U t) (lsubst_tt B U T) 
  end.

(** ** Term variables
 The function [lsubst_ee], defined below, replaces a term variable 
 with a term. Note that the [tm_abs] case also does not check the 
 equality between variables. *)
Fixpoint lsubst_ee (b : lvar) (u : tm) (t : tm) {struct t} : tm :=
  match t with
    | tm_lvar a    => if a == b then u else tm_lvar a
    | tm_fvar x T  => tm_fvar x T
    | tm_abs T t   => tm_abs T (lsubst_ee (S b) u t)
    | tm_app t1 t2 => tm_app (lsubst_ee b u t1) (lsubst_ee b u t2)
    | tm_tabs T t  => tm_tabs T (lsubst_ee b u t)
    | tm_tapp t T  => tm_tapp (lsubst_ee b u t) T
  end.

(** ** Type parameters 
 The functions [fsubst_tt] and [fsubst_te], defined below, replace
 a type parameter with a type. Note that [fsubst_tt] replaces a type
 parameter with a type only when both a parameter and its annotated 
 type are matched. Locally nameless representation makes the [typ_all]
 case (for [fsubst_tt]) and the [tm_tabs] case (for [fsubst_te]) simple. *)
Fixpoint fsubst_tt (Y:ftvar) (U:typ) (S : typ) (T : typ) {struct T} : typ :=
  match T with
    | typ_top       => typ_top
    | typ_ltvar A   => typ_ltvar A
    | X ^^ T        => 
      if ftvar_dec (X, T) (Y, U) then S else (X ^^ (fsubst_tt Y U S T))
    | T1 --> T2     => (fsubst_tt Y U S T1) --> (fsubst_tt Y U S T2)
    | typ_all T1 T2 => typ_all (fsubst_tt Y U S T1) (fsubst_tt Y U S T2)
  end.

Fixpoint fsubst_te (Y:ftvar) (U:typ) (S:typ) (t:tm) {struct t} : tm :=
  match t with
    | tm_lvar a    => tm_lvar a
    | tm_fvar x T  => tm_fvar x (fsubst_tt Y U S T) 
    | tm_abs T t   => tm_abs (fsubst_tt Y U S T) (fsubst_te Y U S t)
    | tm_app t1 t2 => tm_app (fsubst_te Y U S t1) (fsubst_te Y U S t2)
    | tm_tabs T t  => tm_tabs (fsubst_tt Y U S T) (fsubst_te Y U S t)
    | tm_tapp t T  => tm_tapp (fsubst_te Y U S t) (fsubst_tt Y U S T)
  end.

(** ** Term parameters
 The function [fsubst_ee], defined below, replaces a type parameter 
 with a term. Note that [fsubst_tt] replaces a term parameter with 
 a term only when both a parameter and its annotated type are matched. 
 Locally nameless representation makes the [tm_abs] case simple. *)
Fixpoint fsubst_ee (y : fvar) (U:typ) (u t: tm) {struct t} : tm :=
  match t with
    | tm_lvar a    => tm_lvar a
    | tm_fvar x T  => if fvar_dec (x, T) (y, U) then u else tm_fvar x T
    | tm_abs T t   => tm_abs T (fsubst_ee y U u t)
    | tm_app t1 t2 => tm_app (fsubst_ee y U u t1) (fsubst_ee y U u t2)
    | tm_tabs T t  => tm_tabs T (fsubst_ee y U u t)
    | tm_tapp t T  => tm_tapp (fsubst_ee y U u t) T
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

Notation "[ ( X , U ) ~> S ] T" := (fsubst_tt X U S T) (at level 67).
Notation "[ ( X , U ) :~> S ] t " := (fsubst_te X U S t) (at level 67).
Notation "[ ( x , U ) ::~> u ] t " := (fsubst_ee x U u t) (at level 67).
(* *************************************************************** *)

(* *************************************************************** *)
(** * Local closure
 A type (or term) is said to be locally closed if every type (and term) 
 variable has a corresponding binder. To formalize local closure of types 
 and terms, we introduce two inductive definitions [lclosed_t] and 
 [lclosed_e] for types and terms, respectively. 

 ** Local closure of types
 For a type variable set [I], [lclosed_t I T] holds if [I] is a set of all
 the unbounded type variable in [T]. Thus, a type [T] is locally closed 
 if [lclosed_t emptyset T] holds. [map_pred_remove_zero I] first remove
 all the occurrence of O in I, and then reduce all the indices in I by 1. *)
Inductive lclosed_t : list ltvar -> typ -> Prop :=
| lclosed_t_top   : lclosed_t emptyset typ_top
| lclosed_t_ltvar : forall A,
  lclosed_t (A :: emptyset) (typ_ltvar A)
| lclosed_t_ftvar : forall X (T : typ),
  lclosed_t emptyset T ->
  lclosed_t emptyset (X ^^ T)
| lclosed_t_arrow : forall I1 I2 (T U : typ),
  lclosed_t I1 T ->
  lclosed_t I2 U ->
  lclosed_t (I1 ++ I2) (T --> U)
| lclosed_t_all   : forall I1 I2 T U,
  lclosed_t I1 T ->
  lclosed_t I2 U -> 
  lclosed_t (I1 ++ (map_pred_remove_zero I2)) (typ_all T U).

Hint Constructors lclosed_t.

(** ** Local closure of terms
 For a type variable set [I], a term variable set [i], [lclosed_e I i t] holds 
 if [I] and [i] are sets of all the unbound type and term variable in [t], 
 respectively. Thus, a term [t] is locally closed 
 if [lclosed_e emptyset emptyset t] holds. *)
Inductive lclosed_e : list ltvar -> list lvar -> tm -> Prop := 
| lclosed_e_lvar : forall a, lclosed_e nil (a :: nil) (tm_lvar a)
| lclosed_e_fvar : forall x T, 
  lclosed_t emptyset T ->
  lclosed_e emptyset emptyset (x ** T)
| lclosed_e_abs  : forall I1 I2 i T t, 
  lclosed_t I1 T ->
  lclosed_e I2 i t ->
  lclosed_e (I1 ++ I2) (map_pred_remove_zero i) (tm_abs T t) 
| lclosed_e_app  : forall I1 I2 i1 i2 t1 t2,
  lclosed_e I1 i1 t1 ->
  lclosed_e I2 i2 t2 ->
  lclosed_e (I1 ++ I2) (i1 ++ i2) (tm_app t1 t2)
| lclosed_e_tabs : forall I1 I2 i T t,
  lclosed_t I1 T ->
  lclosed_e I2 i t ->
  lclosed_e (I1 ++ (map_pred_remove_zero I2)) i (tm_tabs T t)
| lclosed_e_tapp : forall I1 I2 i t T,
  lclosed_e I1 i t ->
  lclosed_t I2 T ->
  lclosed_e (I1 ++ I2) i (tm_tapp t T).

Hint Constructors lclosed_e.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Subtyping relation 
 It is straightforward to define the subtyping relation. The [sub_top] 
 and [sub_refl_tvar] cases require types to be locally closed. This 
 implies that the subtyping relation holds only for locally closed types. 
 The [sub_refl_tvar] case requires the annotated type to be well-formed,
 which corresponds the well-formed context requirement for the System Fsub
 with typing contexts. Note the use of the exist-fresh style 
 in the [sub_all] case. *)
Inductive sub : typ -> typ -> Prop :=
| sub_top        : forall T, 
  lclosed_t emptyset T -> 
  sub T typ_top
| sub_refl_tvar  : forall T X,
  lclosed_t emptyset T ->
  sub (X ^^ T) (X ^^ T)
| sub_trans_tvar : forall T U X,
  sub T U ->
  sub (X ^^ T) U
| sub_arrow      : forall T1 T2 U1 U2,
  sub U1 T1 ->
  sub T2 U2 ->
  sub (T1 --> T2) (U1 --> U2)
| sub_all        : forall T1 T2 U1 U2 X,
  sub U1 T1 ->
  ~ In X (FV_tt T2) ->
  ~ In X (FV_tt U2) ->
  ~ In X (FV_tt T1) ->
  ~ In X (FV_tt U1) ->
  sub ({O ~> X ^^ U1} T2) ({O ~> X ^^ U1} U2) ->
  sub (typ_all T1 T2) (typ_all U1 U2). 

Hint Constructors sub.

(** ** Subtyping relation with sizes 
 We formally define the size of proofs using the inductive definition 
 [subLH]. If [subLH n T U] holds, it means that there is a proof of 
 [sub T U] whose size is [n]. Note that the definition of [subLH] is 
 the same as [sub] except the annotated size.

 Lemma [sub_subLH] and [subLH_sub] formally state the equivalence 
 between [sub] and [subLH]. *)
Inductive subLH : nat -> typ -> typ -> Prop :=
| subLH_top        : forall T, 
  lclosed_t emptyset T -> 
  subLH O T typ_top
| subLH_refl_tvar  : forall T X,
  lclosed_t emptyset T ->
  subLH O (X ^^ T) (X ^^ T)
| subLH_trans_tvar : forall T U X n,
  subLH n T U ->
  subLH (S n) (X ^^ T) U
| subLH_arrow      : forall T1 T2 U1 U2 n1 n2,
  subLH n1 U1 T1 ->
  subLH n2 T2 U2 ->
  subLH (S (max n1 n2)) (T1 --> T2) (U1 --> U2)
| subLH_all        : forall T1 T2 U1 U2 X n1 n2,
  subLH n1 U1 T1 ->
  ~ In X (FV_tt T2) ->
  ~ In X (FV_tt U2) ->
  ~ In X (FV_tt T1) ->
  ~ In X (FV_tt U1) ->
  subLH n2 ({O ~> X ^^ U1} T2) ({O ~> X ^^ U1} U2) ->
  subLH (S (max n1 n2)) (typ_all T1 T2) (typ_all U1 U2). 

Hint Constructors subLH.

Lemma sub_subLH : forall T U,
  sub T U -> exists n, subLH n T U.
Proof.
  induction 1.
  exists 0; auto.
  exists 0; auto.
  inversion IHsub  as [k ?].
  exists (S k); auto.
  inversion IHsub1 as [n1 ?].
  inversion IHsub2 as [n2 ?].
  exists (S (max n1 n2)); auto.
  inversion IHsub1 as [n1 ?].
  inversion IHsub2 as [n2 ?].
  exists (S (max n1 n2)); eauto.
Qed.

Lemma subLH_sub : forall T U n,
  subLH n T U -> sub T U.
Proof.
  induction 1; eauto.
Qed.

Hint Resolve sub_subLH subLH_sub.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Typing relation 
 It is also straightforward to define the typing relation. The [typing_fvar] 
 case requires the annotate type [T] to be locally closed, which implies the
 typing relation holds only for locally closed types (We will formally prove 
 this later). Note the use of the exist-fresh style in the [typing_abs] and 
 [typing_tabs] cases. *)
Inductive typing : tm -> typ -> Prop :=
| typing_fvar : forall x T,
  lclosed_t emptyset T ->
  typing (x ** T) T
| typing_abs  : forall T U t x,
  lclosed_t emptyset T ->
  ~ In x (FV_ee t) ->
  typing ({O ::~> x ** T} t) U ->
  typing (tm_abs T t) (T --> U)
| typing_app  : forall t t' T U,
  typing t (T --> U) ->
  typing t' T ->
  typing (tm_app t t') U
| typing_tabs : forall T t U X,
  lclosed_t emptyset T ->
  ~ In X (FV_te t ++ FV_tt U) ->
  typing ({O :~> X ^^ T} t) ({O ~> X ^^ T} U) ->
  typing (tm_tabs T t) (typ_all T U)
| typing_tapp : forall t T U S,
  typing t (typ_all U S) ->
  sub T U ->
  typing (tm_tapp t T) ({O ~> T} S)
| typing_sub  : forall t T U,
  typing t T ->
  sub T U ->
  typing t U.

Hint Constructors typing.

(** ** Typing relation with sizes 
 We formally define the size of proofs using the inductive definition 
 [typingLH]. If [typingLH n t T] holds, it means that there is a proof 
 of [typing t T] whose size is [n]. Note that the definition of [typingLH] 
 is the same as [typing] except the annotated size.

 Lemma [typing_typingLH] and [typingLH_typing] formally state the equivalence 
 between [typing] and [typingLH]. *)
Inductive typingLH : nat -> tm -> typ -> Prop :=
| typing_fvarLH : forall x T,
  lclosed_t emptyset T ->
  typingLH O (x ** T) T
| typing_absLH  : forall T U t x k,
  lclosed_t emptyset T ->
  ~ In x (FV_ee t) -> 
  typingLH k ({O ::~> x ** T} t) U -> 
  typingLH (S k) (tm_abs T t) (T --> U)
| typing_appLH  : forall t t' T U k1 k2,
  typingLH k1 t (T --> U) ->
  typingLH k2 t' T ->
  typingLH (S (max k1 k2)) (tm_app t t') U
| typing_tabsLH : forall T t U X k,
  lclosed_t emptyset T ->
  ~ In X (FV_te t ++ FV_tt U) ->
  typingLH k ({O :~> X ^^ T} t) ({O ~> X ^^ T} U) ->
  typingLH (S k) (tm_tabs T t) (typ_all T U)
| typing_tappLH : forall t T U S k,
  typingLH k t (typ_all U S) ->
  sub T U -> 
  typingLH (Datatypes.S k) (tm_tapp t T) ({O ~> T} S)
| typing_subLH  : forall t T U k,
  typingLH k t T ->
  sub T U ->
  typingLH (S k) t U.

Hint Constructors typingLH.

Lemma typing_typingLH : forall t T,
  typing t T -> exists n, typingLH n t T.
Proof.
  induction 1.
  exists 0; auto.
  inversion IHtyping as [k ?].
  exists (S k); eauto.
  inversion IHtyping1 as [k1 ?].
  inversion IHtyping2 as [k2 ?].
  exists (S (max k1 k2)); eauto.
  inversion IHtyping as [k ?].
  exists (S k); eauto.
  inversion IHtyping as [k ?].
  exists (Datatypes.S k); eauto.
  inversion IHtyping as [k ?].
  exists (S k); eauto.
Qed.

Lemma typingLH_typing : forall t T n,
  typingLH n t T -> 
  typing t T.
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
| value_abs  : forall T t, value (tm_abs T t)
| value_tabs : forall T t, value (tm_tabs T t).

Inductive red : tm -> tm -> Prop :=
| red_app_1 : forall t1 t1' t2,
              red t1 t1' ->
              red (tm_app t1 t2) (tm_app t1' t2)
| red_app_2 : forall t1 t2 t2',
              value t1 ->
              red t2 t2' ->
              red (tm_app t1 t2) (tm_app t1 t2')
| red_abs   : forall T t u,
              value u -> 
              red (tm_app (tm_abs T t) u) ({O ::~> u} t)
| red_tapp  : forall t t' T,
              red t t' ->
              red (tm_tapp t T) (tm_tapp t' T)
| red_tabs  : forall T t U,
              red (tm_tapp (tm_tabs T t) U) ({O :~> U} t).

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
    | typ_ftvar _ _ => idtac
    | typ_arrow _ _ => idtac
    | typ_all _ _ => idtac
    | _ => fail
  end 
with filter_e e :=
  match e with
    | tm_lvar _ => idtac
    | tm_fvar _ _ => idtac
    | tm_abs _ _ => idtac
    | tm_app _ _ => idtac
    | tm_tabs _ _ => idtac
    | tm_tapp _ _ => idtac
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
  end in
  match goal with
    | H: ?X = ?X |- _ => clear H; simplifyTac tac
    | H: ?X <> ?X |- _ => try congruence
    | H: context [?X == ?Y] |- _ => 
      destruct (X == Y); [ try subst X | idtac ]; simplifyTac tac
    | H: context [?X ==_t ?Y] |- _ => 
      destruct (X ==_t Y); [ try subst X | idtac ]; simplifyTac tac
    | H: context [?X ==_T ?Y] |- _ => 
      destruct (X ==_T Y); [ try subst X | idtac ]; simplifyTac tac
    | |- context [?X == ?Y] => 
      destruct (X == Y); [ try subst X | idtac ]; simplifyTac tac
    | |- context [?X ==_t ?Y] => 
      destruct (X ==_t Y); [ try subst X | idtac ]; simplifyTac tac
    | |- context [?X ==_T ?Y] => 
      destruct (X ==_T Y); [ try subst X | idtac ]; simplifyTac tac
    | H: context[ remove _ _ ?l ] |- _ =>
      filter_list l; simpl remove in H; simplifyTac tac
    | H : context[ ?C ?t ] |- _ =>
      filter_var_t C; filter_t t; simpl C in H; simplifyTac tac
    | H : context[ ?C ?e ] |- _ =>
      filter_var_e C; filter_e e; simpl C in H; simplifyTac tac
    | H : context[ lsubst_tt _ _ ?t ] |- _ =>
      filter_t t; simpl lsubst_tt in H; simplifyTac tac
    | H : context[ fsubst_tt _ _ _ ?t ] |- _ =>
      filter_t t; simpl fsubst_tt in H; simplifyTac tac
    | H : context[ ?S _ _ ?e ] |- _ =>
      filter_lsubst_e S; filter_e e; simpl S in H; simplifyTac tac
    | H : context[ ?S _ _ _ ?e ] |- _ =>
      filter_fsubst_e S; filter_e e; simpl S in H; simplifyTac tac
    | |- context[ remove _ _ ?l ] =>
      filter_list l; simpl remove; simplifyTac tac
    | |- context[ ?C ?t ] =>
      filter_var_t C; filter_t t; simpl C; simplifyTac tac
    | |- context[ ?C ?e ] =>
      filter_var_e C; filter_e e; simpl C; simplifyTac tac
    | |- context[ lsubst_tt _ _ ?t ] =>
      filter_t t; simpl lsubst_tt; simplifyTac tac
    | |- context[ fsubst_tt _ _ _ ?t ] =>
      filter_t t; simpl fsubst_tt; simplifyTac tac
    | |- context[ ?S _ _ ?e ] =>
      filter_lsubst_e S; filter_e e; simpl S; simplifyTac tac
    | |- context[ ?S _ _ _ ?e ] =>
      filter_fsubst_e S; filter_e e; simpl S; simplifyTac tac
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

(** [lclosed_t] is invertible. *)
Lemma lclosed_t_ltvar_split : forall T A X U I0,
  lclosed_t I0 ({A ~> X ^^ U} T) ->
  (exists I, (lclosed_t I T /\ remove eq_nat_dec A I = I0)).
Proof.
  induction T; intros; auto.
  inversion H; exists (emptyset:list ltvar); Simplify by eauto.
  Simplify by eauto; inversion H; subst.
    exists (A :: emptyset); Simplify by eauto.
    exists (n :: emptyset); Simplify by eauto.
  Simplify by eauto; inversion H; subst.
     exists (emptyset : list ltvar); Simplify by eauto.
  Simplify by eauto; inversion H; subst.
  destruct (IHT1 _ _ _ _ H3) as [I1' [Ha Ha']]. 
  destruct (IHT2 _ _ _ _ H4) as [I2' [Hb Hb']].
  exists (I1' ++ I2'); split; Simplify by eauto.
    rewrite list_remove_app; rewrite Ha'; rewrite Hb'; eauto.
  Simplify by eauto; inversion H; clear H.
    destruct (IHT1 _ _ _ _ H3) as [I1' [Ha Ha']].   
    destruct (IHT2 _ _ _ _ H4) as [I2' [Hb Hb']].
    exists (I1' ++ (map_pred_remove_zero I2')); split; eauto.     
      rewrite list_remove_app; rewrite Ha'. 
      rewrite swap_remove_map_pred_remove_zero; rewrite Hb'.
      eauto.
Qed.

(** [lclosed_t] is stable under type variable substitution. *)
Lemma lclosed_t_subst_ltvar : forall T U I A,
  lclosed_t emptyset U ->
  lclosed_t I T ->
  lclosed_t (remove eq_nat_dec A I) ({A ~> U} T).
Proof.
  induction T; intros; inversion H0; subst; Simplify by eauto. 
    rewrite list_remove_app; eauto.
    rewrite list_remove_app; rewrite swap_remove_map_pred_remove_zero; auto.
Qed.

(** [lclosed_t] is also stable under type parameter substitution. *)
Lemma lclosed_t_subst_ftvar : forall T U U' X I,
  lclosed_t I T ->
  lclosed_t emptyset U ->
  lclosed_t I ([(X, U') ~> U] T).
Proof.
  induction 1; intros; Simplify by eauto.
Qed.  

Hint Resolve lclosed_t_subst_ltvar lclosed_t_subst_ftvar : subst_aux.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Properties of substitution over types 
 Our solution exploits several properties of substitution over types. *)
Hint Resolve sym_eq notIn_remove_notIn notIn_n_pred_notIn_S_n : nochange.

(** Type variable substitution over types has no effect if they do not 
 include such a type variable. *)
Lemma subst_ltvar_nochange_t : forall I T,
  lclosed_t I T -> 
  forall A U, 
    ~ In A I -> {A ~> U} T = T.
Proof.
  induction 1; intros; 
    Simplify by (Destruct notIn by (f_equal; eauto with nochange)).
      eapply IHlclosed_t2.
      eapply notIn_remove_notIn with (m := O); eauto with nochange.
Qed.

(** Type parameter substitution over types also has no effect if they 
 do not include such a type parameter. *)
Lemma subst_ftvar_nochange_t : forall T U S X, 
  ~ In X (FV_tt T) -> [(X, U) ~> S] T = T. 
Proof.
  induction T; intros; 
    Simplify by (Destruct notIn by (f_equal; eauto with nochange)).
    inversion e; subst; congruence.
Qed.  

Hint Resolve subst_ltvar_nochange_t subst_ftvar_nochange_t : nochange.

Fixpoint synsize_t (T:typ) :=
  match T with
    | typ_top     => 0
    | typ_ltvar _ => 0
    | _ ^^ T      => S (synsize_t T)
    | T --> U     => S (synsize_t T + synsize_t U)
    | typ_all T U => S (synsize_t T + synsize_t U)
  end.

Lemma lem_subst_ftvar_nochange_t_idemp : forall T S,
  synsize_t S <= synsize_t T -> 
  forall X U, [(X, T) ~> U] S = S.
Proof.
  induction S; intros; Simplify by (f_equal; eauto with arith). 
    inversion e; subst; firstorder using le_Sn_n.
Qed.

(** We may swap variable and parameter substitution. *)
Lemma subst_rename_ftvar_ltvar_t : forall T U S X Y,
  forall A,
    [(X,U) ~> Y^^U] ({A ~> S} T) = {A ~> [(X,U) ~> Y^^U] S} ([(X,U) ~> Y^^U] T).
Proof.
  induction T; intros; Simplify by (f_equal; eauto; congruence). 
Qed.

Lemma subst_ftvar_ltvar_t : forall T U S S' X,
  lclosed_t emptyset S ->
  forall A,
    [(X,U) ~> S] ({A ~> S'} T) = {A ~> [(X,U) ~> S] S'} ([(X,U) ~> S] T).
Proof.
  induction T; intros; Simplify by (f_equal; eauto with nochange; congruence). 
Qed.

(** We may replace a type variable with a fresh type parameter, and then 
 replace the type parameter with a given type instead of directly replacing 
 the type variable with the given type. *)
Lemma subst_seq_ftvar_ltvar_t : forall T U S X,
  ~ In X (FV_tt T) ->
  forall A,
    [(X,U) ~> S] ({A ~> (X^^U)} T) = {A ~> S} T.
Proof.
  induction T; intros; 
    Simplify by (Destruct notIn by (f_equal; eauto with nochange; congruence)).
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Basic properties of [sub] *)

(** [sub] deals with locally closed types only. *)
Lemma sub_lclosed_t : forall T U, 
  sub T U -> lclosed_t emptyset T /\ lclosed_t emptyset U.
Proof.
  induction 1; intros; firstorder.
  unsimpl (emptyset ++ emptyset:list ltvar); eauto.
  unsimpl (emptyset ++ emptyset:list ltvar); eauto.
  destruct (lclosed_t_ltvar_split _ _ _ _ H7) as [I1 [Ha' Ha'']].
  replace (emptyset:list ltvar) 
    with (emptyset ++ (map_pred_remove_zero I1)); eauto.
    simpl; rewrite Ha''; eauto.
  destruct (lclosed_t_ltvar_split _ _ _ _ H8) as [I2 [Ha' Ha'']].
  replace (emptyset:list ltvar) 
    with (emptyset ++ (map_pred_remove_zero I2)); eauto.
    simpl; rewrite Ha''; eauto.
Qed.
(* *************************************************************** *)

(** ** Renaming property of [sub]
 As is well-known in the literature, the exists-fresh style necessitates 
 various renaming properties. This section presents the proof of Lemma 
 [sub_rename_ftvar] which formally states the renaming property of [sub].

 We first prove Lemma [lclosed_t_rename_ftvar], and the prove Lemma 
 [sub_rename_ftvar] using it. *)
Lemma lclosed_t_rename_ftvar : forall T U X Y I,
  lclosed_t I T ->
  lclosed_t I ([(X, U) ~> Y ^^ U] T).
Proof.
  induction 1; intros; Simplify by eauto.
    inversion e; subst; eauto.
Qed.

Hint Resolve lclosed_t_rename_ftvar : rename_aux.

(** The proof proceeds by induction on the size of [sub T U] proofs. *)
Lemma sub_rename_ftvar_aux : forall m n T U,
  n < m ->
  subLH n T U ->
  forall X Y S,
      subLH n ([(X,S) ~> Y^^S] T) 
              ([(X,S) ~> Y^^S] U).
Proof.
  induction m.
  firstorder using lt_n_O. 
  destruct 2; intros; Simplify by eauto with rename_aux.
  inversion e; subst; eauto.
  inversion e; subst.
    rewrite <- (lem_subst_ftvar_nochange_t_idemp S S) at 1; eauto with arith.
  eauto with arith.
  econstructor; eauto with arith.
  set (L := FV_tt ([(X0, S)~> Y ^^ S]T2) ++
           FV_tt ([(X0, S)~> Y ^^ S]U2) ++ 
           FV_tt ([(X0, S)~> Y ^^ S]T1) ++
           FV_tt ([(X0, S)~> Y ^^ S]U1) ++
           (X0 :: nil)).
  destruct (pick_fresh L) as [Z Hfresh'].
  unfold L in Hfresh'.
  apply subLH_all with Z; Destruct notIn by (eauto with arith).
    replace (Z ^^ ([ (X0, S)~> Y ^^ S] U1)) 
      with ([ (X0, S)~> Y ^^ S] (Z ^^ U1)) by (Simplify by congruence).
    repeat (rewrite <- (subst_rename_ftvar_ltvar_t) by auto).
    apply IHm; eauto with arith.
      rewrite <- subst_seq_ftvar_ltvar_t 
        with (T := T2) (X := X) (U := U1) by eauto.
      rewrite <- subst_seq_ftvar_ltvar_t 
        with (T := U2) (X := X) (U := U1) by eauto.
      eauto with arith. 
Qed.

Lemma sub_rename_ftvar : forall T U,
  sub T U ->
  forall X Y S,
      sub ([(X, S) ~> Y ^^ S] T) 
          ([(X, S) ~> Y ^^ S] U).
Proof.
  intros.
  destruct (sub_subLH H) as [n ?].
  eauto using sub_rename_ftvar_aux. 
Qed.

Hint Resolve sub_rename_ftvar : rename_aux.

Lemma sub_ltvar_subst_rename_ftvar : forall T U,
  forall X, ~ In X (FV_tt T) -> ~ In X (FV_tt U) ->
  forall S A B Y, 
  sub ({A ~> X ^^ S} T) ({B ~> X ^^ S} U) ->
  sub ({A ~> Y ^^ S} T) ({B ~> Y ^^ S} U).
Proof.
  intros.
  rewrite <- subst_seq_ftvar_ltvar_t with (A := A) (X := X) (U := S) by eauto.
  rewrite <- subst_seq_ftvar_ltvar_t with (A := B) (X := X) (U := S) by eauto.
  eauto with rename_aux.
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
Definition sub_transitivity_on T := forall U S,
  sub U T -> sub T S -> sub U S.

Lemma sub_narrowing_aux : forall m n T U,
  n < m ->
  subLH n T U ->
  forall S S',
    sub_transitivity_on S ->
    sub S' S ->
    forall X,
      sub ([(X, S) ~> X ^^ S'] T)
          ([(X, S) ~> X ^^ S'] U).
Proof.
  induction m.
  firstorder using lt_n_O. 
  destruct 2; intros.
  destruct (sub_lclosed_t H2) as [? ?]; eauto with subst_aux.
  destruct (sub_lclosed_t H2) as [? ?].
  Simplify by eauto with subst_aux. 
  Simplify by eauto with arith.
    inversion e; subst.
    apply H1; eauto.
    erewrite <- lem_subst_ftvar_nochange_t_idemp at 1; eauto with arith.
  Simplify by idtac.
  econstructor; eauto with arith.
  set (L := X0 :: FV_tt ([ (X0, S)~> X0 ^^ S'] T2) ++
            FV_tt ([ (X0, S)~> X0 ^^ S'] U2) ++ 
            FV_tt ([ (X0, S)~> X0 ^^ S'] T1) ++
            FV_tt ([ (X0, S)~> X0 ^^ S'] U1)).
  destruct (pick_fresh L) as [Y HfreshL].
  unfold L in HfreshL.
  Simplify by (Destruct notIn by eauto).
  constructor 5 with Y; eauto with arith.
    destruct (sub_lclosed_t H5) as [? ?].
    destruct (sub_lclosed_t (subLH_sub H0_)) as [? ?].
    replace (Y ^^ ([ (X0, S)~> X0 ^^ S'] U1))
      with ([ (X0, S)~> X0 ^^ S' ] (Y ^^ U1)) by Simplify by congruence.
    repeat rewrite <- subst_ftvar_ltvar_t by eauto.
    forwards Hdelta : (sub_rename_ftvar_aux (lt_n_Sn n2) H0_0 X Y U1).
    eapply IHm with n2; eauto with arith.
    rewrite <- subst_seq_ftvar_ltvar_t with (T := T2) (X := X) (U := U1);
      eauto.
    rewrite <- subst_seq_ftvar_ltvar_t with (T := U2) (X := X) (U := U1);
      eauto.
Qed.

Lemma sub_narrowing : forall T U,
  sub T U ->
  forall S S',
    sub_transitivity_on S ->
    sub S' S ->
    forall X,
      sub ([(X, S) ~> X ^^ S'] T)
          ([(X, S) ~> X ^^ S'] U).
Proof.
  intros.
  destruct (sub_subLH H) as [n ?].
  eauto using sub_narrowing_aux.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** *** Transitivity 
 We then prove the transitivity of [sub] by induction on the size 
 of types. The size of types is defined by function [size_t]. *)
Fixpoint size_t (T : typ) : nat :=
  match T with
    | typ_top         => 0
    | typ_ltvar _     => 0
    | typ_ftvar _ _   => 0
    | typ_arrow T1 T2 => S (size_t T1 + size_t T2)
    | typ_all T1 T2   => S (size_t T1 + size_t T2)
  end.

Lemma size_t_nochange_ltvar : forall T A X U,
  size_t ({A ~> X ^^ U} T) = size_t T.
Proof.
  induction T; intros; Simplify by (simpl; eauto).
Qed.

(** Lemma [sub_trans_ftvar_aux] deals with the [typ_ftvar] case. *)
Lemma sub_trans_ftvar_aux : forall A S U X,
  sub A S ->
  S = (X ^^ U) ->
  forall S', sub S S' -> sub A S'.
Proof.
  induction 1; intros; try discriminate; eauto.
Qed.

(** Lemma [sub_trans_fun_aux] deals with the [typ_arrow] case. *)
Lemma sub_trans_fun_aux : forall T U U1 U2 S,
  sub_transitivity_on U1 ->
  sub_transitivity_on U2 ->
  sub T U ->
  sub U S ->
  U = U1 --> U2 ->
  sub T S.
Proof.
  induction 3; intros; try discriminate; eauto.
  inversion H2; subst; clear H2.
    destruct (sub_lclosed_t H1_) as [? ?].
    destruct (sub_lclosed_t H1_0) as [? ?].
    inversion H1; subst; econstructor; eauto.
      unsimpl (emptyset ++ emptyset:list ltvar); eauto.
Qed.

(** Lemma [sub_trans_forall_aux] deals with the [typ_all] case. *) 
Lemma sub_trans_forall_aux : forall T U U1 U2 S,
  (forall S, size_t S < size_t U -> sub_transitivity_on S) ->
  sub T U ->
  U = typ_all U1 U2 ->
  sub U S ->
  sub T S.
Proof.
  intros until 2. 
  induction H0; intros; try discriminate; eauto.
  clear IHsub1 IHsub2.
  inversion H4; subst; clear H4.
  inversion H5 as [ B | | | | ? ? S1 S2 Y]; subst.
  econstructor.
    destruct (sub_lclosed_t H0_0) as [H' _].
    destruct (sub_lclosed_t H0_) as  [_ H''].
    destruct (lclosed_t_ltvar_split _ _ _ _ H') as [I [Ha Hb]].
    replace (emptyset :list ltvar) with (emptyset ++ (map_pred_remove_zero I)) 
      by (simpl; rewrite Hb; eauto).
    econstructor; eauto.
  set (L := FV_tt T2 ++ FV_tt U2 ++ FV_tt S2 ++ FV_tt T1 ++ FV_tt S1).
  destruct (pick_fresh L) as [Z Hfresh].
  unfold L in Hfresh.
  assert (sub ({O ~> Z^^U1}T2) ({O ~> Z^^U1}U2)).
    eapply sub_ltvar_subst_rename_ftvar; eauto.
  assert (sub ({O ~> Z^^S1}T2) ({O ~> Z^^S1}U2)).
    Destruct notIn by idtac.
    rewrite <- (subst_seq_ftvar_ltvar_t T2 U1 (Z^^S1) Z) by eauto.
    rewrite <- (subst_seq_ftvar_ltvar_t U2 U1 (Z^^S1) Z) by eauto.
    eapply sub_narrowing; Simplify by eauto with arith.
  assert (sub ({O ~> Z^^S1} U2) ({O ~> Z^^S1}S2)).
    eapply sub_ltvar_subst_rename_ftvar; eauto.
  assert (sub_transitivity_on ({O ~> Z^^S1} U2)).
    apply H; Simplify by idtac.
    rewrite size_t_nochange_ltvar; eauto with arith.
  assert (sub ({O ~> Z^^S1} T2) ({O ~> Z^^S1} S2)) by auto.
  assert (sub_transitivity_on U1).
    apply H; Simplify by eauto with arith.
  assert (sub S1 T1) by eauto.
  Destruct notIn by eauto.
Qed.

(** Using these lemmas, we may complete the proof of the transitivity. *)
Lemma sub_transitivity_aux : forall n T,
  size_t T < n -> sub_transitivity_on T.
Proof.
  induction n; intros.
  firstorder using lt_n_O. 
  destruct T; unfold sub_transitivity_on; intros.
  inversion H1; assumption.
  inversion H1; inversion H2; eauto.
  eauto using sub_trans_ftvar_aux.
  Simplify by idtac.
  assert (size_t T1 < n) by eauto with arith.
  assert (size_t T2 < n) by eauto with arith.
  eauto using sub_trans_fun_aux.
  Simplify by idtac.
  assert (forall S, 
    size_t S < size_t (typ_all T1 T2) -> 
    sub_transitivity_on S) by eauto with arith.
  eauto using sub_trans_forall_aux.
Qed.

Lemma sub_transitivity : forall T U S, sub T U -> sub U S -> sub T S.
Proof.
  intros.
  forwards Ha : sub_transitivity_aux (Datatypes.S (size_t U)) U; 
    eauto with arith.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Reflexivity of [sub]
 Reflexivity of [sub] is straightforward to prove. The proof proceeds
 by induction on the size of types.*)
Lemma sub_reflexivity_aux : forall n T,
  size_t T < n -> lclosed_t emptyset T -> sub T T.
Proof.
  induction n. 
  firstorder using lt_n_O.
  destruct T; intros H' H; inversion H; Simplify by eauto.
  assert (size_t T1 < n) by eauto with arith.  
  assert (size_t T2 < n) by eauto with arith.
  assert (I1 = emptyset) by firstorder using app_eq_nil.
  assert (I2 = emptyset) by firstorder using app_eq_nil.
  subst; eauto.
  set (L := FV_tt T1 ++ FV_tt T2).
  destruct (pick_fresh L) as [X Hfresh].
  unfold L in Hfresh.
  assert (I1 = emptyset) by firstorder using app_eq_nil; subst I1.
  assert (map_pred_remove_zero I2 = emptyset) by firstorder using app_eq_nil.
  constructor 5 with (X := X); Destruct notIn by eauto.
    apply IHn; eauto with arith.     
    apply IHn; subst.
      rewrite size_t_nochange_ltvar; eauto with arith.
      replace (emptyset : list ltvar) with (remove eq_nat_dec O I2) 
        by eauto using map_eq_nil.
      eauto using lclosed_t_subst_ltvar.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Challenge 2A: Type Safety 
 This section presents our solution to the POPLmark Challenge 2A. *)
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Properties of [lclosed_e]
 Unlike [sub] which uses [lclosed_t] only, [typing] uses both [lclosed_t]
 and [lclosed_e]. This section presents properties of [lclosed_e] that 
 we will use in the rest. *)

(** [lclosed_e] is also invertible. *)
Lemma lclosed_e_lvar_split : forall t I i0 a x T,
  lclosed_e I i0 ({a ::~> x ** T} t) -> 
    (exists i, lclosed_e I i t /\ remove eq_nat_dec a i = i0). 
Proof.
  induction t; intros; Simplify by try congruence.
  inversion H; subst.
    exists (a :: emptyset); split; Simplify by eauto.
  inversion H; subst.
    exists (n :: emptyset); split; Simplify by eauto.
  inversion H; subst.
    exists (emptyset : list lvar); eauto.
  inversion H; subst.
    forwards Ha : (IHt _ _ _ _ _ H5).
    destruct Ha as [i0 [Hb Hc]].
    exists (map_pred_remove_zero i0); split; eauto.
      rewrite swap_remove_map_pred_remove_zero; congruence.
  inversion H. 
    forwards Ha : (IHt1 _ _ _ _ _ H4); destruct Ha as [ia [? ?]].
    forwards Hb : (IHt2 _ _ _ _ _ H5); destruct Hb as [ib [? ?]].
    exists (ia ++ ib); split; eauto.
      rewrite <- H7; rewrite <- H9; eauto using list_remove_app.
  inversion H; subst.
    forwards Ha : (IHt _ _ _ _ _ H5); destruct Ha as [ia [? ?]].
    exists ia; eauto.
  inversion H; subst.
    forwards Ha : (IHt _ _ _ _ _ H4); destruct Ha as [ia [? ?]].
    exists ia; eauto.
Qed.

Lemma lclosed_e_ltvar_split : forall t I0 i A X T,
  lclosed_e I0 i ({A :~> X ^^ T} t) ->
    (exists I, lclosed_e I i t /\ remove eq_nat_dec A I = I0).
Proof.
  induction t; intros; Simplify by try congruence.
  inversion H; subst.
    exists (emptyset:list ltvar); Simplify by eauto.
  inversion H; subst.
    exists (emptyset:list ltvar); Simplify by eauto.
  inversion H.
    forwards Ha : (IHt _ _ _ _ _ H5); destruct Ha as [Ia [? ?]].
    forwards Hb : (lclosed_t_ltvar_split _ _ _ _ H4); destruct Hb as [Ib [? ?]].
    subst; exists (Ib ++ Ia); eauto using list_remove_app.
  inversion H; subst.
    forwards Ha : (IHt1 _ _ _ _ _ H4); destruct Ha as [Ia [? ?]].
    forwards Hb : (IHt2 _ _ _ _ _ H5); destruct Hb as [Ib [? ?]].
    subst; exists (Ia ++ Ib); eauto using list_remove_app.
  inversion H; subst.
    destruct (lclosed_t_ltvar_split _ _ _ _ H4) as [Ia [? ?]].
    destruct (IHt _ _ _ _ _ H5) as [Ib [? ?]].
    subst; exists (Ia ++ map_pred_remove_zero Ib); split; eauto.
      rewrite list_remove_app; rewrite swap_remove_map_pred_remove_zero; eauto. 
  inversion H; subst.
    destruct (IHt _ _ _ _ _ H4) as [Ia [? ?]].
    destruct (lclosed_t_ltvar_split _ _ _ _ H5) as [Ib [? ?]].
    subst; exists (Ia ++ Ib); eauto using list_remove_app.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Properties of substitution over terms.  
 For the proof of type safety, we deal with not only substitution over 
 types but also substitution over terms, and thus we will present its 
 properties in this section. *)

(** Variable substitution over terms has no effect if they do not 
 include such a variable. *)
Lemma subst_lvar_nochange_e : forall t I i a u,
  lclosed_e I i t ->
  ~ In a i ->
  { a ::~> u } t = t.
Proof.
  induction t; intros; inversion H; subst;
    Simplify by Destruct notIn by (f_equal; firstorder).
      eapply IHt; eauto.
      eapply notIn_remove_notIn with (m := 0); eauto with nochange.
Qed.

Lemma subst_ltvar_nochange_e : forall t I i A T,
  lclosed_e I i t ->
  ~ In A I ->
  {A :~> T} t = t.
Proof.
  induction t; intros; inversion H; subst;
    Destruct notIn by Simplify by (f_equal; eauto with nochange).
      eapply IHt; eauto.
      eapply notIn_remove_notIn with (m := 0); eauto with nochange.
Qed.

(** Parameter substitution over terms also has no effect on terms 
 if they do not include such a parameter. *)
Lemma subst_fvar_nochange_e : forall t u x T,
  ~ In x (FV_ee t) -> [(x, T) ::~> u] t = t.
Proof.
  induction t; intros; Simplify by Destruct notIn by (f_equal; eauto). 
    inversion e; subst; congruence.
Qed.

Lemma subst_ftvar_nochange_e : forall t X T U, 
  ~ In X (FV_te t) -> ([ ( X , T ) :~> U ] t) = t.
Proof.
  induction t; intros; 
    Simplify by Destruct notIn by (f_equal; eauto with nochange). 
Qed.

Hint Resolve subst_lvar_nochange_e subst_ltvar_nochange_e : nochange.
Hint Resolve subst_fvar_nochange_e subst_ftvar_nochange_e : nochange.

(** We may swap variable and parameter substitution. *) 
Lemma subst_lvar_lvar_e : forall t a x T b y U,
  a <> b -> 
  {b ::~> y ** U}({a ::~> x ** T} t) = {a ::~> x ** T}({b ::~> y ** U} t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto).
Qed.

Lemma subst_fvar_lvar_e : forall t u a x T y U I,
  lclosed_e I emptyset u -> 
  x <> y -> 
  [(y, U) ::~> u]({a ::~> x ** T} t) = {a ::~> x ** T}([(y, U) ::~> u] t).
Proof.
  induction t; intros; 
    Simplify by (f_equal; eauto with nochange; congruence). 
Qed.

Lemma subst_ltvar_lvar_e : forall t A X a x T U ,
  {A :~> X ^^ T} ({a ::~> x ** U} t) = {a ::~> x ** U} ({A :~> X^^T} t).
Proof.
  induction t; intros; Simplify by congruence.
Qed.

Lemma subst_ltvar_fvar_e : forall t A X T x U u,
  lclosed_e emptyset emptyset u -> 
  {A :~> X^^T}([(x, U) ::~> u] t) = [(x, U) ::~> u]({A :~> X^^T}t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto with nochange; congruence).
Qed.

Lemma subst_ftvar_lvar_e : forall t u X T U a,
  [(X, T) :~> U]({a ::~> u} t) = {a ::~> ([(X, T) :~> U] u)}([ (X, T) :~> U] t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto).
Qed.
  
Lemma subst_ftvar_ltvar_e : forall t A X T U U',
  lclosed_t emptyset U -> 
  [(X, T) :~> U] ({A :~> U'} t) = {A :~> [(X, T) ~> U] U'} ([(X, T) :~> U] t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto using subst_ftvar_ltvar_t).
Qed.

Lemma subst_rename_ftvar_ltvar_e : forall t A X Y T U,
  [(X, T) :~> (Y^^T)] ({A :~> U} t) = 
    {A :~> [(X, T)~>(Y^^T)] U} ([(X, T) :~> (Y^^T)] t).
Proof.
  induction t; intros; 
    Simplify by (f_equal; eauto using subst_rename_ftvar_ltvar_t).
Qed.

(** We may replace a variable with a fresh parameter, and then replace 
 the parameter with a given type (or term) instead of directly replacing 
 the variable with the given type (or term). *)
Lemma subst_seq_fvar_lvar_e : forall t u a x T,
  ~ In x (FV_ee t) -> 
  [(x, T) ::~> u]({a ::~> x ** T} t) = {a ::~> u} t.
Proof.
  induction t; intros; Simplify by Destruct notIn 
    by (f_equal; eauto with nochange; congruence). 
Qed.

Lemma subst_seq_ftvar_ltvar_e : forall t T U X,
  ~ In X (FV_te t) ->
  forall A,
    [(X,T) :~> U] ({A :~> (X^^T)} t) = {A :~> U} t.
Proof.
  induction t; intros; Simplify by Destruct notIn 
    by (f_equal; eauto using subst_seq_ftvar_ltvar_t with nochange).
Qed.

(** [FV_te] and [FV_ee] are stable under substitutions. *)
Lemma FV_te_nochange_lvar : forall t a x y T,
  FV_te ({a ::~> x ** T} t) = FV_te ({a ::~> y ** T} t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto).
Qed.

Hint Resolve FV_te_nochange_lvar : nochange.

Lemma FV_ee_nochange_ltvar : forall t T A, 
  FV_ee ({A :~> T} t) = FV_ee t.
Proof.
  induction t; intros; Simplify by eauto. 
    rewrite IHt1; rewrite IHt2; eauto.
Qed.
 
Lemma FV_ee_nochange_ftvar : forall t X T Y U,
  FV_ee ([(X, T) :~> Y^^U] t) = FV_ee t.
Proof.
  induction t; intros; Simplify by eauto.
    rewrite IHt1; rewrite IHt2; eauto.
Qed.

Hint Resolve FV_ee_nochange_ltvar FV_ee_nochange_ftvar : nochange.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Basic properties of [typing] *)

(** [typing] deals with locally closed types and terms only. *) 
Lemma typing_lclosed_et : forall t T,
  typing t T -> lclosed_e emptyset emptyset t /\ lclosed_t emptyset T.
Proof.
  induction 1; Simplify by eauto.
  destruct IHtyping as [Ha Hb].
  destruct (lclosed_e_lvar_split _ _ _ _ Ha) as [I [? ?]].
  split.
    rewrite <- emptyset_plus at 1.
    pattern (emptyset: list ltvar) at 3; 
      replace (emptyset:list ltvar) with (map_pred_remove_zero I)
        by (rewrite H3; eauto); eauto.
    unsimpl (emptyset ++ emptyset : list ltvar); eauto.
  destruct IHtyping1; destruct IHtyping2.
  split. 
    rewrite <- emptyset_plus; eauto.
    inversion H2; subst.
    destruct (app_eq_nil _ _ H5) as [? ?]; subst; eauto.
  destruct IHtyping.
  destruct (lclosed_e_ltvar_split _ _ _ _ H2) as [Ia [? ?]].
  destruct (lclosed_t_ltvar_split _ _ _ _ H3) as [Ib [? ?]].
  split.
    pattern (emptyset:list ltvar) at 1; 
      replace (emptyset:list ltvar) with (emptyset ++ map_pred_remove_zero Ia) 
        by (rewrite H5; eauto); eauto. 
    pattern (emptyset:list ltvar) at 1; 
      replace (emptyset:list ltvar) with (emptyset ++ map_pred_remove_zero Ib) 
        by (rewrite H7; eauto); eauto.
  destruct IHtyping.
  destruct (sub_lclosed_t H0) as [? ?].
  split.
    rewrite <- emptyset_plus at 1; eauto.
    inversion H2; subst.
    destruct (app_eq_nil _ _ H5) as [? ?]; subst.
    assert ( remove eq_nat_dec 0 I2 = map_pred_remove_zero I2 ).
      rewrite (map_eq_nil pred (remove eq_nat_dec O I2) H5); eauto.
    replace (map_pred_remove_zero I2) with (remove eq_nat_dec O I2).
    simpl; eauto using lclosed_t_subst_ltvar.      
  destruct (sub_lclosed_t H0).
  destruct IHtyping; eauto.
Qed.
(* *************************************************************** *)

(** ** Renaming property of Typing 
 As is well-known in the literature, the exists-fresh style necessitates 
 various renaming properties. This section proves two lemmas which states 
 the renaming property of [typing] for term and type parameters, respectively. 
*)

(** *** Term parameter renaming 
 This section presents the proof of Lemma [typingLH_subst_lvar_rename_fvar]
 which states the term parameter renaming property of [typing]. The proof
 proceeds by induction on the sum of the size of [typing] proofs and the 
 size of terms whose definition is given as follows: *)
Fixpoint size_e (t : tm) : nat :=
  match t with
    | tm_lvar _     => 0
    | tm_fvar _ _   => 0
    | tm_abs _ t  => S (size_e t)
    | tm_app t1 t2  => S (size_e t1 + size_e t2)
    | tm_tabs _ t => S (size_e t)
    | tm_tapp t _   => S (size_e t)
  end.

Lemma size_e_nochange_lvar : forall t a x T,
  size_e ({a ::~> x ** T} t) = size_e t.
Proof.
  induction t; intros; Simplify by eauto. 
Qed.

Lemma size_e_nochange_ltvar : forall t A X T,
  size_e ({ A :~> X ^^ T} t) = size_e t.
Proof.
  induction t; intros; Simplify by eauto.
Qed.

Hint Resolve size_e_nochange_lvar size_e_nochange_ltvar : nochange.

Lemma typingLH_subst_lvar_rename_fvar : forall k t u a x y T U n,
  n + size_e t < k -> 
  typingLH n u T -> 
  u = {a ::~> x ** U} t -> 
  typingLH n ({a ::~> y ** U} t) T.
Proof.
  induction k.
  firstorder using lt_n_O.
  destruct 2; intro; Simplify by try congruence.
  destruct t; Simplify by try discriminate; inversion H1; subst; eauto.
  destruct t; Simplify by try discriminate; inversion H3; subst; eauto.
    set (L := FV_ee ({S a ::~> y ** U} t1)).
    destruct (pick_fresh L) as [x' Hfresh].
    unfold L in Hfresh.
    constructor 2 with (x := x'); auto.
    assert ( k0 + size_e ({S a ::~> y ** U}t1) < k ).
      rewrite size_e_nochange_lvar; eauto with arith.
    assert ( k0 + size_e ({O ::~> x0 ** t}t1) < k ).
      rewrite size_e_nochange_lvar; eauto with arith.
    eapply IHk with (u := {O ::~> x0 ** t}({ S a ::~> y ** U } t1)); eauto.
    rewrite subst_lvar_lvar_e by congruence.
    eapply IHk with (u := {S a ::~> x ** U}({ O ::~> x0 ** t } t1)); eauto.
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
      erewrite FV_te_nochange_lvar; eassumption.
      simpl in H; rewrite <- plus_Snm_nSm in H.
      assert ( k0 + size_e ({O :~> X ^^ t}t1) < k ).
        rewrite size_e_nochange_ltvar; eauto with arith.
      rewrite subst_ltvar_lvar_e. 
      eapply IHk with (u := {a ::~> x** U}({O :~> X ^^ t} t1)); eauto.
      rewrite <- subst_ltvar_lvar_e; eauto.
  destruct t; Simplify by try discriminate.
    inversion H2; subst; clear H2.
    assert (k0 + size_e t < k) by eauto with arith; eauto.
  eauto with arith.
Qed.

(** *** Type parameter renaming 
 This section presents the proof of Lemma [typingLH_subst_ltvar_rename_ftvar]
 which states the type parameter renaming property of [typing]. The proof
 proceeds by induction on the size of [typing] proofs. *)
Lemma typing_rename_ftvar_aux : forall m n t T,
  n < m -> 
  typingLH n t T ->  
  forall X Y U,
  typingLH n ([(X, U) :~> Y ^^ U] t) ([(X, U) ~> Y ^^ U] T).
Proof.
  induction m.
  firstorder using lt_n_O. 
  destruct 2; intros; Simplify by eauto with rename_aux.
  constructor 2 with (x := x); eauto with rename_aux.
    rewrite FV_ee_nochange_ftvar; eauto.
    unsimpl ([ (X, U0) :~> Y ^^ U0](x ** T)).
    erewrite <- subst_ftvar_lvar_e; eauto with arith.
  econstructor; eauto with arith.
    unsimpl ([(X, U0)~> Y^^U0](T --> U)); eauto with arith.
  set (L := X0 :: FV_te t ++ FV_te ([(X0, U0):~>Y^^U0] t) ++ 
                  FV_tt U ++ FV_tt ([(X0, U0)~>Y^^U0] U)).
  destruct (pick_fresh L) as [Z HfreshL].
  unfold L in HfreshL.
  constructor 4 with (X := Z); Destruct notIn by eauto with rename_aux.
  repeat replace (Z ^^ ([ (X0, U0)~> Y ^^ U0]T)) 
    with ([ (X0, U0) ~> Y ^^ U0 ] (Z ^^ T )) by Simplify by congruence.
  rewrite <- subst_rename_ftvar_ltvar_t.
  rewrite <- subst_rename_ftvar_ltvar_e.
  eapply IHm; eauto with arith.
  erewrite <- subst_seq_ftvar_ltvar_t with (X := X) by eauto.
  erewrite <- subst_seq_ftvar_ltvar_e with (X := X) by eauto.
  eapply IHm; eauto with arith.
  rewrite subst_rename_ftvar_ltvar_t.
  econstructor 5 with (U := [(X, U0) ~> Y ^^ U0] U); eauto with rename_aux.
    unsimpl ([ (X, U0) ~> Y ^^ U0 ] (typ_all U S)); eauto with arith.
  econstructor; eauto with rename_aux arith.
Qed.

Hint Resolve typing_rename_ftvar_aux : rename_aux.

Lemma typingLH_subst_ltvar_rename_ftvar : forall m t T,
  forall X, ~ In X (FV_te t) -> ~ In X (FV_tt T) ->
  forall U Y A B ,
  typingLH m ({A :~> X ^^ U} t) ({B ~> X ^^ U} T) ->
  typingLH m ({A :~> Y ^^ U} t) ({B ~> Y ^^ U} T).
Proof.
  intros.
  erewrite <- subst_seq_ftvar_ltvar_t with (X := X) by eauto.
  erewrite <- subst_seq_ftvar_ltvar_e with (X := X) by eauto.
  eauto using typing_rename_ftvar_aux with arith.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Substitution lemma 
 This section presents the main result: [typing] is stable under type
 and term parameter substitution.  

 *** Type parameter substitution lemma
 We first prove Lemma [typing_subst_ftvar] which shows that [typing] 
 is stable under type parameter substitution. The proof proceeds by 
 induction on the size of [typing] proofs. Note the use of the renaming 
 lemmas in the [typing_abs] and [typing_tabs] cases. *)
Lemma sub_subst_ftvar_aux : forall m n T U,
  n < m
  -> subLH n T U
  -> forall X S S', 
    sub S' S
    -> sub ([(X, S) ~> S'] T) ([(X, S) ~> S'] U).
Proof.
  induction m.
  firstorder using lt_n_O.
  destruct 2; intros.
  Simplify by firstorder using sub_lclosed_t with subst_aux.
  destruct (sub_lclosed_t H1) as [? ?].
  Simplify by eauto using sub_reflexivity_aux with subst_aux arith.
  assert (n < m) by eauto with arith.
  Simplify by eauto.
    inversion e; subst; clear e.
    forwards IHsub' : IHm H2 H0 H1.
    erewrite lem_subst_ftvar_nochange_t_idemp in IHsub';
    eauto using sub_transitivity.
  assert (n1 < m) by eauto with arith.
  assert (n2 < m) by eauto with arith.
  Simplify by eauto.
  set (L := 
    FV_tt ([(X0, S)~> S'] T2) ++ FV_tt ([(X0, S) ~> S'] U2) ++
    FV_tt ([(X0, S)~> S'] T1) ++ FV_tt ([(X0, S)~> S'] U1) ++ (X0 :: nil)
  ).
  destruct (pick_fresh L) as [Y Hfresh'].
  unfold L in Hfresh'.
  Simplify by eauto.
  constructor 5 with (X := Y); Destruct notIn by eauto with arith.
  assert (n2 < m) by eauto with arith.
  assert (n2 < Datatypes.S n2) by eauto with arith.
  destruct (sub_lclosed_t H4) as [? ?].
  forwards Ha : (sub_rename_ftvar_aux H10 H0_0 X Y U1).
  repeat rewrite subst_seq_ftvar_ltvar_t in Ha by assumption.
  forwards Hb : (IHm n2 _ _ H10 Ha X0 _ _ H4).
  repeat rewrite subst_ftvar_ltvar_t in Hb by assumption.
  Simplify by eauto.
    inversion e; congruence.
Qed.

Lemma sub_subst_ftvar : forall T U,
  sub T U
  -> forall X S S', 
      sub S' S 
    -> sub ([(X,S) ~> S'] T) ([(X,S) ~> S'] U).
Proof.
  intros.
  destruct (sub_subLH H) as [n H']; eauto using sub_subst_ftvar_aux.
Qed.

Hint Resolve sub_subst_ftvar : subst_aux.

Lemma typing_sub_subst_ftvar_aux : forall m n t X T U U',
    n < m
  -> typingLH n t T
  -> sub U' U 
  -> typing ([(X, U) :~> U'] t) ([(X, U) ~> U'] T).
Proof.
  induction m.
  firstorder using lt_n_O.
  destruct 2; intros Hsub; 
    destruct (sub_lclosed_t Hsub) as [? ?]; 
      Simplify by eauto with subst_aux.
  set (L := FV_ee ([(X, U) :~> U'] t)).
  destruct (pick_fresh L) as [y HfreshL].
  unfold L in HfreshL.
  constructor 2 with (x := y); eauto with subst_aux.
  unsimpl ([ (X, U) :~> U' ] (y ** T)); rewrite <- subst_ftvar_lvar_e.
  eapply IHm; eauto using typingLH_subst_lvar_rename_fvar with arith.
  assert (k1 < m) by eauto with arith.
  assert (k2 < m) by eauto with arith.  
  econstructor 3 with (T := [(X, U) ~> U'] T); eauto.
    unsimpl ([(X, U) ~> U'] (T --> U0)); eauto.
  set (L := X :: FV_te ([(X, U):~>U']t) ++ FV_tt ([(X,U)~>U']U0)).
  destruct (pick_fresh L) as [Y HfreshL].
  unfold L in HfreshL.
  econstructor 4 with (X := Y); 
    Destruct notIn by eauto using lclosed_t_subst_ftvar.
  replace (Y ^^ ([ (X, U)~> U']T)) 
    with ([ (X, U) ~> U' ] Y ^^ T) by Simplify by congruence.
  rewrite <- subst_ftvar_ltvar_e by eauto.
  rewrite <- subst_ftvar_ltvar_t by eauto.
  eapply IHm; eauto using typingLH_subst_ltvar_rename_ftvar with arith.
  rewrite subst_ftvar_ltvar_t by eauto.
  constructor 5 with (U := [(X,U) ~> U'] U0); eauto with subst_aux. 
    unsimpl ([(X,U) ~> U'](typ_all U0 S)).
    eapply IHm with (n := k); eauto with arith.
  constructor 6 with (T := [(X, U) ~> U'] T); eauto with subst_aux. 
    eapply IHm with (n:=k); eauto with arith.
Qed.

Lemma typing_sub_subst_ftvar : forall t T U U' X,
  typing t T
  -> sub U' U 
  -> typing ([(X, U) :~> U'] t) ([(X,U) ~> U'] T).
Proof.
  intros.
  destruct (typing_typingLH H) as [n HsubLH'].
  eauto using typing_sub_subst_ftvar_aux.
Qed.

Lemma typing_subst_ltvar : forall t T A B X U U',
  typing ({A :~> X ^^ U} t) ({B ~> X ^^ U} T)
  -> ~ In X (FV_te t ++ FV_tt T)
  -> sub U' U
  -> typing ({A :~> U'} t) ({B ~> U'} T).
Proof.
  intros.
  destruct (sub_lclosed_t H1) as [? ?].
  Destruct notIn by idtac.
  replace U' with ([ (X, U)~> U'] X ^^ U) by Simplify by congruence.
  erewrite <- subst_ftvar_nochange_t with (T := T) (X := X) (U := U) (S := U') 
    by eauto.
  rewrite <- subst_ftvar_ltvar_t by eauto.
  rewrite <- subst_ftvar_nochange_e with (t := t) (X := X) (T := U) (U := U') 
    by eauto.
  rewrite <- subst_ftvar_ltvar_e by eauto.
  eauto using typing_sub_subst_ftvar.
Qed.

(** *** Term parameter substitution lemma
 We then prove Lemma [typing_subst_fvar] which shows that [typing] is stable
 under term parameter substitution. The proof also proceeds by induction on
 the size of [typing] proofs. Note the use of the renaming lemmas in the 
 [typing_abs] and [typing_tabs] cases. *)
Lemma typingLH_subst_fvar : forall m n t T u x U, 
  n < m 
  -> typingLH n t T 
  -> typing u U 
  -> typing ([(x, U) ::~> u] t) T.
Proof.
  induction m.
  firstorder using lt_n_O.
  destruct 2; intro H'; Simplify by eauto.
  inversion e; subst; eauto.
  set (L := x :: FV_ee ([(x, U) ::~> u] t)).
  destruct (pick_fresh L) as [y Hfresh].
  unfold L in Hfresh.
  constructor 2 with (x := y); Destruct notIn by eauto.
    destruct (typing_lclosed_et H') as [? ?].
    rewrite <- subst_fvar_lvar_e with (I := emptyset) by eauto.
    eapply IHm; eauto with arith.
    eapply typingLH_subst_lvar_rename_fvar; eauto with arith.
  assert (k1 < m) by eauto with arith.
  assert (k2 < m) by eauto with arith.
  eauto.
  set (L := FV_te ([(x, U)::~>u]t) ++ FV_tt U0).
  destruct (pick_fresh L) as [Y Hfresh].
  unfold L in Hfresh.
  constructor 4 with (X := Y); Destruct notIn by eauto.
    destruct (typing_lclosed_et H') as [? ?].
    rewrite subst_ltvar_fvar_e by eauto.
    eapply IHm; eauto with arith.
    eapply typingLH_subst_ltvar_rename_ftvar; 
      Destruct notIn by eauto with arith.
  assert (k < m) by auto with arith; eauto.
  assert (k < m) by auto with arith; eauto.
Qed.

Lemma typing_subst_fvar : forall t T u U x, 
  typing t T -> typing u U -> typing ([(x, U) ::~> u] t) T.
Proof.
  intros.
  destruct (typing_typingLH H) as [k ?]; eauto using typingLH_subst_fvar.
Qed.

Lemma typing_subst_lvar : forall a x T t u U,
  ~ In x (FV_ee t) 
  -> typing ({a ::~> x ** U} t) T
  -> typing u U
  -> typing ({a ::~> u} t) T.
Proof.
  intros.
  rewrite <- subst_seq_fvar_lvar_e with (x := x) (T := U) by eauto.
  eauto using typing_subst_fvar.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Preservation 
 Preservation is straightforward to prove once we prove the substitution 
 lemmas. Lemma [app_red_preservation] deals with the [red_abs] case, and
 Lemma [tapp_red_preservation] deals with the [red_tabs] case. *)
Lemma app_red_preservation : forall t0 T U0 U1 U2 t u,
  typing t0 T
  -> t0 = tm_abs U0 t
  -> sub T (U1 --> U2)
  -> typing u U1
  -> typing ({O ::~> u} t) U2.
Proof.
  induction 1; simpl; intros Ht0 Hsub Hu;
    inversion Ht0; subst; inversion Hsub; subst; 
    eauto using typing_subst_lvar, sub_transitivity.
Qed.

Lemma tapp_red_preservation : forall t0 T0 T t U U1 U2,
  typing t0 T0
  -> t0 = tm_tabs T t
  -> sub T0 (typ_all U1 U2)
  -> sub U U1
  -> typing ({O :~> U} t) ({O ~> U} U2).
Proof.
  induction 1; simpl; intros He HsubD HsubA; inversion He; subst.
  clear IHtyping He.
  inversion HsubD; subst.
  constructor 6 with (T := ({O ~> U} U0)).
    eapply typing_subst_ltvar; 
      Destruct notIn by eauto using sub_reflexivity_aux.
    eauto using sub_transitivity.
    erewrite <- subst_seq_ftvar_ltvar_t with (T := U0) (X := X0) by eauto.
    erewrite <- subst_seq_ftvar_ltvar_t with (T := U2) (X := X0) by eauto.    
    eapply sub_subst_ftvar; eauto.
  eauto using sub_transitivity.
Qed.

Lemma preservation_t : forall t T, 
  typing t T -> 
  forall u, red t u -> typing u T.
Proof.
  induction 1; intros u Ha; inversion Ha; subst; eauto.
  destruct (typing_lclosed_et H) as [_ Hclosed_t].
  inversion Hclosed_t; subst.
  eapply app_red_preservation; eauto using sub_reflexivity_aux.
  destruct (typing_lclosed_et H) as [_ Hclosed_t].
  inversion Hclosed_t; subst.
  eapply tapp_red_preservation; eauto using sub_reflexivity_aux.
Qed.

(** To guarantee the soundness, we additionally show that reduction does 
 not introduce new parameters. *)
Lemma FV_ee_sum : forall t u x,
  incl (FV_ee ({x ::~> u} t)) (FV_ee t ++ FV_ee u).
Proof.
  induction t; intros; Simplify by eauto with v62.
    eapply incl_app; eapply incl_tran; eauto with v62.
Qed.

Lemma preservation_fv : forall t u,
  red t u -> incl (FV_ee u) (FV_ee t).
Proof.
  induction 1; intros; Simplify by eauto using FV_ee_sum with v62.
    rewrite FV_ee_nochange_ltvar; eauto with v62.
Qed.

Lemma preservation : forall t T, 
  typing t T -> 
  forall u, red t u -> typing u T /\ incl (FV_ee u) (FV_ee t).
Proof.
  eauto using preservation_t, preservation_fv.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Progress 
 Progress is also straightforward to prove. *)
Hint Constructors value.

(** We first show that there are canonical types for type and term 
 abstraction. *)
Lemma abs_subtype_form : forall T1 T2 S,
  sub (T1 --> T2) S ->
  S = typ_top \/ exists S1 S2, S = S1 --> S2.
Proof.
  intros; inversion H; auto.
  right; exists U1 U2; auto.
Qed.

Lemma abs_typing_form : forall t T0 t0 S, 
  typing t S
  -> t = tm_abs T0 t0
  -> S = typ_top \/ exists S0 S1, S = S0 --> S1.
Proof.
  intros; induction H; try congruence.
  right; exists T U; auto.
  intuition.
    left; subst; inversion H1; auto.
    destruct H3 as [S0 [S1 Ha]]; subst.
    eauto using abs_subtype_form.
Qed.

Lemma tabs_subtype_form : forall T1 T2 S,
  sub (typ_all T1 T2) S
  -> S = typ_top \/ exists S1 S2, S = typ_all S1 S2.
Proof.
  intros; inversion H; auto.
  right; exists U1 U2; auto.
Qed.

Lemma tabs_typing_form : forall t T0 t0 S, 
  typing t S
  -> t = tm_tabs T0 t0
  -> S = typ_top \/ exists S0 S1, S = typ_all S0 S1.
Proof.
  intros; induction H; try congruence.
  right; exists T U; auto.
  intuition.
    left; subst; inversion H1; auto.
    destruct H3 as [S0 [S1 Ha]]; subst.
    eauto using tabs_subtype_form.
Qed.

(** We then show that there are canonical values for arrow and all types *)
Lemma canonical_form_abs : forall t T U,
  value t 
  -> typing t (T --> U)
  -> exists T0 t0, t = tm_abs T0 t0.
Proof.
  induction 1; simpl; intros; eauto.
  inversion H. 
  assert (tm_tabs T0 t = tm_tabs T0 t); auto.
  destruct (tabs_typing_form H0 H4).
    subst; inversion H1.
    destruct H5 as [S0 [S1 Hb]]; subst.
    inversion H1.
Qed.

Lemma canonical_form_tabs : forall t T U,
  value t
  -> typing t (typ_all T U)
  -> exists T0 t0, t = tm_tabs T0 t0.
Proof.
  induction 1; simpl; intros; eauto.
  inversion H. 
  assert (tm_abs T0 t = tm_abs T0 t); auto.
  destruct (abs_typing_form H0 H4).
    subst; inversion H1.
    destruct H5 as [S0 [S1 Hb]]; subst.
    inversion H1.
Qed.

(** Finally, we show that a well-typed term is never stuck: either it is 
 a value, or it can reduce. The proof proceeds by simple induction on the
 typing relation, and exploits the canonical forms of values for arrow and
 all types. *)
Lemma progress : forall t T,
  typing t T -> 
  FV_ee t = emptyset -> 
  value t \/ exists u, red t u.
Proof.
  induction 1; simpl; intro Hve; try congruence; auto.
  assert (FV_ee t = emptyset) by firstorder using app_eq_nil.
  assert (FV_ee t' = emptyset) by firstorder using app_eq_nil.
  destruct (IHtyping1 H1).
    destruct (IHtyping2 H2).
      destruct (canonical_form_abs H3 H) as [T0 [t0 ?]]; subst.
      right; eauto.
      destruct H4 as [t'0 ?].
      right; exists (tm_app t t'0); auto.
    destruct H3 as [t'' ?].
    right; exists (tm_app t'' t'); auto.
  destruct (IHtyping Hve).
    destruct (canonical_form_tabs H1 H) as [T0 [t0 ?]]; subst.
    right; eauto.
    destruct H1 as [t'0 ?].
    right; exists (tm_tapp t'0 T); auto.
Qed.
(* *************************************************************** *)
