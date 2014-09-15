(** This file presents a cofinite-quantification style mechanization of 
 System Fsub without contexts using locally named representation.
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
 - Challenge 2A: Type Safety  *)
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
| typ_ftvar : ftvar -> typ -> typ
| typ_arrow : typ -> typ -> typ
| typ_all   : ltvar -> typ -> typ -> typ.

Inductive tm : Set :=
| tm_lvar : lvar -> tm
| tm_fvar : fvar -> typ -> tm
| tm_abs  : lvar -> typ -> tm -> tm
| tm_app  : tm -> tm -> tm
| tm_tabs : ltvar -> typ -> tm -> tm
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
 Locally named representation makes the [typ_all] case for [FV_tt] 
 and the [tm_tabs] case for [FV_te] simple because variables and 
 parameters are syntactically distinct. *)
Fixpoint FV_tt (T:typ) : list ftvar :=
  match T with
    | typ_top       => nil
    | typ_ltvar _   => nil
    | alpha ^^ T    => alpha :: FV_tt T
    | T --> U       => FV_tt T ++ FV_tt U
    | typ_all _ T U => FV_tt T ++ FV_tt U
  end.

Fixpoint FV_te (t:tm) : list ftvar :=
  match t with
    | tm_lvar _     => nil 
    | tm_fvar _ T   => FV_tt T
    | tm_abs _ T t  => FV_tt T ++ FV_te t
    | tm_app t t'   => FV_te t ++ FV_te t'
    | tm_tabs _ T t => FV_tt T ++ FV_te t 
    | tm_tapp t T   => FV_te t ++ FV_tt T 
end.

(** ** Term parameters
 The function [FV_ee], defined below, calculates the set of term 
 parameters in a term. Locally named representation also makes 
 the [tm_abs] case simple for the same reason. *)
Fixpoint FV_ee (t:tm) : list fvar :=
  match t with
    | tm_lvar _     => nil 
    | tm_fvar x _   => x :: nil
    | tm_abs _ _ t  => FV_ee t
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
    | X ^^ T          => X ^^ T
    | T1 --> T2       => typ_arrow (lsubst_tt B U T1) (lsubst_tt B U T2)
    | typ_all A T1 T2 => 
      if A == B then typ_all A (lsubst_tt B U T1) T2
        else typ_all A (lsubst_tt B U T1) (lsubst_tt B U T2)
  end.

Fixpoint lsubst_te (B : ltvar) (U : typ)  (t : tm) {struct t} : tm :=
  match t with
    | tm_lvar a     => tm_lvar a
    | tm_fvar x T   => tm_fvar x T
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
    | tm_fvar x T   => tm_fvar x T
    | tm_abs a T t  => 
      if a == b then tm_abs a T t else tm_abs a T (lsubst_ee b u t)
    | tm_app t1 t2  => tm_app (lsubst_ee b u t1) (lsubst_ee b u t2)
    | tm_tabs A T t => tm_tabs A T (lsubst_ee b u t)
    | tm_tapp t T   => tm_tapp (lsubst_ee b u t) T
  end.

(** ** Type parameters 
   The functions [fsubst_tt] and [fsubst_te], defined below, replace
 a type parameter with a type. Note that [fsubst_tt] replaces a type
 parameter with a type only when both a parameter and its annotated
 type are matched. Locally named representation makes the [typ_all] 
 case (for [fsubst_tt]) and the [tm_tabs] case (for [fsubst_te]) simple. *)
Fixpoint fsubst_tt (Y:ftvar) (U:typ) (S : typ) (T : typ) {struct T} : typ :=
  match T with
    | typ_top         => typ_top
    | typ_ltvar A     => typ_ltvar A
    | X ^^ T          => 
      if ftvar_dec (X, T) (Y, U)
        then S else (X ^^ (fsubst_tt Y U S T))
    | T1 --> T2       => (fsubst_tt Y U S T1) --> (fsubst_tt Y U S T2)
    | typ_all A T1 T2 => typ_all A (fsubst_tt Y U S T1) (fsubst_tt Y U S T2)
  end.

Fixpoint fsubst_te (Y:ftvar) (U:typ) (S:typ) (t:tm) {struct t} : tm :=
  match t with
    | tm_lvar a     => tm_lvar a
    | tm_fvar x T   => tm_fvar x (fsubst_tt Y U S T) 
    | tm_abs a T t  => tm_abs a (fsubst_tt Y U S T) (fsubst_te Y U S t)
    | tm_app t1 t2  => tm_app (fsubst_te Y U S t1) (fsubst_te Y U S t2)
    | tm_tabs A T t => tm_tabs A (fsubst_tt Y U S T) (fsubst_te Y U S t)
    | tm_tapp t T   => tm_tapp (fsubst_te Y U S t) (fsubst_tt Y U S T)
  end.

(** ** Term parameters
 The function [fsubst_ee], defined below, replaces a type parameter 
 with a term. Note that [fsubst_tt] replaces a term parameter with 
 a term only when both a parameter and its annotated type are matched. 
 Locally named representation makes the [tm_abs] case simple. *)
Fixpoint fsubst_ee (y : fvar) (U:typ) (u t: tm) {struct t} : tm :=
  match t with
    | tm_lvar a     => tm_lvar a
    | tm_fvar x T   => if fvar_dec (x, T) (y, U) then u else tm_fvar x T
    | tm_abs a T t  => tm_abs a T (fsubst_ee y U u t)
    | tm_app t1 t2  => tm_app (fsubst_ee y U u t1) (fsubst_ee y U u t2)
    | tm_tabs A T t => tm_tabs A T (fsubst_ee y U u t)
    | tm_tapp t T   => tm_tapp (fsubst_ee y U u t) T
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
 if [lclosed_t emptyset T] holds. *)
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
| lclosed_t_all   : forall I1 I2 A T U,
  lclosed_t I1 T ->
  lclosed_t I2 U -> 
  lclosed_t (I1 ++ (remove eq_nat_dec A I2)) (typ_all A T U).

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
| lclosed_e_abs  : forall I1 I2 i a T t, 
  lclosed_t I1 T ->
  lclosed_e I2 i t ->
  lclosed_e (I1 ++ I2) (remove eq_nat_dec a i) (tm_abs a T t) 
| lclosed_e_app  : forall I1 I2 i1 i2 t1 t2,
  lclosed_e I1 i1 t1 ->
  lclosed_e I2 i2 t2 ->
  lclosed_e (I1 ++ I2) (i1 ++ i2) (tm_app t1 t2)
| lclosed_e_tabs : forall I1 I2 i A T t,
  lclosed_t I1 T ->
  lclosed_e I2 i t ->
  lclosed_e (I1 ++ (remove eq_nat_dec A I2)) i (tm_tabs A T t)
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
 with typing contexts. Note the use of the cofinite-quantification style 
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
| sub_all        : forall T1 T2 U1 U2 A B L,
  sub U1 T1 ->
  (forall X, ~ In X L -> sub ({A ~> X ^^ U1} T2) ({B ~> X ^^ U1} U2)) ->
  sub (typ_all A T1 T2) (typ_all B U1 U2). 

Hint Constructors sub.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Typing relation 
 It is also straightforward to define the typing relation. The [typing_fvar] 
 case requires the annotate type [T] to be locally closed, which implies the
 typing relation holds only for locally closed types (We will formally prove 
 this later). Note the use of the cofinite-quantification style in the 
 [typing_abs] and [typing_tabs] cases. *)
Inductive typing : tm -> typ -> Prop :=
| typing_fvar : forall x T,
  lclosed_t emptyset T ->
  typing (x ** T) T
| typing_abs  : forall a T U t L,
  lclosed_t emptyset T ->
  (forall x, ~ In x L -> typing ({a ::~> x ** T} t) U) ->
  typing (tm_abs a T t) (T --> U)
| typing_app  : forall t t' T U,
  typing t (T --> U) ->
  typing t' T ->
  typing (tm_app t t') U
| typing_tabs : forall A T t B U L,
  lclosed_t emptyset T ->
  (forall X, ~ In X L -> typing ({A :~> X ^^ T} t) ({B ~> X ^^ T} U)) ->
  typing (tm_tabs A T t) (typ_all B T U)
| typing_tapp : forall t A T U S,
  typing t (typ_all A U S) ->
  sub T U ->
  typing (tm_tapp t T) ({A ~> T} S)
| typing_sub  : forall t T U,
  typing t T ->
  sub T U ->
  typing t U.

Hint Constructors typing.
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
| red_tabs  : forall A T t U,
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
    | typ_ftvar _ _ => idtac
    | typ_arrow _ _ => idtac
    | typ_all _ _ _ => idtac
    | _ => fail
  end 
with filter_e e :=
  match e with
    | tm_lvar _ => idtac
    | tm_fvar _ _ => idtac
    | tm_abs _ _ _ => idtac
    | tm_app _ _ => idtac
    | tm_tabs _ _ _ => idtac
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
    exists (I1' ++ (remove eq_nat_dec A I2)); split; auto.
      rewrite list_remove_app; rewrite list_remove_repeat; rewrite Ha'; eauto.
    destruct (IHT1 _ _ _ _ H3) as [I1' [Ha Ha']].   
    destruct (IHT2 _ _ _ _ H5) as [I2' [Hb Hb']].
    exists (I1' ++ (remove eq_nat_dec n I2')); split; eauto.      
      rewrite list_remove_app; rewrite list_remove_twice.
      rewrite Ha'; rewrite Hb'; eauto.
Qed.

(** [lclosed_t] is stable under type variable substitution. *)
Lemma lclosed_t_subst_ltvar : forall T U I A,
  lclosed_t emptyset U ->
  lclosed_t I T ->
  lclosed_t (remove eq_nat_dec A I) ({A ~> U} T).
Proof.
  induction T; intros; inversion H0; subst; Simplify by eauto. 
    rewrite list_remove_app; eauto.
    rewrite list_remove_app; rewrite list_remove_repeat; eauto.
    rewrite list_remove_app; rewrite list_remove_twice; eauto.
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
Hint Resolve sym_eq list_remove_in : nochange.

(** Type variable substitution over types has no effect if they do not 
 include such a type variable. *)
Lemma subst_ltvar_nochange_t : forall I T,
  lclosed_t I T -> 
  forall A U, 
    ~ In A I -> {A ~> U} T = T.
Proof.
  induction 1; intros; 
    Simplify by (Destruct notIn by (f_equal; eauto with nochange)).
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
    | typ_top       => 0
    | typ_ltvar _   => 0
    | _ ^^ T        => S (synsize_t T)
    | T --> U       => S (synsize_t T + synsize_t U)
    | typ_all _ T U => S (synsize_t T + synsize_t U)
  end.

Lemma lem_subst_ftvar_nochange_t_idemp : forall T S,
  synsize_t S <= synsize_t T -> 
  forall X U, [(X, T) ~> U] S = S.
Proof.
  induction S; intros; Simplify by (f_equal; eauto with arith). 
    inversion e; subst; firstorder using le_Sn_n.
Qed.

(** We may swap parameter and variable substitutions. *)
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
  induction 1; intros; try solve [firstorder].
  unsimpl (emptyset ++ emptyset:list ltvar); firstorder.
  destruct (pick_fresh L) as [X Hfresh].
  destruct (H1 X Hfresh) as [Ha Hb].
  split.
    destruct (lclosed_t_ltvar_split _ _ _ _ Ha) as [I1 [Ha' Ha'']].
    replace (emptyset:list ltvar) with (emptyset ++ (remove eq_nat_dec A I1));
      firstorder.
    destruct (lclosed_t_ltvar_split _ _ _ _ Hb) as [I2 [Ha' Ha'']].
    replace (emptyset:list ltvar) with (emptyset ++ (remove eq_nat_dec B I2)); 
      firstorder.
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

Lemma sub_narrowing : forall T U,
  sub T U ->
  forall S S',
    sub_transitivity_on S ->
    sub S' S ->
    forall X,
      sub ([(X, S) ~> X ^^ S'] T)
          ([(X, S) ~> X ^^ S'] U).
Proof.
  induction 1; intros; try solve [Simplify by eauto].
  destruct (sub_lclosed_t H1) as [? ?].
  Simplify by eauto with subst_aux. 
  destruct (sub_lclosed_t H1) as [? ?].
  Simplify by eauto with subst_aux.
  Simplify by eauto.
    inversion e; subst; clear e.
    eapply H0; eauto.
    erewrite <- lem_subst_ftvar_nochange_t_idemp at 1; eauto.
  Simplify by eauto.
  constructor 5 with (X :: L); intros; Destruct notIn by eauto.
    destruct (sub_lclosed_t H3) as [? _].
    replace (X0 ^^ [ (X, S)~> X ^^ S']U1) 
      with ([ (X, S) ~> X ^^ S' ] X0 ^^ U1) by Simplify by congruence.
    repeat rewrite <- subst_ftvar_ltvar_t by eauto.
    apply H1; eauto.
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
    | typ_all _ T1 T2 => S (size_t T1 + size_t T2)
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
Lemma sub_trans_forall_aux : forall T U U1 U2 S A,
  (forall S, size_t S < size_t U -> sub_transitivity_on S) ->
  sub T U ->
  U = typ_all A U1 U2 ->
  sub U S ->
  sub T S.
Proof.
  intros until 2. 
  induction H0; intros; try discriminate; eauto.
  inversion H3; inversion H4; subst.
  constructor 1.
  destruct (pick_fresh L) as [X Hfresh].
  destruct (sub_lclosed_t H0) as [_ ?].
  destruct (sub_lclosed_t (H1 _ Hfresh)) as [H_T2 _].
  destruct (lclosed_t_ltvar_split _ _ _ _ H_T2) as [I [Ha Hb]].
  replace (emptyset:list ltvar) with (emptyset ++ (remove eq_nat_dec A0 I));
    eauto.
  set (L' := L ++ L0 ++ FV_tt T2 ++ FV_tt U2).
  econstructor 5 with L'.
    eapply (H U1); Simplify by eauto with arith.
    intros; unfold L' in H5; Destruct notIn by eauto.
  apply (H ({A ~> X ^^ U4} U2)); Simplify by eauto.
    rewrite size_t_nochange_ltvar; eauto with arith. 
  erewrite <- subst_seq_ftvar_ltvar_t with (T := T2) (X := X) by eauto. 
  erewrite <- subst_seq_ftvar_ltvar_t with (T := U2) (X := X) by eauto. 
  eapply sub_narrowing; eauto with arith.
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
    size_t S < size_t (typ_all n0 T1 T2) -> 
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
  destruct T; intros H' H; inversion H; subst; Simplify by eauto.
  assert (size_t T1 < n) by eauto with arith.  
  assert (size_t T2 < n) by eauto with arith.
  assert (I1 = emptyset) by firstorder using app_eq_nil.
  assert (I2 = emptyset) by firstorder using app_eq_nil.
  subst; eauto.
  set (L := FV_tt T1 ++ FV_tt T2).
  assert (I1 = emptyset) by firstorder using app_eq_nil; subst I1.
  constructor 5 with L. 
    apply IHn; eauto with arith.
    intros; apply IHn.
      rewrite size_t_nochange_ltvar; eauto with arith.
      replace (emptyset : list ltvar) with (remove eq_nat_dec n0 I2).
      eauto with subst_aux. 
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
    exists (remove eq_nat_dec a i); eauto using list_remove_repeat.
  inversion H; subst.
    forwards Ha : (IHt _ _ _ _ _ H6).
    destruct Ha as [i0 [Hb Hc]].
    exists (remove eq_nat_dec n i0).
    rewrite <- Hc; eauto using list_remove_twice.
  inversion H. 
    forwards Ha : (IHt1 _ _ _ _ _ H4); destruct Ha as [ia [? ?]].
    forwards Hb : (IHt2 _ _ _ _ _ H5); destruct Hb as [ib [? ?]].
    exists (ia ++ ib); split; eauto.
      rewrite <- H7; rewrite <- H9; eauto using list_remove_app.
  inversion H; subst.
    forwards Ha : (IHt _ _ _ _ _ H6); destruct Ha as [ia [? ?]].
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
    forwards Ha : (IHt _ _ _ _ _ H6); destruct Ha as [Ia [? ?]].
    forwards Hb : (lclosed_t_ltvar_split _ _ _ _ H4); destruct Hb as [Ib [? ?]].
    subst; exists (Ib ++ Ia); eauto using list_remove_app.
  inversion H; subst.
    forwards Ha : (IHt1 _ _ _ _ _ H4); destruct Ha as [Ia [? ?]].
    forwards Hb : (IHt2 _ _ _ _ _ H5); destruct Hb as [Ib [? ?]].
    subst; exists (Ia ++ Ib); eauto using list_remove_app.
  inversion H; subst.
    destruct (lclosed_t_ltvar_split _ _ _ _ H4) as [I0 [? ?]]; subst.
    exists (I0 ++ (remove eq_nat_dec A I2)); split; eauto.
      rewrite list_remove_app; rewrite list_remove_repeat; eauto.
  inversion H; subst.
    destruct (lclosed_t_ltvar_split _ _ _ _ H4) as [Ia [? ?]].
    destruct (IHt _ _ _ _ _ H6) as [Ib [? ?]].
    subst; exists (Ia ++ (remove eq_nat_dec n Ib)); split; eauto.
      rewrite list_remove_app; rewrite list_remove_twice; eauto.
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
Qed.

Lemma subst_ltvar_nochange_e : forall t I i A T,
  lclosed_e I i t ->
  ~ In A I ->
  {A :~> T} t = t.
Proof.
  induction t; intros; inversion H; subst;
    Destruct notIn by Simplify by (f_equal; eauto with nochange).
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

(** We may swap variable and parameter substitutions. *) 
Lemma subst_fvar_lvar_e : forall t u a x T y U I,
  lclosed_e I emptyset u -> 
  x <> y -> 
  [(y, U) ::~> u]({a ::~> x ** T} t) = {a ::~> x ** T}([(y, U) ::~> u] t).
Proof.
  induction t; intros; 
    Simplify by (f_equal; eauto with nochange; congruence). 
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

(** [FV_te] and [FV_ee] are stable under substitutions. *)
Lemma FV_te_nochange_lvar : forall t a x y T,
  FV_te ({a ::~> x ** T} t) = FV_te ({a ::~> y ** T} t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto).
Qed.

Hint Resolve FV_te_nochange_lvar : nochange.

Lemma FV_ee_nochange_ltvar : forall A T t, 
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
  destruct (pick_fresh L) as [x Hfresh].
  destruct (H1 _ Hfresh) as [Ha Hb].
  destruct (lclosed_e_lvar_split _ _ _ _ Ha) as [I [? ?]].
  split.
    rewrite <- emptyset_plus at 1.
    pattern (emptyset: list ltvar) at 3; 
      replace (emptyset:list ltvar) with (remove eq_nat_dec a I); eauto.
    unsimpl (emptyset ++ emptyset : list ltvar); eauto.
  destruct IHtyping1; destruct IHtyping2.
  split. 
    rewrite <- emptyset_plus; eauto.
    inversion H2; subst.
    destruct (app_eq_nil _ _ H5) as [? ?]; subst; eauto.
  destruct (pick_fresh L) as [X Hfresh].
  destruct (H1 _ Hfresh) as [? ?].
  destruct (lclosed_e_ltvar_split _ _ _ _ H2) as [Ia [? ?]].
  destruct (lclosed_t_ltvar_split _ _ _ _ H3) as [Ib [? ?]].
  split.
    pattern (emptyset:list ltvar) at 1; 
      replace (emptyset:list ltvar) with (emptyset ++ remove eq_nat_dec A Ia); 
        eauto. 
    pattern (emptyset:list ltvar) at 1; 
      replace (emptyset:list ltvar) with (emptyset ++ remove eq_nat_dec B Ib); 
        eauto.
  destruct IHtyping.
  destruct (sub_lclosed_t H0) as [? ?].
  split.
    rewrite <- emptyset_plus at 1; eauto.
    inversion H2; subst.
    destruct (app_eq_nil _ _ H5) as [? ?]; subst.
    simpl; eauto using lclosed_t_subst_ltvar.
  destruct (sub_lclosed_t H0).
  destruct IHtyping; eauto.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Substitution lemma 
 This section presents the main result: [typing] is stable under type
 and term parameter substitution.  

 *** Type parameter substitution lemma
 We first prove Lemma [typing_subst_ftvar] which shows that [typing] 
 is stable under type parameter substitution. The proof proceeds by 
 induction on the structure of [typing] proofs. *)
Lemma sub_subst_ftvar : forall T U,
  sub T U ->
  forall X S S', 
    sub S' S -> 
    sub ([(X, S) ~> S'] T) ([(X, S) ~> S'] U).
Proof.
  induction 1; intros ? ? ? Hsub; destruct (sub_lclosed_t Hsub);
    Simplify by eauto with subst_aux.
  eauto using sub_reflexivity_aux with arith.
  inversion e; subst.
  eapply sub_transitivity with (U := [ (X0, S) ~> S' ] S); eauto.
  rewrite lem_subst_ftvar_nochange_t_idemp; eauto with arith.
  constructor 5 with (L := X :: L); eauto.
    intros; Destruct notIn by eauto.
    replace (X0 ^^ ([ (X, S)~> S']U1)) 
      with ([ (X, S) ~> S' ] X0 ^^ U1) by Simplify by congruence.
    repeat (rewrite <- subst_ftvar_ltvar_t by eauto).
    eapply H1; eauto.
Qed.

Hint Resolve sub_subst_ftvar : subst_aux.

Lemma typing_sub_subst_ftvar : forall t X T U U',
  typing t T -> 
  sub U' U -> 
  typing ([(X, U) :~> U'] t) ([(X, U) ~> U'] T).
Proof.
  induction 1; intros Hsub; destruct (sub_lclosed_t Hsub); 
    Simplify by eauto with subst_aux.
  constructor 2 with L; eauto with subst_aux.
    intros; Destruct notIn by eauto.
    replace ( x ** ([ (X, U)~> U']T) ) 
      with ( [ (X, U) :~> U' ] x **  T ) by Simplify by congruence.
    rewrite <- subst_ftvar_lvar_e.    
    eapply H1; eauto.
  constructor 4 with (X :: L); eauto with subst_aux.
    intros; Destruct notIn by eauto.
    replace ( X0 ^^ ([ (X, U)~> U']T) )
      with ( [ (X, U) ~> U' ] X0 ^^ T ) by Simplify by congruence.
    rewrite <- subst_ftvar_ltvar_e by eauto.
    rewrite <- subst_ftvar_ltvar_t by eauto.
    apply H1; eauto.
  rewrite subst_ftvar_ltvar_t by assumption.
  constructor 5 with (U := [ (X, U) ~> U' ] U0); eauto with subst_aux.
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
 the structure of [typing] proofs. *)
Lemma typing_subst_fvar : forall t T u x U, 
  typing t T -> 
  typing u U -> 
  typing ([(x, U) ::~> u] t) T.
Proof.
  induction 1; intros; Simplify by eauto.
  inversion e; subst; eauto.
  constructor 2 with (x :: L); eauto.
    intros; Destruct notIn by eauto.
    destruct (typing_lclosed_et H2) as [? _].
    erewrite <- subst_fvar_lvar_e by eauto.
    apply H1; eauto.
  constructor 4 with L; eauto.
    intros; Destruct notIn by eauto.
    destruct (typing_lclosed_et H2) as [? _].    
    rewrite subst_ltvar_fvar_e by eauto.
    apply H1; eauto.
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
Lemma app_red_preservation : forall t0 T a U0 U1 U2 t u,
  typing t0 T -> 
  t0 = tm_abs a U0 t ->
  sub T (U1 --> U2) -> 
  typing u U1 ->
  typing ({a ::~> u} t) U2.
Proof.
  induction 1; intros He0 Hsub He'; inversion He0; subst.
  inversion Hsub; subst.
    set (L' := L ++ FV_ee t).
    destruct (pick_fresh L') as [x Hfresh]. 
    unfold L' in Hfresh; Destruct notIn by eauto.
    eapply typing_subst_lvar with (x := x); eauto.
    eapply IHtyping; eauto using sub_transitivity.
Qed.

Lemma tapp_red_preservation : forall t0 T0 A B T t U U1 U2,
  typing t0 T0
  -> t0 = tm_tabs A T t
  -> sub T0 (typ_all B U1 U2)
  -> sub U U1
  -> typing ({A :~> U} t) ({B ~> U} U2).
Proof.
  induction 1; simpl; intros He HsubD HsubA; inversion He; subst.  
    inversion HsubD; subst.
    set (L' := FV_te t ++ FV_tt U2 ++ FV_tt U0 ++ L ++ L0).
    destruct (pick_fresh L') as [X Hfresh].
    unfold L' in Hfresh; Destruct notIn by eauto.
    constructor 6 with (T := {B0 ~> U} U0).
      eapply typing_subst_ltvar with (X := X); Destruct notIn by eauto.
        eauto using sub_transitivity.
      erewrite <- subst_seq_ftvar_ltvar_t with (T := U0) (X := X) by eauto.
      erewrite <- subst_seq_ftvar_ltvar_t with (T := U2) (X := X) by eauto.    
      eapply sub_subst_ftvar; eauto.
    eauto using sub_transitivity.
Qed.

Lemma preservation_t : forall t T, 
  typing t T -> 
  forall u, red t u -> typing u T.
Proof.
  induction 1; intros u Ha; inversion Ha; subst; eauto.
  destruct (typing_lclosed_et H) as [_ Hclosed_t].
  inversion Hclosed_t.
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

Lemma abs_typing_form : forall t a T0 t0 S, 
  typing t S
  -> t = tm_abs a T0 t0
  -> S = typ_top \/ exists S0 S1, S = S0 --> S1.
Proof.
  intros; induction H; try congruence.
  right; exists T U; auto.
  intuition.
    left; subst; inversion H1; auto.
    destruct H3 as [S0 [S1 Ha]]; subst.
    eauto using abs_subtype_form.
Qed.

Lemma tabs_subtype_form : forall A T1 T2 S,
  sub (typ_all A T1 T2) S
  -> S = typ_top \/ exists B S1 S2, S = typ_all B S1 S2.
Proof.
  intros; inversion H; auto.
  right; exists B U1 U2; auto.
Qed.

Lemma tabs_typing_form : forall t A T0 t0 S, 
  typing t S
  -> t = tm_tabs A T0 t0
  -> S = typ_top \/ exists A0 S0 S1, S = typ_all A0 S0 S1.
Proof.
  intros; induction H; try congruence.
  right; exists B T U; auto.
  intuition.
    left; subst; inversion H1; auto.
    destruct H3 as [A0 [S0 [S1 Ha]]]; subst.
    eauto using tabs_subtype_form.
Qed.

(** We then show that there are canonical values for arrow and all types *)
Lemma canonical_form_abs : forall t T U,
  value t 
  -> typing t (T --> U)
  -> exists a T0 t0, t = tm_abs a T0 t0.
Proof.
  induction 1; simpl; intros; eauto.
  inversion H. 
  assert (tm_tabs A T0 t = tm_tabs A T0 t); auto.
  destruct (tabs_typing_form H0 H4).
    subst; inversion H1.
    destruct H5 as [A0 [S0 [S1 Hb]]]; subst.
    inversion H1.
Qed.

Lemma canonical_form_tabs : forall t A T U,
  value t
  -> typing t (typ_all A T U)
  -> exists A0 T0 t0, t = tm_tabs A0 T0 t0.
Proof.
  induction 1; simpl; intros; eauto.
  inversion H. 
  assert (tm_abs a T0 t = tm_abs a T0 t); auto.
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
      destruct (canonical_form_abs H3 H) as [a0 [T0 [t0 ?]]]; subst.
      right; eauto.
      destruct H4 as [t'0 ?].
      right; exists (tm_app t t'0); auto.
    destruct H3 as [t'' ?].
    right; exists (tm_app t'' t'); auto.
  destruct (IHtyping Hve).
    destruct (canonical_form_tabs H1 H) as [A0 [T0 [t0 ?]]]; subst.
    right; eauto.
    destruct H1 as [t'0 ?].
    right; exists (tm_tapp t'0 T); auto.
Qed.
(* *************************************************************** *)
