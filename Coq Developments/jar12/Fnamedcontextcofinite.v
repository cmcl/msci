(** This file presents a cofinite-quantification style mechanization of System 
 Fsub with contexts using locally named representation. 
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
 paramertes bound in a typing context. *)
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
(** ** Substitution 
 We refer to an operation on typing contexts that replaces all the 
 occurrence of a specific parameter in the type of each typing binding 
 with a type as "substitution".

 For example, substituting [X] into [Y ^^] on [[X ~<: Y ^^; Y ~<: X ^^]] 
 results in [[X ~<: Y ^^; Y ~<: Y ^^]]. 

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
 contexts. Note the use of the cofinite-quantification style in the 
 [sub_all] case. *)
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
| sub_all        : forall Gamma T1 T2 U1 U2 A B L,
  sub Gamma U1 T1 ->
  (forall X, ~ In X L -> 
    sub (X ~<: U1 :: Gamma) ({ A ~> X ^^ } T2) ({ B ~> X ^^ } U2)) ->
  sub Gamma (typ_all A T1 T2) (typ_all B U1 U2). 

Hint Constructors sub.
(* *************************************************************** *)

(* *************************************************************** *)
(** * Typing relation 
 It is also straightforward to define the typing relation. The 
 [typing_fvar] case requires typing contexts to be well-formed,
 which implies that the typing relation holds only for well-formed 
 typing contexts. The [typing_fvar] case also requires term binding
 [x ~: T] to be in a well-formed typing context, which implies the
 typing relation holds only for locally closed types (We will formally 
 prove this later). Note the use of the cofinite-quantification style 
 in the [typing_abs] and [typing_tabs] cases. *)
Inductive typing : ctxt -> tm -> typ -> Prop :=
| typing_fvar : forall Gamma x T,
  ctxt_okay Gamma ->
  In (x ~: T) Gamma ->
  typing Gamma (x **) T
| typing_abs  : forall Gamma a T U t L,
  lclosed_t Gamma emptyset T ->
  (forall x, ~ In x L ->
    typing (x ~: T :: Gamma) ({a ::~> x **} t) U) ->
  typing Gamma (tm_abs a T t) (T --> U)
| typing_app  : forall Gamma t t' T U,
  typing Gamma t (T --> U) -> 
  typing Gamma t' T -> 
  typing Gamma (tm_app t t') U
| typing_tabs : forall Gamma A B t T U L,
  lclosed_t Gamma emptyset T -> 
  (forall X, ~ In X L ->
    typing (X ~<: T :: Gamma) ({A :~> X ^^} t) ({B ~> X ^^} U)) -> 
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
    | ctxt_ftvar_subst_map => idtac
    | _ => fail
  end
with filter_subst_b S :=
  match S with
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

Lemma ctxt_okay_unique_ftvar : forall Gamma X T,
  ctxt_okay (X ~<: T :: Gamma) ->
  ~ In X (FV_tc Gamma).
Proof.
  induction Gamma; intros; Simplify by eauto.
  destruct a; inversion H; inversion H3;
    subst; Simplify by (Destruct notIn by eauto with incl_param).
Qed.

(** Every parameter in [Gamma] is distinct if [ctxt_okay Gamma] holds. *)
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
  induction 1; intros; Simplify by Destruct notIn by eauto.
  intuition; eauto.
  unsimpl (emptyset ++ emptyset:list ltvar); intuition; eauto.
  set (L' := FV_tt T2 ++ FV_tt U2 ++ L).
  destruct (pick_fresh L') as [X Hfresh].
  unfold L' in Hfresh.
  destruct H1 with (X := X) as [HT HU]; Destruct notIn by (intuition; eauto).  
    destruct (lclosed_t_ltvar_split _ _ H2 HT) as [I1 [Ha' Ha'']].
    replace (emptyset : list ltvar) with (emptyset ++ remove eq_nat_dec A I1);
      eauto.
    destruct (lclosed_t_ltvar_split _ _ H4 HU) as [I2 [Ha' Ha'']].
    replace (emptyset:list ltvar) with (emptyset ++ remove eq_nat_dec B I2);
      eauto.
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
Lemma permuting_sub : forall Gamma0 T U,
  sub Gamma0 T U ->
  forall Gamma Delta bind bind',
  Gamma0 = (Delta ++ (bind :: bind' :: Gamma)) ->
  ctxt_okay (Delta ++ (bind' :: bind :: Gamma)) ->
  sub (Delta ++ (bind' :: bind :: Gamma)) T U.
Proof.
  induction 1; intros; subst; eauto with permuting_aux.
  set (L' := dom_tc (Delta ++ bind' :: bind :: Gamma0) ++ L).
  constructor 5 with (L := L'); eauto.
    unfold L'; destruct (sub_lclosed_t H) as [? ?].
    intros; rewrite list_cons_cons_move_app.
    eapply H1; Destruct notIn by eauto.
      rewrite <- list_cons_cons_move_app.
      econstructor; eauto with permuting_aux.
Qed.

Hint Resolve permuting_sub : permuting_aux.

(** *** Weakening 
 This section proves Lemma [weakening_sub_cons] and [weakening_sub_concat]
 which state the weakening property of [sub]. 
 
 We first prove Lemma [weakening_sub_cons] by induction on the structure of
 [sub] proofs. *)
Lemma weakening_sub_cons : forall Gamma T U,
  sub Gamma T U ->
  forall bind,
    ctxt_okay (bind :: Gamma) ->
    sub (bind :: Gamma) T U.
Proof.
  induction 1; intros; eauto.  
  assert (incl (dom_tc Gamma) (dom_tc (bind :: Gamma))) 
    by (destruct bind; Simplify by eauto with v62).
  eauto using lclosed_t_incl.
  assert (incl (dom_tc Gamma) (dom_tc (bind :: Gamma))) 
    by (destruct bind; Simplify by eauto with v62).
  eauto using lclosed_t_incl.
  econstructor; Destruct In by eauto.
  assert (incl (dom_tc Gamma) (dom_tc (bind :: Gamma))) 
    by (destruct bind; Simplify by eauto with v62).
  set (L' := dom_tc (bind :: Gamma) ++ L).
  constructor 5 with (L := L'); eauto.
    unfold L'; intros; Destruct notIn by eauto.
    destruct (sub_lclosed_t H).
    assert (ctxt_okay (bind :: X ~<: U1 :: Gamma)).
      destruct bind; inversion H2; subst.
      econstructor; Simplify by Destruct notIn by eauto.
        eapply lclosed_t_incl; Simplify by eauto with v62.
      econstructor; Simplify by Destruct notIn by eauto.
        eapply lclosed_t_incl; Simplify by eauto with v62.
    unsimpl (emptyset ++ X ~<: U1 :: bind :: Gamma).
    apply permuting_sub 
      with (Gamma0 := emptyset ++ bind :: X ~<: U1 :: Gamma); simpl; eauto.
      econstructor; eauto. 
      eauto using lclosed_t_incl.
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

Hint Resolve weakening_sub_cons weakening_sub_concat : weakening_aux.
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

Lemma sub_narrowing_aux : forall Gamma0 T U,
  sub Gamma0 T U ->
  forall Gamma Gamma' X S S',
    Gamma0 = Gamma' ++ X ~<: S :: Gamma ->
    sub_transitivity_on S ->
    sub Gamma S' S ->
    sub (Gamma' ++ X ~<: S' :: Gamma) T U.
Proof.
  induction 1; intros; subst; eauto.
  constructor 1.
    destruct (sub_lclosed_t H3) as [? ?]; eauto with narrowing_aux.
    apply lclosed_t_incl with (Gamma := Gamma' ++ X ~<: S :: Gamma0);
      Simplify by (eauto with v62).
  constructor 2.
    destruct (sub_lclosed_t H3) as [? ?]; eauto with narrowing_aux.
    apply lclosed_t_incl with (Gamma := Gamma' ++ X0 ~<: S :: Gamma0);
      Simplify by (eauto with v62).
  destruct (X == X0); subst.
    assert (T = S).
      forwards Hokay : sub_ctxt_okay H0.
      eapply ctxt_okay_unique_ftvar_bind
        with (X := X0) (Gamma := Gamma' ++ X0 ~<: S :: Gamma0); eauto.
        Destruct In by eauto.
      subst.      
    constructor 3 with (T := S'); auto with v62.
      apply H2; eauto.
        rewrite list_cons_move_app.
        eapply weakening_sub_concat; eauto.
          forwards Hokay : (sub_ctxt_okay H0).
          destruct (sub_lclosed_t H3) as [? ?].
          rewrite <- list_cons_move_app; eauto with narrowing_aux.
    constructor 3 with (T := T); eauto with v62.
      Destruct In by eauto.
        inversion H0; congruence.
  set (L' := L).
  destruct (pick_fresh L') as [Z HfreshL].
  constructor 5 with L'; Destruct notIn by eauto.
    intros; rewrite list_cons_cons_move_app.
    eapply H1; simpl; eauto.
Qed.

Lemma sub_narrowing : forall T U X S Gamma Gamma' ,
  sub (Gamma' ++ X ~<: S :: Gamma) T U ->
  forall S',
    sub_transitivity_on S ->
    sub Gamma S' S ->
      sub (Gamma' ++ X ~<: S' :: Gamma) T U.
Proof.
  intros; eauto using sub_narrowing_aux.
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
  induction T; intros; Simplify by (simpl; eauto).
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
  destruct (sub_lclosed_t H1_).
  destruct (sub_lclosed_t H1_0). 
  inversion H2; subst; clear H2.
  inversion H1; subst.
  econstructor; eauto.
    unsimpl (emptyset ++ emptyset:list ltvar); eauto. 
  econstructor; eauto.  
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
  inversion H3; inversion H4; subst; clear H3.
  econstructor; eauto.
    set (L' := FV_tt T2 ++ L).
    destruct (pick_fresh L') as [X Hfresh].
    unfold L' in Hfresh; Destruct notIn by eauto.
    destruct (sub_lclosed_t H0).
    destruct (sub_lclosed_t (H1 _ H6)).
    destruct (lclosed_t_ltvar_split _ _ H3 H10)as [I [Ha Hb]].
    replace (emptyset:list ltvar) with (emptyset ++ (remove eq_nat_dec A0 I));
      eauto.
  constructor 5 with (L := L ++ L0).
    apply H with (S' := U1); simpl; eauto with arith.
    intros; Destruct notIn by eauto.
    apply (H ({A ~> X ^^} U2)); eauto.
      rewrite size_t_nochange_ltvar; simpl; eauto with arith.
      unsimpl (emptyset ++ X ~<: U4 :: Gamma).
      eapply sub_narrowing with (S := U1); simpl; eauto.  
        apply H; simpl; eauto with arith.
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
  assert (I1 = emptyset) by firstorder using app_eq_nil; subst.
  assert (remove eq_nat_dec n0 I2 = emptyset) by firstorder using app_eq_nil.
  constructor 5 with (L := L); Destruct notIn by eauto.
    apply IHn; eauto with arith.
    intros; unfold L in H2; Destruct notIn by apply IHn.
      rewrite size_t_nochange_ltvar; eauto with arith.
      econstructor; Destruct notIn by eauto.
      replace (emptyset : list ltvar) with (remove eq_nat_dec n0 I2).
      eapply lclosed_t_subst_ltvar; eauto with v62.
        eapply lclosed_t_incl with (Gamma := Gamma);
          Simplify by eauto with v62.
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
  Gamma0 = ((X ~<: T) :: Gamma) ->
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
  Gamma0 = ((x ~: T) :: Gamma) ->
  lclosed_e Gamma I i t.
Proof.
  induction 2; intros; subst; auto.
  Simplify by (firstorder; congruence).
  constructor 3; eauto.
    replace Gamma with (emptyset ++ Gamma); eauto.
    eapply strengthen_lclosed_t_fvar_app_aux; Simplify by (simpl; eauto).
  Simplify by (Destruct notIn by eauto).
  constructor 5; eauto.
  unsimpl (emptyset ++ Gamma).
  eapply strengthen_lclosed_t_fvar_app_aux;  
    Simplify by (Destruct notIn by (simpl; eauto)).
  constructor 6; eauto.
  unsimpl (emptyset ++ Gamma).
  eapply strengthen_lclosed_t_fvar_app_aux;
    Simplify by (Destruct notIn by (simpl; eauto)).
Qed.

Lemma strengthen_lclosed_e_ftvar_aux : forall Gamma0 Gamma X T I i t,
  ~ In X (FV_te t) ->
  lclosed_e Gamma0 I i t ->
  Gamma0 = ((X ~<: T) :: Gamma) ->
  lclosed_e Gamma I i t.
Proof.
  induction 2; intros; subst; 
    Simplify by (Destruct notIn by eauto with strengthen_aux).
Qed.

Hint Resolve strengthen_lclosed_e_fvar_aux : strengthen_aux.
Hint Resolve strengthen_lclosed_e_ftvar_aux : strengthen_aux.
  
Lemma strengthen_ctxt_okay : forall Gamma Delta Gamma0 x T ,
  ctxt_okay Gamma0 ->
  Gamma0 = Gamma ++ (x ~: T) :: Delta ->
  ctxt_okay (Gamma ++ Delta).
Proof.
  induction Gamma; intros; subst; inversion H; eauto.
    simpl; econstructor; 
      Simplify by (Destruct notIn by eauto with strengthen_aux).
    simpl; econstructor; 
      Simplify by (Destruct notIn by eauto with strengthen_aux).
Qed.

Hint Resolve strengthen_ctxt_okay : strengthen_aux.

Lemma strengthen_sub : forall Gamma0 U U',
  sub Gamma0 U U' ->
  forall Gamma x T Delta,
    Gamma0 = Gamma ++ x ~: T :: Delta ->
    sub (Gamma ++ Delta) U U'.
Proof.
  induction 1; intros; subst; eauto with strengthen_aux.
  econstructor; Destruct In by (try discriminate; eauto with arith).
  set (L' := L).
  econstructor 5 with L'; eauto. 
    intros; unfold L' in H2.
    rewrite list_cons_cons_move_app.
    eapply H1; simpl; eauto.
Qed.

Hint Resolve strengthen_sub : strengthen_aux.
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

Lemma subst_ltvar_fvar_e : forall t A X x t' Gamma I,
  lclosed_e Gamma emptyset I t' ->
  {A :~> X ^^}([x ::~> t'] t) = [x ::~> t']({A :~> X ^^} t).
Proof.
  induction t; intros; Simplify by (f_equal; eauto with nochange). 
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

(* Lemma FV_te_rename_fvar_nochange : forall t x y, *)
(*   FV_te ([x ::~> y **] t) = FV_te t. *)
(* Proof. *)
(*   induction t; intros; Simplify by (f_equal; eauto).  *)
(* Qed. *)

(* Hint Resolve FV_te_rename_fvar_nochange : nochange. *)

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
    destruct (pick_fresh L) as [X Hfresh].
    forwards Hokay : (H1 _ Hfresh).
    inversion Hokay; eauto.
    destruct (pick_fresh L) as [X Hfresh].
    forwards Hokay : (H1 _ Hfresh).
    inversion Hokay; eauto.
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
      destruct (pick_fresh L) as [x Hfresh].
      forwards Hclosed : H1 Hfresh.
      eapply strengthen_lclosed_t_fvar_app_aux; simpl; eauto.
    inversion IHtyping1; subst; eauto with v62.
      destruct (app_eq_nil _ _ H1) as [? ?]; subst; eauto.
    set (L' := FV_tt U ++ L).
    destruct (pick_fresh L') as [X Hfresh].
    unfold L' in Hfresh; Destruct notIn by eauto.
    forwards Hclosed : H1 H3.
    destruct (lclosed_t_ltvar_split _ _ H2 Hclosed) as [I [? ?]].
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
  set (L' := FV_ee t ++ L).
  destruct (pick_fresh L') as [x Hfresh].
  unfold L' in Hfresh; Destruct notIn by eauto.
  forwards Hclosed : H1 H3.
  destruct (lclosed_e_lvar_split _ _ H2 Hclosed) as [i [? ?]].
  rewrite <- H5 at 2; rewrite <- emptyset_plus; eauto.
  rewrite <- emptyset_plus; eauto.
  Destruct notIn by idtac.
  set (L' := FV_te t ++ L).
  destruct (pick_fresh L') as [x Hfresh].
  unfold L' in Hfresh; Destruct notIn by eauto.
  forwards Hclosed : H1 H3.
  destruct (lclosed_e_ltvar_split _ _  H2 Hclosed) as [I [? Hsplit]].
  rewrite <- Hsplit at 1.
  unsimpl (emptyset ++ remove eq_nat_dec A I); eauto.
  destruct (sub_lclosed_t H0) as [? ?].
  rewrite <- emptyset_plus; eauto.
Qed.
(* *************************************************************** *)

(* *************************************************************** *)
(** ** Structural properties of [typing]
 *** Permutation 
 This section proves Lemma [permuting_typingLH] which states the permutation 
 property of [typing]. *)
Lemma permuting_typing : forall Gamma0 t T ,
  typing Gamma0 t T ->
  forall Gamma bind bind' Delta,
    Gamma0 = Gamma ++ bind :: bind' :: Delta ->
    ctxt_okay (Gamma ++ bind' :: bind :: Delta) ->
    typing (Gamma ++ bind' :: bind :: Delta) t T.
Proof.
  induction 1; intros; subst; eauto with permuting_aux.
  set (L' := dom_ec Gamma0 ++ dom_ec (bind' :: bind :: Delta) ++ 
             FV_ee t ++ L).
  constructor 2 with (L := L'); 
    Simplify by (Destruct notIn by eauto with permuting_aux).
    intros; unfold L' in H2; Destruct notIn by eauto.
    assert (  ctxt_okay ((x ~: T :: Gamma0) ++ bind' :: bind :: Delta ) ).
      rewrite <- list_cons_cons_move_app.
      econstructor; Simplify by Destruct notIn by eauto with permuting_aux.
    rewrite list_cons_cons_move_app; eauto.
  set (L' := FV_tc Gamma0 ++ FV_tc (bind' :: bind :: Delta) ++ 
             FV_te t ++ FV_tt U ++ L).
  constructor 4 with (L := L'); 
    Simplify by (Destruct notIn by (eauto with permuting_aux)).
    intros; unfold L' in H2; Destruct notIn by eauto.
    assert ( ctxt_okay ((X ~<: T :: Gamma0) ++ bind' :: bind :: Delta) ).
      rewrite <- list_cons_cons_move_app.
      econstructor; Simplify by Destruct notIn by eauto with permuting_aux.
    rewrite list_cons_cons_move_app; eauto.
Qed.
 
Hint Resolve permuting_typing : permuting_aux.

(** *** Weakening 
 This section proves Lemma [weakening_typing] which states the weakening 
 property of [typing]. The proof proceeds by induction on the structure 
 of [typing] proofs. (See Lemma [weakening_typingLH] for details) *)
Lemma weakening_typing : forall Gamma t T,
    typing Gamma t T -> 
    forall bind,
      ctxt_okay (bind :: Gamma) ->
      typing (bind :: Gamma) t T.
Proof.
  induction 1; intros; eauto with weakening_aux v62.
  set (L' := dom_ec Gamma ++ dom_ec (bind :: Gamma) ++ 
             FV_ee t ++ L).
  assert (lclosed_t (bind :: Gamma) emptyset T).
    eapply lclosed_t_incl with (Gamma := Gamma); eauto.
      destruct bind; Simplify by eauto with v62.
  constructor 2 with L'; Simplify by (Destruct notIn by eauto).
    intros; unfold L' in H4; Destruct notIn by eauto.
    assert ( ctxt_okay (bind :: x ~: T :: Gamma) ).
      destruct bind; eauto; inversion H2; subst; econstructor; 
          Simplify by (Destruct notIn by eauto); 
          eapply lclosed_t_incl with (Gamma := Gamma); 
            Simplify by eauto with v62.
    unsimpl (emptyset ++ x ~: T :: bind :: Gamma).
    eapply permuting_typing 
      with (Gamma0 := emptyset ++ bind :: x ~: T :: Gamma); simpl; eauto.
  set (L' := dom_tc Gamma ++ FV_tc (bind :: Gamma) ++ 
             FV_te t ++ FV_tt U ++ FV_tt T ++ L).
  assert (lclosed_t (bind :: Gamma) emptyset T).
    eapply lclosed_t_incl with (Gamma := Gamma); eauto.
      destruct bind; Simplify by eauto with v62.
  constructor 4 with L'; Simplify by (Destruct notIn by eauto).
    intros; unfold L' in H4; Destruct notIn by eauto.
    assert (  ctxt_okay (bind :: X ~<: T :: Gamma) ).
      destruct bind; eauto; inversion H2; subst; econstructor; 
          Simplify by (Destruct notIn by eauto); 
          eapply lclosed_t_incl with (Gamma := Gamma); 
            Simplify by eauto with v62.   
    unsimpl (emptyset ++ X ~<: T :: bind :: Gamma).
    eapply permuting_typing
      with (Gamma0 := emptyset ++ bind :: X ~<: T :: Gamma); simpl; eauto.
Qed.

Hint Resolve weakening_typing : weakening_aux.
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
 induction on the structure of [typing] proofs. *)
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

Lemma sub_subst_ftvar : forall Gamma0 U' U,
  sub Gamma0 U' U -> 
  forall Gamma X T Delta R,
    Gamma0 = Gamma ++ (X ~<: T :: Delta) -> 
    sub Delta R T -> 
    sub (([X ==> R] Gamma) ++ Delta) ([X ~> R] U') ([X ~> R] U).
Proof.
  induction 1; intros; subst; Simplify by eauto with subst_aux.
  assert ( lclosed_t (([X0 ==> R] Gamma0) ++ Delta) emptyset R).
    destruct (sub_lclosed_t H2) as [? _].
    eapply lclosed_t_incl with (Gamma := Delta); Simplify by eauto with v62.
  eapply sub_reflexivity_aux; eauto with subst_aux.
  assert ( lclosed_t (([X0 ==> R]Gamma0) ++ Delta) emptyset (X ^^) ).
    destruct (sub_lclosed_t H2) as [? _].
    replace (X ^^) with ([ X0 ~> R ] X ^^ ) by Simplify by eauto.  
    eapply lclosed_t_subst_ftvar_remove; eauto.
  eapply sub_reflexivity_aux; eauto with subst_aux.
  forwards Hokay : (sub_ctxt_okay H0).
  assert (ctxt_okay (([X0 ==> R]Gamma0) ++ Delta)).
    eauto using ctxt_okay_subst_ftvar.
  apply sub_transitivity with (U := [X0 ~> R] T); eauto.
  assert (T0 = T).
    eapply ctxt_okay_unique_ftvar_bind 
      with (Gamma := Gamma0 ++ X0 ~<: T0 :: Delta); eauto.
      Destruct In by eauto.
  subst T.
  destruct (sub_lclosed_t H2) as [? ?].
  assert (~ In X0 (FV_tt T0)).
    forwards Hokay' : ctxt_okay_app Hokay.
    inversion Hokay'; eauto with incl_param.
  rewrite -> subst_ftvar_nochange_t; eauto with weakening_aux.
  constructor 3 with (T := [X0 ~> R] T); eauto.
  assert ( ~ In X0 (FV_tc Delta) ).
    forwards Hokay : ctxt_okay_app (sub_ctxt_okay H0).    
    eauto using ctxt_okay_unique_ftvar.
  replace (X ~<: ([X0 ~> R]T)) 
    with (ctxt_ftvar_subst X0 R (X ~<: T)) by Simplify by eauto.
  rewrite ftvar_subst_ctxt_nochange 
    with (Gamma := Delta) (X := X0) (T := R) by eauto.
  Destruct In by eauto using ftvar_subst_ctxt_bind_in.
    inversion H0; congruence.
  set (L' := X :: FV_tc (([X ==> R]Gamma0) ++ Delta) ++
            FV_tt ([X ~> R] T2) ++ FV_tt ([X ~> R] U2) ++
            (dom_tc ((X ~<: U1 :: Gamma0) ++ X ~<: T :: Delta)) ++ L).
  constructor 5 with L'; eauto.
    intros; unfold L' in H2; Destruct notIn by eauto.
    destruct (sub_lclosed_t H3) as [? _].
    replace (X0 ~<: ([X ~> R] U1) :: ([X ==> R]Gamma0) ++ Delta) 
      with (([X ==> R] X0 ~<: U1 :: Gamma0) ++ Delta) by auto.
    replace (X0 ^^) with ([X ~> R] X0 ^^) by Simplify by eauto. 
    repeat erewrite <- subst_ftvar_ltvar_t; eauto.
    eapply H1; simpl; eauto.
Qed.

Hint Resolve sub_subst_ftvar : subst_aux.

Lemma typing_subst_ftvar_aux : forall Gamma0 t T,
  typing Gamma0 t T ->
  forall Gamma X U U' Delta,
    Gamma0 = Gamma ++ X ~<: U :: Delta ->
    sub Delta U' U ->
    typing (([X ==> U']Gamma) ++ Delta) ([X :~> U'] t) ([X ~> U'] T).
Proof.
  induction 1; intros; subst; Simplify by eauto with subst_aux.
  econstructor; eauto with subst_aux.
  assert ( ~ In X (FV_tc Delta) ).
    forwards Hokay : ctxt_okay_app H. 
    eauto using ctxt_okay_unique_ftvar.
  rewrite ftvar_subst_ctxt_nochange 
    with (Gamma := Delta) (X := X) (T := U') by eauto.
  unsimpl (ctxt_ftvar_subst X U' (x ~: T)).
  Destruct In by eauto using ftvar_subst_ctxt_bind_in.
    inversion H0; congruence.
  constructor 2 with L; eauto with subst_aux.  
  intros.
    replace (x ~: ([X ~> U'] T) :: ([X ==> U'] Gamma0) ++ Delta) with 
      (([X ==> U'] (x ~: T :: Gamma0)) ++ Delta) by eauto.
    unsimpl ([X :~> U'] x **); rewrite <- subst_ftvar_lvar_e.
    eapply H1; simpl; eauto.
  constructor 4 with (L := X :: L); intros; 
    Destruct notIn by eauto with subst_aux.
    destruct (sub_lclosed_t H3) as [? _].
    replace (X0 ~<: ([X ~> U'] T) :: ([X ==> U'] Gamma0) ++ Delta) 
      with (([X ==> U'] (X0 ~<: T :: Gamma0)) ++ Delta) by eauto.
    replace (X0 ^^) with ([X ~> U'] X0 ^^) by Simplify by eauto.
    rewrite <- subst_ftvar_ltvar_e with (Gamma := Delta) by eauto.
    rewrite <- subst_ftvar_ltvar_t with (Gamma := Delta) by eauto.
    eapply H1; simpl; eauto.
  destruct (sub_lclosed_t H2) as [? _].
  rewrite subst_ftvar_ltvar_t with (Gamma := Delta) by auto.
  constructor 5 with (T' := [X ~> U'] T'); eauto with subst_aux.
Qed.

Hint Resolve typing_subst_ftvar_aux : subst_aux.

Lemma typing_subst_ftvar : forall  Gamma0 t T,
  typing Gamma0 t T ->
  forall X U U' Gamma,
    Gamma0 = X ~<: U :: Gamma ->
    sub Gamma U' U ->
    typing Gamma ([X :~> U'] t) ([X ~> U'] T).
Proof.
  intros.
  unsimpl (([X ==> U'] emptyset) ++ Gamma).
  eauto using typing_subst_ftvar_aux. 
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
 the structure of [typing] proofs. *)
Lemma typing_subst_fvar_aux : forall Gamma0 t T,
  typing Gamma0 t T ->
  forall Gamma x U u Delta,
    Gamma0 = Gamma ++ x ~: U :: Delta ->
    typing (Gamma ++ Delta) u U ->
    typing (Gamma ++ Delta) ([ x ::~> u ] t) T.
Proof.
  induction 1; intros; subst; Simplify by eauto using strengthen_sub.  
  assert (T = U). 
    eapply ctxt_okay_unique_fvar_bind; Destruct In by eauto.
      inversion H0; subst; eauto with v62.
  subst; eauto.  
  econstructor; eauto with strengthen_aux.
    Destruct In by congruence.
  set (L' :=  x :: dom_ec (Gamma0 ++ Delta) ++ L).
  constructor 2 with (L := L').
    unsimpl (emptyset ++ Gamma0).
    eapply strengthen_lclosed_t_fvar_app_aux; simpl; eauto.
    intros; unfold L' in H2; Destruct notIn by eauto.
    assert ( ctxt_okay (x0 ~: T :: Gamma0 ++ Delta) ).
      eauto using typing_ctxt_okay with strengthen_aux.
    erewrite <- subst_fvar_lvar_e
      with (Gamma := Gamma0 ++ Delta) by eauto using typing_lclosed_e.
    rewrite list_cons_cons_move_app.
    eapply H1; simpl; eauto using weakening_typing.
  set (L' := dom_tc (Gamma0 ++ Delta) ++ L).
  constructor 4 with (L := L'); eauto with strengthen_aux.
    intros; unfold L' in H2; Destruct notIn by eauto.
    assert ( ctxt_okay (X ~<: T :: Gamma0 ++ Delta) ).
      econstructor; eauto using typing_ctxt_okay with strengthen_aux.
    erewrite subst_ltvar_fvar_e with (Gamma := Gamma0 ++ Delta)
      by eauto using typing_lclosed_e.
    rewrite list_cons_cons_move_app.
    eapply H1; simpl; eauto using weakening_typing.
Qed.

Lemma typing_subst_fvar : forall Gamma x U t u T,
  typing (x ~: U :: Gamma) t T ->
  typing Gamma u U ->
  typing Gamma ([ x ::~> u ] t) T.
Proof.
  intros.
  unsimpl (emptyset ++ Gamma).
  eapply typing_subst_fvar_aux; simpl; eauto.
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
 leamms. Lemma [app_red_preservation] deals with the [red_abs] case, and
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
  set (L' := FV_ee t ++ L).
  destruct (pick_fresh L') as [x Hfresh].
  unfold L' in Hfresh; Destruct notIn by eauto.
  eauto using typing_subst_lvar.
  eauto using IHtyping, sub_transitivity.
Qed.

Lemma tapp_red_preservation : forall Gamma t0 A T B T0 t U1 U2 R,
  typing Gamma t0 T0
  -> t0 = tm_tabs A T t
  -> sub Gamma T0 (typ_all B U1 U2)
  -> sub Gamma R U1
  -> typing Gamma ({A :~> R} t) ({B ~> R} U2).
Proof.
  induction 1; simpl; intros He HsubD HsubA; inversion He; subst.
  inversion HsubD; subst.
  set (L' := FV_te t ++ FV_tt U ++ FV_tt U2 ++ L ++ L0).
  destruct (pick_fresh L') as [X0 Hfresh].
  unfold L' in Hfresh; Destruct notIn by eauto.
  constructor 6 with (T := ({B0 ~> R} U)).
    eapply typing_subst_ltvar with (X := X0); eauto.
      eauto using sub_transitivity.
    unsimpl (([X0 ==> R] emptyset) ++ Gamma).
    rewrite <- subst_seq_ftvar_ltvar_t with (X := X0) (A := B0) by eauto.
    rewrite <- subst_seq_ftvar_ltvar_t with (X := X0) (A := B) by eauto.
    eapply sub_subst_ftvar; simpl; eauto.
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
