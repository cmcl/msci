(**
  Type safety of System F with linear types 

    Original authors: Brian Aydemir and Arthur Chargu\'eraud, with help from             
    Aaron Bohannon, Jeffrey Vaughan, and Dimitrios Vytiniotis. 

    Author: Jeongbong Seo 

  This is a modification of the Coq proof script 
    by Karl Mazurak, Jianzhou Zhao, and Steve Zdancewic,
  which is described in 
    Lightweight linear types in System F^O, TLDI 2010. 

  Main modification is to introduce annotated free variables and to drop out typing context.
 *)

(**
   We use 'Metatheory' library to handle a set of variable.
*)
Require Export Metatheory.
Require Export Extra.
Require Import Omega.

(* *************************************************************** *)
(** * Contents
 - #<a href="##definition">Definitions</a>#
  - #<a href="##syntax">Syntax (pre-terms)</a>#
  - #<a href="##open">Opening terms</a>#
  - #<a href="##env">Environments</a>#
  - #<a href="##wf">Well-formedness</a>#
  - #<a href="##lc">Local closure</a>#
  - #<a href="##split">Linear Context Splitting</a>#
  - #<a href="##values">Values</a>#
  - #<a href="##typing_doc">Typing</a>#
  - #<a href="##reduction">Reduction</a>#
  - #<a href="##auto">Automation</a>#
 - #<a href="##infra">Infrastructure lemmas and tactic definitions for F^O</a>#
  - #<a href="##fv">Free variables</a>#
  - #<a href="##subst">Substitution</a>#
  - #<a href="##pick_fresh">The "pick fresh" tactic</a>#
  - #<a href="##apply_fresh">The "pick fresh and apply" tactic</a>#
  - #<a href="##properties">Properties of opening and substitution</a>#
  - #<a href="##lenv_prop">Properites of the [lenv_split] relation</a>#
 - #<a href="##lemmas">Administrative lemmas for F^O</a>#
  - #<a href="##wft">Properties of [wf_typ], [wf_lenv], and [lenv_split]</a>#
  - #<a href="##lc2">Properties of substitution</a># 
  - #<a href="##regularity">Regularity lemmas</a>#
  - #<a href="##auto3">Automation</a>#
 - #<a href="##soundness">Type safefy proofs for F^O</a>#
  - #<a href="##typing_prop">Properties of typing</a>#
  - #<a href="##preservation">Preservation</a>#
  - #<a href="##progress">Progress</a>#

 *)
(* *************************************************************** *)

(* ********************************************************************** *)
(** * #<a name="definition"></a># Definition *)

(** We use locally nameless representation, no typing context, cofinite quantification. 
  - #<a href="##syntax">Syntax (pre-terms)</a>#
  - #<a href="##open">Opening terms</a>#
  - #<a href="##env">Environments</a>#
  - #<a href="##wf">Well-formedness</a>#
  - #<a href="##lc">Local closure</a>#
  - #<a href="##split">Linear Context Splitting</a>#
  - #<a href="##values">Values</a>#
  - #<a href="##typing_doc">Typing</a>#
  - #<a href="##reduction">Reduction</a>#
  - #<a href="##auto">Automation</a>#
*)

(* ********************************************************************** *)
(** ** #<a name="syntax"></a># Syntax (pre-terms) *)

(** Binding variables are represented as natural numbers and
   free variables are represented as atom type which is defined in Metatheory libaray.
*)
Notation ltvar := nat.
Notation ftvar := atom.
Notation lvar := nat.
Notation fvar := atom.
(* Add :for readability *)

(**
   We use the following notations for types:
   - kinds            k, k'
   - types            T, U, S
   - type variables   A, B, C
   - type parameters  X, Y, Z

   Similarly, we use the following notations for terms:
   - terms            t, u, s
   - term variables   a, b, c
   - term parameters  x, y, z

   We inductively define the kinds, types, and terms of System F^O:
<<
   - kinds k, k'     :=  lin | nonlin
   - types T, U, S   :=  A | X ^^ k | T -(k)-> U | \forall ^^ k. T | T * U
   - terms t, u, s   :=  a | x : T | \lambda : T ^^ k. t | t u | 
                         \Lambda ^^ k. t | t [ T ] | (t, u) | \fst t | \snd t
>>
*)

Inductive kn : Set :=
  | kn_lin
  | kn_nonlin
.

Inductive typ : Set :=
  | typ_bvar : ltvar -> typ
  | typ_fvar : ftvar -> kn -> typ
  | typ_arrow : kn -> typ -> typ -> typ
  | typ_all : kn -> typ -> typ
  | typ_with : typ -> typ -> typ (* its kind is always lin *)
.
(* Change : Annotated typ_fvar *)

Inductive exp : Set :=
  | exp_bvar : lvar -> exp
  | exp_fvar : fvar -> typ -> exp
  | exp_abs : kn -> typ -> exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_tabs : kn -> exp -> exp
  | exp_tapp : exp -> typ -> exp
  | exp_apair : exp -> exp -> exp
  | exp_fst : exp -> exp
  | exp_snd : exp -> exp
.
(* Change : Annotated exp_fvar *)

Coercion typ_bvar : ltvar >-> typ.
Coercion exp_bvar : lvar >-> exp.

Lemma eq_kn_dec: forall (k1 k2:kn), {k1 = k2} + {~k1 = k2}.
Proof.
  decide equality.
Qed.
(* No Change : from end part of file *)

Lemma ftvar_dec : forall (p q : (ftvar * kn)), {p = q} + {p <> q}.
Proof.
  repeat decide equality.
Qed.

Lemma fvar_dec : forall (p q : (fvar * typ)), {p = q} + {p <> q}.
Proof.
  repeat decide equality.
Qed.
(* Add : Due to absence of coercion relation, we need a new method to decide equality. *) 

Lemma eq_typ_dec: forall (t1 t2:typ), {t1 = t2} + {~t1 = t2}.
Proof.
  repeat decide equality. 
Qed.
(* Change : simplified *)

Notation  "alpha ^^ k" := (typ_fvar alpha k) (at level 65).
Notation "A -( k )-> B" := (typ_arrow k A B) (at level 65).
Notation "X ** A" := (exp_fvar X A) (at level 65).
(* Add : for readability *)

(* ********************************************************************** *)
(** ** #<a name="open"></a># Opening terms *)

(** We define opening funtions which substitute type variables and term
   variables appearing in types, expressions. We are using locally nameless
   representation, we do not have to worry about variable captures. *)

Fixpoint open_tt_rec (K : ltvar) (U : typ) (T : typ)  {struct T} : typ :=
  match T with
  | typ_bvar J => if eq_nat_dec K J then U else (typ_bvar J)
  | typ_fvar X k => typ_fvar X k
  | typ_arrow k T1 T2 => typ_arrow k (open_tt_rec K U T1) (open_tt_rec K U T2)
  | typ_all k T2 => typ_all k (open_tt_rec (S K) U T2)
  | typ_with T1 T2 => typ_with (open_tt_rec K U T1) (open_tt_rec K U T2)
  end.
(* Change : typ_fvar *)

Fixpoint open_te_rec (K : ltvar) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x t => exp_fvar x t
  | exp_abs k V e1 => exp_abs k (open_tt_rec K U V)  (open_te_rec K U e1)
  | exp_app e1 e2 => exp_app (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_tabs k e1 => exp_tabs k (open_te_rec (S K) U e1)
  | exp_tapp e1 V => exp_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  | exp_apair e1 e2 => exp_apair (open_te_rec K U e1) (open_te_rec K U e2)
  | exp_fst e1 => exp_fst (open_te_rec K U e1)
  | exp_snd e1 => exp_snd (open_te_rec K U e1)
  end.
(* Change : exp_fvar *)

Fixpoint open_ee_rec (k : lvar) (f : exp) (e : exp)  {struct e} : exp :=
  match e with
  | exp_bvar i => if eq_nat_dec k i then f else e
  | exp_fvar x t => exp_fvar x t
  | exp_abs K V e1 => exp_abs K V (open_ee_rec (S k) f e1)
  | exp_app e1 e2 => exp_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_tabs K e1 => exp_tabs K (open_ee_rec k f e1)
  | exp_tapp e1 V => exp_tapp (open_ee_rec k f e1) V
  | exp_apair e1 e2 => exp_apair (open_ee_rec k f e1) (open_ee_rec k f e2)
  | exp_fst e1 => exp_fst (open_ee_rec k f e1)
  | exp_snd e1 => exp_snd (open_ee_rec k f e1)
  end.
(* Change : exp_fvar *)

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te e U := open_te_rec 0 U e.
Definition open_ee e1 e2 := open_ee_rec 0 e2 e1.
(* No change *)

Notation "{: a ~> C :} A" := (open_tt_rec a C A) (at level 67).
Notation "{: a :~> C :} e" := (open_te_rec a C e) (at level 67).
Notation "{: x ::~> e0 :} e " := (open_ee_rec x e0 e) (at level 67).
Notation "{: ~> C :} A" := (open_tt A C) (at level 67).
Notation "{: :~> C :} e" := (open_te e C) (at level 67).
Notation "{: ::~> e0 :} e " := (open_ee e e0) (at level 67).
Notation " p === q " := (ftvar_dec p q) (at level 70).
Notation " p ==== q " := (fvar_dec p q) (at level 70).
(* Add : for readability *)


(* ********************************************************************** *)
(** ** #<a name="env"></a># Environments *)

(** Although we adopt type-annotated free variables(type parameters and term
   parameters), we still need to maintain a context of term variables whose types
   have [kn_lin] kind, namely a linear context, so as to trace linear-kind
   term variables and to ensure that they are used exactly once. *)

Inductive lbinding : Set :=
  | lbind_typ : typ -> lbinding.

Notation lenv := (list (fvar * lbinding)).
Notation lempty := (@nil (fvar * lbinding)).
(* No change *)

Lemma eq_lbnd_dec: forall (a b:lbinding), {a = b}+{~a=b}.
Proof.
  decide equality. 
    apply eq_typ_dec.
Qed.
(* No Change *)

Lemma eq_lbinding_dec: forall (x y:(atom * lbinding)%type), {x = y}+{~x = y}.
Proof.
  decide equality.
    apply eq_lbnd_dec.
Qed.
(* No Change *)

(* ********************************************************************** *)
(** ** #<a name="wf"></a># Well-formedness *)

(** A type [t] with a kind [k] is well-formed, [wf_typ t k], iff all type variables
   appearing in [t] are bounded and the kind of [t] is a subtype of [k]. 
   Note that a product type must has a kind [kn_lin] ([wf_typ_with])  
   and [kn_nonlin] is a subtype of [kn_lin] ([wf_typ_sub]). *)

Inductive wf_typ : typ -> kn -> Prop :=
  | wf_typ_var : forall K (X : fvar),
      wf_typ (typ_fvar X K) K
  | wf_typ_arrow : forall K1 K2 K T1 T2,
      wf_typ T1 K1 ->
      wf_typ T2 K2 ->
      wf_typ (typ_arrow K T1 T2) K
  | wf_typ_all : forall L K1 K2 T2,
      (forall A : ftvar, A `notin` L ->
        wf_typ (open_tt T2 (A ^^ K1)) K2) ->
      wf_typ (typ_all K1 T2) K2
  | wf_typ_with : forall K1 K2 T1 T2,
      wf_typ T1 K1 ->
      wf_typ T2 K2 ->
      wf_typ (typ_with T1 T2) kn_lin
  | wf_typ_sub : forall T,
      wf_typ T kn_nonlin ->
      wf_typ T kn_lin
.
(* Change : Drop out context *)

(** A context [e] is well-formed, [wf_lenv e], iff all term variables in [e] 
   are distinct and all types in [e] are well-formed with a kind [kn_lin]. *)

Inductive wf_lenv : lenv -> Prop :=
  | wf_lenv_empty : wf_lenv lempty
  | wf_lenv_typ : forall (D:lenv) (X:fvar) (T:typ),
      wf_lenv D ->
      X `notin` dom D -> 
      wf_typ T kn_lin ->
      wf_lenv ([(X, lbind_typ T)] ++ D).


(* ********************************************************************** *)
(** ** #<a name="lc"></a># Local closure *)

(*
Inductive type : typ -> Prop :=
  | type_var : forall K X,
      type (typ_fvar X K)
  | type_arrow : forall K T1 T2,
      type T1 ->
      type T2 ->
      type (typ_arrow K T1 T2)
  | type_all : forall L K T2,
      (forall X : ftvar, X `notin` L -> type (open_tt T2 (X ^^ K))) ->
      type (typ_all K T2)
  | type_with : forall T1 T2,
      type T1 ->
      type T2 ->
      type (typ_with T1 T2)
.
*)

(** A type [t] is locally closed, [type t], iff [t] is well-formed. *)
Definition type T := exists K, wf_typ T K.

(** An expression [e] is locally closed, [expr e], iff every term variable in [e]
    is bounded and every type variable in [e] is also locally-closed.
    We are using cofinite quantification for the cases [expr_abs] and [expr_tabs].
    *)
Inductive expr : exp -> Prop :=
  | expr_fvar : forall X t,
      type t ->
      expr (exp_fvar X t)
  | expr_abs : forall L K t e1,
      type t ->
      (forall X : fvar, X `notin` L -> expr (open_ee e1 (X ** t))) ->
      expr (exp_abs K t e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_app e1 e2)
  | expr_tabs : forall L K e1,
      (forall A : ftvar, A `notin` L -> expr (open_te e1 (A ^^ K))) ->
      expr (exp_tabs K e1)
  | expr_tapp : forall e1 V,
      expr e1 ->
      type V ->
      expr (exp_tapp e1 V)
  | expr_apair : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (exp_apair e1 e2)
  | expr_fst : forall e1,
      expr e1 ->
      expr (exp_fst e1)
  | expr_snd : forall e1,
      expr e1 ->
      expr (exp_snd e1)
.


(* ********************************************************************** *)
(** ** #<a name="split"></a># Linear Context Splitting *)

(** [levn_split e_1 e_2 e_3] means that [e_3] can be divided into [e_1] and [e_2].  *)

Inductive lenv_split : lenv -> lenv -> lenv -> Prop :=
  | lenv_split_empty:
       lenv_split lempty lempty lempty
  | lenv_split_left: forall D1 D2 D3 X T,
       lenv_split D1 D2 D3 ->
       X `notin` dom D3 ->
       wf_typ T kn_lin ->
       lenv_split ([(X, lbind_typ T)]++D1) D2 ([(X, lbind_typ T)]++D3)
  | lenv_split_right: forall D1 D2 D3 X T,
       lenv_split D1 D2 D3 ->
       X `notin` dom D3 ->
       wf_typ T kn_lin ->
       lenv_split D1 ([(X, lbind_typ T)]++D2) ([(X, lbind_typ T)]++D3).
(* No change *)

(* ********************************************************************** *)
(** ** #<a name="values"></a># Values *)

Inductive value : exp -> Prop :=
  | value_abs : forall K T e1,
      expr (exp_abs K T e1) ->
      value (exp_abs K T e1)
  | value_tabs : forall K e1,
      expr (exp_tabs K e1) ->
      value (exp_tabs K e1)
  | value_apair : forall e1 e2,
      expr e1 ->
      expr e2 ->
      value (exp_apair e1 e2)
.
(* No change *)

(* ********************************************************************** *)
(** ** #<a name="typing_doc"></a># Typing *)

(** Typing relation is defined as follows. For the case of type parameters and 
 lambda abstractions, two rules are defined accroding to a kind of a type. 
 Note the use of the cofinite-quantification style in the rules [typing_abs],
 [typing_labs], and [typing_tabs] *)

Inductive typing : lenv -> exp -> typ -> Prop :=
  | typing_unvar : forall X T,
      wf_typ T kn_nonlin ->
      typing lempty (exp_fvar X T) T
  | typing_linvar : forall X T,
      wf_typ T kn_lin ->
      typing [(X, lbind_typ T)] (exp_fvar X T) T
  | typing_abs : forall L K D T1 e1 T2,
      wf_typ T1 kn_nonlin -> 
      (forall X : fvar, X `notin` L ->
        typing D (open_ee e1 (X ** T1)) T2) ->
      (K = kn_nonlin -> D = lempty) ->
      typing D (exp_abs K T1 e1) (typ_arrow K T1 T2)
  | typing_labs : forall L K D T1 e1 T2,
      wf_typ T1 kn_lin -> 
      (forall X : fvar, X `notin` L ->
        typing ([(X, lbind_typ T1)] ++ D) (open_ee e1 (X ** T1)) T2) ->
      (K = kn_nonlin -> D = lempty) ->
      typing D (exp_abs K T1 e1) (typ_arrow K T1 T2)
  | typing_app : forall T1 K D1 D2 D3 e1 e2 T2,
      typing D1 e1 (typ_arrow K T1 T2) ->
      typing D2 e2 T1 ->
      lenv_split D1 D2 D3 ->
      typing D3 (exp_app e1 e2) T2
  | typing_tabs : forall L D K e1 T1,
      (forall A : ftvar, A `notin` L -> value (open_te e1 (A ^^ K))) ->
      (forall A : ftvar, A `notin` L ->
        typing D (open_te e1 (A ^^ K)) (open_tt T1 (A ^^ K))) ->
      typing D (exp_tabs K e1) (typ_all K T1)
  | typing_tapp : forall K D e1 T T2,
      typing D e1 (typ_all K T2) ->
      wf_typ T K ->
      typing D (exp_tapp e1 T) (open_tt T2 T)
  | typing_apair : forall D e1 e2 T1 T2,
      typing D e1 T1 ->
      typing D e2 T2 ->
      typing D (exp_apair e1 e2) (typ_with T1 T2)
  | typing_fst : forall D e T1 T2,
      typing D e (typ_with T1 T2) ->
      typing D (exp_fst e) T1
  | typing_snd : forall D e T1 T2,
      typing D e (typ_with T1 T2) ->
      typing D (exp_snd e) T2
.
(* Change : Drop out typing context, typing_var ->  typing_unvar/typing_linvar *)


(* ********************************************************************** *)
(** ** #<a name="reduction"></a># Reduction *)

Inductive red : exp -> exp -> Prop :=
  | red_app_1 : forall e1 e1' e2,
      expr e2 ->
      red e1 e1' ->
      red (exp_app e1 e2) (exp_app e1' e2)
  | red_app_2 : forall e1 e2 e2',
      value e1 ->
      red e2 e2' ->
      red (exp_app e1 e2) (exp_app e1 e2')
  | red_tapp : forall e1 e1' V,
      type V ->
      red e1 e1' ->
      red (exp_tapp e1 V) (exp_tapp e1' V)
  | red_abs : forall K T e1 v2,
      expr (exp_abs K T e1) ->
      value v2 ->
      red (exp_app (exp_abs K T e1) v2) (open_ee e1 v2)
  | red_tabs : forall K e1 T,
      expr (exp_tabs K e1) ->
      type T ->
      red (exp_tapp (exp_tabs K e1) T) (open_te e1 T)
  | red_fst_cong : forall e e',
      red e e' ->
      red (exp_fst e) (exp_fst e')
  | red_fst_beta : forall e1 e2,
      expr e1 ->
      expr e2 ->
      red (exp_fst (exp_apair e1 e2)) e1
  | red_snd_cong : forall e e',
      red e e' ->
      red (exp_snd e) (exp_snd e')
  | red_snd_beta : forall e1 e2,
      expr e1 ->
      expr e2 ->
      red (exp_snd (exp_apair e1 e2)) e2
.
(* Change : wf_typ instead of type in red_tapp, red_tabs. *)

(* ********************************************************************** *)
(** ** #<a name="auto"></a># Automation *)

(** We declare most constructors as [Hint]s to be used by the [auto]
   and [eauto] tactics.  We exclude constructors from the subtyping
   and typing relations that use cofinite quantification.  It is
   unlikely that [eauto] will find an instantiation for the finite
   set [L], and in those cases, [eauto] can take some time to fail.
   (A priori, this is not obvious.  In practice, one adds as hints
   all constructors and then later removes some constructors when
   they cause proof search to take too long.) *)

Hint Constructors expr wf_typ wf_lenv value red lenv_split.
Hint Resolve typing_unvar typing_linvar typing_app typing_tapp typing_apair typing_fst typing_snd.

(* ********************************************************************** *)
(** ** #<a name="cases"></a># Cases Tactic  *)
(** Following tactics help to insert case markers in a proof. *)

Tactic Notation "typ_cases" tactic(first) tactic(c) :=
  first;
  [ c "typ_bvar" |  c "typ_fvar" | 
    c "typ_arrow" | c "typ_all" | c "typ_with" ].

Tactic Notation "exp_cases" tactic(first) tactic(c) :=
  first;
  [ c "exp_bvar" |  c "exp_fvar" | 
    c "exp_abs" | c "exp_app" |
    c "exp_tabs" | c "exp_tapp" | 
    c "exp_apair" | c "exp_fst" | c "exp_snd" ].

Tactic Notation "expr_cases" tactic(first) tactic(c) :=
  first;
  [ c "expr_fvar"
    c "expr_abs" | c "expr_app" |
    c "expr_tabs" | c "expr_tapp" |
    c "expr_apair" | c "expr_fst" | c "expr_snd" ].

Tactic Notation "wf_typ_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_typ_var" | c "wf_typ_arrow" | c "wf_typ_all" | c "wf_typ_with" | c "wf_typ_sub" ].


Tactic Notation "wf_lenv_cases" tactic(first) tactic(c) :=
  first;
  [ c "wf_lenv_empty" | c "wf_lenv_typ" ].


Tactic Notation "lenv_split_cases" tactic(first) tactic(c) :=
  first;
  [ c "lenv_split_empty" | c "lenv_split_left" | c "lenv_split_right" ].

Tactic Notation "value_cases" tactic(first) tactic(c) :=
  first;
  [ c "value_abs" | c "value_tabs" | c "value_apair" ].

Tactic Notation "red_cases" tactic(first) tactic(c) :=
  first;
  [ c "red_app_1" |  c "red_app_2" | 
    c "red_tapp" | c "red_abs" | c "red_tabs" | 
    c "red_fst_cong" | c "red_fst_beta" | 
    c "red_snd_cong" | c "red_snd_beta" ].

Tactic Notation "typing_cases" tactic(first) tactic(c) :=
  first;
  [ c "typing_unvar" | c "typing_linvar" |
    c "typing_abs" | c "typing_labs" | c "typing_app" | 
    c "typing_tabs" | c "typing_tapp" | 
    c "typing_apair" | c "typing_fst" | c "typing_snd" ].

(* ********************************************************************** *)
(** * #<a name="infra"></a># Infrastructure lemmas and tactic definitions for F^O *)

(** This section contains a number of definitions, tactics, and lemmas
   that are based only on the syntax of the language at hand.  While
   the exact statements of everything here would change for a
   different language, the general structure of this file (i.e., the
   sequence of definitions, tactics, and lemmas) would remain the
   same.                                                                       
                                                                            
Table of contents:
  - #<a href="##fv">Free variables</a>#
  - #<a href="##subst">Substitution</a>#
  - #<a href="##pick_fresh">The "pick fresh" tactic</a>#
  - #<a href="##apply_fresh">The "pick fresh and apply" tactic</a>#
  - #<a href="##properties">Properties of opening and substitution</a>#
  - #<a href="##lenv_prop">Properites of the [lenv_split] relation</a># *)

(* ********************************************************************** *)
(** ** #<a name="fv"></a># Free variables *)

(** In this section, we define free variable functions.  The functions
 [fv_tt] and [fv_te] calculate the set of atoms used as free type
 variables in a type or expression, respectively.  The function
 [fv_ee] calculates the set of atoms used as free expression
 variables in an expression.  Cases involving binders are
 straightforward since bound variables are indices, not names, in
 locally nameless representation. *)

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | typ_bvar J => {}
  | typ_fvar X k => singleton X
  | typ_arrow K T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | typ_all K T2 => (fv_tt T2)
  | typ_with T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  end.
(* Minor Change : typ_fvar +k *)

Fixpoint fv_te (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x t => fv_tt t
  | exp_abs K V e1  => (fv_tt V) `union` (fv_te e1)
  | exp_app e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_tabs K e1 => (fv_te e1)
  | exp_tapp e1 V => (fv_tt V) `union` (fv_te e1)
  | exp_apair e1 e2 => (fv_te e1) `union` (fv_te e2)
  | exp_fst e1 => (fv_te e1)
  | exp_snd e1 => (fv_te e1)
  end.
(* Minor Change : exp_fvar +t *)

Fixpoint fv_ee (e : exp) {struct e} : atoms :=
  match e with
  | exp_bvar i => {}
  | exp_fvar x t => singleton x
  | exp_abs K V e1 => (fv_ee e1)
  | exp_app e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_tabs K e1 => (fv_ee e1)
  | exp_tapp e1 V => (fv_ee e1)
  | exp_apair e1 e2 => (fv_ee e1) `union` (fv_ee e2)
  | exp_fst e1 => (fv_ee e1)
  | exp_snd e1 => (fv_ee e1)
  end.
(* Minor Change : exp_fvar +t *)

Fixpoint fv_lenv (D : lenv) {struct D} : atoms :=
  match D with
  | nil => {}
  | cons (X, lbind_typ T) l => 
      singleton X `union` fv_tt T `union` fv_lenv l
  end.
(* No Change *)

(* ********************************************************************** *)
(** ** #<a name="subst"></a># Substitution *)

(** In this section, we define substitution for expression and type
    variables appearing in types, expressions, and environments.
    Substitution differs from opening because opening replaces type variables
    whereas substitution replaces type parameters. The definitions
    below are relatively simple for two reasons.
      - We are using locally nameless representation, where bound variables
        (type variables) are represented using indices.  Thus, there is no
        need to rename variables to avoid capture.
      - The definitions below assume that the term being substituted
        in, i.e., the second argument to each function, is locally
        closed.  Thus, there is no need to shift indices when passing
        under a binder. *)

Fixpoint subst_tt (alpha : ftvar) (ka : kn) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | typ_bvar J => typ_bvar J
  | typ_fvar beta kb => if (alpha,ka) === (beta,kb) then U else T
  | typ_arrow K T1 T2 => typ_arrow K (subst_tt alpha ka U T1) (subst_tt alpha ka U T2)
  | typ_all K T2 => typ_all K (subst_tt alpha ka U T2)
  | typ_with T1 T2 => typ_with (subst_tt alpha ka U T1) (subst_tt alpha ka U T2)
  end.
(* Change : Free type variables carry their own kind. *)

Fixpoint subst_te (alpha : ftvar) (ka : kn) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar x t => exp_fvar x (subst_tt alpha ka U t)
  | exp_abs K V e1 => exp_abs K (subst_tt alpha ka U V)  (subst_te alpha ka U e1)
  | exp_app e1 e2 => exp_app  (subst_te alpha ka U e1) (subst_te alpha ka U e2)
  | exp_tabs K e1 => exp_tabs K  (subst_te alpha ka U e1)
  | exp_tapp e1 V => exp_tapp (subst_te alpha ka U e1) (subst_tt alpha ka U V)
  | exp_apair e1 e2 => exp_apair  (subst_te alpha ka U e1) (subst_te alpha ka U e2)
  | exp_fst e1 => exp_fst  (subst_te alpha ka U e1)
  | exp_snd e1 => exp_snd  (subst_te alpha ka U e1)
  end.
(* Change : Free type variables carry their own kind. *)

Fixpoint subst_ee (x : fvar) (tx : typ) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | exp_bvar i => exp_bvar i
  | exp_fvar y ty => if (x, tx) ==== (y, ty) then u else e
  | exp_abs K V e1 => exp_abs K V (subst_ee x tx u e1)
  | exp_app e1 e2 => exp_app (subst_ee x tx u e1) (subst_ee x tx u e2)
  | exp_tabs K e1 => exp_tabs K (subst_ee x tx u e1)
  | exp_tapp e1 V => exp_tapp (subst_ee x tx u e1) V
  | exp_apair e1 e2 => exp_apair (subst_ee x tx u e1) (subst_ee x tx u e2)
  | exp_fst e1 => exp_fst (subst_ee x tx u e1)
  | exp_snd e1 => exp_snd (subst_ee x tx u e1)
  end.
(* Change : Free variables carry their own type. *)

Definition subst_tlb (alpha : ftvar) (ka : kn) (P : typ) (b : lbinding) : lbinding :=
  match b with
  | lbind_typ T => lbind_typ (subst_tt alpha ka P T)
  end.
(* No Change *)

Notation "[: ( alpha , k ) ~> C :] B" := (subst_tt alpha k C B) (at level 67).
Notation "[: ( alpha , k ) :~> C :] e " := (subst_te alpha k C e) (at level 67).
Notation "[: ( X , A ) ::~> e :] e0 " := (subst_ee X A e e0) (at level 67).
(* Add : for readability. *)

(* ********************************************************************** *)
(** ** #<a name="pick_fresh"></a># The "[pick fresh]" tactic *)

(** The "[pick fresh]" tactic introduces a fresh atom into the context.
    We define it in two steps.

    The first step is to define an auxiliary tactic [gather_atoms],
    meant to be used in the definition of other tactics, which returns
    a set of atoms in the current context.  The definition of
    [gather_atoms] follows a pattern based on repeated calls to
    [gather_atoms_with].  The one argument to this tactic is a
    function that takes an object of some particular type and returns
    a set of atoms that appear in that argument.  It is not necessary
    to understand exactly how [gather_atoms_with] works.  If we add a
    new inductive datatype, say for kinds, to our language, then we
    would need to modify [gather_atoms].  On the other hand, if we
    merely add a new type, say products, then there is no need to
    modify [gather_atoms]; the required changes would be made in
    [fv_tt]. *)

Ltac gather_atoms :=
  let A := ltac_map (fun x : atoms => x) in
  let B := ltac_map (fun x : atom => singleton x) in
  let C := ltac_map (fun x : exp => fv_te x) in
  let D := ltac_map (fun x : exp => fv_ee x) in
  let E := ltac_map (fun x : typ => fv_tt x) in
  let F := ltac_map (fun x : lenv => dom x) in
  let G := ltac_map (fun x : lenv => fv_lenv x) in
  simplify_list_of_atom_sets (A ++ B ++ C ++ D ++ E ++ F ++ G).

(** The second step in defining "[pick fresh]" is to define the tactic
    itself.  It is based on the [(pick fresh ... for ...)] tactic
    defined in the [Atom] library.  Here, we use [gather_atoms] to
    construct the set [L] rather than leaving it to the user to
    provide.  Thus, invoking [(pick fresh x)] introduces a new atom
    [x] into the current context that is fresh for "everything" in the
    context. *)

Tactic Notation "pick" "fresh" ident(x) :=
  let L := gather_atoms in (pick fresh x for L).
(* No Chnage. *)

(* *********************************************************************** *)
(** ** #<a name="apply_fresh"></a># The "[pick fresh and apply]" tactic *)

(** This tactic is implementation specific only because of its
    reliance on [gather_atoms], which is itself implementation
    specific.  The definition below may be copied between developments
    without any changes, assuming that the other other developments
    define an appropriate [gather_atoms] tactic.  For documentation on
    the tactic on which the one below is based, see the
    [Metatheory] library. *)

Tactic Notation
      "pick" "fresh" ident(atom_name) "and" "apply" constr(lemma) :=
  let L := gather_atoms in
  pick fresh atom_name excluding L and apply lemma.
(* No Chnage. *)

(* ********************************************************************** *)
(** ** #<a name="properties"></a># Properties of opening and substitution *)

(** The following lemmas provide useful structural properties of
    substitution and opening.  While the exact statements are language
    specific, we have found that similar properties are needed in a
    wide range of languages.

    Below, we indicate which lemmas depend on which other lemmas.
    Since [te] functions depend on their [tt] counterparts, a similar
    dependency can be found in the lemmas.

    The lemmas are split into three sections, one each for the [tt],
    [te], and [ee] functions.  The most important lemmas are the
    following:
      - Substitution and opening commute with each other, e.g.,
        [subst_tt_open_tt_var].
      - Opening a term is equivalent to opening the term with a fresh
        name and then substituting for that name, e.g.,
        [subst_tt_intro].

    We keep the sections as uniform in structure as possible.  In
    particular, we state explicitly strengthened induction hypotheses
    even when there are more concise ways of proving the lemmas of
    interest. *)


(* ********************************************************************** *)
(** *** Properties of type substitution in types *)

(** The next lemma is the strengthened induction hypothesis for the
    lemma that follows, which states that opening a locally closed
    term is the identity.  This lemma is not otherwise independently
    useful. *)

Lemma open_tt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T.
Proof with try solve [congruence | eauto].
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
  Case "typ_bvar".
    destruct (eq_nat_dec j n)... destruct (eq_nat_dec i n)...
Qed.
(* No Change. *)

(** Opening a locally closed term is the identity.  This lemma depends
    on the immediately preceding lemma. *)

Lemma open_tt_rec_type : forall P U k,
  type P ->
  P = open_tt_rec k U P.
Proof with try solve [congruence | intuition].
  intros P U k Htyp; revert k. destruct Htyp as [K HWFT].
  induction HWFT; intros; simpl; f_equal...
  Case "typ_all".
    unfold open_tt in *.
    pick fresh X.
    apply (open_tt_rec_type_aux T2 0 (typ_fvar X K1))...
Qed.
(* No Change. *)

(** If a name is fresh for a term, then substituting for it is the
    identity. *)

Lemma subst_tt_fresh : forall alpha ka U T,
   alpha `notin` fv_tt T ->
   T = subst_tt alpha ka U T.
Proof with try solve [congruence | intuition].
  induction T; simpl; intro H; f_equal...
  Case "typ_fvar".
    destruct (ftvar_dec (alpha, ka) (a, k))...
    inversion e; contradict H; fsetdec.
Qed.
(* Change : destruct(equality test), X -> alpha ^^ ka  *)

(** Substitution commutes with opening under certain conditions.  This
    lemma depends on the fact that opening a locally closed term is
    the identity. *)

Lemma subst_tt_open_tt_rec : forall T1 T2 alpha ka P k,
  type P ->
  subst_tt alpha ka P (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_tt alpha ka P T2) (subst_tt alpha ka P T1).
Proof with try solve [congruence | intuition].
  intros T1 T2 alpha ka P k WP. revert k.
  induction T1; intros K; simpl; f_equal...
  Case "typ_bvar".
    destruct (eq_nat_dec K n); subst...
  Case "typ_fvar".
    destruct (ftvar_dec (alpha, ka) (a, k)); subst... apply open_tt_rec_type...
Qed.
(* Change : destruct(equality test). X -> alpha ^^ ka *)

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero. *)

Lemma subst_tt_open_tt : forall T1 T2 (alpha:ftvar) ka P,
  type P ->
  subst_tt alpha ka P (open_tt T1 T2) = open_tt (subst_tt alpha ka P T1) (subst_tt alpha ka P T2).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_tt.
  apply subst_tt_open_tt_rec...
Qed.
(* Change : X -> alpha ^^ ka *)

(** The next lemma is a direct corollary of the immediately preceding
    lemma---here, we're opening the term with a variable.  In
    practice, this lemma seems to be needed as a left-to-right rewrite
    rule, when stated in its current form. *)

Lemma subst_tt_open_tt_var : forall (alpha beta:ftvar) ka kb P T,
  beta <> alpha ->
  type P ->
  open_tt (subst_tt alpha ka P T) (beta ^^ kb) = subst_tt alpha ka P (open_tt T (beta ^^ kb)).
Proof with try solve [congruence | intuition].
  intros alpha beta ka kb P T Neq Wu.
  unfold open_tt.
  rewrite subst_tt_open_tt_rec...
  simpl.
  destruct (ftvar_dec (alpha, ka) (beta, kb))...
Qed.
(* Change : destruct(equality test). X -> alpha ^^ ka *)

(** The next lemma states that opening a term is equivalent to first
    opening the term with a fresh name and then substituting for the
    name.  This is actually the strengthened induction hypothesis for
    the version we use in practice. *)

Lemma subst_tt_intro_rec : forall alpha ka T2 U k,
  alpha `notin` fv_tt T2 ->
  open_tt_rec k U T2 = subst_tt alpha ka U (open_tt_rec k (typ_fvar alpha ka) T2).
Proof with try solve [congruence | intuition].
  induction T2; intros U K Fr; simpl in *; f_equal...
  Case "typ_bvar".
    destruct (eq_nat_dec K n)... simpl. destruct (ftvar_dec (alpha, ka) (alpha, ka))...
  Case "typ_fvar".
    destruct (ftvar_dec (alpha, ka) (a, k))... inversion e; contradict Fr; fsetdec.
Qed.
(* Change : destruct(equality test), X -> alpha ^^ ka *)

(** The next lemma is a direct corollary of the immediately preceding
    lemma---the index is specialized to zero.  *)

Lemma subst_tt_intro : forall (alpha : ftvar) ka T2 U,
  alpha `notin` fv_tt T2 ->
  open_tt T2 U = subst_tt alpha ka U (open_tt T2 (alpha ^^ ka)).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_tt.
  apply subst_tt_intro_rec...
Qed.
(* Change : X -> alpha ^^ ka *)

(* ********************************************************************** *)
(** *** Properties of type substitution in expressions *)

(** This section follows the structure of the previous section.  The
    one notable difference is that we require two auxiliary lemmas to
    show that substituting a type in a locally-closed expression is
    the identity. *)

Lemma open_te_rec_expr_aux : forall e j u i P ,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) ->
  e = open_te_rec i P e.
Proof with try solve [congruence | eauto].
  induction e; intros j u i P H; simpl in *; inversion H; f_equal...
Qed.
(* No Change *)

Lemma open_te_rec_type_aux : forall e j Q i P,
  i <> j ->
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) ->
  e = open_te_rec i P e.
Proof.
  induction e; intros j Q i P Neq Heq; simpl in *; inversion Heq;
    f_equal; eauto using open_tt_rec_type_aux.
Qed.
(* No Change *)

Lemma open_te_rec_expr : forall e U k,
  expr e ->
  e = open_te_rec k U e.
Proof with try solve [congruence | intuition].
  intros e U k WF. revert k.
  induction WF; intros; simpl; f_equal; eauto using open_tt_rec_type;
  try solve [
    unfold open_ee in *;
    pick fresh X;
    eapply open_te_rec_expr_aux with (j := 0) (u := (X ** t));
    try solve [congruence | intuition]
  | unfold open_te in *;
    pick fresh X;
    eapply open_te_rec_type_aux with (j := 0) (Q := typ_fvar X K);
    try solve [congruence | intuition]
  ].
Qed.
(* No Change *)

Lemma subst_te_open_te_rec : forall e T alpha ka P k,
  type P  ->
  subst_te alpha ka P (open_te_rec k T e) =
    open_te_rec k (subst_tt alpha ka P T) (subst_te alpha ka P e).
Proof.
  intros e T alpha P kp k WU. revert k.
  induction e; intros K; simpl; f_equal; eauto using subst_tt_open_tt_rec.
Qed.
(* Change : X -> alpha ^^ ka *)

Lemma subst_te_open_te : forall e T alpha ka P,
  type P ->
  subst_te alpha ka P (open_te e T) = open_te (subst_te alpha ka P e) (subst_tt alpha ka P T).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_te.
  eapply subst_te_open_te_rec...
Qed.
(* Change : X -> alpha ^^ ka *)

Lemma subst_te_open_te_var : forall (alpha beta:ftvar) ka kb P e,
  beta <> alpha ->
  type P ->
  open_te (subst_te alpha ka P e) (beta ^^ kb) = subst_te alpha ka P (open_te e (beta ^^ kb)).
Proof with try solve [congruence | intuition].
  intros alpha beta ka kb P e Neq WU.
  unfold open_te.
  rewrite subst_te_open_te_rec...
  simpl.
  destruct (ftvar_dec (alpha, ka) (beta, kb))...
Qed.
(* Change : destruct(equality test). X -> alpha ^^ ka *)

Lemma subst_te_intro_rec : forall alpha ka e U k,
  alpha `notin` fv_te e ->
  open_te_rec k U e = subst_te alpha ka U (open_te_rec k (typ_fvar alpha ka) e).
Proof.
  induction e; intros U K Fr; simpl in *; f_equal;
    auto using subst_tt_intro_rec, subst_tt_fresh.
Qed.
(* Change : X -> alpha ^^ ka *)

Lemma subst_te_intro : forall (alpha : ftvar) ka e U,
  alpha `notin` fv_te e ->
  open_te e U = subst_te alpha ka U (open_te e (alpha ^^ ka)).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_te.
  apply subst_te_intro_rec...
Qed.
(* Change : X -> alpha ^^ ka *)


(* ********************************************************************** *)
(** *** Properties of expression substitution in expressions *)

(** This section follows the structure of the previous two sections. *)

Lemma open_ee_rec_expr_aux : forall e j v u i,
  i <> j ->
  open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof with try solve [congruence | eauto].
  induction e; intros j v u i Neq H; simpl in *; inversion H; f_equal...
  Case "exp_bvar".
    destruct (eq_nat_dec j n)... destruct (eq_nat_dec i n)...
Qed.
(* No Change *)

Lemma open_ee_rec_type_aux : forall e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; intros j V u i H; simpl; inversion H; f_equal; eauto.
Qed.
(* No Change *)

Lemma open_ee_subst_ee_rec: forall e X tx Y T U n,
  Y <> X ->
  {: n ::~> Y ** T :}e = [: (X, tx) ::~> U :]({: n ::~> Y ** T :}e) ->
  e = [: (X, tx) ::~> U :]e.
Proof with try (inversion Eq; simpl in *; f_equal; eauto).
  intros e X tx Y T U.
  (exp_cases (induction e) Case); intros n0 NotIn Eq...
Qed.
(* Add : Used in LinFp_Soundness: non_susbst *)

Lemma open_te_subst_ee_rec: forall e X tx alpha ka U n,
  {: n :~> alpha ^^ ka :}e = [: (X, tx) ::~> U :]({: n :~> alpha ^^ ka :}e) ->
  e = [: (X, tx) ::~> U :]e.
Proof with try (inversion Eq; simpl in *; f_equal; eauto).
  intros e X tx alpha ka U.
  (exp_cases (induction e) Case); intros n0 Eq...
Qed.
(* Add : Used in LinFp_Soundness: non_subst *)

Lemma open_ee_rec_expr : forall u e k,
  expr e ->
  e = open_ee_rec k u e.
Proof with try solve [congruence | intuition].
  intros u e k Hexpr. revert k.
  induction Hexpr; intros; simpl; f_equal; try solve [congruence | intuition];
  try solve [
    unfold open_ee in *;
    pick fresh X;
    eapply open_ee_rec_expr_aux with (j := 0) (v := (X ** t));
    try solve [congruence | intuition]
  | unfold open_te in *;
    pick fresh X;
    eapply open_ee_rec_type_aux with (j := 0) (V := typ_fvar X K);
    try solve [congruence | intuition]
  ].
Qed.
(* No Change *)

Lemma subst_ee_open_ee_rec : forall e1 e2 x tx u k,
  expr u ->
  subst_ee x tx u (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_ee x tx u e2) (subst_ee x tx u e1).
Proof with try solve [congruence | intuition].
  intros e1 e2 x tx u k WP. revert k.
  induction e1; intros K; simpl; f_equal...
  Case "exp_bvar".
    destruct (eq_nat_dec K n); subst...
  Case "exp_fvar".
    destruct ((x, tx) ==== (a, t))... inversion e; apply open_ee_rec_expr...
Qed.
(* Change : x -> x ** tx *)

Lemma subst_ee_open_ee : forall e1 e2 x tx u,
  expr u ->
  subst_ee x tx u (open_ee e1 e2) =
    open_ee (subst_ee x tx u e1) (subst_ee x tx u e2).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_ee.
  apply subst_ee_open_ee_rec...
Qed.
(* Change : x -> x ** tx *)

Lemma subst_ee_open_ee_var : forall (x y:fvar) tx ty u e,
  y <> x ->
  expr u ->
  open_ee (subst_ee x tx u e) (exp_fvar y ty) = subst_ee x tx u (open_ee e (exp_fvar y ty)).
Proof with try solve [congruence | intuition].
  intros x y tx ty u e Neq Wu.
  unfold open_ee.
  rewrite subst_ee_open_ee_rec; simpl; destruct ((x, tx) ==== (y, ty))...
Qed.
(* Change : x -> x ** tx *)

Lemma subst_te_open_ee_rec : forall e1 e2 alpha ka P k,
  subst_te alpha ka P (open_ee_rec k e2 e1) =
    open_ee_rec k (subst_te alpha ka P e2) (subst_te alpha ka P e1).
Proof with try solve [congruence | intuition].
  induction e1; intros e2 alpha ka P K; simpl; f_equal...
  Case "exp_bvar".
    destruct (eq_nat_dec K n)...
Qed.
(* Change : Z -> alpha ^^ ka *)

Lemma subst_te_open_ee : forall e1 e2 alpha ka P,
  subst_te alpha ka P (open_ee e1 e2) = open_ee (subst_te alpha ka P e1) (subst_te alpha ka P e2).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_ee.
  apply subst_te_open_ee_rec...
Qed.
(* Change : Z -> alpha ^^ ka *)

Lemma subst_te_open_ee_var : forall alpha ka (x:fvar) tx P e,
  open_ee (subst_te alpha ka P e) (exp_fvar x (subst_tt alpha ka P tx)) = subst_te alpha ka P (open_ee e (exp_fvar x tx)).
Proof with try solve [congruence | intuition].
  intros.
  rewrite subst_te_open_ee...
Qed.
(* Change + : New substitution rule. (Type substitution distributes into annotated type in free variable.) *)

Lemma subst_ee_open_te_rec : forall e P x tx u k,
  expr u ->
  subst_ee x tx u (open_te_rec k P e) = open_te_rec k P (subst_ee x tx u e).
Proof with try solve [congruence | intuition].
 induction e; intros P x tx u K Hexp; simpl; f_equal...
    destruct ((x, tx) ==== (a, t))... apply open_te_rec_expr...
Qed.
(* Change : z -> x ** tx *)

Lemma subst_ee_open_te : forall e P x tx u,
  expr u ->
  subst_ee x tx u (open_te e P) = open_te (subst_ee x tx u e) P.
Proof with try solve [congruence | intuition].
  intros.
  unfold open_te.
  apply subst_ee_open_te_rec...
Qed.
(* Change : z -> x ** tx *)

Lemma subst_ee_open_te_var : forall x tx (alpha:ftvar) ka u e,
  expr u ->
  open_te (subst_ee x tx u e) (alpha ^^ ka) = subst_ee x tx u (open_te e (alpha ^^ ka)).
Proof with try solve [congruence | intuition].
  intros x tx alpha ka u e H.
  rewrite subst_ee_open_te...
Qed.
(* Change : z -> x ** tx, X -> alpha ^^ ka *)

Lemma subst_ee_intro_rec : forall X tx e u k,
  X `notin` fv_ee e ->
  open_ee_rec k u e = subst_ee X tx u (open_ee_rec k (X ** tx) e).
Proof with try solve [congruence | intuition].
  induction e; intros u K Fr; simpl in *; f_equal...
  Case "exp_bvar".
    destruct (eq_nat_dec K n)... simpl. destruct ((X, tx) ==== (X, tx))...
  Case "exp_fvar".
    destruct ((X, tx) ==== (a, t))... inversion e; contradict Fr; fsetdec.
Qed.
(* Change : x -> X ** tx. destruct(equality test)  *)

Lemma subst_ee_intro : forall (X : fvar) tx e u,
  X `notin` fv_ee e ->
  open_ee e u = subst_ee X tx u (open_ee e (exp_fvar X tx)).
Proof with try solve [congruence | intuition].
  intros.
  unfold open_ee.
  apply subst_ee_intro_rec...
Qed.
(* Change : x -> X ** tx *)

(* ********************************************************************** *)
(** ** #<a name="lenv_prop"></a># Properites of the [lenv_split] relation *)

(** Basic properties of the env_split relation. *)

Lemma dom_lenv_split: forall E1 E2 E3,
  lenv_split E1 E2 E3  -> 
  dom E3 [=] dom E1 `union` dom E2.
Proof.
  intros E1 E2 E3 S.
  induction S; simpl; try fsetdec. 
Qed.
(* Change : No typing context *)

Lemma lenv_split_commute: forall E1 E2 E3,
  lenv_split E1 E2 E3 ->
  lenv_split E2 E1 E3.
Proof.
  intros E1 E2 E3 S.
  induction S; auto.
Qed.
(* Change : No typing context *)

Lemma lenv_split_empty_left: forall E F,
  lenv_split lempty E F ->
  E = F.
Proof.
  induction E; intros F H; inversion H; auto.
  Case "con".
    rewrite (IHE D3); auto.
Qed.
(* Change : No typing context *)

Lemma lenv_split_empty_right: forall E F,
  lenv_split E lempty F ->
  E = F.
Proof.
  intros. 
  eapply lenv_split_empty_left. 
  eapply lenv_split_commute; eauto.
Qed.
(* Change : No typing context *)

(** [wf_lenv_split D_1 D_2 D_3] implies that all contexts [D_1], [D_2], and [D_3] are well-formed. *)
Lemma wf_lenv_split: forall D1 D2 D3,
  lenv_split D1 D2 D3  ->
  wf_lenv D3.
Proof.
  intros D1 D2 D3 S.
  (lenv_split_cases (induction S) Case); simpl_env in *; 
    try solve [ eauto | eapply wf_lenv_typ; eauto ].
Qed.
(* Change : No typing context *)

Lemma wf_lenv_split_left: forall D1 D2 D3,
  lenv_split D1 D2 D3 ->
  wf_lenv D1.
Proof.
  intros D1 D2 D3 S.
  (lenv_split_cases (induction S) Case); auto.
  Case "lenv_split_left".
    apply wf_lenv_typ; auto.
      rewrite (dom_lenv_split D1 D2 D3) in H; auto.
Qed.
(* Change : No typing context *)

Lemma wf_lenv_split_right: forall D1 D2 D3,
  lenv_split D1 D2 D3 ->
  wf_lenv D2.
Proof.
  intros. 
  eapply wf_lenv_split_left. 
  eapply lenv_split_commute; eauto.
Qed.
(* Change : No typing context *)

Hint Extern 1 (wf_lenv ?D) =>
  match goal with
  | H: lenv_split _ _ _ |- _ => apply (wf_lenv_split _ _ _ H)
  | H: lenv_split _ _ _ |- _ => apply (wf_lenv_split_left _ _ _ H)
  | H: lenv_split _ _ _ |- _ => apply (wf_lenv_split_right _ _ _ H)
  end.
(* Change : No typing context *)

(** If [lenv_split D_1 D_2 D_3] then an element in [D_3] is found in
   either [D_1] or [D_2]. *)
Lemma lenv_split_cases_mid: forall D1 D2 DL x T DR,
  lenv_split D1 D2 (DL ++ [(x, lbind_typ T)] ++ DR) ->
  (exists D1L, exists D1R, exists D2L, exists D2R,
    D1 = D1L ++ [(x, lbind_typ T)] ++ D1R /\
    D2 = D2L ++ D2R /\
    lenv_split D1L D2L DL /\
    lenv_split D1R D2R DR) \/
  (exists D1L, exists D1R, exists D2L, exists D2R,
    D1 = D1L ++ D1R /\
    D2 = D2L ++ [(x, lbind_typ T)] ++ D2R /\
    lenv_split D1L D2L DL /\
    lenv_split D1R D2R DR).
Proof.
  intros D1 D2 DL x T DR S.
  remember (DL ++ [(x, lbind_typ T)] ++ DR) as D3.
  generalize dependent DR. generalize dependent DL.
  (lenv_split_cases (induction S) Case);  
    intros DL DR EQ; subst; simpl_env in *.
  Case "lenv_split_empty".
    destruct DL; inversion EQ.
  Case "lenv_split_left".
    destruct DL; simpl in *; inversion EQ; subst; simpl_env in *.
    SCase "nil".
      left. 
      exists lempty. exists D1. exists lempty. exists D2. 
      simpl_env. 
      repeat split; auto. 
    SCase "con".
      lapply (IHS DL DR); auto.
      intros J.
      destruct J as [J | J].
      SSCase "left".
        destruct J as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]].
        left. exists ([(X, lbind_typ T0)] ++ D1L).
        exists D1R. exists D2L. exists D2R.
        simpl_env in *. 
        repeat split; subst; auto.
      SSCase "right".
        destruct J as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]].
        right. exists ([(X, lbind_typ T0)] ++ D1L).
        exists D1R. exists D2L. exists D2R.
        simpl_env in *. 
        repeat split; subst; auto.
  Case "lenv_split_right".
    destruct DL; simpl in *; inversion EQ; subst; simpl_env in *.
    SCase "nil".
      right.
      exists lempty. exists D1. exists lempty. exists D2.
      simpl_env in *. 
      repeat split; auto. 
    SCase "con".
      lapply (IHS DL DR); auto.
      intros J.
      destruct J as [J | J].
      SSCase "left".
        destruct J as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]].
        left. exists D1L. 
        exists D1R. exists ([(X, lbind_typ T0)] ++ D2L). exists D2R.
        simpl_env in *. repeat split; subst; auto.
      SSCase "right".
        destruct J as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]].
        right. exists D1L. 
        exists D1R. exists ([(X, lbind_typ T0)] ++ D2L). exists D2R.
        subst. simpl_env in *. repeat split; auto.
Qed.
(* Change : little simplified *)

(** If [lenv_split D_1 D_2 D_3] then [D_1] and [D_2] are distinct. *)
Lemma lenv_split_not_in_left: forall D1 D2 D3 x,
  lenv_split D1 D2 D3 ->
  x `in` dom D1 ->
  x `notin` dom D2.
Proof.
  intros D1 D2 D3 x S.
  (lenv_split_cases (induction S) Case);  
    intros; simpl_env in *; try fsetdec.
  Case "lenv_split_left".
    rewrite (dom_lenv_split D1 D2 D3) in H; auto.
      fsetdec.
  Case "lenv_split_right".
    rewrite (dom_lenv_split D1 D2 D3) in H; auto.
      fsetdec.
Qed.
(* Change : NO typing context *)

Lemma lenv_split_not_in_right: forall D1 D2 D3 x,
  lenv_split D1 D2 D3 ->
  x `in` dom D2 ->
  x `notin` dom D1.
Proof.
  intros.
  eapply lenv_split_not_in_left.
    eapply lenv_split_commute; eauto.  
    auto.
Qed.
(* Change : NO typing context *)

(** If [lenv_split D_1 D_2 D_3] then we can append another context [F] to in front of both [D_1] and [D_3]. *)
Lemma lenv_split_lin_weakening_left: forall F D1 D2 D3,
  lenv_split D1 D2 D3 ->
  wf_lenv (F ++ D3) ->
  lenv_split (F ++ D1) D2 (F ++ D3).
Proof.
  induction F; intros D1 D2 D3 S WFL; simpl_env in *; auto.
  Case "con".
    destruct a.
    inversion WFL; subst.
    apply lenv_split_left; auto.
Qed.
(* Change : NO typing context *)

(** If [lenv_split D_1 D_2 D_3] then we can eliminate an element from both [D_1] and [D_3]. *)
Lemma lenv_split_sub_left: forall D1L D1R D2 DL DR x U F,
   lenv_split
        (D1L ++ [(x, lbind_typ U)] ++ D1R) 
        D2 
        (DL ++ [(x, lbind_typ U)] ++ DR) ->
   wf_lenv (DL ++ F ++ DR) ->
   lenv_split
        (D1L ++ F ++ D1R) 
        D2
        (DL ++ F ++ DR).
Proof.
  intros D1L D1R D2 DL DR x U F S.
  remember (D1L ++ [(x, lbind_typ U)] ++ D1R) as D1.
  remember (DL ++ [(x, lbind_typ U)] ++ DR) as D3.
  generalize dependent D1R. generalize dependent D1L.
  generalize dependent DR. generalize dependent DL.
  (lenv_split_cases (induction S) Case);  
    intros DL DR EQ1 D1L D1R EQ2 WFL; subst; auto.
  Case "lenv_split_empty".
    destruct DL; inversion EQ1.
  Case "lenv_split_left".
    destruct DL; inversion EQ1; subst.
    SCase "nil".
      destruct D1L; inversion EQ2; subst; simpl_env in *. 
      SSCase "nil".
        apply lenv_split_lin_weakening_left; auto.
      SSCase "con".
        rewrite (dom_lenv_split (D1L ++ [(x, lbind_typ U)] ++ D1R) D2 DR) in H; auto.
          simpl_env in *.
          assert False as J. fsetdec. 
          tauto. 
    SCase "nil".
      destruct D1L; inversion EQ2; subst; simpl_env in *. 
      SSCase "nil".
        assert False. fsetdec. 
        tauto. 
      SSCase "con".
        inversion WFL; subst.
        apply lenv_split_left; auto.
  Case "lenv_split_right".
    destruct DL; inversion EQ1; subst; simpl_env in *. 
    SCase "nil".
      rewrite (dom_lenv_split (D1L ++ [(x, lbind_typ U)] ++ D1R) D2 DR) in H; auto.
        simpl_env in *. 
        assert False. fsetdec. 
        tauto.
    SCase "con".
      inversion WFL; subst.
      apply lenv_split_right; auto.
Qed.
(* Change : No typing context *)

(** If [lenv_split D_1 D_2 D_3] then we can eliminate an element from both [D_2] and [D_3]. *)
Lemma lenv_split_sub_right: forall D1 D2L D2R DL DR x U F,
   lenv_split  
        D1
        (D2L ++ [(x, lbind_typ U)] ++ D2R) 
        (DL ++ [(x, lbind_typ U)] ++ DR) ->
   wf_lenv (DL ++ F ++ DR) ->
   lenv_split 
        D1
        (D2L ++ F ++ D2R) 
        (DL ++ F ++ DR).
Proof.
  intros.
  apply lenv_split_commute. 
  eapply lenv_split_sub_left; eauto.
    apply lenv_split_commute; eauto.
Qed.
(* Change : No typing context *)

(** If [lenv_split D_1 D_2 D_3] then we can add an element to an arbitrary position of both [D_1] and [D_3]. *)
Lemma lenv_split_weakening_left: forall D1L D1R D2L D2R D3L D3R x T,
  lenv_split (D1L ++ D1R) (D2L ++ D2R) (D3L ++ D3R) ->
  lenv_split D1L D2L D3L ->
  lenv_split D1R D2R D3R ->
  wf_lenv (D3L ++ [(x, lbind_typ T)] ++ D3R) ->
  lenv_split (D1L ++ [(x, lbind_typ T)] ++ D1R) (D2L ++ D2R) (D3L ++ [(x, lbind_typ T)]++ D3R).
Proof.
  intros D1L D1R D2L D2R D3L D3R x T S.
  remember (D1L ++ D1R) as D1.
  remember (D2L ++ D2R) as D2.
  remember (D3L ++ D3R) as D3.
  generalize dependent D1L. generalize dependent D1R.
  generalize dependent D2L. generalize dependent D2R.
  generalize dependent D3L. generalize dependent D3R.
  (lenv_split_cases (induction S) Case);
    intros D3R D3L EQ3 D2R D2L EQ2 D1R D1L EQ1 SL SR WFL; subst; simpl_env in *.
  Case "lenv_split_empty".
    destruct D3L; destruct D3R; inversion EQ3; subst; simpl_env.
    destruct D2L; destruct D2R; inversion EQ2; subst; simpl_env.
    destruct D1L; destruct D1R; inversion EQ1; subst; simpl_env.
    rewrite_env ([(x, lbind_typ T)] ++ nil).
    simpl_env in WFL. inversion WFL; subst.
    apply lenv_split_left; auto. 
  Case "lenv_split_left".
    destruct D3L; inversion EQ3.
    SCase "D3L=nil".
      destruct D1L; inversion EQ1.
      SSCase "D1L=nil".
        destruct D3R; simpl_env in EQ3; inversion EQ3.
        SSSCase "D3R=con".
          destruct D1R; simpl_env in EQ1; inversion EQ1.
          SSSSCase "D1R=con"; subst; simpl_env in *.
            inversion WFL; subst.
            apply lenv_split_left; auto.
      SSCase "D1L=con".
        inversion SL.
    SCase "D3L=con".
      destruct D1R; simpl_env in EQ1; inversion EQ1; subst.
      SSCase "D2R=nil".
        simpl_env in *. 
        inversion WFL; subst.
        apply lenv_split_left; auto.
          rewrite_env (D1 ++ [(x, lbind_typ T)] ++ nil).
          eapply IHS; auto.
          inversion SL; auto. subst.
          rewrite (dom_lenv_split ([(X, lbind_typ T0)] ++ D1) D2 D3L) in H; auto.
          simpl in H.
          assert False. fsetdec. tauto.
      SSCase "D2R=con".
        inversion SL; subst; simpl_env in *.
        SSSCase "SL1".
          inversion WFL; subst.
          apply lenv_split_left; auto. 
            eapply IHS; auto. 
              inversion EQ1; auto.
        SSSCase "SL2".
          assert (dom (D3L ++ D3R) [=] dom D3L `union` dom D3R) as J.
            rewrite dom_app; auto. fsetdec.
          rewrite <- J in H.
          rewrite (dom_lenv_split D1 ([(X, lbind_typ T0)] ++ D2 ++ D2R) (D3L ++ D3R)) in H; auto.
          simpl in H; auto.
          assert False. fsetdec. tauto.
  Case "lenv_split_right".
    destruct D3L; inversion EQ3.
    SCase "D3L=nil".
      destruct D2L; inversion EQ2.
      SSCase "D2L=nil".
        destruct D3R; inversion EQ3.
        SSSCase "D3R=con".
          destruct D2R; inversion EQ2.
          SSSSCase "D2R=con"; subst; simpl_env in *.
            inversion SL; simpl_env in *.
            inversion WFL; subst.
            apply lenv_split_left; auto. 
      SSCase "D2L=con".
        inversion SL.
    SCase "D3L=con".
      subst. simpl_env in *.
      destruct D2L; inversion EQ2.
      SSCase "D2L=nil".
        destruct D2R; inversion EQ2.
        SSSCase "D2R=con".
          subst. simpl_env in *.
          rewrite (dom_lenv_split D1R ([(X, lbind_typ T0)] ++ D2R) D3R) in H; auto.
          simpl in H. 
          assert False. fsetdec. tauto.
      SSCase "D2L=con".
        inversion WFL; subst.
        apply lenv_split_right; subst; auto.  
          eapply IHS; auto.  
          inversion SL; subst; simpl_env in *.
          SSSCase "SL1".
            assert (dom (D3L ++ D3R) [=] dom D3L `union` dom D3R) as J.
              rewrite dom_app; fsetdec.
            rewrite <- J in H.
            rewrite (dom_lenv_split ([(X, lbind_typ T0)] ++ D1 ++ D1R) 
               (D2L ++ D2R) (D3L ++ D3R)) in H; auto.
            simpl in H; auto.
            assert False. fsetdec. tauto.
          SSSCase "SL2".
            inversion WFL; auto.
Qed.
(* Change : No typing context *)

(** If [lenv_split D_1 D_2 D_3] then we can add an element to an arbitrary position of both [D_2] and [D_3]. *)      
Lemma lenv_split_weakening_right: forall D1L D1R D2L D2R D3L D3R x T,
  lenv_split (D1L ++ D1R) (D2L ++ D2R) (D3L ++ D3R) ->
  lenv_split D1L D2L D3L ->
  lenv_split D1R D2R D3R ->
  wf_lenv (D3L ++ [(x, lbind_typ T)] ++ D3R) ->
  lenv_split (D1L ++ D1R) (D2L ++ [(x, lbind_typ T)] ++ D2R) (D3L ++ [(x, lbind_typ T)]++ D3R).
Proof.   
  intros. 
  apply lenv_split_commute. 
  apply lenv_split_weakening_left; try (apply lenv_split_commute; auto); auto.
Qed.
(* Change : No typing context *)

Lemma lenv_split_cases_app: forall DL D1 D2 DR,
  lenv_split D1 D2 (DL ++ DR) ->
  exists D1L, exists D1R, exists D2L, exists D2R,
    lenv_split D1L D2L DL /\
    lenv_split D1R D2R DR /\
    D1L ++ D1R = D1 /\
    D2L ++ D2R = D2.
Proof.
  intros DL.
  induction DL; intros D1 D2 DR S.
  Case "empty".
    exists lempty. exists D1. exists lempty. exists D2.
    simpl_env in *; repeat split; auto. 
  Case "cons".
    destruct a. simpl_env in S.
    inversion S; subst.
    SCase "left".
      lapply (IHDL D0 D2 DR); auto.
      intros.
      destruct H as [D1L [D1R [D2L [D2R [S2 [S3 [Q1 Q2]]]]]]].
      exists ([(a, lbind_typ T)] ++ D1L).
      exists D1R.
      exists D2L.
      exists D2R.
      subst; simpl_env in *; repeat split; auto.
    SCase "right".
      lapply (IHDL D1 D3 DR); auto.
      intros.
      destruct H as [D1L [D1R [D2L [D2R [S2 [S3 [Q1 Q2]]]]]]].
      exists D1L.
      exists D1R.
      exists ([(a, lbind_typ T)] ++ D2L).
      exists D2R.
      subst; simpl_env in *; repeat split; auto.
Qed.
(* Change : No typing context *)

Lemma lenv_split_permute: forall D1 D2 D3,
  lenv_split D1 D2 D3 ->
  permute D3 (D1 ++ D2).
Proof.
  intros D1 D2 D3 S.
  (lenv_split_cases (induction S) Case); simpl_env; auto.
  Case "lenv_split_empty".
    apply permute_empty.
  Case "lenv_split_left".
    rewrite_env (lempty ++ [(X, lbind_typ T)] ++ (D1 ++ D2)).
    apply permute_cons; auto.
  Case "lenv_split_right".
    apply permute_cons; auto.
Qed.
(* Change : No typing context *)

(** When reasoning about the [binds] relation and [map], we
    occasionally encounter situations where the binding is
    over-simplified.  The following hint undoes that simplification,
    thus enabling [Hint]s from the [Environment] library. *)

Hint Extern 1 (binds _ (?F (subst_tt ?alpha ?ka ?U ?T)) _) =>
  unsimpl (subst_tlb alpha ka U (F T)).

(* ********************************************************************** *)
(** * #<a name="lemmas"></a># Administrative lemmas for F^O *)

(**
  - #<a href="##wft">Properties of [wf_typ], [wf_lenv], and [lenv_split]</a>#
  - #<a href="##lc2">Properties of substitution</a>#
  - #<a href="##regularity">Regularity lemmas</a>#
  - #<a href="##auto3">Automation</a>#
*)

(* ********************************************************************** *)
(** ** #<a name="wft"></a># Properties of [wf_typ], [wf_lenv], and [lenv_split] *)

(** A well-formed type [T] is locally closed. *)
Lemma type_from_wf_typ : forall T K,
  wf_typ T K -> type T.
Proof.
  intros; unfold type; eauto.
Qed.

(** Well-formedness is preserved under type substitution. *)
Lemma wf_typ_subst_tb : forall alpha ka P T K,
  wf_typ T K ->
  wf_typ P ka->
  wf_typ (subst_tt alpha ka P T) K.
Proof with simpl_env; eauto using type_from_wf_typ.
  intros alpha ka P T K WT WP.
  (wf_typ_cases (induction WT) Case); (*intros F EQ;*) subst; simpl subst_tt...
  Case "wf_typ_var".
    destruct ((alpha, ka) === (X, K)). inversion e; subst...
        apply wf_typ_var.
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite subst_tt_open_tt_var...
Qed.

(** Well-formedness is preserved under renaming. *)
Lemma wf_typ_rename : forall T (x y:ftvar) K1 K2, 
  y `notin` (fv_tt T)  ->
  x `notin` (fv_tt T) ->
  wf_typ (open_tt T (x ^^ K1)) K2 ->
  wf_typ (open_tt T (y ^^ K1)) K2.
Proof.
  intros. 
  erewrite (subst_tt_intro x); eauto.
  eapply wf_typ_subst_tb; eauto.
Qed.
(* Add : No typing context. from extra lemmas *)

Lemma wf_all_exists : forall T (alpha:ftvar) K1 K2,
  alpha `notin` (fv_tt T) ->
  wf_typ (open_tt T (alpha ^^ K1)) K2 ->
  wf_typ (typ_all K1 T) K2.
Proof.
  intros.
  pick fresh y and apply wf_typ_all.
  apply (wf_typ_rename T alpha). auto. solve_notin. auto.
Qed.
(* Add : No typing context. from extra lemmas *)

(** This is an auxiliary lemma for case analysis of a kind [K]. 
   [destruct K] is not enough because [wf_typ t kn_lin] does not ensure that the kind of [t] is genuinely [kn_lin],
   as it can be derived from [wf_typ t kn_nonlin] by the rule [wf_typ_sub].
   Using this lemma, we can handle that case. *)
Lemma kn_cases : forall t K,
  wf_typ t K ->
  wf_typ t kn_nonlin \/ ~ wf_typ t kn_nonlin.
Proof.
  intros; induction H.
  Case "fvar".
    destruct K; [right; intuition; inversion H | left; auto].
  Case "arrow".
    destruct K.
    right; intro Ha; inversion Ha.
    left; eauto.
  Case "forall".
    pick fresh Y; assert  (FR: Y `notin` L) by solve_notin.
    destruct (H0 Y FR).
    left; apply (wf_all_exists T2 Y); eauto.
    right; intro; inversion H2; subst.
    pick fresh Z.
    lapply (H6 Z); eauto; intros.
    apply H1; apply (wf_typ_rename T2 Z Y); auto.  
  Case "with".
    right; intro Ha; inversion Ha.
  Case "sub".
    left; auto.
Qed.
(* Add : to case analysis genuine kind of free variable *)

(** A well-formed environment [D] consists of distinct elements. *)
Lemma uniq_from_wf_lenv: forall D,
  wf_lenv D ->
  uniq D.
Proof.
  induction D; intros; auto.
  destruct a.
  inversion H; auto.
Qed.
(* Change : No typing context. *)

(** We add [uniq_from_wf_env] as a hint here since it helps blur the
    distinction between [wf_env] and [uniq] in proofs.  The lemmas in
    the [Environment] library use [uniq], whereas here we naturally have
    (or can easily show) the stronger [wf_env].  Thus,
    [uniq_from_wf_env] serves as a bridge that allows us to use the
    environments library. *)

Hint Resolve uniq_from_wf_lenv.

Lemma wf_lenv_lin_weakening: forall D1 D2 x TX,
  wf_typ TX kn_lin ->
  wf_lenv (D1 ++ D2) ->
  x `notin` dom (D1 ++ D2) ->
  wf_lenv (D1 ++ [(x, lbind_typ TX)] ++ D2).
Proof.
  intros D1 D2 x TX WFT WFL.
  remember (D1 ++ D2) as D.
  generalize dependent D1. generalize dependent D2.
  (wf_lenv_cases (induction WFL) Case);
    intros D2 D1 EQ NIN1.
  Case "wf_lenv_empty".
   destruct D1; destruct D2; inversion EQ; subst; simpl_env in *.
   rewrite_env ([(x, lbind_typ TX)] ++ nil).
   apply wf_lenv_typ; auto.
  Case "wf_lenv_typ".
    destruct D1; destruct D2; inversion EQ; subst; simpl_env in *.
    SCase "D1=nil, D2=con".
      apply wf_lenv_typ; auto. 
    SCase "D1=con, D2=nil".
      rewrite_env (D1 ++ [(x, lbind_typ TX)] ++ nil); auto.
    SCase "D1=con, D2=con".
      apply wf_lenv_typ; auto. 
Qed.
(* Change : No typing context *)

Lemma wf_lenv_split_both: forall D1 D2 D3,
  lenv_split D1 D2 D3 ->
  wf_lenv (D1 ++ D2).
Proof.
  intros D1 D2 D3 S.
  (lenv_split_cases (induction S) Case); simpl_env in *; auto.
  Case "lenv_split_left".
    apply wf_lenv_typ; auto. 
      rewrite (dom_lenv_split D1 D2 D3) in H; auto.
  Case "lenv_split_right".
    apply wf_lenv_lin_weakening; auto.
      rewrite (dom_lenv_split D1 D2 D3) in H; auto.
Qed.
(* Change : No typing context *)

(** [lenv_split] relation is preserved under type substitution. *)
Lemma lenv_split_subst_tb : forall D1 D2 D3 alpha ka P,
  lenv_split D1 D2 D3 ->
  wf_typ P ka ->
  lenv_split (map (subst_tlb alpha ka P) D1)
             (map (subst_tlb alpha ka P) D2)
             (map (subst_tlb alpha ka P) D3).
Proof with eauto using wf_typ_subst_tb.
  intros D1 D2 D3 alpha ka P S.
  (lenv_split_cases (induction S) Case); intros WFT; simpl_env in *; auto.
  Case "lenv_split_left".
    apply lenv_split_left... 
  Case "lenv_split_right".
    apply lenv_split_right... 
Qed.
(* Change : Simplified. 14 lines -> 6 lines. *)

(** [lenv_split] relation is preserved under permutation. *)
Lemma lenv_split_exists_permute: forall D1 D2 D3 DX,
  lenv_split D1 D2 D3 ->
  permute D3 DX ->
  exists D1P, exists D2P,
    permute D1 D1P /\
    permute D2 D2P /\
    lenv_split D1P D2P DX.
Proof.
  intros D1 D2 D3 DX.
  intros S.
  generalize dependent DX.
  (lenv_split_cases (induction S) Case); 
    intros DX PERM; inversion PERM; subst.
  Case "lenv_split_empty".
    exists lempty. exists lempty.
    repeat split; try apply permute_empty; try apply lenv_split_empty. 
    auto.
  Case "lenv_split_left".
    lapply (IHS (DL ++ DR)); auto.
    intros EX.
    destruct EX as [D1P [D2P [PERM1 [PERM2 S2]]]].
    lapply (lenv_split_cases_app DL D1P D2P DR); intros; auto.
    destruct H1 as [D1l [D1R [D2L [D2R [S3 [S4 [Q1 Q2]]]]]]]; subst.
    exists (D1l ++ [(X, lbind_typ T)] ++ D1R).
    exists (D2L ++ D2R).
    repeat split; auto.
      apply permute_cons. auto.
      apply lenv_split_weakening_left; auto.
        apply wf_lenv_lin_weakening; auto.
          rewrite (dom_permute _ D3 (DL ++ DR)) in H; auto.
  Case "lenv_split_right".
    lapply (IHS (DL ++ DR)); auto.
    intros EX.
    destruct EX as [D1P [D2P [PERM1 [PERM2 S2]]]].
    lapply (lenv_split_cases_app DL D1P D2P DR); intros; auto.
    destruct H1 as [D1l [D1R [D2L [D2R [S3 [S4 [Q1 Q2]]]]]]]; subst.
    exists (D1l ++ D1R).
    exists (D2L ++ [(X, lbind_typ T)] ++ D2R).
    repeat split; auto.
      apply permute_cons; auto.
      apply lenv_split_weakening_right; auto.
        apply wf_lenv_lin_weakening; auto. 
          rewrite (dom_permute _ D3 (DL ++ DR)) in H; auto.
Qed.
(* Change : No typing context *)


(* *********************************************************************** *)
(** ** #<a name="lc2"></a># Properties of substitution *)

(** *** Local closure is preserved under substitution *)

(** While these lemmas may be considered properties of substitution, we
    separate them out due to the lemmas that they depend on. *)

(** The following lemma depends on [subst_tt_open_tt_var]. *)

Lemma subst_tt_type : forall alpha ka P T,
  type T ->
  type P ->
  type (subst_tt alpha ka P T).
Proof with try solve [congruence | eauto].
  intros alpha ka P T HT HP. unfold type in *.
  destruct HT as [K0 WFT].
  induction WFT; simpl...
  Case "wf_typ_fvar".
    destruct ((alpha, ka) === (X, K))...

  Case "wf_typ_arrow".
    destruct IHWFT1; destruct IHWFT2; exists K...

  Case "wf_typ_all".
    pick fresh Y; destruct_notin.
    destruct (H0 Y Fr) as [K wftyp].
    exists K. rewrite <- subst_tt_open_tt_var in wftyp...
    eapply wf_all_exists; eauto.
    clear H H0 HP wftyp.
    induction T2; simpl in *; destruct_notin; try apply notin_union; eauto.
    destruct ((alpha,ka) === (a, k))...
  
  Case "wf_typ_pair".
    destruct IHWFT1; destruct IHWFT2; exists kn_lin...
Qed.
(* No Change  *)

(** The following lemma depends on [subst_tt_type] and
    [subst_te_open_ee_var]. *)

Lemma subst_te_expr : forall alpha ka P e,
  expr e ->
  type P ->
  expr (subst_te alpha ka P e).
Proof with eauto using subst_tt_type.
  intros alpha ka P e He Hp.
  induction He; simpl; eauto using subst_tt_type;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton alpha);
    intros;
    try rewrite subst_te_open_ee_var;
    try rewrite subst_te_open_te_var;
    eauto using subst_tt_type
  ].
Qed.
(* Change : Z -> alpha ^^ ka *)

(** The following lemma depends on [subst_ee_open_ee_var] and
    [subst_ee_open_te_var]. *)


Lemma subst_ee_expr : forall x tx e1 e2,
  expr e1 ->
  expr e2 ->
  expr (subst_ee x tx e2 e1).
Proof with auto.
  intros x tx e1 e2 He1 He2.
  induction He1; simpl; auto;
  try solve [
    econstructor;
    try instantiate (1 := L `union` singleton x);
    try instantiate (1 := kt);
    try instantiate (1 := kv);
    intros;
    try rewrite subst_ee_open_ee_var;
    try rewrite subst_ee_open_te_var;
    auto
  ].
  Case "expr_var".
    destruct ((x, tx) ==== (X, t)); auto; firstorder using expr_fvar.
Qed.
(* Change : x -> x ** tx *)

(** We add as hints the fact that local closure is preserved under
    substitution.  This is part of our strategy foexprr automatically
    discharging local-closure proof obligations. *)

Hint Resolve subst_tt_type subst_te_expr subst_ee_expr.

(** *** Valueness is preserved under substitution with locally closed types or expressions *)

Lemma value_through_subst_te : forall e Z P k,
  type P ->
  value e ->
  value (subst_te Z k P e).
Proof.
  intros e Z P k Typ H.
  (value_cases (induction H) Case); simpl; auto using subst_te_expr.
  Case "value_abs".
    assert (expr (subst_te Z k P (exp_abs K T e1))) as J.
      apply subst_te_expr; auto.
    apply value_abs; auto.
  Case "value_tabs".
    assert (expr (subst_te Z k P (exp_tabs K e1))) as J.
      apply subst_te_expr; auto.
    apply value_tabs; auto.
Qed.
(* Change : Z -> Z ^^ k *)

Lemma value_through_subst_ee: forall e1 x xt u,
  expr u ->
  value e1 ->
  value (subst_ee x xt u e1).
Proof.
  intros e1 x xt u EX V.
  (value_cases (induction V) Case); simpl; auto.
  Case "value_abs".
    inversion H; subst.
    apply value_abs. 
      pick fresh z and apply expr_abs; auto.
        rewrite subst_ee_open_ee_var; auto.
  Case "value_tabs".
    inversion H; subst.
    apply value_tabs.
      pick fresh X and apply expr_tabs.
        rewrite subst_ee_open_te_var; auto.
Qed.
(* Change : x -> x ** xt *)

(** *** Substitution makes no effect for some cases *)

(** Assume [typing D e T]. A substitution for a term parameter which is not
   found in the linear context [D] and has a genuine linear kind, [kn_lin], does not affect [e]. *)
Lemma non_subst : forall X tx D e T U,
  typing D e T ->
  X `notin` dom D ->
  wf_typ tx kn_lin /\ ~ wf_typ tx kn_nonlin->
  e = [: (X, tx) ::~> U :]e.
Proof with try simpl in *; f_equal; eauto.
  intros X tx D e T U Typ NotIn Lin.
  (typing_cases (induction Typ) Case)...
  Case "typing_unvar".
    destruct ((X,tx) ==== (X0,T)); auto. inversion e; subst; intuition.
  Case "typing_linvar".
    destruct ((X,tx) ==== (X0,T)); auto. inversion e; subst; contradict NotIn; auto.
  Case "typing_abs".
    unfold open_ee in H1; pick fresh Y; eapply open_ee_subst_ee_rec; eauto.
  Case "typing_labs".
    unfold open_ee in H1; pick fresh Y; eapply open_ee_subst_ee_rec; eauto.
  Case "typing_app".
    rewrite (dom_lenv_split _ _ _ H) in NotIn; auto.  
    rewrite (dom_lenv_split _ _ _ H) in NotIn; auto.
  Case "typing_tabs".
    pick fresh alpha.
    unfold open_te in H1;
      eapply open_te_subst_ee_rec; eauto.
Qed.

Lemma subst_tlb_identity: forall D alpha ka T,
  alpha `notin` fv_lenv D ->
  D = (map (subst_tlb alpha ka T) D).
Proof.
  intros D alpha ka T H. 
  induction D; simpl; auto.
  Case "D=con".
    destruct a. destruct l.
    simpl; simpl in H. 
    rewrite <- IHD; auto.
    rewrite <- subst_tt_fresh; auto.
Qed.
(* Change : No typing context *)


(* ********************************************************************** *)
(** ** #<a name="regularity"></a># Regularity lemmas *)

(** [typing D e T] implies that 
    - the linear context [D] is well-formed,
    - [e] is locally closed, and
    - [T] is well-formed (with [kn_lin]).
   Note that we use [kn_lin] for the well-formedness of type [T] 
   since it is the most general case in result of the subtype relation. *)
Lemma typing_regular : forall D e T,
  typing D e T ->
  wf_lenv D /\ expr e /\ wf_typ T kn_lin.
Proof with simpl_env; try solve [intuition | eauto].
  intros D e T H; (typing_cases (induction H) Case)...
  Case "typing_unvar".
    repeat split...
    apply expr_fvar; eapply type_from_wf_typ; eauto.
  Case "typing_linvar".
    repeat split...
    rewrite_env ([(X,lbind_typ T)] ++ lempty); auto.
    apply expr_fvar; eapply type_from_wf_typ; eauto.
  Case "typing_abs".
    pick fresh y.
    destruct (H1 y)...
    destruct H4 as [EXP WFT].
    repeat split...
    SCase "expr".
      pick fresh x and apply expr_abs. 
      eapply type_from_wf_typ; eauto.
        lapply (H1 x); auto...
    SCase "wf_typ".
      destruct K.
      SSCase "K=lin".
        eapply wf_typ_arrow; eauto.
      SSCase "K=nonlin".
        eapply wf_typ_sub.
         eapply wf_typ_arrow; eauto.
  Case "typing_labs".
    pick fresh y.
    destruct (H1 y)...
    destruct H4 as [EXP WFT].
    repeat split...
    SCase "wf_lenv".
      inversion H3; auto.
    SCase "expr".
      pick fresh x and apply expr_abs.
      eapply type_from_wf_typ; eauto.
      lapply (H1 x); auto...
    SCase "wf_typ".
      destruct K.
      SSCase "K=lin".
        eapply wf_typ_arrow; eauto.
      SSCase "K=nonlin".
        eapply wf_typ_sub; eauto.
  Case "typing_app".
    destruct IHtyping1 as [WFL1 [EX1 J1]]...
    destruct IHtyping2 as [WFL2 [EX2 J2]]...
    repeat split...
    SCase "wf_typ".
      inversion J1; subst; auto.
      SSCase "K=lin".
        destruct K2; auto.
      SSCase "K=lin".
        inversion H2; subst; auto.
        destruct K2; auto. 
  Case "typing_tabs".
    pick fresh Y.
    destruct (H1 Y) as [WFL [EX WT]]...
    repeat split...
    SCase "expr".
      pick fresh X and apply expr_tabs.
      destruct (H1 X) as [B [C CC]]...
    SCase "wf_typ".
      pick fresh X and apply wf_typ_all.
      destruct (H1 X) as [B [C CC]]...
  Case "typing_tapp".
    repeat split...
    SCase "expr".
      apply (expr_tapp).               
      tauto.                         
      eapply type_from_wf_typ; eauto.
    SCase "wf_typ".
      destruct IHtyping as [_ [_ WF]].
      inversion WF; subst... 
      SSCase "wf_typ_all".
        pick fresh Y.
        rewrite (subst_tt_intro Y) with (ka := K); auto.  
        eapply (wf_typ_subst_tb Y K); auto.
      SSCase "wf_typ_sub".
        apply wf_typ_sub.
          inversion H1; subst...
          pick fresh Y.
          rewrite (subst_tt_intro Y) with (ka := K); auto.
        eapply (wf_typ_subst_tb Y K); auto.
  Case "typing_apair".
    destruct IHtyping1 as [WFL1 [EX1 J1]]...
    destruct IHtyping2 as [WFL2 [EX2 J2]]...
  Case "typing_fst".
    destruct IHtyping as [WFL1 [EX J]]...
    repeat split...
    SCase "wf_typ".
      inversion J; subst; auto.
      SSCase "wf_typ_with".
        destruct K1; auto. 
      SSCase "wf_typ_sub".
        inversion H0; subst; auto.
  Case "typing_snd".
    destruct IHtyping as [WFL1 [EX J]]...
    repeat split...
    SCase "wf_typ".
      inversion J; subst; auto.
      SSCase "wf_typ_with".
        destruct K2; auto. 
      SSCase "wf_typ_sub".
        inversion H0; subst; auto.
Qed.
(* Change : simplified. 126 lines -> 101 lines *)

(** Every value is locally closed. *)
Lemma value_regular : forall e,
  value e ->
  expr e.
Proof.
  intros e H. induction H; auto.
Qed.
(* No change *)

(** Reduction relation [red] handles only locally closed expressions. *)
Lemma red_regular : forall e e',
  red e e' ->
  expr e /\ expr e'.
Proof with try solve [solve_notin | intuition | eauto].
  intros e e' H.
    induction H; assert(J := value_regular); split...
  Case "red_abs".
    inversion H. pick fresh y. rewrite (subst_ee_intro y) with (tx := T)...
  Case "red_tabs".
    inversion H. pick fresh Y. rewrite (subst_te_intro Y) with (ka := K)...
Qed.
(* Change : Cannot proove a case "red_tapp" automatically. *)


(* *********************************************************************** *)
(** ** #<a name="auto3"></a># Automation *)

(** The lemma [uniq_from_wf_env] was already added above as a hint since it
    helps blur the distinction between [wf_env] and [uniq] in proofs.

    As currently stated, the regularity lemmas are ill-suited to be
    used with [auto] and [eauto] since they end in conjunctions.  Even
    if we were, for example, to split [sub_regularity] into three
    separate lemmas, the resulting lemmas would be usable only by
    [eauto] and there is no guarantee that [eauto] would be able to
    find proofs effectively.  Thus, the hints below apply the
    regularity lemmas and [type_from_wf_typ] to discharge goals about
    local closure and well-formedness, but in such a way as to
    minimize proof search.

    The first hint introduces an [wf_env] fact into the context.  It
    works well when combined with the lemmas relating [wf_env] and
    [wf_typ].  We choose to use those lemmas explicitly via [(auto
    using ...)] tactics rather than add them as hints.  When used this
    way, the explicitness makes the proof more informative rather than
    more cluttered (with useless details).

    The other three hints try outright to solve their respective
    goals. *)

Hint Extern 1 (wf_lenv ?D) =>
  match goal with
  | H: typing _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ H))
  end.
(* Change : No typing context *)

Hint Extern 1 (wf_typ ?T kn_lin) =>
  match goal with
  | H: typing _ _ T |- _ => apply (proj2 (proj2 (typing_regular _ _ _ H)))
  end.
(* Change : No typing context *)

Hint Extern 1 (type ?T) =>
  let go E := apply (type_from_wf_typ E); auto in
  match goal with
  | H: typing ?E _ _ T |- _ => go E
  end.

Hint Extern 1 (expr ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj1 (proj2 (typing_regular _ _ _ H)))
  | H: red ?e _ |- _ => apply (proj1 (red_regular _ _ H))
  | H: red _ ?e |- _ => apply (proj2 (red_regular _ _ H))
  | H: value ?e |- _ => apply (value_regular _ H)
  end.
(* Change : No typing context *)

(* ********************************************************************** *)
(** * #<a name="soundness"></a># Type-safety proofs for F^O *)

(**
 In parentheses are given the label of the corresponding lemma in
 the appendix (informal proofs) of the POPLmark Challenge.       

 - #<a href="##typing_prop">Properties of typing</a>#
 - #<a href="##preservation">Preservation</a>#
 - #<a href="##progress">Progress</a>#
*)

(* ********************************************************************** *)
(** ** #<a name="typing_prop"></a># Properties of typing *)

(** The linear context is unordered. *)

Lemma typing_permute: forall D1 D2 e t,
  typing D1 e t ->
  permute D1 D2 ->
  typing D2 e t.
Proof.
  intros D1 D2 e t TYP PERM.
  generalize dependent D2.
  (typing_cases (induction TYP) Case); 
    intros DX PERM; eauto.
  Case "typing_unvar".
    inversion PERM; subst; auto.
  Case "typing_linvar".
    inversion PERM; subst.
    inversion H4; subst.
    destruct DL; destruct DR; subst; simpl_env in *;
      try solve [inversion H0].
      apply typing_linvar; auto.
  Case "typing_abs".
    pick fresh x and apply typing_abs; auto.
      intros. lapply H2; intros; auto. subst.
      inversion PERM; auto.
  Case "typing_labs".
    pick fresh x and apply typing_labs; auto.
      apply (H1 x); auto.
        rewrite_env (lempty ++ [(x, lbind_typ T1)] ++ DX).
        apply permute_cons; auto.
        intros. lapply H2; intros; auto. subst. 
        inversion PERM; auto.
  Case "typing_app".
    assert (exists D1P, exists D2P,
      permute D1 D1P /\
      permute D2 D2P /\
      lenv_split D1P D2P DX) as J.
      eapply lenv_split_exists_permute; eauto.
    destruct J as [D1P [D2P [PERM2 [PERM3 S]]]].
    apply (typing_app T1 K D1P D2P DX); auto.
  Case "typing_tabs".
    pick fresh X and apply typing_tabs; eauto.
Qed.
(* Change : No typing context *)

(** The linear context is unordered. *)
Lemma typing_split: forall D3 e T D1 D2,
  typing (D1 ++ D2) e T ->
  lenv_split D1 D2 D3 ->
  typing D3 e T.
Proof.
  intros.
  apply (typing_permute (D1 ++ D2) D3); auto.
    apply permute_sym; eauto.
      apply eq_lbinding_dec.
      eapply lenv_split_permute; eauto.
Qed.
(* Change : No typing context *)

(** The linear context is empty for non-linear kind term. *)
Lemma value_nonlin_inversion: forall D e T,
  typing D e T ->
  value e ->
  wf_typ T kn_nonlin ->
  D = lempty.
Proof.
  intros D e T Typ.
  (typing_cases (induction Typ) Case);  
    intros V WFT; 
    try solve [ auto | 
                inversion V |
                inversion WFT; subst; auto].
  Case "typing_tabs".
    inversion V; subst. 
    inversion WFT; subst.
    pick fresh X.
    apply (H1 X); auto.
Qed.
(* Change : No typing context *)

(************************************************************************ *)
(** *** Type substitution preserves typing (11) *)
    
Lemma typing_through_subst_te : forall D alpha ka e T P,
  typing D e T ->
  wf_typ P ka ->
  typing (map (subst_tlb alpha ka P) D) (subst_te alpha ka P e) (subst_tt alpha ka P T).
Proof with simpl_env;
           eauto 6 using wf_typ_subst_tb.
  intros D alpha ka e T P Typ PsubK.
  (typing_cases (induction Typ) Case); simpl subst_te in *; simpl subst_tt in *...
  Case "typing_linvar".
     simpl. apply typing_linvar...
  Case "typing_abs".
    pick fresh y and apply typing_abs...
    rewrite subst_te_open_ee_var...
    intros; rewrite H2; auto.
  Case "typing_labs".
    pick fresh y and apply typing_labs...
    rewrite subst_te_open_ee_var...
    rewrite_env (map (subst_tlb alpha ka P) ([(y, lbind_typ T1)] ++ D)).
    apply H1...
    intros. rewrite H2; auto.
  Case "typing_app".
    eapply typing_app; eauto. 
      eapply lenv_split_subst_tb; eauto.
  Case "typing_tabs".
    pick fresh Y and apply typing_tabs.
      rewrite subst_tt_fresh with (T:= Y ^^ K) (alpha:= alpha) (ka := ka) (U:=P); auto.
      rewrite <- subst_te_open_te; auto.
      apply value_through_subst_te; auto.
        eapply type_from_wf_typ; eauto.
      eapply type_from_wf_typ; eauto.
      erewrite subst_te_open_te_var; eauto using type_from_wf_typ.
      erewrite subst_tt_open_tt_var; eauto using type_from_wf_typ.
  Case "typing_tapp".
    erewrite subst_tt_open_tt...
      eapply type_from_wf_typ; eauto. 
Qed.
(* Change : No typing context. Simplified : 49 lines -> 33 lines. *)

(************************************************************************ *)
(** *** Substitution preserves typing (8) *)

Lemma typing_through_subst_ee_nonlin: forall D e T x xt u,
  typing D e T ->
  typing lempty u xt ->
  x `notin` dom D ->
  typing D (subst_ee x xt u e) T.
Proof.
  intros D e T x xt u H1 H2 H3.
  typing_cases (induction H1) Case.
  Case "typing_unvar".
    simpl. destruct ((x,xt) ==== (X, T)); try inversion e; subst; auto.
  Case "typing_linvar".
    simpl. destruct ((x,xt) ==== (X, T)); try inversion e; subst; auto; contradict H3; simpl; fsetdec.
  Case "typing_abs".
    pick fresh Y and apply typing_abs; auto; rewrite subst_ee_open_ee_var; auto.
  Case "typing_labs".
    pick fresh Y and apply typing_labs; auto; rewrite subst_ee_open_ee_var; auto.
  Case "typing_app".
    rewrite (dom_lenv_split _ _ _ H) in H3.
    eapply typing_app; eauto.
  Case "typing_tabs".
    pick fresh Y and apply typing_tabs; auto;
    lapply (H Y); auto; intros;
    rewrite subst_ee_open_te_var; auto;
    apply value_through_subst_ee; auto.
  Case "typing_tapp".
    pick fresh Y; apply typing_tapp with (K := K); auto; rewrite subst_ee_open_te_var; auto.
  Case "typing_apair".
    pick fresh Y; apply typing_apair; auto.
  Case "typing_fst".
    eapply typing_fst; eauto.
  Case "typing_snd".
    eapply typing_snd; eauto.
Qed.
  
Lemma typing_through_subst_ee_lin: forall D2 x U D1 e T F u,
  value u ->
  typing (D2 ++ [(x, lbind_typ U)] ++ D1) e T ->
  typing F u U ->
  wf_lenv (D2 ++ F ++ D1) ->
  typing (D2 ++ F ++ D1) (subst_ee x U u e) T.
Proof.
  intros D2 x U D1 e T F u Value TYP.
  remember (D2 ++ [(x, lbind_typ U)] ++ D1) as D.
  generalize dependent D2. generalize dependent D1.
  (typing_cases (induction TYP) Case);  
    intros DR DL EQ TYPU WFL; subst; simpl_env in *; simpl; eauto.
  Case "typing_unvar".
    destruct DL; inversion EQ.
  Case "typing_linvar".
    destruct DL; inversion EQ; subst. 
    SCase "DL=nil".
      simpl_env in *. simpl.
      destruct ((x, U) ==== (x, U)); tauto.
    SCase "DL=con".
      destruct DL; inversion EQ.
  Case "typing_abs".
    pick fresh y and apply typing_abs; auto.
      rewrite subst_ee_open_ee_var; auto.
      intros. lapply H2; auto. 
      intros. destruct DL; inversion H4.
  Case "typing_labs".
    pick fresh y and apply typing_labs; auto.
      rewrite_env (([(y, lbind_typ T1)] ++ DL) ++ F ++ DR).
      rewrite subst_ee_open_ee_var; auto.
      apply H1; simpl_env; auto. 
      intros. lapply H2; auto. 
      intros. destruct DL; inversion H4.
  Case "typing_app".
    lapply (lenv_split_cases_mid D1 D2 DL x U DR); auto.
    intros C.
    destruct C as [LEFT | RIGHT].
    SCase "left".
      destruct LEFT as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]]; subst.
      lapply (IHTYP1 D1R D1L); auto.
      intros I. 
      assert (x `notin` dom (D2L++D2R)) as J.
        eapply lenv_split_not_in_left; eauto.
          simpl_env. fsetdec.
      lapply I; auto. intros TYPE1.
        apply (typing_app T1 K (D1L ++ F ++ D1R) (D2L ++ D2R)).
          assert (wf_lenv (D1L ++ F ++ D1R)) as JJ.
            eapply wf_lenv_split_left. 
              eapply lenv_split_sub_left; eauto.
          apply TYPE1; auto.
          (* ADD START*)
          destruct (typing_regular F u U TYPU) as [_ [_ Hc]].
          destruct (kn_cases _ _ Hc).
          SSCase " kn_nonlin ".
            rewrite (value_nonlin_inversion F u U TYPU Value H0) in TYPU.
            apply typing_through_subst_ee_nonlin; auto.
          SSCase " ~kn_nonlin ".
            erewrite <- non_subst; eauto.
          (* ADD END*)
          eapply lenv_split_sub_left; eauto.
    SCase "right".
      destruct RIGHT as [D1L [D1R [D2L [D2R [Q1 [Q2 [S1 S2]]]]]]]; subst.
      lapply (IHTYP2 D2R D2L); auto. 
      intros I.
      assert (x `notin` dom (D1L++D1R)) as J.
        eapply lenv_split_not_in_right; eauto.
          simpl_env. fsetdec.
      lapply I; auto. intros TYPE2. 
        apply (typing_app T1 K (D1L ++ D1R) (D2L ++ F ++ D2R)); auto.
          (* ADD START*)
          destruct (typing_regular F u U TYPU) as [_ [_ Hc]].
          destruct (kn_cases _ _ Hc).
          SSCase " kn_nonlin ".
            rewrite (value_nonlin_inversion F u U TYPU Value H0) in TYPU.
            apply typing_through_subst_ee_nonlin; auto.
          SSCase " ~kn_nonlin ".
            erewrite <- non_subst; eauto.
          (* ADD END*)
          assert (wf_lenv (D2L ++ F ++ D2R)) as JJ.
            eapply wf_lenv_split_right. 
              eapply lenv_split_sub_right; eauto.
          apply TYPE2; auto. 
          eapply lenv_split_sub_right; eauto.
  Case "typing_tabs".
    pick fresh X and apply typing_tabs.
      rewrite <- subst_ee_open_te; auto.
      apply value_through_subst_ee; auto.
      rewrite subst_ee_open_te_var; auto.
Qed.
(*  Change : Add one more condition. (value u) *)
    
(* ********************************************************************** *)
(** ** #<a name="preservation"></a># Preservation (20) *)

Lemma preservation : forall D e e' T,
  typing D e T ->
  red e e' ->
  typing D e' T.
Proof with simpl_env; eauto.
  intros D e e' T Typ. 
  generalize dependent e'.
  (typing_cases (induction Typ) Case); 
    intros e' Red; try solve [ inversion Red; subst; eauto ].
  Case "typing_app".
    inversion Red; subst...
    inversion Typ1; subst.
    SCase "typing_abs".
      pick fresh x.
      rewrite (subst_ee_intro x T1); auto.
      assert (D2 = lempty) as J.
        apply (value_nonlin_inversion D2 e2 T1); auto.
      subst D2.
      lapply (H10 x); auto.
        intros H0.
        assert (D1 = D3) as J.
          apply (lenv_split_empty_right D1 D3); auto. 
        subst D1.
        eapply typing_through_subst_ee_nonlin; eauto.
    SCase "typing_labs".
      pick fresh x.
      rewrite (subst_ee_intro x T1); auto.
      apply (typing_split D3 (subst_ee x T1 e2 (open_ee e0 (x ** T1))) T2 D2 D1); auto.
        apply (typing_through_subst_ee_lin lempty x T1 D1); simpl_env; auto.
          eapply wf_lenv_split_both. 
            eapply lenv_split_commute; eauto.
          apply lenv_split_commute; auto.
  Case "typing_tapp".
    inversion Red; subst...
    inversion Typ. subst.
    pick fresh X.
    lapply (H8 X); auto.
      intros.
      rewrite (subst_te_intro X) with (ka := K)...
      rewrite (subst_tt_intro X) with (ka := K)...
      rewrite (subst_tlb_identity D X) with (ka := K) (T := T); eauto.
      apply (typing_through_subst_te )...
  Case "typing_fst".
    inversion Red; subst...
    inversion Typ; subst...
  Case "typing_snd".
    inversion Red; subst...
    inversion Typ; subst...
Qed.
(* Change : No typing context *)


(* ********************************************************************** *)
(** ** #<a name="progress"></a># Progress *)

(* ********************************************************************** *)
(** *** Canonical forms (14) *)

Lemma canonical_form_abs : forall e K U1 U2,
  value e ->
  typing nil e (typ_arrow K U1 U2) ->
  exists K1, exists V, exists e1, (e = exp_abs K1 V e1) /\ (K = kn_nonlin -> K1 = kn_nonlin).
Proof.
  intros e K U1 U2 Val Typ.
  remember lempty as D.
  remember (typ_arrow K U1 U2) as T.
  revert U1 U2 HeqT HeqD.
  (typing_cases (induction Typ) Case); 
    intros U1 U2 EQT EQD; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
  Case "typing_abs".
    inversion EQT. subst. 
    exists K. exists U1. exists e1. tauto.
  Case "typing_labs".
    inversion EQT. subst. 
    exists K. exists U1. exists e1. tauto.
Qed.
(* Change : No typing context *)

Lemma canonical_form_tabs : forall e Q U1,
  value e ->
  typing lempty e (typ_all Q U1) ->
  exists V, exists e1, e = exp_tabs V e1.
Proof.
  intros e Q U1 Val Typ.
  remember (typ_all Q U1) as T.
  revert Q U1 HeqT.
  (typing_cases (induction Typ) Case); 
    intros Q U1 EQT; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
Qed.
(* Change : No typing context *)

Lemma canonical_form_with : forall e U1 U2,
  value e ->
  typing lempty e (typ_with U1 U2) ->
  exists e1, exists e2, e = exp_apair e1 e2.
Proof.
  intros e U1 U2 Val Typ.
  remember (typ_with U1 U2) as T.
  revert U1 U2 HeqT.
  (typing_cases (induction Typ) Case); 
    intros U1 U2 EQT; subst;
    try solve [ inversion Val | inversion EQT | eauto ].
Qed.
(* Change : No typing context *)

(* ********************************************************************** *)
(** *** Progress (16) *)

Lemma progress : forall e T,
  (forall X, X `notin` fv_ee e) ->   (* {} [=] fv_ee e -> *)
  typing lempty e T ->
  value e \/ exists e', red e e'.
Proof with eauto.
  intros e T NotIn Typ.
  remember lempty as D. generalize dependent NotIn.
  generalize dependent HeqD.
  assert (Typ' : typing D e T)... 
  (typing_cases (induction Typ) Case); intros EQD XNotIn; subst...
  Case "typing_unvar".
    elim (XNotIn X). simpl; auto.
  Case "typing_linvar".
    inversion EQD.
  Case "typing_app".
    right.
    inversion H; subst.
    simpl in XNotIn.
    destruct IHTyp1 as [Val1 | [e1' Rede1']]... intros X. remember (XNotIn X). fsetdec.
    SCase "Val1".
      destruct IHTyp2 as [Val2 | [e2' Rede2']]... intros X. remember (XNotIn X). fsetdec.
      SSCase "Val2".
        destruct (canonical_form_abs _ _ _ _ Val1 Typ1) as [K1 [S [e3 [EQE EQK]]]]; subst.
        exists (open_ee e3 e2)...
  Case "typing_tapp".
    right.
    destruct IHTyp as [Val1 | [e1' Rede1']]...
    SCase "Val1".
      destruct (canonical_form_tabs _ _ _ Val1 Typ) as [S [e3 EQ]]; subst.
      exists (open_te e3 T)...
      apply red_tabs; eauto. eapply type_from_wf_typ; eauto.
    SCase "e1' Rede1'".
      exists (exp_tapp e1' T)...
      apply red_tapp; eauto using type_from_wf_typ.
  Case "typing_fst".
    right.
    destruct IHTyp as [Val | [e' Rede']]...
    SCase "Val".
      destruct (canonical_form_with _ _ _ Val Typ) as [e1 [e2 EQE]]; subst.
      apply value_regular in Val. inversion Val; subst.
      exists e1...
  Case "typing_snd".
    right.
    destruct IHTyp as [Val | [e' Rede']]...
    SCase "Val".
      destruct (canonical_form_with _ _ _ Val Typ) as [e1 [e2 EQE]]; subst.
      apply value_regular in Val. inversion Val; subst.
      exists e2...
Qed.
(* Change : typing context *)
