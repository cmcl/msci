(** A duality function that commutes with unfold - Giovanni Bernardi *)

Require Import Metatheory Tactics List Coq.Program.Tactics.
Require Import ssreflect.
Set Implicit Arguments.

(* Language of session types. *)
Inductive STyp : Set :=
  | fvar : atom -> STyp
  | bvar : nat -> STyp
  | REC : STyp -> STyp (* Special constructor for notation. *)
  | styp_out : STyp -> STyp -> STyp
  | styp_in : STyp -> STyp -> STyp
  | END : STyp. (* Special constructor for notation. *)

Coercion bvar: nat >-> STyp.
Coercion fvar: atom >-> STyp.

(** The notation for sessions has been altered from the standard presentation
    to fit within allowable notations in Coq.
*)
Notation "'!' T '#' S" := (styp_out T S) (at level 68, right associativity).
Notation "'?' T '#' S" := (styp_in T S) (at level 68, right associativity).

(** Free variables *)
Fixpoint FV (L : STyp) : atoms :=
  match L with
  | fvar x => singleton x
  | ! T # U
  | ? T # U
    => FV T `union` FV U
  | REC T => FV T
  | _ => empty
  end.

(* A session type expression is closed in FV is empty. *)

(* Capture avoiding substitution can be defined thusly: *)
Fixpoint subst (S: STyp) (x: atom) (T: STyp) :=
  match T with
  | fvar y => if x == y is left _ then S else T
  | ! T' # S' => ! (subst S x T') # (subst S x S')
  | ? T' # S' => ? (subst S x T') # (subst S x S')
  | REC T' => REC (subst S x T')
  | _ => T
  end.

Notation "[ x ~> u ] T" := (subst u x T) (at level 68, right associativity).

Fixpoint open_typ (U: STyp) (k: nat) (T: STyp) :=
  match T with
  | bvar n => if k == n is left _ then U else T
  | ! T' # S' => ! (open_typ U k T') # (open_typ U k S')
  | ? T' # S' => ? (open_typ U k T') # (open_typ U k S')
  | REC T' => REC (open_typ U (S k) T')
  | _ => T
  end.

Definition open T U := open_typ U 0 T.

(* Guarded recursion variable. *)
Inductive GRV : nat -> STyp -> Prop :=
  | grv_outl : forall X T (GX: GRV X T), GRV X (! X # T)
  | grv_outr : forall X T (GX: GRV X T), GRV X (! T # X)
  | grv_out : forall X S T (GXS: GRV X S) (GXT: GRV X T),
                GRV X (! T # S)
  | grv_inl : forall X T (GX: GRV X T), GRV X (? X # T)
  | grv_inr : forall X T (GX: GRV X T), GRV X (? T # X)
  | grv_in : forall X S T (GXS: GRV X S) (GXT: GRV X T),
               GRV X (? T # S)
  | grv_rec : forall X T (GX: GRV (S X) T) (GT: GRV 0 T),
                GRV X (REC T)
  | grv_end : forall X, GRV X END
  | grv_neq : forall X Y (NEQ: X <> Y), GRV X Y.

Hint Constructors GRV.

Inductive guarded : STyp -> Prop :=
  | grd_rec : forall T (GT: GRV 0 T),
                guarded (REC T)
  | grd_out : forall S T (GS: guarded S) (GT: guarded T),
                guarded (! T # S)
  | grd_in : forall S T (GS: guarded S) (GT: guarded T),
               guarded (? T # S)
  | grd_end : guarded END.

Hint Constructors guarded.

Example not_guarded : ~ guarded (REC 0).
Proof. ii; inv H; inv GT; auto. Qed.

Definition T := REC 0.
Example not_guarded_2 : ~ guarded (? END # T).
Proof. ii; inv H; auto using not_guarded. Qed.

Definition problem_rec := REC (REC (? 0 # 1)).
Example problem_rec_guarded: guarded problem_rec.
Proof. unfold problem_rec; auto. Qed.

Inductive closed: STyp -> Prop :=
  | closed_fvar: forall x, closed (fvar x)
  | closed_out: forall S T (CS: closed S) (CT: closed T),
                  closed (! T # S)
  | closed_in : forall S T (CS: closed S) (CT: closed T),
                  closed (? T # S)
  | closed_rec : forall (L:atoms) T (CT: forall (x:atom) (NL: x `notin` L),
                                           closed (open T x)),
                   closed (REC T)
  | closed_end : closed END.

Hint Constructors closed.

Reserved Notation "T `sunfold` U" (at level 68, right associativity).

Inductive sunfold : STyp -> STyp -> Prop :=
  | sunfold_rec : forall S S' (UNF: (open S (REC S)) `sunfold` S'),
                    (REC S) `sunfold` S'
  | sunfold_id : forall S S' (NEQ: S <> REC S'), S `sunfold` S
where "T `sunfold` U" := (sunfold T U).

Hint Constructors sunfold.

(* ``Example 2.1. [ Unfolding a term ]
   Let T = rec X.T', T' = rec Y.?( Y ).X and T'' = rec Y.?( Y ).T.
   In this example we show that unfold (T) =?( T'' ).T . Since
   unfold is a function, it suffices to derive T unfold ?( T'' ).T by
   instantiating the inference rules in (U) above.The derivation
   tree is the one on the right.''
*)
Definition T2' := REC (? 0 # 1).
Definition T2 := REC T2'.
Definition T2'' := REC (? 0 # T2).

Example twopointone : T2 `sunfold` (? T2'' # T2).
Proof.
  rewrite {1}/T2 / T2'; apply sunfold_rec; rewrite /open /open_typ; ss.
  apply sunfold_rec; rewrite /open /open_typ; ss; rewrite -/T2 -/T2''.
  apply sunfold_id with (S' := END); ii; discriminate.
Qed.