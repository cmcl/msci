(** Beginning of the file for GV infrastructure. *)
Require Import Metatheory Coq.Program.Tactics Program.Equality.
Require Import GV_Definitions.

Set Implicit Arguments.

Lemma eq_kind_dec: forall (x y : kind), sumbool (x = y) (x <> y).
Proof. decide equality. Qed.

Hint Resolve eq_kind_dec.

Instance EqDec_kind : @EqDec_eq kind.
Proof. exact eq_kind_dec. Defined.

Lemma eq_typ_dec: forall (x y : typ), sumbool (x = y) (x <> y).
Proof. decide equality. Qed.

Instance EqDec_typ : @EqDec_eq typ.
Proof. exact eq_typ_dec. Defined.

(* Try to solve some proof obligations related to vars. *)
Ltac vcrush :=
  destruct_all var; des; ss; des; try easy.

(** Following ``Engineering Formal Metatheory'', we need some properties
    regarding opening and substitution w.r.t locally closed terms.
*)
Section GVBasicSubstOpenProperties.

  Lemma open_rec_same :
    forall t j v i u
           (NEQ: i <> j)
           (EQ: {i ~> u}({j ~> v} t) = {j ~> v} t),
      {i ~> u} t = t.
  Proof.
    induction t; ii; ss; auto
    ; try (by f_equal; inversion EQ; firstorder)
    ; des; auto.
    - subst n; exfalso; auto.
    - subst n; ss; destruct (i == i); auto; []; exfalso; auto.
  Qed.

  Lemma open_var_rec_comm:
    forall t j i (u v:atom)
           (NEQ: i <> j),
      {i ~> u}({j ~> v} t) = {j ~> v} ({i ~> u}t).
  Proof.
    induction t; ii; vcrush; tryfalse; f_equal; firstorder.
  Qed.

  Lemma lc_no_bvar:
    forall t u k
           (LC: lc t),
      {k ~> u}t = t.
  Proof.
    ii; generalize dependent k; induction LC; s; ii; f_equal; auto
    ; try (by unfold open in *; pick fresh x for L
           ; apply open_rec_same with (j := 0)(v := x); auto).
    Case "let".
      unfold open in *; pick fresh x for L; pick fresh y.
      apply open_rec_same with (j := 0)(v := y); auto.
      apply open_rec_same with (j := 1)(v := x); auto.
  Qed.

  Lemma lc_open_subst:
    forall t u (x y: atom) k
           (NEQ: x <> y)
           (LCU: lc u),
      {k ~> y} ([x ~> u]t) = [x ~> u]({k ~> y} t).
  Proof.
    ii; unfold open; generalize dependent k.
    induction t; ii; f_equal; auto.
    vcrush; auto using lc_no_bvar.
  Qed.

  Lemma subst_eq_var:
    forall (x : atom) u,
      [x ~> u]x = u.
  Proof.
    ii; des; auto.
  Qed.

  Lemma subst_neq_var :
    forall (x y : atom) u,
      y <> x -> [x ~> u]y = y.
  Proof.
    ii; des; auto; []; exfalso; auto.
  Qed.

  Lemma subst_open_rec :
    forall t1 t2 u (x : atom) k,
      lc u ->
      [x ~> u] ({k ~> t2} t1) = {k ~> [x ~> u] t2} ([x ~> u] t1).
  Proof.
    induction t1; ii; try (by f_equal; eauto).
    vcrush; symmetry; auto using lc_no_bvar.
  Qed.

  Lemma subst_open_var :
    forall (x y : atom) u t
           (NEQ: y <> x)
           (LC: lc u),
      open ([x ~> u] t) y = [x ~> u] (open t y).
  Proof.
    ii; unfold open; auto using lc_open_subst.
  Qed.

  Lemma subst_intro :
    forall (x : atom) u t
           (NIN: x `notin` (GVFV t)),
      open t u = [x ~> u](open t x).
  Proof.
    ii; unfold open; generalize 0.
    induction t; intros bv; ss; try (solve [f_equal; eauto]).
    - vcrush; apply notin_singleton_1 in NIN; tryfalse. 
    - destruct_all var; f_equal; eauto.
  Qed.

  Lemma subst_lc :
    forall t u x
           (LCT: lc t)
           (LC: lc u),
      lc ([ x ~> u ] t).
  Proof.
    ii; induction LCT; simpl; auto.
    Case "lc_id".
      ss; destruct (x == x0); subst; eauto.
    Case "lc_abs".
      pick fresh y and apply lc_abs; eauto.
      unfold open in *; rewrite lc_open_subst; auto.
    Case "let".
      obtain atoms L' as LEQ.
      apply lc_let with (L:=L'); ii; substs; destruct_notin; auto.
      unfold open in *; rewrite !lc_open_subst; auto.
      apply H; fsetdec.
    Case "case".
      pick fresh y and apply lc_case; auto
      ; by unfold open in *; rewrite lc_open_subst; auto.
    Case "connect".
      pick fresh y and apply lc_connect; auto; unfold open in *
      ; rewrite lc_open_subst; auto.
  Qed.

End GVBasicSubstOpenProperties.

Section GVFVProperties.

  Lemma open_fv_proc_1:
    forall x y k M
           (NEQ: x <> y)
           (FV: x `in` GVFV ({k ~> y}M)),
      x `in` GVFV M.
  Proof.
    i; gen k; induction M; ii; destruct_all var; des; ss; destruct_in
    ; tryfalse; eauto.
  Qed.

  Lemma open_fv_proc_2:
    forall x y k M
           (FV: x `in` GVFV M),
      x `in` GVFV ({k ~> y}M).
  Proof.
    i; gen k; induction M; ii; destruct_all var; des; ss; destruct_in
    ; eauto.
  Qed.

  Lemma open_nfv_proc_1:
    forall x y k M
           (NEQ: x <> y)
           (NFV: x `notin` GVFV M),
      x `notin` GVFV ({k ~> y}M).
  Proof.
    i; gen k; induction M; ii; destruct_all var; des; ss; destruct_in; eauto.
  Qed.

  Lemma open_nfv_proc_2:
    forall x y k M
           (NFV: x `notin` GVFV ({k ~> y}M)),
      x `notin` GVFV M.
  Proof.
    i; gen k; induction M; ii; destruct_all var; des; ss; destruct_in; eauto.
  Qed.

End GVFVProperties.
