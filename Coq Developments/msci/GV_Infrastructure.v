(** Beginning of the file for GV infrastructure. *)
Require Import Metatheory Coq.Program.Tactics Program.Equality.
Require Import GV_Definitions.

Set Implicit Arguments.

Lemma eq_kind_dec: forall (x y : kind), sumbool (x = y) (x <> y).
Proof. decide equality. Qed.

Hint Resolve eq_kind_dec.

Instance EqDec_kind : @EqDec_eq kind.
Proof. exact eq_kind_dec. Defined.

(** Uses heterogeneous equality but I believe this to be sound. *)
Lemma eq_typ_dec: forall {k} (x y : typ k),
  sumbool (x = y) (x <> y).
Proof. 
  ii; generalize dependent y; dependent induction x
  ; dependent destruction y; auto; try (by right; ii; discriminate).
  - destruct (k == k0) as [KEQ|]
    ; [symmetry in KEQ; subst
      |right; ii; inversion H; inversion H2; congruence].
    specialize (IHx1 y1); specialize (IHx2 y2); destruct IHx1; destruct IHx2
    ; try (by right; ii; inversion H; repeat simpl_existT; congruence).
    left; congruence.
  - destruct (k == k0) as [KEQ|]
    ; [symmetry in KEQ; subst
      |right; ii; inversion H; inversion H2; congruence].
    specialize (IHx1 y1); specialize (IHx2 y2); destruct IHx1; destruct IHx2
    ; try (by right; ii; inversion H; repeat simpl_existT; congruence).
    left; congruence.
  - specialize (IHx1 y1); specialize (IHx2 y2); destruct IHx1; destruct IHx2
    ; try (by right; ii; inversion H; repeat simpl_existT; congruence).
    left; congruence.
  - specialize (IHx1 y1); specialize (IHx2 y2); destruct IHx1; destruct IHx2
    ; try (by right; ii; inversion H; repeat simpl_existT; congruence).
    left; congruence.
  - destruct (kt == kt0) as [KEQ|]
    ; [symmetry in KEQ; subst
      |right; ii; inversion H; inversion H2; congruence].
    destruct (ku == ku0) as [KEQ|]
    ; [symmetry in KEQ; subst
      |right; ii; inversion H; inversion H2; congruence].
    specialize (IHx1 y1); specialize (IHx2 y2); destruct IHx1; destruct IHx2
    ; try (by right; ii; inversion H; repeat simpl_existT; congruence).
    left; congruence.
  - destruct (kt == kt0) as [KEQ|]
    ; [symmetry in KEQ; subst
      |right; ii; inversion H; inversion H2; congruence].
    destruct (ku == ku0) as [KEQ|]
    ; [symmetry in KEQ; subst
      |right; ii; inversion H; inversion H2; congruence].
    specialize (IHx1 y1); specialize (IHx2 y2); destruct IHx1; destruct IHx2
    ; try (by right; ii; inversion H; repeat simpl_existT; congruence).
    left; congruence.
  - destruct (kt == kt0) as [KEQ|]
    ; [symmetry in KEQ; subst
      |right; ii; inversion H; inversion H2; congruence].
    destruct (ku == ku0) as [KEQ|]
    ; [symmetry in KEQ; subst
      |right; ii; inversion H; inversion H2; congruence].
    specialize (IHx1 y1); specialize (IHx2 y2); destruct IHx1; destruct IHx2
    ; try (by right; ii; inversion H; repeat simpl_existT; congruence).
    left; congruence.
Qed.

Instance EqDec_typ {k}: @EqDec_eq (typ k).
Proof. exact eq_typ_dec. Defined.

(** Following ``Engineering Formal Metatheory'', we need some properties
    regarding opening and substitution w.r.t locally closed terms.
*)
Section GVBasicSubstOpenProperties.

  (* try to solve some proof obligations related to vars. *)
  Ltac vcrush :=
    destruct_all var; des; ss; des; try easy.

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

  Lemma lc_no_bvar:
    forall t u k
           (LC: lc t),
      {k ~> u}t = t.
  Proof.
    ii; generalize dependent k; induction LC; s; ii; f_equal; auto
    ; try (by unfold open in *; pick fresh x for L
           ; apply open_rec_same with (j := 0)(v := x); auto).
    Case "let".
      unfold open in *; pick fresh x for L; pick fresh y for L'.
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
      pick fresh y and apply lc_abs.
      unfold open in *; rewrite lc_open_subst; auto.
    Case "let".
      (* TODO: tactic for introducing list of fresh variables. *)
      apply lc_let with (L' := L `union` L' `union` singleton x)
                          (L := L `union` L' `union` singleton x); ii; auto.
      unfold open in *; rewrite !lc_open_subst; auto.
    Case "case".
      pick fresh y and apply lc_case; auto
      ; by unfold open in *; rewrite lc_open_subst; auto.
    Case "connect".
      pick fresh y and apply lc_connect; unfold open in *
      ; rewrite lc_open_subst; auto.
  Qed.

End GVBasicSubstOpenProperties.
