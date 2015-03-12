(** Beginning of the file for CP mechanisation as described in

    Philip Wadler. 2012. Propositions as sessions. In Proceedings of the 17th
    ACM SIGPLAN international conference on Functional programming (ICFP '12).
    ACM, New York, NY, USA, 273-286. DOI=10.1145/2364527.2364568
    http://doi.acm.org/10.1145/2364527.2364568

*)
Require Import Metatheory.Metatheory CP_Definitions.
Require Import Coq.Sorting.Permutation.

Set Implicit Arguments.

Hint Resolve eq_nat_dec.

Section CPPropProperties.

  Lemma eq_pvar_dec : forall (x y : pvar), sumbool (x = y) (x <> y).
  Proof. decide equality. Qed.


  Lemma eq_prop_dec: forall (x y : prop), sumbool (x = y) (x <> y).
  Proof. decide equality; auto using eq_pvar_dec. Qed.

  Global Instance EqDec_prop : @EqDec_eq prop.
  Proof. exact eq_prop_dec. Defined.

  Lemma prop_dual_involutive:
    forall A, A = ¬(¬A).
  Proof.
    induction A; simpl; f_equal; auto.
  Qed.

  Lemma prop_eq_dual:
    forall A (EQ: A = ¬A),
      False.
  Proof. ii; induction A; ss; tryfalse. Qed.

  Lemma prop_dual_self:
    forall A, dual_props A (¬A).
  Proof. induction A; ss; eauto. Qed.

  Lemma prop_dual_equiv_dual_props:
    forall A dA (DUA: dual_props A dA), dA = ¬A.
  Proof. ii; induction DUA; subst; auto using prop_dual_involutive. Qed.

  Lemma dual_props_equiv_prop_dual:
    forall A dA (DUA: dA = ¬A), dual_props A dA.
  Proof. ii. induction A; ss; rewrite DUA; eauto using prop_dual_self. Qed.

  Lemma prop_dual_iff:
    forall A dA, dA = ¬A <-> dual_props A dA.
  Proof.
    ii; split; auto using prop_dual_equiv_dual_props,
               dual_props_equiv_prop_dual.
  Qed.

  Lemma prop_dual_eq:
    forall A B (EQ: ¬A = ¬B), A = B.
  Proof.
    ii; induction A; by rewrite ->prop_dual_iff in EQ; apply dual_sym in EQ
    ; rewrite <-prop_dual_iff in EQ; rewrite <-!prop_dual_involutive in EQ
    ; subst; reflexivity.
  Qed.

  Lemma prop_dual_preserves_subst:
    forall A B X, ¬({{A // X}}B) = {{A // X}}(¬B).
  Proof.
    intros; induction B; simpl; f_equal; auto; destruct p; auto
    ; match goal with
        | |- context[?X == ?Y] => destruct (X == Y)
      end; auto using prop_dual_involutive.
  Qed.

  Lemma prop_dual_preserves_open:
    forall k x A, ¬prop_open_rec k x A = prop_open_rec k x (¬A).
  Proof.
    ii; gen k; induction A; ii; f_equal; auto; destruct p; des; auto.
  Qed.

  Lemma prop_dual_open_prop:
    forall x A, ¬open_prop A x = open_prop (¬A) x.
  Proof.
    ii; rewrite /open_prop prop_dual_preserves_open; auto.
  Qed.

End CPPropProperties.

Section CPBasicSubstOpenProperties.

  Lemma open_rec_same :
    forall t j v i u
           (NEQ: i <> j)
           (EQ: {i ~> u}({j ~> v} t) = {j ~> v} t),
      {i ~> u} t = t.
  Proof.
    induction t; ii; des; substs; tryfalse; f_equal; inv EQ; firstorder.
  Qed.

  Lemma open_rec_comm:
    forall t j v i u
           (NEQ: i <> j),
      {i ~> u}({j ~> v} t) = {j ~> v} ({i ~> u}t).
  Proof.
    induction t; ii; destruct_all pname; des; subst
    ; solve [exfalso; auto
            |f_equal; firstorder].
  Qed.    

  Lemma lc_no_bvar:
    forall t u k
           (LC: lc_proc t),
      {k ~> u}t = t.
  Proof.
    ii; generalize dependent k; induction LC; s; ii; f_equal; auto
    ; try (by unfold open_proc in *; pick fresh z for L
           ; apply open_rec_same with (j := 0)(v := z); auto).
  Qed.

  Lemma lc_open_subst:
    forall t u (x y: atom) k
           (NEQ: x <> y),
      {k ~> y} ([x ~> u]t) = [x ~> u]({k ~> y} t).
  Proof.
    ii; unfold open_proc; generalize dependent k.
    induction t; by ii; destruct_all pname; des; subst; f_equal; auto.
  Qed.

  Lemma subst_fresh:
    forall (x:atom) u t
           (NIN: x `notin` fv_proc t),
      [x ~> u]t = t.
  Proof.
    induction t; ii; try (destruct_all pname; des; subst; f_equal
                          ; solve [auto | fsetdec]).
  Qed.

  Lemma subst_open_rec:
    forall P x y k,
      [y ~> x] ({k ~> y} P) = {k ~> x} ([y ~> x] P).
  Proof.
    ii; gen k; induction P; ii; destruct_all pname; des; tryfalse
    ; f_equal; auto.
  Qed.

  Lemma subst_open_var :
    forall (x y : atom) u t
           (NEQ: y <> x),
      open_proc ([x ~> u] t) y = [x ~> u] (open_proc t y).
  Proof.
    ii; unfold open_proc; auto using lc_open_subst.
  Qed.

  Lemma subst_intro_open_rec:
    forall x u t k
           (NIN: x `notin` (fv_proc t)),
      {k ~> u} t = [x ~> u]({k ~> x} t).
  Proof.
    ii; gen k; induction t; ii; destruct_all pname; des; substs; f_equal
    ; solve [auto|fsetdec].
  Qed.

  Lemma subst_intro :
    forall (x : atom) u t
           (NIN: x `notin` (fv_proc t)),
      open_proc t u = [x ~> u](open_proc t x).
  Proof.
    ii; unfold open_proc; rewrite~ <-subst_intro_open_rec.
  Qed.

  Lemma subst_id:
    forall (x:atom) t,
      [x ~> x]t = t.
  Proof.
    induction t; ss; try (destruct_all pname; des; substs; f_equal
                          ; solve [auto | fsetdec]).
  Qed.

  Ltac subst_lc_tac Constructor :=
    pick fresh y and apply Constructor; auto
    ; by unfold open_proc in *; rewrite lc_open_subst; auto.

  Lemma subst_lc :
    forall t u x
           (LCT: lc_proc t),
      lc_proc ([ x ~> u ] t).
  Proof.
    ii; induction LCT; s; des; subst; auto
    ; solve [subst_lc_tac lc_p_cut
            |subst_lc_tac lc_p_output
            |subst_lc_tac lc_p_input
            |subst_lc_tac lc_p_accept
            |subst_lc_tac lc_p_request].
  Qed.

End CPBasicSubstOpenProperties.

Section CPSwapBinders.

  Lemma swap_binders_id:
    forall P i,
      {i <~> i} P = P.
  Proof.
    intro; induction P; i; ss; destruct_all pname; des; substs; f_equal; auto.
  Qed.

  Lemma swap_binders_comm:
    forall P i j,
      {i <~> j}P = {j <~> i}P.
  Proof.
    induction P; ii; destruct_all pname; des; substs; tryfalse; f_equal; auto.
  Qed.

  Lemma swap_binders_fv:
    forall P i j,
      fv_proc ({i <~> j}P) = fv_proc P.
  Proof.
    ii; destruct (i == j); substs; [rewrite~ swap_binders_id|]; gen i j.
    induction P; ii; destruct_all pname; des; substs; tryfalse
    ; repeat (f_equal; auto).
  Qed.

  Lemma swap_binders_open_id:
    forall P x i j,
      {i ~> x}({j ~> x}({i <~> j}P)) = {i ~> x}({j ~> x}P).
  Proof.
    ii; destruct (i == j); substs; [rewrite~ swap_binders_id|].
    gen i j; induction P; ii; destruct_all pname; des; substs; tryfalse
    ; f_equal; auto.
  Qed.

  Lemma swap_binders_open:
    forall P x y i j,
      {i ~> x}({j ~> y}({i <~> j}P)) = {j ~> x}({i ~> y}P).
  Proof.
    ii; destruct (i == j); substs; [rewrite~ swap_binders_id|].
    destruct (x == y); substs
    ; [rewrite swap_binders_open_id; rewrite~ open_rec_comm|].
    gen i j; induction P; ii; destruct_all pname; des; substs; tryfalse
    ; f_equal; auto.
  Qed.

End CPSwapBinders.

Section CPAllRequestsProperties.

  Lemma requests_one:
    forall x A, all_requests (x ~ ? A).
  Proof. ii; apply* all_reqs_cons. Qed.

  Lemma requests_app:
    forall xs ys
           (REQXS: all_requests xs)
           (REQYS: all_requests ys),
      all_requests (xs ++ ys).
  Proof with auto.
    induction xs as [|x xs']...
    introv REQXS REQYS; inverts REQXS; simpl_env...
  Qed.

  Lemma requests_inv_app:
    forall xs ys
           (REQS: all_requests (xs++ys)),
      all_requests xs /\ all_requests ys.
  Proof with auto.
    induction xs as [|x xs']...
    ii; inverts REQS; specializes IHxs' REQS0; des; splits; simpl_env...
  Qed.

  Lemma requests_perm:
    forall xs ys
           (PER: Permutation xs ys)
           (REQS: all_requests xs),
      all_requests ys.
  Proof.
    i; induction PER; auto.
    - destruct x; rewrite !cons_app_one; inverts REQS; auto.
    - destruct x; destruct y; rewrite !cons_app_one; inverts REQS
      ; inverts REQS0; auto.
  Qed.

  Lemma requests_binds_cod:
    forall (x:atom) A Ω
           (REQS: all_requests Ω)
           (BNDS: binds x A Ω),
    exists B, A = ? B.
  Proof.
    ii; induction REQS; analyze_binds BNDS; eauto.
  Qed.

End CPAllRequestsProperties.

(** Tactic for destructing all_requests hypotheses. *)
Ltac des_reqs :=
  repeat match goal with
           | [H: all_requests (_ ++ _) |- _] =>
             apply requests_inv_app in H; des
         end.

(** Helpful tactics for solving simple permutations. *)
Ltac bring_to_start X :=
  try (eapply Permutation_trans
       ; [|by repeat first [apply (Permutation_app_comm X _)
                           |apply Permutation_app_head]])
  ; first [apply Permutation_app_head
          |eapply Permutation_trans
           ; [| by repeat first [apply (three_way_perm X)
                                |apply Permutation_app_head]]
           ; bring_to_start X].

Ltac solve_perm :=
  by repeat first [rewrite !app_assoc
                  |rewrite !cons_app_one
                  |match goal with 
                       |- Permutation (?x ++ _) _ => bring_to_start x
                   end].

(** Helpful tactics for handling In predicate destruction. *)

Ltac analyze_in x :=
  match goal with
    | [H: x `in` dom ?E |- _] =>
      let a := fresh "a" in
      let E1 := fresh "E1" in
      let E2 := fresh "E2" in
      let EQ := fresh "EQ" in
      apply in_env_split in H
      ; inversion_clear H as (a & E1 & E2 & EQ)
      ; substs~; des_reqs
  end.

Ltac extract_bnd x A :=
  match goal with
    | [H: Permutation (_++x~A) ?F |- _] =>
      let BNDS := fresh "BNDS" in
      forwards~ BNDS: Perm_binds x A H; analyze_binds_uniq BNDS
      ; try (by applys~ uniq_perm H)
      ; try (match goal with
               | [H: binds x A ?E |- _] =>
                 let E1 := fresh "E1" in
                 let E2 := fresh "E2" in
                 let EQ := fresh "EQ" in
                 apply binds_env_split in H
                 ; inversion_clear H as (E1 & E2 & EQ)
                 ; substs~; des_reqs
             end)
  end.

Section CPPermProperties.

  Lemma perm_dom_uniq:
    forall Γ Δ1 Δ2 x (A B:prop)
           (UN: uniq (Γ++x~A))
           (PER: Permutation (Γ++x~A) (Δ1++x~B++Δ2)),
      Permutation Γ (Δ1++Δ2).
  Proof.
    intros; forwards UN1: uniq_perm PER; [solve_uniq|].
    eapply uniq_perm in UN; [|apply Permutation_app_comm].
    inv UN1; inv UN; destruct (B == A); substs~.
    - rewrite <-H0 in *; apply Permutation_sym,Permutation_nil in PER.
      apply app_eq_nil in PER; des; substs~. eauto.
      rewrite !cons_app_one in *; apply nil_eq_app in H0; des.
      apply app_eq_nil in H3; des; substs~; auto.
    - rewrite <-H0 in *; apply Permutation_sym,Permutation_nil in PER.
      apply app_eq_nil in PER; des; substs~. eauto.
      rewrite !cons_app_one in *; apply nil_eq_app in H0; des.
      apply app_eq_nil in H3; des; substs~.
    - eapply Permutation_trans in PER; [|apply Permutation_app_comm].
      applys~ Permutation_cons_app_inv PER.
    - extract_bnd x A.
  Qed.

  Lemma perm_cod_uniq:
    forall Γ Δ1 Δ2 x (A B:prop)
           (UN: uniq (Γ++x~A))
           (PER: Permutation (Γ++x~A) (Δ1++x~B++Δ2)),
      A = B.
  Proof.
    intros; forwards UN1: uniq_perm PER; [solve_uniq|].
    eapply uniq_perm in UN; [|apply Permutation_app_comm].
    inv UN1; inv UN; destruct (B == A); substs~.
    - rewrite <-H0 in *; apply Permutation_sym,Permutation_nil in PER.
      apply app_eq_nil in PER; des; tryfalse.
    - extract_bnd x A. 
  Qed.

End CPPermProperties.

Section CPFVProperties.

  Lemma open_fv_proc_1:
    forall x y k P
           (NEQ: x <> y)
           (FV: x `in` fv_proc ({k ~> y}P)),
      x `in` fv_proc P.
  Proof.
    i; gen k; induction P; ii; destruct_all pname; des; destruct_in; tryfalse
    ; eauto.
  Qed.

  Lemma open_fv_proc_2:
    forall x y k P
           (FV: x `in` fv_proc P),
      x `in` fv_proc ({k ~> y}P).
  Proof.
    i; gen k; induction P; ii; destruct_all pname; des; destruct_in; eauto.
  Qed.

  Lemma open_nfv_proc_1:
    forall x y k P
           (NEQ: x <> y)
           (NFV: x `notin` fv_proc P),
      x `notin` fv_proc ({k ~> y}P).
  Proof.
    i; gen k; induction P; ii; destruct_all pname; des; destruct_in; eauto.
  Qed.

  Lemma open_nfv_proc_2:
    forall x y k P
           (NFV: x `notin` fv_proc ({k ~> y}P)),
      x `notin` fv_proc P.
  Proof.
    i; gen k; induction P; ii; destruct_all pname; des; destruct_in; eauto.
  Qed.

  Lemma remove_nfv_proc_eq:
    forall P k (x y:atom)
           (NFX: x `notin` fv_proc P)
           (NFY: y `notin` fv_proc P),
      remove y (fv_proc ({k ~> y}P))[=]remove x (fv_proc ({k ~> x}P)).
  Proof.
    induction P; ii; destruct_notin
    ; try (by destruct_all pname; des; destruct_notin; fsetdec).
    - rewrite !remove_union; rewrite~ (IHP1 (S k) x y)
      ; rewrite~ (IHP2 (S k) y x); fsetdec.
    - destruct_all pname; des; destruct_notin; rewrite !remove_union
      ; rewrite~ (IHP1 (S k) x y); rewrite~ (IHP2 k y x); fsetdec.
    - destruct_all pname; des; destruct_notin; rewrite !remove_union
      ; rewrite~ (IHP (S k) x y); fsetdec.
    - destruct_all pname; des; destruct_notin; rewrite !remove_union
      ; rewrite~ (IHP k x y); fsetdec.
    - destruct_all pname; des; destruct_notin; rewrite !remove_union
      ; rewrite~ (IHP k x y); fsetdec.
    - destruct_all pname; des; destruct_notin; rewrite !remove_union
      ; rewrite~ (IHP1 k x y); rewrite~ (IHP2 k y x); fsetdec.
    - destruct_all pname; des; destruct_notin; rewrite !remove_union
      ; rewrite~ (IHP (S k) x y); fsetdec.
    - destruct_all pname; des; destruct_notin; rewrite !remove_union
      ; rewrite~ (IHP (S k) x y); fsetdec.
    - destruct_all pname; des; destruct_notin; rewrite !remove_union
      ; rewrite~ (IHP k x y); fsetdec.
    - destruct_all pname; des; destruct_notin; rewrite !remove_union
      ; rewrite~ (IHP k x y); fsetdec.
  Qed.

End CPFVProperties.

Lemma wt_nin_env:
  forall (Γ Δ:penv) (x:atom)
         (NIN: x `notin` dom Γ)
         (IN: x `in` dom Δ)
         (PER: Permutation Γ Δ),
    False.
Proof.
  ii; apply NIN; analyze_in x; apply Permutation_sym in PER
  ; forwards: Perm_in x PER; simpl_env; fsetdec.
Qed.

Hint Resolve eq_pvar_dec eq_prop_dec.

Hint Resolve requests_one requests_app.

Hint Resolve open_fv_proc_1 open_fv_proc_2 open_nfv_proc_1 open_nfv_proc_2.