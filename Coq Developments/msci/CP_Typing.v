(** Beginning of the file for CP mechanisation as described in

    Philip Wadler. 2012. Propositions as sessions. In Proceedings of the 17th
    ACM SIGPLAN international conference on Functional programming (ICFP '12).
    ACM, New York, NY, USA, 273-286. DOI=10.1145/2364527.2364568
    http://doi.acm.org/10.1145/2364527.2364568

*)
Require Import Metatheory.Metatheory CP_Definitions CP_Infrastructure.
Require Import Coq.Sorting.Permutation.

Set Implicit Arguments.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * prop) => dom x) in
  let D := gather_atoms_with (fun x : proc => fv_proc x) in
  constr:(A `union` B `union` C `union` D).

(** Helper tactic to obtain all the atoms in the context of a goal. *)
Tactic Notation
  "obtain" "atoms" ident(atoms_name) "as" ident(H)
   :=    
     let L := gather_atoms in
     let L := beautify_fset L in
     set (atoms_name:=L); def_to_eq atoms_name H L.

Lemma cp_implies_uniq: forall Γ P
    (CP: P ⊢cp Γ),
  uniq Γ.
Proof.
  ii; induction CP; auto; try (by destruct_uniq; eauto)
  ; by pick fresh y; destruct_notin; specializes H Fr; destruct_uniq
  ; eauto.
Qed.

Lemma ignore_env_order: forall Γ Δ P
    (INB: Permutation Γ Δ)
    (WT: P ⊢cp Γ),
  P ⊢cp Δ.
Proof.
  ii; gen Δ; induction WT; ii; try (by econstructor; ss; eauto).
  - apply Permutation_length_1_inv in INB; substs; simpl_env; auto.
  - apply Permutation_length_1_inv in INB; substs; simpl_env; auto.
Qed.

Lemma typing_weaken:
  forall Γ Δ E P xs
         (WT: P ⊢cp Γ ++ E) (UN: uniq(Γ ++ Δ ++ E))
         (FVC: forall x, x `in` dom Δ <-> In x xs)
         (NDUP: NoDupA Logic.eq xs)
         (REQS: all_requests Δ),
    weakenv xs P ⊢cp Γ ++ Δ ++ E.
Proof.
  i; gen Γ Δ E P; induction xs as [|x xs]; ii.
  - destruct Δ; auto; destruct p as [y a]; specializes FVC y; des;ss;fsetdec.
  - forwards FVX: FVC x; des; exploit FVX1; auto; ii.
    analyze_in x.
    rewrite <-!app_assoc,app_assoc.
    eapply ignore_env_order
    ; [apply Permutation_app_head; apply Permutation_app_comm|].
    simpl_env in *; inverts REQS2.
    apply cp_weaken with (A:=A)(Δ:=Γ++E1++E2++E)
    ; [solve_perm|applys uniq_perm UN;solve_perm|].
    rewrite <-(app_assoc E1); apply~ IHxs; [| |solve_uniq]; inv NDUP; auto.
    ii; simpl_env in *; specializes FVC x0; rewrite !dom_app in *; des; ii.
    + destruct_in; analyze_in x0; rewrite !dom_app in *; ss.
      { exploit FVC0; [fsetdec|].
        ii; destruct_in; auto; []
        ; subst; destruct_uniq; solve_notin; solve_uniq. }
      { exploit FVC0; [fsetdec|].
        ii; des; auto; []; subst; destruct_uniq; solve_notin; solve_uniq. }
    + destruct (x == x0); [apply InA_iff_In in H; subst; ss; tryfalse|].
      specialize (FVC1 (or_intror H)); destruct_in; auto; tryfalse.
Qed.

Lemma in_env_fv_1:
  forall P Γ x
         (WT: P ⊢cp Γ)
         (IN: x `in` dom Γ),
    x `in` fv_proc P.
Proof.
  ii; induction WT.
  - forwards IN2: Perm_in PER IN; ss; fsetdec.
  - pick fresh y; destruct_notin; specializes H Fr; specializes H0 Fr; s; des.
    forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in.
    + exploit H; [fsetdec|]; []; ii; apply open_fv_proc_1 in H; auto.
    + exploit H0; [fsetdec|]; []; ii; apply open_fv_proc_1 in H0; auto.
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
    exploit H; [fsetdec|]; ii; apply open_fv_proc_1 in H; auto.
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
    exploit H; [fsetdec|]; ii; apply open_fv_proc_1 in H; auto.
  - forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
  - forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
  - forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
    exploit H; [fsetdec|]; ii; apply open_fv_proc_1 in H; auto.
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
    exploit H; [fsetdec|]; ii; apply open_fv_proc_1 in H; auto.
  - forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
  - ss; fsetdec.
  - forwards IN2: Perm_in PER IN; rewrite !dom_app in *; destruct_in
    ; try (by ss; fsetdec).
  - ss; fsetdec.
Qed.

Lemma in_env_fv_2:
  forall P Γ x
         (WT: P ⊢cp Γ)
         (IN: x `in` fv_proc P),
    x `in` dom Γ.
Proof.
  ii; induction WT.
  - apply Permutation_sym in PER; applys Perm_in PER; ss; fsetdec.
  - pick fresh y; destruct_notin; specializes H Fr; specializes H0 Fr; des; i.
    apply Permutation_sym in PER; applys Perm_in PER; ss
    ; rewrite !dom_app in *; destruct_in.
    + apply (open_fv_proc_2 y 0) in IN0; fsetdec.
    + apply (open_fv_proc_2 y 0) in IN1; fsetdec.
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    apply Permutation_sym in PER; applys Perm_in PER; ss
    ; rewrite !dom_app in *; destruct_in; try (by ss; fsetdec).
    apply (open_fv_proc_2 y 0) in IN0; fsetdec.
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
    apply (open_fv_proc_2 y 0) in IN1; fsetdec.
  - apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
  - apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
  - apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
    apply (open_fv_proc_2 y 0) in IN1; fsetdec.
  - pick fresh y; destruct_notin; specializes H Fr; s; des.
    apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
    apply (open_fv_proc_2 y 0) in IN1; fsetdec.
  - apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
  - ss; fsetdec.
  - apply Permutation_sym in PER; applys Perm_in PER; ss
    ; destruct_in; try (by ss; fsetdec).
  - ss; fsetdec.
Qed.

Lemma in_env_fv:
  forall P Γ x
         (WT: P ⊢cp Γ),
    x `in` dom Γ <-> x `in` fv_proc P.
Proof. ii; split; eauto using in_env_fv_1,in_env_fv_2. Qed.

Lemma nfv_env_proc_1:
  forall Γ P x
         (WT: P ⊢cp Γ)
         (NIN: x `notin` dom Γ),
    x `notin` fv_proc P.
Proof. ii; eauto using in_env_fv_2. Qed.

Lemma nfv_env_proc_2:
  forall Γ P x
         (WT: P ⊢cp Γ)
         (NIN: x `notin` fv_proc P),
    x `notin` dom Γ.
Proof. ii; eauto using in_env_fv_1. Qed.

Lemma nfv_env_proc:
  forall Γ P x
         (WT: P ⊢cp Γ),
    x `notin` dom Γ <-> x `notin` fv_proc P.
Proof. i; split; eauto using nfv_env_proc_1,nfv_env_proc_2. Qed.

Lemma cp_implies_lc:
  forall P Γ
         (WT: P ⊢cp Γ),
    lc_proc P.
Proof.
  ii; induction WT; eauto
  ; pick fresh y; destruct_notin; specializes H Fr; eauto.
Qed.

Lemma typing_subst_fwd:
  forall Γ w x y z A B
         (UNY: uniq (Γ ++ y ~ A))
         (UNX: uniq (Γ ++ z ~ A))
         (PER: Permutation (Γ ++ z ~ A) (w ~ ¬B ++ x ~ B)),
    [z ~> y](w ⟷ x) ⊢cp Γ ++ y ~ A.
Proof.
  ii; des; substs.
  - apply uniq_perm in PER; auto; []; inv PER; ss; substs; fsetdec.
  - rewrite cons_app_one in PER; rewrite <- app_nil_l in PER
    ; forwards EQ: perm_cod_uniq PER; apply perm_dom_uniq in PER; substs~.
    apply cp_fwd with (A:=B); first [auto|solve_uniq].
    eapply Permutation_trans; [apply Permutation_app|]; [exact PER|auto|].
    solve_perm.
  - rewrite <- app_nil_r in PER; rewrite cons_app_one,app_assoc in PER.
    forwards EQ: perm_cod_uniq PER; apply perm_dom_uniq in PER; substs~.
    apply cp_fwd with (A:=B); first [auto|solve_uniq].
  - simpl_env in *; apply Perm_in with (x:=z) in PER; rewrite !dom_app in *
    ; ss; fsetdec.
Qed.

Lemma typing_subst:
  forall Γ P (x y:atom) A
         (NINX: uniq (Γ ++ y ~ A))
         (WT: P ⊢cp Γ ++ (x ~ A)),
    [x ~> y]P ⊢cp Γ ++ (y ~ A).
Proof.
  ii; destruct (x == y); substs; [by rewrite subst_id|].
  remember (Γ++x~A) as Γ'; assert (PER: Permutation Γ' (Γ++x~A)) by substs~.
  clear HeqΓ'; gen A Γ; induction WT; i; substs; auto.
  - applys* typing_subst_fwd.
  - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
    forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
    ; forwards~ BNDS: Perm_binds x A0 PER.
    extract_bnd x A0; [rewrite !app_assoc in *|rewrite <-app_assoc in *]
    ; apply perm_dom_uniq in PER; auto; s; obtain atoms L' as LEQ.
    + eapply cp_cut with (L:=L')(ΔP:=E1++E2++y~A0)(ΔQ:=ΔQ)
      ; ii; substs; auto; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { rewrite~ subst_open_var; rewrite cons_app_one.
        rewrite <-!app_assoc; apply~ H; rewrite !app_assoc; try solve_perm.
        apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX.
        destruct_uniq; solve_uniq. }
      { specializes CPQ NL; forwards FV: nfv_env_proc_1 x CPQ; [solve_notin|].
        rewrite* subst_fresh. }
    + eapply cp_cut with (L:=L')(ΔP:=ΔP)(ΔQ:=E1++E2++y~A0)
      ; ii; substs; auto; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|].
        solve_perm. }
      { specializes CPP NL; forwards FV: nfv_env_proc_1 x CPP; [solve_notin|].
        rewrite* subst_fresh. }
      { rewrite~ subst_open_var; rewrite cons_app_one.
        rewrite <-!app_assoc; apply~ H0; rewrite !app_assoc; try solve_perm.
        apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX.
        destruct_uniq; solve_uniq. }
  - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
    forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
    ; forwards~ BNDS: Perm_binds x A0 PER.
    extract_bnd x A0; try rewrite !dom_app in *; destruct_notin.
    + s; des; clear H1; rewrite <-app_nil_l in PER
      ; apply perm_dom_uniq in PER; auto; ss; obtain atoms L' as LEQ
      ; eapply cp_output with (L:=L')(ΔP:=ΔP)(ΔQ:=ΔQ); ii; substs; auto
      ; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { specializes CPP NL; forwards~ FV: nfv_env_proc_1 x0 CPP
        ; rewrite* subst_fresh. }
      { rewrite !cons_app_one.
        eapply ignore_env_order; [apply Permutation_app_comm|].
        forwards UNX: uniq_perm_app PER NINX.
        apply~ IHWT; [destruct_uniq; solve_uniq|solve_perm]. }
    + rewrite !app_assoc in *; rewrite <-app_assoc in *.
      apply perm_dom_uniq in PER; auto; ss; obtain atoms L' as LEQ
      ; destruct_notin; destruct (x0 == x); tryfalse.
      clear n0; eapply cp_output with (L:=L')(ΔP:=E1++E2++y~A0)(ΔQ:=ΔQ)
      ; ii; substs; auto; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { rewrite~ subst_open_var; rewrite cons_app_one.
        rewrite <-!app_assoc; apply~ H; rewrite !app_assoc; try solve_perm.
        apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX.
        destruct_uniq; solve_uniq. }
      { rewrite~ subst_fresh; forwards~ FV: nfv_env_proc_1 x WT. }
    + rewrite <-2 app_assoc in *; apply perm_dom_uniq in PER; auto; ss
      ; obtain atoms L' as LEQ; destruct_notin; destruct (x0 == x)
      ; tryfalse.
      clear n0; eapply cp_output with (L:=L')(ΔP:=ΔP)(ΔQ:=E1++E2++y~A0)
      ; ii; substs; auto; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { specializes CPP NL; forwards FV: nfv_env_proc_1 x CPP; [solve_notin|].
        rewrite* subst_fresh. }
      { rewrite cons_app_one; rewrite <-!app_assoc.
        apply~ IHWT; rewrite !app_assoc; try solve_perm.
        apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
        ; destruct_uniq; [solve_uniq|solve_notin]. }
  - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
    forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
    ; forwards~ BNDS: Perm_binds x A0 PER.
    extract_bnd x A0; simpl_env; destruct_notin.
    + s; des; clear H1; rewrite <-app_nil_l in PER
      ; apply perm_dom_uniq in PER; auto; ss; obtain atoms L' as LEQ
      ; eapply cp_input with (L:=L')(ΔP:=ΔP); ii; substs; auto
      ; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { rewrite~ subst_open_var; rewrite !cons_app_one.
        eapply ignore_env_order
        ; [apply Permutation_app|]; [auto|apply Permutation_app_comm|].
        rewrite <-app_assoc; forwards UNX: uniq_perm_app PER NINX.
        apply~ H; [destruct_uniq; solve_uniq|solve_perm]. }
    + rewrite <-app_assoc in *; apply perm_dom_uniq in PER; auto; ss
      ; obtain atoms L' as LEQ; destruct_notin; destruct (x0 == x)
      ; tryfalse.
      clear n0; eapply cp_input with (L:=L')(ΔP:=E1++E2++y~A0)
      ; ii; substs; auto; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { rewrite~ subst_open_var; rewrite !cons_app_one.
        rewrite <-!app_assoc; apply~ H; rewrite !app_assoc; try solve_perm.
        apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX.
        destruct_uniq; solve_uniq. }
  - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
    forwards~ UN2: cp_implies_uniq WT; apply Permutation_sym in PER
    ; forwards~ UN3: uniq_perm PER; [solve_uniq|]
    ; apply Permutation_sym in PER.
    forwards~ BNDS: Perm_binds x A0 PER.
    extract_bnd x A0; simpl_env in *; destruct_notin.
    + s; des; clear H0; rewrite <-app_nil_l in PER
      ; apply perm_dom_uniq in PER; auto; ss; eapply cp_left with (Δ:=Δ)
      ; ii; substs; auto; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { rewrite !cons_app_one.
        eapply ignore_env_order; [apply Permutation_app_comm|].
        forwards UNX: uniq_perm_app PER NINX.
        apply~ IHWT; [destruct_uniq; solve_uniq|solve_perm]. }
    + rewrite <-app_assoc in *; apply perm_dom_uniq in PER; auto; ss
      ; destruct_notin; destruct (x0 == x); tryfalse.
      clear n0; eapply cp_left with (Δ:=E1++E2++y~A0); ii; substs; auto.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { rewrite !cons_app_one; rewrite <-!app_assoc.
        apply~ IHWT; rewrite !app_assoc; try solve_perm.
        apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
        ; destruct_uniq; [solve_uniq|solve_notin]. }
  - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
    forwards~ UN2: cp_implies_uniq WT; apply Permutation_sym in PER
    ; forwards~ UN3: uniq_perm PER; [solve_uniq|]
    ; apply Permutation_sym in PER.
    forwards~ BNDS: Perm_binds x A0 PER.
    extract_bnd x A0; simpl_env in *; destruct_notin.
    + s; des; clear H0; rewrite <-app_nil_l in PER
      ; apply perm_dom_uniq in PER; auto; ss; eapply cp_right with (Δ:=Δ)
      ; ii; substs; auto; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { rewrite !cons_app_one.
        eapply ignore_env_order; [apply Permutation_app_comm|].
        forwards UNX: uniq_perm_app PER NINX.
        apply~ IHWT; [destruct_uniq; solve_uniq|solve_perm]. }
    + rewrite <-app_assoc in *; apply perm_dom_uniq in PER; auto; ss
      ; destruct_notin; destruct (x0 == x); tryfalse.
      clear n0; eapply cp_right with (Δ:=E1++E2++y~A0); ii; substs; auto.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { rewrite !cons_app_one; rewrite <-!app_assoc.
        apply~ IHWT; rewrite !app_assoc; try solve_perm.
        apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
        ; destruct_uniq; [solve_uniq|solve_notin]. }
  - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
    forwards~ UN2: cp_implies_uniq WT1; apply Permutation_sym in PER
    ; forwards~ UN3: uniq_perm PER; [solve_uniq|]
    ; apply Permutation_sym in PER.
    forwards~ BNDS: Perm_binds x A0 PER.
    extract_bnd x A0; simpl_env in *; destruct_notin.
    + s; des; clear H0; rewrite <-app_nil_l in PER
      ; apply perm_dom_uniq in PER; auto; ss; eapply cp_choice with (Δ:=Δ)
      ; ii; substs; auto; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { rewrite !cons_app_one.
        eapply ignore_env_order; [apply Permutation_app_comm|].
        forwards UNX: uniq_perm_app PER NINX.
        apply~ IHWT1; [destruct_uniq; solve_uniq|solve_perm]. }
      { rewrite !cons_app_one.
        eapply ignore_env_order; [apply Permutation_app_comm|].
        forwards UNX: uniq_perm_app PER NINX.
        apply~ IHWT2; [destruct_uniq; solve_uniq|solve_perm]. }
    + rewrite <-app_assoc in *; apply perm_dom_uniq in PER; auto; ss
      ; destruct_notin; destruct (x0 == x); tryfalse.
      clear n0; eapply cp_choice with (Δ:=E1++E2++y~A0); ii; substs; auto.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { rewrite !cons_app_one; rewrite <-!app_assoc.
        apply~ IHWT1; rewrite !app_assoc; try solve_perm.
        apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
        ; destruct_uniq; [solve_uniq|solve_notin]. }
      { rewrite !cons_app_one; rewrite <-!app_assoc.
        apply~ IHWT2; rewrite !app_assoc; try solve_perm.
        apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
        ; destruct_uniq; [solve_uniq|solve_notin]. }
  - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
    forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
    ; forwards~ BNDS: Perm_binds x A0 PER.
    analyze_binds_uniq BNDS; simpl_env in *; destruct_notin.
    + s; des; clear H1; rewrite <-app_nil_l in PER
      ; apply perm_dom_uniq in PER; auto; ss; obtain atoms L' as LEQ
      ; eapply cp_accept with (L:=L')(Δ:=Δ); ii; substs; auto
      ; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { specializes CPP NL; forwards~ FV: nfv_env_proc_1 x0 CPP
        ; rewrite* subst_fresh. }
    + forwards~ EQC: requests_binds_cod BindsTac.
      extract_bnd x A0; inversion_clear EQC as (B); substs; auto.
      rewrite <-app_assoc in *; apply perm_dom_uniq in PER; auto; ss
      ; obtain atoms L' as LEQ; destruct_notin; destruct (x0 == x)
      ; tryfalse; des_reqs.
      clear n0; eapply cp_accept with (L:=L')(Δ:=E1++E2++y~? B); ii
      ; substs; auto; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { rewrite~ subst_open_var; rewrite !cons_app_one; rewrite <-!app_assoc.
        apply~ H; rewrite !app_assoc; try solve_perm.
        apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
        ; destruct_uniq; solve_uniq. }
  - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
    forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
    ; forwards~ BNDS: Perm_binds x A0 PER.
    extract_bnd x A0; simpl_env in  *; destruct_notin.
    + s; des; clear H1; rewrite <-app_nil_l in PER
      ; apply perm_dom_uniq in PER; auto; ss; obtain atoms L' as LEQ
      ; eapply cp_request with (L:=L')(Δ:=Δ); ii; substs; auto
      ; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { specializes CPP NL; forwards~ FV: nfv_env_proc_1 x0 CPP
        ; rewrite* subst_fresh. }
    + rewrite <-app_assoc in *; apply perm_dom_uniq in PER; auto; ss
      ; obtain atoms L' as LEQ; destruct_notin; destruct (x0 == x)
      ; tryfalse; des_reqs.
      clear n0; eapply cp_request with (L:=L')(Δ:=E1++E2++y~A0); ii
      ; substs; auto; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { rewrite~ subst_open_var; rewrite !cons_app_one; rewrite <-!app_assoc.
        apply~ H; rewrite !app_assoc; try solve_perm.
        apply~ uniq_push; forwards UNX: uniq_perm_app PER NINX
        ; destruct_uniq; solve_uniq. }
  - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
    forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
    ; forwards~ BNDS: Perm_binds x A0 PER.
    extract_bnd x A0; simpl_env in *; destruct_notin.
    + s; des; clear H0; rewrite <-app_nil_l in PER
      ; apply perm_dom_uniq in PER; auto; ss
      ; apply cp_weaken with (A:=A)(Δ:=Δ); ii; substs; auto; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { forwards~ FV: nfv_env_proc_1 x0 WT; rewrite~ subst_fresh. }
    + rewrite <-app_assoc in *; apply perm_dom_uniq in PER; auto; ss
      ; obtain atoms L' as LEQ; destruct_notin; destruct (x0 == x)
      ; tryfalse; des_reqs.
      clear n0; apply cp_weaken with (A:=A)(Δ:=E1++E2++y~A0); ii; substs; auto
      ; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { rewrite <-app_assoc.
        apply~ IHWT; rewrite !app_assoc; try solve_perm.
        forwards UNX: uniq_perm_app PER NINX; destruct_uniq; solve_uniq. }
  - eapply Permutation_sym,Permutation_trans in PER
    ; [|apply Permutation_app_comm]; apply Permutation_sym in PER; ss.
    apply Permutation_length_1_inv in PER; inverts PER; ss.
    des; tryfalse; auto.
  - eapply Permutation_trans in PER; [|apply Permutation_sym; exact PER0].
    forwards~ UN2: uniq_perm PER0; forwards~ UN3: uniq_perm PER
    ; forwards~ BNDS: Perm_binds x A PER.
    extract_bnd x A; simpl_env in *; destruct_notin.
    + s; des; clear H0; rewrite <-app_nil_l in PER
      ; apply perm_dom_uniq in PER; auto; ss; eapply cp_empin with (Δ:=Δ)
      ; ii; substs; auto; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { forwards~ FV: nfv_env_proc_1 x0 WT; rewrite~ subst_fresh. }
    + rewrite <-app_assoc in *; apply perm_dom_uniq in PER; auto; ss
      ; destruct_notin; destruct (x0 == x)
      ; tryfalse; des_reqs.
      clear n0; eapply cp_empin with (Δ:=E1++E2++y~ A)
      ; ii; substs; auto; destruct_notin.
      { eapply Permutation_trans; [apply Permutation_app|]
        ; [exact PER|auto|]; []; solve_perm. }
      { rewrite <-app_assoc; apply IHWT; try solve_perm.
        forwards UNX: uniq_perm_app PER NINX; destruct_uniq; solve_uniq. }
  - eapply Permutation_sym,Permutation_trans,Permutation_sym in PER
    ; [|apply Permutation_app_comm].
    apply Permutation_length_1_inv in PER; inverts PER; s; des; auto.
Qed.

Lemma typing_rename:
  forall Γ P k (x y : atom) A
         (NINX: x `notin` dom Γ `union` fv_proc P)
         (NINY: y `notin` dom Γ `union` fv_proc P)
         (WTX: {k ~> x}P ⊢cp (x ~ A) ++ Γ),
    {k ~> y}P ⊢cp (y ~ A) ++ Γ.
Proof.
  ii; destruct (x == y); subst; auto; simpl_env in *.
  forwards UN: cp_implies_uniq WTX.
  rewrite (@subst_intro_open_rec x); auto.
  eapply ignore_env_order; [apply Permutation_app_comm|].
  apply typing_subst with (A := A); [solve_uniq|].
  eapply ignore_env_order; [apply Permutation_app_comm|]; auto.
Qed.

Lemma wt_nin_proc:
  forall Γ P k (x:atom)
         (NIN: x `notin` dom Γ)
         (WT: {k ~> x}P ⊢cp Γ),
    P ⊢cp Γ.
Proof.
  i; remember ({k ~> x}P) as P'; gen P k; induction WT; ii
  ; match goal with
    | |- context[?P ⊢cp ?Γ] => destruct P; try discriminate; inv HeqP'
    end.
  - forwards UN1: uniq_perm PER UN.
    destruct_all pname; des; destr_eq H0; destr_eq H1; subst
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    apply cp_fwd with (A:=A); auto.
  - pick fresh y and apply cp_cut; destruct_notin
    ; try (solve [eassumption|auto]); specializes H Fr; specializes H0 Fr
    ; first [apply H with (k0:=S k)|apply H0 with (k0:=S k)]
    ; solve [rewrite /open_proc; rewrite~ open_rec_comm
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H1; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    pick fresh y and apply cp_output; destruct_notin; ss
    ; try (solve [eassumption|auto])
    ; first [specializes H Fr; apply H with (k0:=S k)
            |apply IHWT with (k0:=k)]
    ; solve [reflexivity
            |rewrite /open_proc; rewrite~ open_rec_comm
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H1; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    pick fresh y and apply cp_input; destruct_notin; ss
    ; try (solve [eassumption|auto]); specializes H Fr; apply H with (k0:=S k)
    ; solve [rewrite /open_proc; rewrite~ open_rec_comm
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H; destr_eq H0; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    applys cp_left PER; apply IHWT with (k0:=k); eauto using wt_nin_env.
  - destruct_all pname; des; destr_eq H; destr_eq H0; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    applys cp_right PER; apply IHWT with (k0:=k); eauto using wt_nin_env.
  - destruct_all pname; des; destr_eq H0; destr_eq H1; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    applys cp_choice PER
    ; first [apply IHWT1 with (k0:=k)
            |apply IHWT2 with (k0:=k)]
    ; solve [reflexivity
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H1; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    pick fresh y and apply cp_accept; destruct_notin; ss
    ; try (solve [eassumption|auto]); specializes H Fr; apply H with (k0:=S k)
    ; solve [rewrite /open_proc; rewrite~ open_rec_comm
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H1; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    pick fresh y and apply cp_request; destruct_notin; ss
    ; try (solve [eassumption|auto]); specializes H Fr; apply H with (k0:=S k)
    ; solve [rewrite /open_proc; rewrite~ open_rec_comm
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H1; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    applys~ cp_weaken PER; apply IHWT with (k0:=k)
    ; solve [reflexivity
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H; substs~; fsetdec.
  - destruct_all pname; des; destr_eq H0; destr_eq H; substs
    ; try (by exfalso; applys wt_nin_env x PER; simpl_env; fsetdec).
    applys~ cp_empin PER; apply IHWT with (k0:=k)
    ; solve [reflexivity
            |rewrite_env (x `notin` dom Γ) in NIN; i
             ; applys wt_nin_env NIN PER; simpl_env; fsetdec].
  - destruct_all pname; des; destr_eq H0; destr_eq H; substs~; fsetdec.
Qed.