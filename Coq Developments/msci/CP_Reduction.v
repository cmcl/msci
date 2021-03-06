(** Beginning of the file for CP mechanisation as described in

    Philip Wadler. 2012. Propositions as sessions. In Proceedings of the 17th
    ACM SIGPLAN international conference on Functional programming (ICFP '12).
    ACM, New York, NY, USA, 273-286. DOI=10.1145/2364527.2364568
    http://doi.acm.org/10.1145/2364527.2364568

*)
Require Import Metatheory.Metatheory.
Require Import CP_Definitions CP_Infrastructure CP_Typing.
Require Import Coq.Sorting.Permutation.

Set Implicit Arguments.

Lemma assoc_1:
  forall P Q R A B Γ
         (LCP: forall x, lc_proc (P ^^ x))
         (WT: ν B → ν A → P ‖ Q ‖ R ⊢cp Γ),
    ν A → P ‖ ν B → {0 <~> 1}Q ‖ R ⊢cp Γ.
Proof.
  ii; inverts WT.
  pick fresh x; destruct_notin; find_specializes; inverts CPP.
  pick fresh y; destruct_notin; find_specializes.
  forwards UN1: uniq_perm PER0 UN0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  specializes LCP y; rewrite /open_proc in CPP0.
  rewrite open_rec_comm,lc_no_bvar in CPP0; auto.
  apply (@open_nfv_proc_1 _ y 0) in NotInTac2; auto.
  apply (nfv_env_proc_2 CPP0) in NotInTac2.
  extract_bnd x B; simpl_env in *; [solve_notin|].
  rewrite <-app_assoc in PER0; apply perm_dom_uniq in PER0; [|solve_uniq].
  eapply Permutation_sym,Permutation_trans,Permutation_sym in PER
  ; [|apply Permutation_app]; [|apply Permutation_sym; exact PER0|auto].
  simpl_env in PER.
  forwards UN2: uniq_perm PER UN.
  obtain atoms L' as LEQ; eapply cp_cut with (L:=L'); try exact PER; auto
  ; i; substs; destruct_notin
  ; apply typing_rename with (x:=y)
  ; try by (simpl_env; simpl fv_proc; try rewrite swap_binders_fv
            ; solve_notin).
  s; simpl_env.
  rewrite <-!app_assoc.
  rewrite <-(swap_binders_fv _ 0 1) in NotInTac3.
  apply (@open_nfv_proc_1 _ y 1) in NotInTac3; [|auto].
  forwards NIN: Perm_notin PER0 NotInTac0; simpl_env in NIN.
  obtain atoms L' as LEQ; eapply cp_cut with (L:=L'); auto
  ; first (simpl_env; destruct_uniq; solve_uniq); i; substs; destruct_notin
  ; apply typing_rename with (x:=x); try (by solve_notin).
  - rewrite <-(swap_binders_fv _ 0 1) in NotInTac49.
    apply (@open_nfv_proc_1 _ y 1) in NotInTac49; [|auto].
    simpl_env; solve_notin.
  - rewrite swap_binders_open,open_rec_comm; auto.
    applys ignore_env_order CPQ0; solve_perm.
  - rewrite /open_proc; rewrite~ open_rec_comm.
    rewrite lc_no_bvar; eauto using cp_implies_lc.
Qed.

Lemma assoc_2:
  forall P Q R A B Γ
         (LCR: forall x, lc_proc (R ^^ x))
         (WT: ν A → P ‖ ν B → {0 <~> 1}Q ‖ R ⊢cp Γ),
    ν B → ν A → P ‖ Q ‖ R ⊢cp Γ.
Proof.
  ii; inverts WT.
  pick fresh x; destruct_notin; find_specializes; inverts CPQ.
  pick fresh y; destruct_notin; find_specializes.
  forwards UN1: uniq_perm PER0 UN0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  specializes LCR y; rewrite /open_proc in CPQ0.
  rewrite open_rec_comm,lc_no_bvar in CPQ0; auto.
  apply (@open_nfv_proc_1 _ y 0) in NotInTac4; auto.
  apply (nfv_env_proc_2 CPQ0) in NotInTac4.
  extract_bnd x (¬A); simpl_env in *; [|solve_notin].
  simpl_env in *; apply perm_dom_uniq in PER0; [|solve_uniq].
  eapply Permutation_sym,Permutation_trans,Permutation_sym in PER
  ; [|apply Permutation_app]; [|auto|apply Permutation_sym; exact PER0].
  rewrite <-!app_assoc in PER.
  forwards UN2: uniq_perm PER UN.
  rewrite /open_proc in CPP0; rewrite swap_binders_open in CPP0.
  obtain atoms L' as LEQ; eapply cp_cut with (L:=L'); try exact PER; auto
  ; i; substs; destruct_notin
  ; apply typing_rename with (x:=y); try (by solve_notin).
  s; simpl_env.
  forwards NIN: Perm_notin PER0 NotInTac1; simpl_env in *.
  rewrite <-app_assoc.
  eapply ignore_env_order
  ; [apply Permutation_app|]; [apply Permutation_app_comm|auto|].
  simpl_env; obtain atoms L' as LEQ; eapply cp_cut with (L:=L'); auto
  ; first (destruct_uniq; solve_uniq); i; substs; destruct_notin
  ; apply typing_rename with (x:=x); try (by solve_notin).
  - rewrite~ open_rec_comm.
    rewrite lc_no_bvar; eauto using cp_implies_lc.
  - rewrite~ open_rec_comm.
    applys ignore_env_order CPP0; solve_perm.
Qed.

Lemma assoc_equiv:
  forall P Q R A B
         (LCP: forall x, lc_proc (P ^^ x))
         (LCR: forall x, lc_proc (R ^^ x)),
    ν B → ν A → P ‖ Q ‖ R =p= ν A → P ‖ ν B → {0 <~> 1}Q ‖ R.
Proof.
  unfold proc_equiv; split; intros WT; eauto using assoc_1,assoc_2.
Qed.

Lemma swap:
  forall P Q A dA Γ
         (DUA: dual_props A dA)
         (WT: ν A → P ‖ Q ⊢cp Γ),
    ν dA → Q ‖ P ⊢cp Γ.
Proof.
  ii; inverts WT; substs.
  pick fresh y; destruct_notin; find_specializes.
  forwards UN1: uniq_perm PER UN.
  applys ignore_env_order (Permutation_sym PER).
  eapply ignore_env_order; [apply Permutation_app_comm|].
  obtain atoms L' as LEQ; eapply cp_cut with (L:=L'); [auto|solve_uniq| |]
  ; i; substs; destruct_notin
  ; apply typing_rename with (x:=y); try by solve_notin.
  - apply prop_dual_iff in DUA; substs; auto.
  - apply prop_dual_iff in DUA; substs; rewrite~ <-prop_dual_involutive.
Qed.

Lemma swap_equiv:
  forall P Q A dA
         (DUA: dual_props A dA),
    ν A → P ‖ Q =p= ν dA → Q ‖ P.
Proof.
  unfold proc_equiv; ii; split; intros WT; eauto using swap.
Qed.

Lemma reduce_equiv:
  forall P Q R S Γ
         (EQPQ: P =p= Q)
         (RED: forall Γ, Q ⊢cp Γ -> R ⊢cp Γ)
         (EQRS: R =p= S)
         (WT: P ⊢cp Γ),
    S ⊢cp Γ.
Proof. firstorder. Qed.

Lemma reduce_congr_cut_l:
  forall P Q R A Γ
         (IHWT: forall x Γ (NFV: x `notin` fv_proc P `union` fv_proc R),
                  P ^^ x ⊢cp Γ -> R ^^ x ⊢cp Γ)
         (WT: ν A → P ‖ Q ⊢cp Γ),
    ν A → R ‖ Q ⊢cp Γ.
Proof.
  ii; inverts WT; substs.
  pick fresh y; destruct_notin; find_specializes.
  forwards UN1: uniq_perm PER UN.
  applys ignore_env_order (Permutation_sym PER).
  obtain atoms L' as LEQ; eapply cp_cut with (L:=L'); [auto|solve_uniq| |]
  ; i; substs; destruct_notin
  ; apply typing_rename with (x:=y); try by solve_notin.
  apply~ IHWT; []; destruct_notin; solve_notin.
Qed.

Lemma reduce_congr_cut_r:
  forall P Q R A Γ
         (IHWT: forall x Γ (NFV: x `notin` fv_proc Q `union` fv_proc R),
                  Q ^^ x ⊢cp Γ -> R ^^ x ⊢cp Γ)
         (WT: ν A → P ‖ Q ⊢cp Γ),
    ν A → P ‖ R ⊢cp Γ.
Proof.
  ii; inverts WT; substs.
  pick fresh y; destruct_notin; find_specializes.
  forwards UN1: uniq_perm PER UN.
  applys ignore_env_order (Permutation_sym PER).
  obtain atoms L' as LEQ; eapply cp_cut with (L:=L'); [auto|solve_uniq| |]
  ; i; substs; destruct_notin
  ; apply typing_rename with (x:=y); try by solve_notin.
  apply~ IHWT; []; destruct_notin; solve_notin.
Qed.

(** Lemmas for proving well-typedness of reduction rules. *)

Lemma reduce_axcut:
  forall P A (w : atom) Γ
         (NFV: w `notin` fv_proc P)
         (WT: ν A → w ⟷ 0 ‖ P ⊢cp Γ),
    P ^^ w ⊢cp Γ.
Proof.
  ii; inversion WT; subst.
  pick fresh y; destruct_notin; find_specializes.
  rewrite /open_proc in CPP; simpl in CPP.
  inverts keep CPP; rewrite !cons_app_one in *.
  forwards UN1: uniq_perm PER0 UN0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  forwards EQC: perm_cod_uniq PER0; [solve_uniq|]; substs~.
  rewrite <-app_nil_r in PER0; rewrite app_assoc in PER0
  ; apply perm_dom_uniq in PER0; [|solve_uniq]; simpl_env in PER0.
  apply Permutation_sym,Permutation_length_1_inv in PER0; substs~; s in PER.
  forwards~ UN3: uniq_perm PER.
  apply Permutation_sym in PER; applys ignore_env_order PER; simpl_env.
  unfold open_proc in *.
  apply typing_rename with (x:=y); try (by destruct_uniq; solve_notin).
Qed.

Lemma reduce_multi:
  forall P Q R A dA B Γ
         (DUA: dual_props A dA)
         (WT: ν A ⨂ B → [A]0 → P ‖ Q ‖ ⟨dA ⟩ 0 → R ⊢cp Γ),
    ν A → P ‖ ν B → Q ‖ {0 <~> 1}R ⊢cp Γ.
Proof.
  ii; inversion WT; subst.
  pick fresh y; destruct_notin
  ; repeat match goal with
             | [H: forall x, x `notin` ?L -> _, H1: ?y `notin` ?L |- _]
               => specializes H H1; rewrite /open_proc in H; s in H
                  ; inverts keep H; simpl_env in *
           end.
  pick fresh z; destruct_notin; find_specializes.

  forwards UNP: uniq_perm PER0 UN0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER0; forwards EQC: perm_cod_uniq PER0
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq]; rewrite app_nil_l in PER0.

  forwards UNQ: uniq_perm PER1 UN1.
  eapply Permutation_trans in PER1; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER1; forwards EQC: perm_cod_uniq PER1
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER1; [|solve_uniq]; rewrite app_nil_l in PER1.

  rewrite /open_proc open_rec_comm in CPP1; auto.
  apply wt_nin_proc in CPP1; [|simpl_env; autounfold; i; destruct_in; auto
                               ; applys wt_nin_env NotInTac0 PER1; simpl_env
                               ; fsetdec].
  eapply Permutation_sym,Permutation_trans in PER
  ; [|apply Permutation_app; apply Permutation_sym; eassumption].
  apply Permutation_sym in PER; forwards UNG: uniq_perm PER UN
  ; apply Permutation_sym in PER.
  applys ignore_env_order PER; simpl_env.
  pick fresh w and apply cp_cut; destruct_notin; auto; first solve_uniq
  ; let v := match goal with
               | |- context[P] => z
               | |- context[Q] => y
             end
    in
    apply typing_rename with (x:=v); try (by try (s; rewrite !swap_binders_fv)
                                          ; destruct_uniq; solve_notin)
    ; clears w.
  eapply ignore_env_order; [apply Permutation_app_comm|]; s.
  simpl_env; pick fresh w and apply cp_cut; destruct_notin; auto
  ; first solve_uniq.
  - rewrite /open_proc; rewrite~ open_rec_comm.
    forwards QEQ: subst_fresh y w Q; [solve_notin|].
    forwards OPQ: subst_open_rec Q w y 0; rewrite QEQ in OPQ.
    eapply ignore_env_order in CPQ0; [|apply Permutation_app_comm].
    apply typing_subst with (y:=w) in CPQ0; [|solve_uniq].
    eapply ignore_env_order in CPQ0; [|apply Permutation_app_comm].
    rewrite OPQ in CPQ0.
    forwards LC: cp_implies_lc CPQ0; rewrite~ lc_no_bvar.
  - unfold open_proc in *.
    rewrite swap_binders_open; rewrite~ open_rec_comm; rewrite <-app_assoc.
    eapply ignore_env_order; [apply Permutation_app_comm|].
    apply typing_rename with (x:=z); try (by destruct_uniq; solve_notin).
    rewrite~ open_rec_comm.
    eapply ignore_env_order; [apply Permutation_app_comm|].
    simpl_env; apply typing_rename with (x:=y)
    ; try (by destruct_uniq; solve_notin).
    rewrite <-app_assoc.
    eapply ignore_env_order; [apply Permutation_app_comm|].
    rewrite~ open_rec_comm.
Qed.

Lemma reduce_add_inl:
  forall P Q R A B Γ
         (WT: ν A ⨁ B → (0[inl] → P) ‖ 0 CASE Q OR R ⊢cp Γ),
    ν A → P ‖ Q ⊢cp Γ.
Proof.
  ii; inversion WT; subst.
  pick fresh y; destruct_notin
  ; repeat match goal with
             | [H: forall x, x `notin` ?L -> _, H1: ?y `notin` ?L |- _]
               => specializes H H1; rewrite /open_proc in H; s in H
                  ; inverts keep H; simpl_env in *
           end.

  forwards UN0: cp_implies_uniq CPP0.
  apply Permutation_sym in PER0; forwards UNQ: uniq_perm PER0; [solve_uniq|]
  ; apply Permutation_sym in PER0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER0; forwards EQC: perm_cod_uniq PER0
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq]; rewrite app_nil_l in PER0.

  forwards UN1: cp_implies_uniq CPP1.
  apply Permutation_sym in PER1; forwards UNP: uniq_perm PER1; [solve_uniq|]
  ; apply Permutation_sym in PER1.
  eapply Permutation_trans in PER1; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER1; forwards EQC: perm_cod_uniq PER1
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER1; [|solve_uniq]; rewrite app_nil_l in PER1.

  eapply Permutation_sym,Permutation_trans in PER
  ; [|apply Permutation_app; apply Permutation_sym; eassumption].
  applys ignore_env_order PER.
  apply Permutation_sym in PER; apply (uniq_perm PER) in UN.
  forwards NINP: Perm_notin PER1 NotInTac0.
  forwards NINQ: Perm_notin PER0 NotInTac1.
  pick fresh x and apply cp_cut; destruct_notin; auto
  ; apply typing_rename with (x:=y); try (by solve_notin).
Qed.

Lemma reduce_add_inr:
  forall P Q R A B Γ
         (WT: ν A ⨁ B → (0[inr] → P) ‖ 0 CASE Q OR R ⊢cp Γ),
    ν B → P ‖ R ⊢cp Γ.
Proof.
  ii; inversion WT; subst.
  pick fresh y; destruct_notin
  ; repeat match goal with
             | [H: forall x, x `notin` ?L -> _, H1: ?y `notin` ?L |- _]
               => specializes H H1; rewrite /open_proc in H; s in H
                  ; inverts keep H; simpl_env in *
           end.

  forwards UN0: cp_implies_uniq CPP0.
  apply Permutation_sym in PER0; forwards UNQ: uniq_perm PER0; [solve_uniq|]
  ; apply Permutation_sym in PER0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER0; forwards EQC: perm_cod_uniq PER0
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq]; rewrite app_nil_l in PER0.

  forwards UN1: cp_implies_uniq CPP1.
  apply Permutation_sym in PER1; forwards UNP: uniq_perm PER1; [solve_uniq|]
  ; apply Permutation_sym in PER1.
  eapply Permutation_trans in PER1; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER1; forwards EQC: perm_cod_uniq PER1
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER1; [|solve_uniq]; rewrite app_nil_l in PER1.

  eapply Permutation_sym,Permutation_trans in PER
  ; [|apply Permutation_app; apply Permutation_sym; eassumption].
  applys ignore_env_order PER.
  apply Permutation_sym in PER; apply (uniq_perm PER) in UN.
  forwards NINP: Perm_notin PER1 NotInTac0.
  forwards NINQ: Perm_notin PER0 NotInTac1.
  pick fresh x and apply cp_cut; destruct_notin; auto
  ; apply typing_rename with (x:=y); try (by solve_notin).
Qed.

Lemma reduce_spawn:
  forall P Q A dA Γ
         (DUA: dual_props A dA)
         (WT: ν ! A → ! ⟨A⟩ 0 → P ‖ ? [dA]0 → Q ⊢cp Γ),
    ν A → P ‖ Q ⊢cp Γ.
Proof.
  ii; inversion WT; subst.
  pick fresh y; destruct_notin
  ; repeat match goal with
             | [H: forall x, x `notin` ?L -> _, H1: ?y `notin` ?L |- _]
               => specializes H H1; rewrite /open_proc in H; s in H
                  ; inverts keep H; simpl_env in *
           end.
  pick fresh z; destruct_notin; find_specializes.

  forwards UNQ: uniq_perm PER0 UN0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER0; forwards EQC: perm_cod_uniq PER0
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq]; rewrite app_nil_l in PER0.

  forwards UNP: uniq_perm PER1 UN1.
  eapply Permutation_trans in PER1; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER1; forwards EQC: perm_cod_uniq PER1
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER1; [|solve_uniq]; rewrite app_nil_l in PER1.

  rewrite /open_proc open_rec_comm in CPP1; auto.
  apply wt_nin_proc in CPP1; [|simpl_env; autounfold; i; destruct_in; auto
                               ; applys wt_nin_env NotInTac0 PER1; simpl_env
                               ; fsetdec].
  rewrite /open_proc open_rec_comm in CPP0; auto.
  apply wt_nin_proc in CPP0; [|simpl_env; autounfold; i; destruct_in; auto
                               ; applys wt_nin_env NotInTac1 PER0; simpl_env
                               ; fsetdec].
  eapply Permutation_sym,Permutation_trans in PER
  ; [|apply Permutation_app; apply Permutation_sym; eassumption].
  apply Permutation_sym in PER; forwards UNG: uniq_perm PER UN
  ; apply Permutation_sym in PER.
  applys ignore_env_order PER; simpl_env.

  pick fresh w and apply cp_cut; destruct_notin; auto
  ; apply typing_rename with (x:=z); try (by destruct_uniq; solve_notin).
Qed.

Lemma reduce_gc:
  forall P Q (y:atom) A Γ
         (NF: y `notin` fv_proc P)
         (WT: ν ! A → ! ⟨A⟩0 → P ‖ ? [] 0 → Q ⊢cp Γ),
    weakenv (elements (remove y (fv_proc (P ^^ y)))) Q ⊢cp Γ.
Proof.
  ii; forwards LC: cp_implies_lc WT; inversion WT; inverts LC; subst.
  pick fresh z; destruct_notin; find_specializes.
  rewrite /open_proc in CPP; simpl in CPP.
  inverts keep CPP; rewrite !cons_app_one in *.
  forwards UN1: uniq_perm PER0 UN0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER0; forwards EQC: perm_cod_uniq PER0
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq]; rewrite app_nil_l in PER0.
  eapply Permutation_sym,Permutation_trans in PER
  ; [|apply Permutation_app]; [|apply Permutation_sym;exact PER0|auto].
  applys ignore_env_order PER; eapply ignore_env_order
  ; [apply Permutation_app_comm|].
  apply Permutation_sym in PER; forwards UN2: uniq_perm PER UN.
  rewrite <-app_nil_r,app_assoc; apply typing_weaken; simpl_env
  ; try solve_uniq; auto using elements_3w.
  - rewrite /open_proc in CPQ; s in CPQ.
    inverts keep CPQ; simpl_env in *.
    forwards UN4: uniq_perm PER1 UN3.
    eapply Permutation_trans in PER1; [|apply Permutation_app_comm].
    rewrite <-app_nil_l in PER1; forwards EQC: perm_cod_uniq PER1
    ; [solve_uniq|]; inverts EQC; substs~.
    apply perm_dom_uniq in PER1; [|solve_uniq]; rewrite app_nil_l in PER1.
    apply Permutation_sym in PER1; apply (ignore_env_order PER1) in CPP1.
    applys wt_nin_proc NotInTac4 CPP1.
  - pick fresh w; destruct_notin; find_specializes.
    rewrite /open_proc in CPP0; rewrite~ open_rec_comm in CPP0.
    forwards PER1: Permutation_app_head (w~A) PER0.
    apply Permutation_sym in PER1; apply (ignore_env_order PER1) in CPP0.
    apply wt_nin_proc in CPP0; [|ss;fsetdec].
    eapply ignore_env_order in CPP0; [|apply Permutation_app_comm].
    forwards UN3: cp_implies_uniq CPP0.
    forwards EQ: remove_nfv_proc_eq NF NotInTac17.
    split; ii.
    + apply InA_iff_In; applys eq_InA_elements EQ.
      apply Permutation_sym in PER0; forwards IN: Perm_in PER0 H.
      apply elements_iff,remove_iff; destruct (x == w)
      ; [analyze_in x; solve_uniq|].
      split; auto.
      apply open_fv_proc_2.
      apply in_env_fv with (x:=x) in CPP0; des; rewrite !dom_app in *.
      by specialize (CPP1 (union_2 _ _ _ IN)); apply open_fv_proc_1 in CPP1.
    + apply equal_sym in EQ; apply InA_iff_In,(eq_InA_elements EQ) in H.
      apply elements_iff,remove_iff in H; des.
      apply in_env_fv with (x:=x) in CPP0; des; rewrite !dom_app in *.
      applys Perm_in PER0.
      apply CPP2 in H0; ss; destruct_in; tryfalse; auto.
Qed.

Lemma reduce_unit:
  forall P Γ
         (WT: ν pp_one → (0 → 0) ‖ ⟨⟩0 → P ⊢cp Γ),
    P ⊢cp Γ.
Proof.
  ii; inversion WT; subst.
  pick fresh y; destruct_notin
  ; repeat match goal with
             | [H: forall x, x `notin` ?L -> _, H1: ?y `notin` ?L |- _]
               => specializes H H1; rewrite /open_proc in H; s in H
                  ; inverts keep H; simpl_env in *
           end.

  forwards UNP: uniq_perm PER0 UN0.
  eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
  rewrite <-app_nil_l in PER0; forwards EQC: perm_cod_uniq PER0
  ; [solve_uniq|]; inverts EQC; substs~.
  apply perm_dom_uniq in PER0; [|solve_uniq]; rewrite app_nil_l in PER0.

  forwards NIN: Perm_notin PER0 NotInTac1.
  apply wt_nin_proc in CPP0; auto.
  forwards PER2: Permutation_sym (Permutation_trans PER PER0).
  applys~ ignore_env_order PER2.
Qed.

(** Commuting conversion *)

Ltac spec_wt WT Fr :=
  specializes WT Fr; rewrite /open_proc in WT; s in WT; simpl_env in *.

Section CPCommutingConversions.

  Lemma reduce_cc_multi_one:
    forall P Q R (x:atom) A B Γ
           (LCQ: lc_proc Q)
           (WT: ν A → ([B] x → P ‖ Q) ‖ R ⊢cp Γ),
      [B] x → (ν A → {0 <~> 1}P ‖ R) ‖ Q ⊢cp Γ.
  Proof.
    ii; inverts WT; substs.
    pick fresh y; destruct_notin; spec_wt CPQ Fr
    ; spec_wt CPP Fr; inverts keep CPP.
    rewrite~ lc_no_bvar in CPQ0.
    apply (nfv_env_proc_2 CPQ0) in NotInTac5.
    pick fresh z; destruct_notin; spec_wt CPP0 NotInTac7.
    forwards UNP: uniq_perm PER0 UN0.
    eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
    extract_bnd y A; simpl_env in *; [|solve_notin].
    rewrite <-app_assoc in PER0; apply perm_dom_uniq in PER0; [|solve_uniq].
    eapply Permutation_sym,Permutation_trans in PER
    ; [|apply Permutation_app]; [|apply Permutation_sym|]; eauto.
    applys ignore_env_order PER; simpl_env in *.
    apply Permutation_sym in PER; forwards UNA: uniq_perm PER UN.
    rewrite <-!app_assoc.
    obtain atoms L' as LEQ
    ; eapply cp_output with (L:=L')(ΔQ:=ΔQ0)(ΔP:=E1++E2++ΔQ); simpl_env
    ; first (by solve_perm); auto; i; substs; destruct_notin.
    apply typing_rename with (x:=z)
    ; try by (simpl_env; simpl fv_proc; rewrite swap_binders_fv
              ; solve_notin).
    clears y0.
    rewrite <-(swap_binders_fv _ 0 1) in NotInTac4.
    apply (@open_nfv_proc_1 _ z 0) in NotInTac4; [|auto].
    forwards NIN2: Perm_notin PER0 NotInTac2; s; simpl_env in *
    ; rewrite <-!app_assoc.
    obtain atoms L' as LEQ; eapply cp_cut with (L:=L')(ΔQ:=ΔQ)
    ; auto; simpl_env; first solve_uniq; i; substs; destruct_notin
    ; apply typing_rename with (x:=y); try by solve_notin.
    - rewrite <-(swap_binders_fv _ 0 1) in NotInTac34.
      apply (@open_nfv_proc_1 _ z 1) in NotInTac34; [|auto].
      simpl_env; solve_notin.
    - rewrite swap_binders_open; rewrite~ open_rec_comm.
      applys ignore_env_order CPP0; solve_perm.
    - rewrite open_rec_comm,lc_no_bvar; eauto using cp_implies_lc.
  Qed.

  Lemma reduce_cc_multi_two:
    forall P Q R (x:atom) A B Γ
           (LCP: forall x, lc_proc (P ^^ x))
           (WT: ν A → ([B] x → P ‖ Q) ‖ R ⊢cp Γ),
      [B] x → P ‖ (ν A → Q ‖ R) ⊢cp Γ.
  Proof.
    ii; inverts WT; substs.
    pick fresh y; destruct_notin; spec_wt CPQ Fr
    ; spec_wt CPP Fr. inverts keep CPP.
    pick fresh z; destruct_notin; spec_wt CPP0 NotInTac7.
    specializes LCP z; rewrite open_rec_comm,lc_no_bvar in CPP0; auto.
    apply (@open_nfv_proc_1 _ z 0) in NotInTac4; auto.
    apply (nfv_env_proc_2 CPP0) in NotInTac4.
    forwards UNP: uniq_perm PER0 UN0.
    eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
    extract_bnd y A; simpl_env in *; [solve_notin|].
    rewrite <- 2 app_assoc in PER0;apply perm_dom_uniq in PER0;[|solve_uniq].
    eapply Permutation_sym,Permutation_trans in PER
    ; [|apply Permutation_app]; [|apply Permutation_sym|]; eauto.
    applys ignore_env_order PER; simpl_env in *.
    apply Permutation_sym in PER; forwards UNA: uniq_perm PER UN.
    obtain atoms L' as LEQ
    ; eapply cp_output with (L:=L')(ΔQ:=E1++E2++ΔQ)(ΔP:=ΔP0); simpl_env
    ; first (by solve_perm); auto; i; substs; destruct_notin.
    - apply typing_rename with (x:=z); auto.
    - obtain atoms L' as LEQ
      ; eapply cp_cut with (L:=L')(ΔP:=x~B0++E1++E2)(ΔQ:=ΔQ)
      ; auto; simpl_env; [solve_perm|destruct_uniq;solve_uniq| |]
      ; i; substs; destruct_notin
      ; apply typing_rename with (x:=y)
      ; try by (simpl_env; simpl fv_proc; try rewrite swap_binders_fv
                ; destruct_uniq; solve_notin).
      clears x0.
      applys ignore_env_order CPQ0; solve_perm.
  Qed.

  Lemma reduce_cc_input:
    forall P Q (x:atom) A B Γ
           (WT: ν A → (⟨B⟩ x → P) ‖ Q ⊢cp Γ),
      ⟨B⟩x → ν A → ({0 <~> 1}P) ‖ Q ⊢cp Γ.
  Proof.
    ii; inverts WT; substs.
    pick fresh y; destruct_notin; spec_wt CPQ Fr
    ; spec_wt CPP Fr; inverts keep CPP.
    pick fresh z; destruct_notin; spec_wt CPP0 NotInTac6.
    forwards UNP: uniq_perm PER0 UN0.
    eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
    extract_bnd y A; simpl_env in *.
    rewrite <-app_assoc in PER0;apply perm_dom_uniq in PER0;[|solve_uniq].
    eapply Permutation_sym,Permutation_trans in PER
    ; [|apply Permutation_app]; [|apply Permutation_sym|]; eauto.
    applys ignore_env_order PER; simpl_env in *.
    apply Permutation_sym in PER; forwards UNA: uniq_perm PER UN.
    obtain atoms L' as LEQ
    ; eapply cp_input with (L:=L')(ΔP:=E1++E2++ΔQ); simpl_env
    ; first (by solve_perm); auto; i; substs; destruct_notin.
    apply typing_rename with (x:=z)
    ; try by (simpl_env; simpl fv_proc; try rewrite swap_binders_fv
              ; destruct_uniq; solve_notin).
    s; simpl_env; clears y0.
    obtain atoms L' as LEQ
    ; eapply cp_cut with (L:=L')(ΔP:=z~B++x~B0++E1++E2)(ΔQ:=ΔQ)
    ; [solve_perm|destruct_uniq;solve_uniq| |]; i; substs; destruct_notin.
    - rewrite <-(swap_binders_fv _ 0 1) in NotInTac4.
      apply (@open_nfv_proc_1 _ z 1) in NotInTac4; [|auto].
      rewrite <-(swap_binders_fv _ 0 1) in NotInTac30.
      apply (@open_nfv_proc_1 _ z 1) in NotInTac30; [|auto].
      apply typing_rename with (x:=y)
      ; try (by simpl_env; destruct_uniq; solve_notin).
      rewrite swap_binders_open; rewrite~ open_rec_comm.
      applys ignore_env_order CPP0; solve_perm.
    - apply typing_rename with (x:=y); auto.
      rewrite~ open_rec_comm; rewrite lc_no_bvar; eauto using cp_implies_lc.
  Qed.

  Lemma reduce_cc_add_inl:
      forall P Q (x:atom) A Γ
             (WT: ν A → (x[inl] → P) ‖ Q ⊢cp Γ),
        x[inl] → (ν A → P ‖ Q) ⊢cp Γ.
  Proof.
    ii; inversion WT; subst.
    pick fresh y; destruct_notin; spec_wt CPP Fr; spec_wt CPQ Fr; inverts CPP.
    forwards UN1: uniq_perm PER UN.
    eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
    extract_bnd y A.
    rewrite <-app_assoc in PER0;apply perm_dom_uniq in PER0;[|solve_uniq].
    eapply Permutation_sym,Permutation_trans in PER
    ; [|apply Permutation_app]; [|apply Permutation_sym|]; eauto.
    applys ignore_env_order PER; simpl_env in *.
    eapply cp_left; eauto.
    apply Permutation_sym in PER; forwards UN2: uniq_perm PER UN.
    rewrite <-!app_assoc.
    pick fresh z and apply cp_cut; first eauto; simpl_env in *
    ; [solve_uniq| |]; i; substs; destruct_notin
    ; apply typing_rename with (x:=y); try (by destruct_uniq; solve_notin).
    applys ignore_env_order CPP0; solve_perm.
  Qed.

  Lemma reduce_cc_add_inr:
    forall P Q (x:atom) A Γ
           (WT: ν A → (x[inr] → P) ‖ Q ⊢cp Γ),
      x[inr] → (ν A → P ‖ Q) ⊢cp Γ.
 Proof.
    ii; inversion WT; subst.
    pick fresh y; destruct_notin; spec_wt CPP Fr; spec_wt CPQ Fr; inverts CPP.
    forwards UN1: uniq_perm PER UN.
    eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
    extract_bnd y A.
    rewrite <-app_assoc in PER0;apply perm_dom_uniq in PER0;[|solve_uniq].
    eapply Permutation_sym,Permutation_trans in PER
    ; [|apply Permutation_app]; [|apply Permutation_sym|]; eauto.
    applys ignore_env_order PER; simpl_env in *.
    eapply cp_right; eauto.
    apply Permutation_sym in PER; forwards UN2: uniq_perm PER UN.
    rewrite <-!app_assoc.
    pick fresh z and apply cp_cut; first eauto; simpl_env in *
    ; [solve_uniq| |]; i; substs; destruct_notin
    ; apply typing_rename with (x:=y); try (by destruct_uniq; solve_notin).
    applys ignore_env_order CPP0; solve_perm.
 Qed.

 Lemma reduce_cc_choice:
   forall P Q R (x:atom) A Γ
          (WT: ν A → (x CASE P OR Q) ‖ R ⊢cp Γ),
     x CASE (ν A → P ‖ R) OR (ν A → Q ‖ R) ⊢cp Γ.
  Proof.
    ii; inversion WT; subst.
    pick fresh y; destruct_notin; spec_wt CPP Fr; spec_wt CPQ Fr; inverts CPP.
    forwards UN1: uniq_perm PER UN.
    eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
    extract_bnd y A.
    rewrite <-app_assoc in PER0;apply perm_dom_uniq in PER0;[|solve_uniq].
    eapply Permutation_sym,Permutation_trans in PER
    ; [|apply Permutation_app]; [|apply Permutation_sym|]; eauto.
    applys ignore_env_order PER; simpl_env in *.
    eapply cp_choice; eauto.
    - apply Permutation_sym in PER; forwards UN2: uniq_perm PER UN.
      rewrite <-!app_assoc.
      pick fresh z and apply cp_cut; first eauto; simpl_env in *
      ; [solve_uniq| |]; i; substs; destruct_notin
      ; apply typing_rename with (x:=y); try (by destruct_uniq; solve_notin).
      applys ignore_env_order CPP0; solve_perm.
    - apply Permutation_sym in PER; forwards UN2: uniq_perm PER UN.
      rewrite <-!app_assoc.
      pick fresh z and apply cp_cut; first eauto; simpl_env in *
      ; [solve_uniq| |]; i; substs; destruct_notin
      ; apply typing_rename with (x:=y); try (by destruct_uniq; solve_notin).
      applys ignore_env_order CPQ0; solve_perm.
  Qed.

  Lemma reduce_cc_accept:
    forall P Q (x:atom) A B Γ
             (REQS: forall Γ Δ
                           (PER: Permutation Γ (x~! B++Δ))
                           (WT: ν A → (! ⟨B⟩x → P) ‖ Q ⊢cp Γ),
                      all_requests Δ)
           (WT: ν A → (! ⟨B⟩x → P) ‖ Q ⊢cp Γ),
      ! ⟨B⟩x → (ν A → {0 <~> 1}P ‖ Q) ⊢cp Γ.
  Proof.
    ii; inverts keep WT; substs.
    pick fresh y; destruct_notin; find_specializes; inverts keep CPP.
    pick fresh z; destruct_notin; find_specializes.
    forwards UNP: uniq_perm PER UN.
    eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
    extract_bnd y A; simpl_env in *.
    rewrite <-app_assoc in PER0;apply perm_dom_uniq in PER0;[|solve_uniq].
    eapply Permutation_sym,Permutation_trans in PER
    ; [|apply Permutation_app]; [|apply Permutation_sym|]; eauto.
    simpl_env in *.
    apply Permutation_sym in PER; forwards UNA: uniq_perm PER UN.
    specialize (REQS _ _ PER WT); des_reqs. clear REQS0 REQS2.
    apply Permutation_sym in PER; applys ignore_env_order PER.
    obtain atoms L' as LEQ; eapply cp_accept with (L:=L'); eauto; i; substs
    ; destruct_notin.
    apply typing_rename with (x:=z)
    ; try by (simpl_env; simpl fv_proc; try rewrite swap_binders_fv
              ; destruct_uniq; solve_notin).
    s; simpl_env; clears y0.
    obtain atoms L' as LEQ
    ; eapply cp_cut with (L:=L')(ΔP:=z~B++E1++E2)(ΔQ:=ΔQ)
    ; [solve_perm|destruct_uniq;solve_uniq| |]; i; substs; destruct_notin.
    - rewrite <-(swap_binders_fv _ 0 1) in NotInTac4.
      apply (@open_nfv_proc_1 _ z 1) in NotInTac4; [|auto].
      rewrite <-(swap_binders_fv _ 0 1) in NotInTac30.
      apply (@open_nfv_proc_1 _ z 1) in NotInTac30; [|auto].
      apply typing_rename with (x:=y)
      ; try (by simpl_env; destruct_uniq; solve_notin).
      rewrite swap_binders_open; rewrite~ open_rec_comm.
      applys ignore_env_order CPP0; solve_perm.
    - apply typing_rename with (x:=y); auto.
      rewrite~ open_rec_comm; rewrite lc_no_bvar; eauto using cp_implies_lc.
  Qed.

  Lemma reduce_cc_request:
    forall P Q (x:atom) A B Γ
           (WT: ν A → (? [B]x → P) ‖ Q ⊢cp Γ),
      ? [B]x → (ν A → {0 <~> 1}P ‖ Q) ⊢cp Γ.
  Proof.
    ii; inverts keep WT; substs.
    pick fresh y; destruct_notin; find_specializes; inverts keep CPP.
    pick fresh z; destruct_notin; find_specializes.
    forwards UNP: uniq_perm PER UN.
    eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
    extract_bnd y A; simpl_env in *.
    rewrite <-app_assoc in PER0;apply perm_dom_uniq in PER0;[|solve_uniq].
    eapply Permutation_sym,Permutation_trans in PER
    ; [|apply Permutation_app]; [|apply Permutation_sym|]; eauto.
    simpl_env in *.
    apply Permutation_sym in PER; forwards UNA: uniq_perm PER UN.
    apply Permutation_sym in PER; applys ignore_env_order PER.
    obtain atoms L' as LEQ; eapply cp_request with (L:=L'); eauto; i; substs
    ; destruct_notin.
    apply typing_rename with (x:=z)
    ; try by (simpl_env; simpl fv_proc; try rewrite swap_binders_fv
              ; destruct_uniq; solve_notin).
    s; simpl_env; clears y0.
    obtain atoms L' as LEQ
    ; eapply cp_cut with (L:=L')(ΔP:=z~B++E1++E2)(ΔQ:=ΔQ)
    ; [solve_perm|destruct_uniq;solve_uniq| |]; i; substs; destruct_notin.
    - rewrite <-(swap_binders_fv _ 0 1) in NotInTac4.
      apply (@open_nfv_proc_1 _ z 1) in NotInTac4; [|auto].
      rewrite <-(swap_binders_fv _ 0 1) in NotInTac30.
      apply (@open_nfv_proc_1 _ z 1) in NotInTac30; [|auto].
      apply typing_rename with (x:=y)
      ; try (by simpl_env; destruct_uniq; solve_notin).
      rewrite swap_binders_open; rewrite~ open_rec_comm.
      applys ignore_env_order CPP0; solve_perm.
    - apply typing_rename with (x:=y); auto.
      rewrite~ open_rec_comm; rewrite lc_no_bvar; eauto using cp_implies_lc.
  Qed.

  Lemma reduce_cc_weaken:
    forall P Q (x:atom) A Γ
           (WT: ν A → (? []x → P) ‖ Q ⊢cp Γ),
      ? []x → (ν A → P ‖ Q) ⊢cp Γ.
  Proof.
    ii; inversion WT; subst.
    pick fresh y; destruct_notin; spec_wt CPP Fr; spec_wt CPQ Fr; inverts CPP.
    forwards UN1: uniq_perm PER UN.
    eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
    extract_bnd y A.
    rewrite <-app_assoc in PER0;apply perm_dom_uniq in PER0;[|solve_uniq].
    eapply Permutation_sym,Permutation_trans in PER
    ; [|apply Permutation_app]; [|apply Permutation_sym|];[|eassumption|auto].
    applys ignore_env_order PER; simpl_env in *.
    eapply cp_weaken; eauto.
    apply Permutation_sym in PER; forwards UN2: uniq_perm PER UN.
    rewrite <-!app_assoc.
    pick fresh z and apply cp_cut; first eauto; simpl_env in *
    ; [solve_uniq| |]; i; substs; destruct_notin
    ; apply typing_rename with (x:=y); try (by destruct_uniq; solve_notin).
    applys ignore_env_order CPP0; solve_perm.
  Qed.

  Lemma reduce_cc_empin:
    forall P Q (x:atom) A Γ
           (WT: ν A → (⟨⟩x → P) ‖ Q ⊢cp Γ),
      ⟨⟩x → (ν A → P ‖ Q) ⊢cp Γ.
  Proof.
    ii; inversion WT; subst.
    pick fresh y; destruct_notin; spec_wt CPP Fr; spec_wt CPQ Fr; inverts CPP.
    forwards UN1: uniq_perm PER UN.
    eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
    extract_bnd y A.
    rewrite <-app_assoc in PER0;apply perm_dom_uniq in PER0;[|solve_uniq].
    eapply Permutation_sym,Permutation_trans in PER
    ; [|apply Permutation_app]; [|apply Permutation_sym|];[|eassumption|auto].
    applys ignore_env_order PER; simpl_env in *.
    eapply cp_empin; eauto.
    apply Permutation_sym in PER; forwards UN2: uniq_perm PER UN.
    rewrite <-!app_assoc.
    pick fresh z and apply cp_cut; first eauto; simpl_env in *
    ; [solve_uniq| |]; i; substs; destruct_notin
    ; apply typing_rename with (x:=y); try (by destruct_uniq; solve_notin).
    applys ignore_env_order CPP0; solve_perm.
  Qed.
  
  Lemma reduce_cc_empcho:
    forall Q (x y:atom) A Γ
           (REQS: forall Γ Δ
                         (PER: Permutation Γ (x~pp_top ++ Δ))
                         (WT: ν A → (? []0 → x CASE 0) ‖ Q ⊢cp Γ),
                    all_requests Δ)
           (NF: y `notin` fv_proc Q)
           (WT: ν A → (? []0 → x CASE 0) ‖ Q ⊢cp Γ),
      weakenv (elements (remove y (fv_proc (Q ^^ y)))) (x CASE 0) ⊢cp Γ.
  Proof.
    ii; inverts keep WT; subst.
    pick fresh z; destruct_notin; find_specializes.
    inverts CPP; inverts CPP0.
    eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
    rewrite <-app_nil_l in PER0.
    extract_bnd z A; apply perm_dom_uniq in PER0; [|solve_uniq]
    ; simpl_env in *.
    eapply Permutation_sym,Permutation_trans in PER
    ; [|apply Permutation_app]; [|apply Permutation_sym|];[|eassumption|auto].
    specialize (REQS _ _ (Permutation_sym PER) WT).
    applys ignore_env_order PER.
    forwards UN2: uniq_perm (Permutation_sym PER) UN; simpl_env in *.
    rewrite <-app_nil_r,app_assoc; apply typing_weaken; simpl_env
    ; try solve_uniq; auto using elements_3w.
    forwards UN3: cp_implies_uniq CPQ.
    forwards EQ: remove_nfv_proc_eq NF NotInTac6.
    split; i.
    + apply InA_iff_In; applys eq_InA_elements EQ.
      apply elements_iff,remove_iff; analyze_in x0; split; auto.
      apply in_env_fv with (x:=x0) in CPQ; des; simpl_env in *.
      apply~ CPQ0.
    + apply equal_sym in EQ; apply InA_iff_In,(eq_InA_elements EQ) in H1.
      apply elements_iff,remove_iff in H1; des.
      apply in_env_fv with (x:=x0) in CPQ; des; simpl_env in *.
      apply CPQ1 in H2; ss; destruct_in; tryfalse; auto.
  Qed.
  
End CPCommutingConversions.

Hint Resolve reduce_axcut reduce_multi reduce_add_inl reduce_add_inr
     reduce_spawn reduce_gc reduce_unit.

Hint Resolve reduce_cc_multi_one reduce_cc_multi_two reduce_cc_input
     reduce_cc_add_inl reduce_cc_add_inr reduce_cc_choice reduce_cc_accept
     reduce_cc_request reduce_cc_weaken reduce_cc_empin reduce_cc_empcho.

Hint Resolve reduce_equiv reduce_congr_cut_l reduce_congr_cut_r.

Theorem proc_sub_red: forall Γ P Q
    (WT: P ⊢cp Γ)
    (RED: P ==>cp Q),
  Q ⊢cp Γ.
Proof. ii; gen Γ; induction RED; subst; eauto. Qed.

Require Import Relation_Operators.

Notation "P '==>cp*' Q" := (clos_refl_trans proc proc_red P Q) (at level 68).

Theorem proc_cut_elim:
  forall P Γ
         (WT: P ⊢cp Γ),
    exists Q, P ==>cp* Q /\ ~ is_cut Q.
Proof.
  ii; induction WT; eauto using rt_refl.
  pick fresh x; destruct_notin; specializes CPP Fr; destruct P.
  {
    rewrite /open_proc in CPP; s in CPP.
    destruct_all pname; des; substs; repeat injs.
    - inv CPP; apply (uniq_perm PER0) in UN0; solve_uniq.
    - inv CPP; simpl_env in *.
      eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
      extract_bnd x A.
      rewrite <-app_nil_r in PER0; rewrite app_assoc in PER0
      ; apply perm_dom_uniq in PER0; [|solve_uniq].
      s in PER0; apply Permutation_sym,Permutation_length_1_inv in PER0.
      simpl_env in PER0; substs.
      specializes H0 Fr; inversion H0 as [Q' IHQ]; des.
      exists Q'; split; auto.
      admit.
    - admit.
    - admit.
  }
  {
    specializes H Fr; inversion H as [P' IHP]; des.
    admit.
  }
  {
    rewrite /open_proc in CPP; s in CPP.
    destruct_all pname; des; substs.
    - specializes H Fr; inverts H; des. admit.
    - inverts CPP; simpl fv_proc in *; destruct_notin; simpl_env in *.
      eapply Permutation_trans in PER0; [|apply Permutation_app_comm].
      extract_bnd x A.
      + apply wt_nin_proc in CPQ0; [|solve_notin].
        forwards LCQ: cp_implies_lc CPQ0.
        eexists; split; [apply rt_step; apply red_cc_multi_one|]; auto.
      + pick fresh y; destruct_notin; find_specializes.
        rewrite /open_proc in CPP0; rewrite~ open_rec_comm in CPP0.
        apply wt_nin_proc in CPP0; [|solve_notin].
        forwards LCP: cp_implies_lc CPP0.
        eexists; split; [apply rt_step; apply red_cc_multi_two|]; auto.
        admit (* forall x, LC (P1 ^^ x) -- a bit too strong... *).
  }
Admitted.