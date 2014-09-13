Require Export Arith.EqNat.
Require Export Arith.Lt.
Require Export Arith.Compare_dec.
Require Export List.
Require Export ListLocal.
Require Import String.
Require Import TypeAssignmentPoly.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import TacticsLocal.
Require Import ResultOpenClose.
Require Import MSets.MSetInterface.


(* ============================================================================= *)

Lemma ctx_add_1a : 
  forall G1 G2 a b, CTX.eq G1 G2 -> CTX.In b (CTX.add a G1) -> CTX.In b (CTX.add a G2).
Proof.
  intros G1 G2 a b Heq_G1G2 Hin_b; destruct (ctx_elt_as_DT.eq_dec a b); subst; intuition.
  apply CTXFacts.add_2.
  apply (proj1 (Heq_G1G2 b)).
  eapply CTXFacts.add_3; eauto.
Qed.

Lemma ctx_add_1 : 
  forall G1 G2 a1 a2, 
    a1 = a2 -> CTX.eq G1 G2 -> CTX.eq (CTX.add a1 G1) (CTX.add a2 G2).
Proof.
  intros G1 G2 a1 a2 Heq_G1G2 b; subst; split; apply ctx_add_1a;
    [auto | apply CTX.eq_equiv; auto].
Qed.

Lemma ctx_add_2 : forall a b G, CTX.In a (CTX.add b G) -> a = b \/ CTX.In a G.
Proof.
  intros a b G Hin.
  destruct (CTX.E.eq_dec a b); subst; [intuition|].
  right.
  eapply CTXFacts.add_3; eauto.
Qed.

Lemma ctx_replace_2 : 
  forall u sigma v old new G, 
    CTX.In (u, sigma) (ctx_replace v old new G) -> 
    (u, sigma) = (v, new) \/ (CTX.In (u, sigma) G).
Proof.
  intros u sigma v old new G Hin.
  destruct (ctx_add_2 _ _ _ Hin).
  left; auto.
  right.
  eapply CTXFacts.remove_3; eauto.
Qed.

Lemma ctx_replace_2_stronger : 
  forall u sigma v old new G, 
    CTX.In (u, sigma) (ctx_replace v old new G) -> 
    (u, sigma) = (v, new) \/ ((CTX.In (u, sigma) G) /\ (u, sigma) <> (v, old)).
Proof.
  intros u sigma v old new G Hin.
  destruct (ctx_add_2 _ _ _ Hin).
  left; auto.
  right; split.
  eapply CTXFacts.remove_3; eauto.
  contradict H.
  eapply CTXFacts.remove_1; intuition.
Qed.

Lemma ctx_remove_1a : 
  forall G1 G2 a b, 
    CTX.eq G1 G2 -> CTX.In b (CTX.remove a G1) -> CTX.In b (CTX.remove a G2).
Proof.
  intros G1 G2 a b Heq_G1G2 Hin_b; destruct (ctx_elt_as_DT.eq_dec a b); subst.
  contradict Hin_b.
  apply CTXFacts.remove_1; intuition.
  apply CTXFacts.remove_2; intuition.
  apply (proj1 (Heq_G1G2 b)).
  eapply CTXFacts.remove_3; eauto.
Qed.

Lemma ctx_remove_1 : 
  forall G1 G2 a1 a2, 
    a1 = a2 -> CTX.eq G1 G2 -> CTX.eq (CTX.remove a1 G1) (CTX.remove a2 G2).
Proof.
  intros G1 G2 a1 a2 Heq_G1G2 b; subst; split; apply ctx_remove_1a;
    [auto | apply CTX.eq_equiv; auto].
Qed.

Lemma ctx_replace_1 : 
  forall G1 G2 u1 u2 old1 old2 new1 new2, 
    u1 = u2 -> old1 = old2 -> new1 = new2 ->
    CTX.eq G1 G2
    -> 
    CTX.eq (ctx_replace u1 old1 new1 G1) (ctx_replace u2 old2 new2 G2).
Proof.
  intros G1 G2 u1 u2 old1 old2 new1 new2 Heq_u1u2 Heq_old1old2 Heq_new1new2 Heq_G1G2;
    subst;
      unfold ctx_replace.
  apply ctx_add_1; intuition.
  apply ctx_remove_1; intuition.
Qed.       

Lemma ctx_equal_preserves_wf : 
  forall G1 G2, G1 |-wf -> CTX.eq G1 G2 -> G2 |-wf.
Proof.
  intros G1 G2 Hwf Heq_G1G2.
  inversion Hwf; subst.
  apply WFCtx; intros.
  eapply H; apply (proj2 (Heq_G1G2 _)); eauto.
  eapply H0; apply (proj2 (Heq_G1G2 _)); eauto.
  elim (H1 x); intros; [left|right;split;destruct H2]; intros rho.
  intros Hin; elim (H2 rho); 
    apply <- (Heq_G1G2 (ValVariable (Var (Free x)), rho)); auto.
  intros Hin; elim (H2 rho); 
    apply <- (Heq_G1G2 (ValName (Nm (Free x)), rho)); auto.
  intros Hin; elim (H3 rho); 
    apply <- (Heq_G1G2 (ValName (CoNm (Free x)), rho)); auto.
Qed.

(*
Print CTX.eq_equiv.
Print ctx_add_1a.
Check CTX.eq_equiv.
Check Equivalence_Transitive.
Check @Equivalence_Transitive ctx.
Check @Equivalence_Transitive ctx CTX.eq.
Check @Equivalence_Transitive ctx CTX.eq CTX.eq_equiv.
Check CTX.eq_equiv.(@Equivalence_Transitive ctx CTX.eq).
*)

Definition CTX_eq_refl := CTX.eq_equiv.(@RelationClasses.Equivalence_Reflexive ctx CTX.eq).
Definition CTX_eq_sym := CTX.eq_equiv.(@RelationClasses.Equivalence_Symmetric ctx CTX.eq).
Definition CTX_eq_trans := CTX.eq_equiv.(@RelationClasses.Equivalence_Transitive ctx CTX.eq).

Lemma ctx_equal_part_1 : 
  forall G1 G2 GL GR, 
    G1 |-part GL (+) GR 
    -> 
    CTX.eq G1 G2
    -> 
    G2 |-part GL (+) GR.
Proof.
  intros G1 G2 GL GR Hpart_G1 Heq_G1G2.
  inversion Hpart_G1; subst.
  apply Partition.
  eapply CTX_eq_trans.
  eapply CTX_eq_sym; eauto.
  auto.
  apply ctx_equal_preserves_wf with (G1 := G1); auto.
  auto.
Qed.

Lemma ctx_equal_preserves_lookup : 
  forall G1 G2 u rho, G1 |-v u : rho -> CTX.eq G1 G2 -> G2 |-v u : rho.
Proof.
  intros G1 G2 u rho Hv_u Heq_G1G2.
  assert (G2 |-wf ).
  apply ctx_equal_preserves_wf with (G1 := G1); auto.
  inversion Hv_u; auto.
  inversion Hv_u; auto.
  apply LContext; subst; auto.
  apply (proj1 (Heq_G1G2 _)); auto.
  apply LToken; auto.
Qed.

Lemma ctx_equal_preserves_free_values_in_context :
  forall G1 G2 P,
    CTX.eq G1 G2 -> free_values_in_context G1 P -> free_values_in_context G2 P.
Proof.
  intros G1 G2 P Heq_G1G2 HfreeG1P.
  unfold free_values_in_context in *.
  intros u Hin.
  destruct (HfreeG1P u Hin) as [rho Hin2].
  exists rho.
  apply (proj1 (Heq_G1G2 _)); auto.
Qed.  

Lemma subset_preserves_well_formed_ctx :
  forall G1 G2,
    G1 |-wf -> CTX.Subset G2 G1 -> G2 |-wf.
Proof.
  intros G1 G2 Hwf Hsubset.
  inversion Hwf; subst; apply WFCtx.
  intros u rho Hin.
  apply H with (rho:=rho); auto.
  intros u sigma1 sigma2 Hin1 Hin2.
  apply H0 with (u:=u) (rho:=sigma1) (sigma:=sigma2); auto.
  intros x; elim (H1 x); [
    intros Hu1;left
    | intros Hu1; destruct Hu1 as [Hu2 Hu3]; right; split
  ]; intros rho.
  pose (Hu1 rho) as Hu4; contradict Hu4; apply Hsubset; auto.
  pose (Hu2 rho) as Hu4; contradict Hu4; apply Hsubset; auto.
  pose (Hu3 rho) as Hu4; contradict Hu4; apply Hsubset; auto.
Qed.

Theorem ctx_equal_preserves_typed : 
  forall G1 P, G1 |-p P -> forall G2, CTX.eq G1 G2 -> G2 |-p P.
Proof.
  intros G1 P HtypP; induction HtypP; intros G2 Heq_G1G2.

  Case "Input"%string.
  eapply TypPrefixInput with (L := L); intros.
  apply ctx_equal_preserves_lookup with (G1 := G); eauto.
  eapply ctx_equal_preserves_free_values_in_context; eauto.
  eapply H2; eauto.
  auto.
  subst.
  apply ctx_add_1; intuition.
  apply ctx_replace_1; intuition.

  Case "Output"%string.
  destruct H3; subst.

  SCase "Removed"%string.
  eapply TypPrefixOutput with (s := s) (rho := rho); intros; subst; eauto.
  eapply ctx_equal_preserves_lookup with (G1 := G); auto.
  apply ctx_equal_preserves_lookup with (G1 := G); auto.
  apply IHHtypP.
  apply ctx_replace_1; intuition.
  apply ctx_remove_1; intuition.
  apply ctx_remove_1; intuition.

  SCase "Not Removed"%string.
  destruct H3; subst.
  eapply TypPrefixOutput with (s := s) (rho := rho) (t := t); 
    [ auto | auto | | | right; split; auto | auto | apply IHHtypP ].
  apply ctx_equal_preserves_lookup with (G1 := G); auto.
  apply ctx_equal_preserves_lookup with (G1 := G); auto.
  apply ctx_replace_1; intuition.

  Case "Par"%string.
  eapply TypPar.
  eapply ctx_equal_part_1; eauto.
  apply IHHtypP1; apply CTX_eq_refl.
  apply IHHtypP2; apply CTX_eq_refl.

  Case "Sum"%string.
  apply TypSum.
  apply IHHtypP1; auto.
  apply IHHtypP2; auto.

  Case "IsEq"%string.
  eapply TypIsEq; eauto.
  apply ctx_equal_preserves_lookup with (G1 := G); auto.
  apply ctx_equal_preserves_lookup with (G1 := G); auto.
  eapply ctx_equal_preserves_free_values_in_context; eauto.

  Case "IsNotEq"%string.
  eapply TypIsNotEq; eauto.
  apply ctx_equal_preserves_lookup with (G1 := G); auto.
  apply ctx_equal_preserves_lookup with (G1 := G); auto.
  eapply ctx_equal_preserves_free_values_in_context; eauto.

  Case "New"%string.
  eapply TypNew; subst.
  intros x G' Hin Heq; subst.
  eapply H0; [
    | reflexivity 
    | apply ctx_add_1; intuition; apply ctx_add_1; intuition; apply Heq_G1G2
  ].
  eauto.
  
  Case "Rep"%string.
  eapply TypRep; eauto.
  apply ctx_equal_preserves_wf with (G1:=G); auto.
  intros a Hin.
  apply -> (Heq_G1G2 a).
  apply H0; auto.

  Case "Zero"%string.
  apply TypZero.
  eapply ctx_equal_preserves_wf; eauto.
Qed.

(* ============================================================================= *)


Lemma partition_is_subset_left : 
  forall a G GL GR, G |-part GL (+) GR -> CTX.In a GL -> CTX.In a G.
Proof.
  intros a G GL GR Hpart Hin.
  inversion Hpart; subst.
  apply <- (H a).
  apply CTXFacts.union_2; auto.
Qed.

Lemma partition_comm : forall G GL GR, G |-part GL (+) GR -> G |-part GR (+) GL.
Proof.
  intros G GL GR Hpart; inversion Hpart; subst.
  apply Partition; intuition.
  split; intuition.
  destruct (CTXFacts.union_1 (proj1 (H a) H2)).
  apply CTXFacts.union_3; auto.
  apply CTXFacts.union_2; auto.
  destruct (CTXFacts.union_1 H2).
  apply (proj2 (H a) (CTXFacts.union_3 GL H3)).
  apply (proj2 (H a) (CTXFacts.union_2 GR H3)).
  destruct (H1 u rho) as [H2|H2']; [ | destruct H2' as [H2|H2]]; intuition.
Qed.

Lemma partition_is_subset_right : 
  forall a G GL GR, G |-part GL (+) GR -> CTX.In a GR -> CTX.In a G.
Proof.
  intros a G GL GR Hpart Hin.
  eapply partition_is_subset_left.
  apply partition_comm; eauto.
  auto.
Qed.

(* ============================================================================= *)

Lemma free_values_in_context_1 : 
  forall G P, G |-p P -> free_values_in_context G P.
Proof.
  intros G P Htyp; induction Htyp; fold free_values_proc in *; subst.
  
  intros v' Hin.
  destruct (in_app_or _ _ _ Hin) as [Hu|Hu]; clear Hin.
  elim (free_values_value_1 _ _ Hu).
  rewrite -> (free_values_value_1 _ _ Hu) in *; clear Hu.
  inversion H; subst.
  eexists; apply H4.

  (* This is where we need to free_values_in_context constraint, because
     there may be no input transitions for s. *)
  apply H0; auto.

  intros v' Hin. 
  destruct (in_app_or _ _ _ Hin) as [Hu|Hu]; clear Hin.
  elim (free_values_value_1 _ _ Hu).
  inversion H1.
  exists (TChannel s); auto.

  fold free_values_proc in *.
  destruct (in_app_or _ _ _ Hu) as [Hu2|Hu2]; clear Hu.
  elim (free_values_value_1 _ _ Hu2).
  inversion H2; subst.
  exists rho; auto.
  inversion Hu2.

  inversion H3; clear H3; subst.
  pose (IHHtyp v' Hu2) as e; inversion e as [sigma Hu3]; clear e.
  destruct (ctx_replace_2 _ _ _ _ _ _ Hu3).
  rewrite -> (prod_eq_elim_fst _ _ _ _ _ _ H3) in *.
  exists (TChannel s).
  inversion H1; subst; auto.
  pose (CTXFacts.remove_3 H3).
  exists sigma; auto.

  destruct H4; subst.
  pose (IHHtyp v' Hu2) as e; inversion e as [sigma Hu3]; clear e.
  destruct (ctx_replace_2 _ _ _ _ _ _ Hu3).
  rewrite -> (prod_eq_elim_fst _ _ _ _ _ _ H3) in *.
  exists (TChannel s).
  inversion H1; subst; auto.
  
  exists sigma; auto.

  intros v' Hin.
  destruct (in_app_or _ _ _ Hin) as [Hu|Hu]; clear Hin;
    fold free_values_proc in *.
  pose (IHHtyp1 v' Hu) as e; inversion e as [sigma Hu2]; clear e.
  exists sigma; eapply partition_is_subset_left; eauto.
  pose (IHHtyp2 v' Hu) as e; inversion e as [sigma Hu2]; clear e.
  exists sigma; eapply partition_is_subset_right; eauto.
  
  intros v' Hin.
  destruct (in_app_or _ _ _ Hin) as [Hu|Hu]; clear Hin;
    fold free_values_proc in *.
  pose (IHHtyp1 v' Hu) as e; inversion e as [sigma Hu2]; clear e.
  exists sigma; auto.
  pose (IHHtyp2 v' Hu) as e; inversion e as [sigma Hu2]; clear e.
  exists sigma; auto.

  intros v' Hin. 
  destruct (in_app_or _ _ _ Hin) as [Hu|Hu]; clear Hin.
  elim (free_values_value_1 _ _ Hu).
  inversion H; subst.
  exists (TSingleton K); auto.
  inversion Hu.
  fold free_values_proc in *.
  destruct (in_app_or _ _ _ Hu) as [Hu2|Hu2]; clear Hu.
  elim (free_values_value_1 _ _ Hu2).
  inversion H0; subst.
  exists (TSingleton L); auto.
  inversion Hu2.
  apply (H1 v' Hu2).

  intros v' Hin. 
  destruct (in_app_or _ _ _ Hin) as [Hu|Hu]; clear Hin.
  elim (free_values_value_1 _ _ Hu).
  inversion H; subst.
  exists (TSingleton K); auto.
  inversion Hu.
  fold free_values_proc in *.
  destruct (in_app_or _ _ _ Hu) as [Hu2|Hu2]; clear Hu.
  elim (free_values_value_1 _ _ Hu2).
  inversion H0; subst.
  exists (TSingleton L); auto.
  inversion Hu2.
  apply (H1 v' Hu2).

  intros v' Hin; clear H.
  destruct v' as [vn|vt|vv]; [
      destruct vn as [i|i]
    | contradict Hin; intros Hu;
      pose (free_values_proc_yields_free_values _ _ Hu) as Hu2;
        inversion Hu2
    | destruct vv as [i]
  ];
  destruct i;
    try (solve [contradict Hin; intros Hu;
      pose (free_values_proc_yields_free_values _ _ Hu) as Hu2;
        inversion Hu2]).
  destruct (fresh_free_id_exists (f :: L)).
  assert (x <> f) as Hu1; [ contradict H; subst; intuition |].
  eelim (H0 x); [
    intros rho Hin2
    | contradict H; apply in_cons; auto
    | reflexivity
    | apply free_values_proc_open; eauto
  ]; clear H0.
  exists rho.
  eapply CTXFacts.add_3 with (x := (ValName (CoNm (Free x)), TChannel (SDual s))).
  discriminate.
  eapply CTXFacts.add_3 with (x := (ValName (Nm (Free x)), TChannel s)).
  contradict Hu1; pose (prod_eq_elim_fst _ _ _ _ _ _ Hu1) as Hu;
    injection Hu; auto.
  auto.

  destruct (fresh_free_id_exists (f :: L)).
  assert (x <> f) as Hu1; [ contradict H; subst; intuition |].
  eelim (H0 x); [
    intros rho Hin2
    | contradict H; apply in_cons; auto
    | reflexivity
    | apply free_values_proc_open; eauto
  ]; clear H0.
  exists rho.
  eapply CTXFacts.add_3 with (x := (ValName (CoNm (Free x)), TChannel (SDual s))).
  contradict Hu1; pose (prod_eq_elim_fst _ _ _ _ _ _ Hu1) as Hu;
    injection Hu; auto.
  eapply CTXFacts.add_3 with (x := (ValName (Nm (Free x)), TChannel s)).
  discriminate.
  auto.

  destruct (fresh_free_id_exists (f :: L)).
  assert (x <> f) as Hu1; [ contradict H; subst; intuition |].
  eelim (H0 x); [
    intros rho Hin2
    | contradict H; apply in_cons; auto
    | reflexivity
    | apply free_values_proc_open; eauto
  ]; clear H0.
  exists rho.
  eapply CTXFacts.add_3 with (x := (ValName (CoNm (Free x)), TChannel (SDual s))).
  discriminate.
  eapply CTXFacts.add_3 with (x := (ValName (Nm (Free x)), TChannel s)).
  discriminate.
  auto.

  intros v' Hin. 
  apply IHHtyp in Hin.
  destruct Hin as [rho Hu1].
  exists rho.
  apply H0; auto.

  intros v' Hin; clear H.
  inversion Hin.
Qed.

(* ============================================================================= *)

Lemma partition_wf : 
  forall G GL GR, G |-part GL (+) GR -> G |-wf.
Proof.
  intros G GL GR Hpart.
  inversion Hpart; subst; intuition.
Qed.

Lemma partition_lookup_left :
  forall G GL GR u rho,
    G |-part GL (+) GR -> GL |-v u : rho -> G |-v u : rho.
Proof.
  intros G GL GR u rho Hpart HlookupGL.
  inversion HlookupGL; subst.
  apply LContext; auto.
  eapply partition_wf; eauto.
  inversion Hpart; subst.
  apply (proj2 (H1 (u, rho))).
  apply CTXFacts.union_2; auto.
  apply LToken; auto.
  eapply partition_wf; eauto.
Qed.

Lemma partition_free_values_in_context_left : 
  forall G GL GR P, 
    G |-part GL (+) GR ->
    free_values_in_context GL P ->
    free_values_in_context G P.
Proof.
  intros G GL GR P Hpart HfreeGL; inversion Hpart; subst.
  intros u Hin.
  elim (HfreeGL u Hin).
  intros rho HinGL.
  exists rho.
  apply (proj2 (H (u, rho))).
  apply CTXFacts.union_2; auto.
Qed.  

(* ============================================================================= *)

Definition free_ids_context (G : ctx) : list free_id := 
  flat_map (fun x => free_ids_value (fst x)) (CTX.elements G).

Lemma context_in_vs_elements_in :
  forall a G, CTX.In a G -> In a (CTX.elements G).
Proof.
  intros a G Hin.
  pose (CTXFacts.elements_1 Hin) as Hin2.
  pose ((proj1 (SetoidList.InA_alt _ _ _ )) Hin2) as Hin3.
  elim Hin3; intros b Hu; destruct Hu as [Hu1 Hu2].
  cbv in Hu1; subst.
  auto.
Qed.

Lemma free_ids_context_vs_context : 
  forall G x u sigma, 
    x :: nil = free_ids_value u
    -> 
    CTX.In (u, sigma) G
    ->
    In x (free_ids_context G).
Proof.
  intros G x u sigma Hfree Hin.
  pose (context_in_vs_elements_in _ _ Hin).
  unfold free_ids_context.
  apply <- in_flat_map.
  eexists; split; eauto.
  unfold fst.
  rewrite <- Hfree.
  intuition.
Qed.

Lemma free_ids_context_vs_context_var : 
  forall G x sigma, 
    CTX.In (ValVariable (Var (Free x)), sigma) G
    ->
    In x (free_ids_context G).
Proof.
  intros.
  eapply free_ids_context_vs_context; eauto.
  intuition.
Qed.

Lemma free_ids_context_vs_context_name : 
  forall x sigma G, 
    CTX.In (ValName (Nm (Free x)), sigma) G
    ->
    In x (free_ids_context G).
Proof.
  intros.
  eapply free_ids_context_vs_context; eauto.
  intuition.
Qed.

Lemma free_ids_context_vs_context_coname : 
  forall x sigma G, 
    CTX.In (ValName (CoNm (Free x)), sigma) G
    ->
    In x (free_ids_context G).
Proof.
  intros.
  eapply free_ids_context_vs_context; eauto.
  intuition.
Qed.

Lemma free_ids_context_replace : 
  forall u sigma v old new G, 
    u <> v
    ->
    CTX.In (u, sigma) (ctx_replace v old new G)
    ->
    CTX.In (u, sigma) G.
Proof.
  intros u sigma v old new G Hneq Hin_usigma.
  unfold ctx_replace in *.
  apply CTXFacts.remove_3 with (x := (v, old)); auto.
  apply CTXFacts.add_3 with (x := (v, new)).
  contradict Hneq.
  injection Hneq; intros; eauto.
  auto.
Qed.

Lemma fresh_for_ctx_partition_left : 
  forall G GL GR u,
    fresh_for_ctx u G
    ->
    G |-part GL (+) GR 
    ->
    fresh_for_ctx u GL.
Proof.
  intros G GL GR u Hfresh_uG Hpart.
  inversion Hfresh_uG; subst; [|apply FToken].
  apply FContext; auto.
  intros v sigma.
  elim (H0 v sigma); intros Hu1.
  left; contradict Hu1.
  inversion Hpart; subst.
  apply <- (H1 (v, sigma)).
  apply CTXFacts.union_2; auto.
  right; auto.
Qed.

Lemma fresh_for_ctx_partition_right : 
  forall G GL GR u,
    fresh_for_ctx u G
    ->
    G |-part GL (+) GR 
    ->
    fresh_for_ctx u GR.
Proof.
  intros G GL GR u Hfresh Hpart.
  apply partition_comm in Hpart.
  eapply fresh_for_ctx_partition_left; eauto.
Qed.

Lemma partition_wf_left: 
  forall G GL GR, G |-part GL (+) GR -> GL |-wf.
Proof.
  intros G GL GR Hpart.
  apply subset_preserves_well_formed_ctx with (G1:=G).
  eapply partition_wf; eauto.
  intros a Hin.
  eapply partition_is_subset_left; eauto.
Qed.

Lemma partition_wf_right: 
  forall G GL GR, G |-part GL (+) GR -> GR |-wf.
Proof.
  intros G GL GR Hpart.
  apply partition_comm in Hpart.
  eapply partition_wf_left; eauto.
Qed.

Lemma fresh_for_ctx_simple : 
  forall u G, G |-wf -> fresh_for_ctx u G -> forall rho, ~ CTX.In (u, rho) G.
Proof.
  intros u G Hwf Hfresh_uG rho Hin.
  inversion Hfresh_uG; subst.
  destruct (H0 u rho); intuition.
  inversion Hwf; subst.
  pose (H _ _ Hin) as f.
  inversion f.
Qed.


Lemma wellformed_ctx_add_1 :
  forall G u rho,
    G |-wf -> free_value u -> fresh_for_ctx u G -> CTX.add (u,rho) G |-wf.
Proof.
  intros G u rho Hwf Hfree_u Hfresh_uG.
  inversion Hwf; subst.
  apply WFCtx; intros.
  destruct (value_dec u0 u); subst; auto.
  apply (H _ rho0).
  eapply CTXFacts.add_3; eauto.
  contradict n.
  erewrite -> prod_eq_elim_fst; eauto.

  destruct (value_dec u0 u); subst; auto.
  assert ((u, rho0) = (u, rho)).
  eapply list_add_4; eauto.
  apply fresh_for_ctx_simple with (rho:=rho0) in Hfresh_uG; auto.

  injection H4; intros; subst.
  destruct (type_dec rho sigma); subst; auto.
  apply CTXFacts.add_3 in H3; 
    [ | unfold ctx_elt_as_DT.eq; intros Hu2; injection Hu2; intros; subst; intuition].
  contradict H3.
  apply fresh_for_ctx_simple; auto.

  apply CTXFacts.add_3 in H2; 
    [ | unfold ctx_elt_as_DT.eq; intros Hu2; injection Hu2; intros; subst; intuition].
  apply CTXFacts.add_3 in H3; 
    [ | unfold ctx_elt_as_DT.eq; intros Hu2; injection Hu2; intros; subst; intuition].
  eapply H0; eauto.

  (inversion Hfresh_uG; subst; [|inversion Hfree_u]; 
  inversion H2; subst; simpl in H3;
    ((destruct (string_dec i x); subst; [
      left; intros sigma Hu1;
        apply CTXFacts.add_3 in Hu1; 
          [ | unfold ctx_elt_as_DT.eq; intros Hu2; discriminate];
          eelim H3; [intros Hu2; apply Hu2; eauto|intuition]
      |
    ])
    || (destruct (string_dec i x); subst; [
    right; split; intros sigma Hu1;
      (apply CTXFacts.add_3 in Hu1; 
        [ | unfold ctx_elt_as_DT.eq; intros Hu2; discriminate]);
      (eelim H3; [intros Hu2; apply Hu2; eauto|intuition])
      |
    ])));
  (destruct (H1 x) as [Hu1|Hu1]; [ 
    left
    | destruct Hu1 as [Hu2 Hu3]; right; split
  ];
  (intros sigma Hin; apply CTXFacts.add_3 in Hin; [
    | try (solve [ 
      discriminate 
      || (unfold ctx_elt_as_DT.eq; intros Hu5; injection Hu5; intros; 
        subst; intuition)
    ])
  ]; 
  (solve [elim (Hu1 sigma); auto] 
    || solve [elim (Hu2 sigma); auto]
      || solve [elim (Hu3 sigma); auto]))).
Qed.


Lemma ctx_add_preserves_partition_left : 
  forall G GL GR u rho, 
    free_value u
    -> 
    fresh_for_ctx u G
    -> 
    G |-part GL (+) GR 
    ->
    (CTX.add (u, rho) G) |-part (CTX.add (u, rho) GL) (+) GR.
Proof.
  intros G GL GR u rho Hfresh_u Hfresh_ctx_u_G Hpart.
  inversion Hfresh_ctx_u_G; [subst|subst;inversion Hfresh_u].
  inversion Hpart; subst; clear H.
  apply Partition.
  intros a; intuition.
  destruct (CTX.E.eq_dec a (u, rho)); subst.
  apply CTXFacts.union_2.
  apply CTXFacts.add_1; intuition.
  assert (CTX.In a G).
  eapply CTXFacts.add_3; eauto.
  pose (proj1 (H1 a) H4).
  destruct (CTXFacts.union_1 i); [apply CTXFacts.union_2|apply CTXFacts.union_3]; intuition.
  destruct (CTXFacts.union_1 H).
  destruct (CTX.E.eq_dec a (u, rho)); subst.
  apply CTXFacts.add_1; intuition.
  eapply CTXFacts.add_2; eauto.
  apply <- (H1 a).
  apply CTXFacts.union_2.
  eapply CTXFacts.add_3; eauto.
  destruct (CTX.E.eq_dec a (u, rho)); subst.
  apply CTXFacts.add_1; intuition.
  eapply CTXFacts.add_2; eauto.
  apply <- (H1 a).
  apply CTXFacts.union_3; auto.

  apply wellformed_ctx_add_1; auto.

  intros v sigma.
  destruct (H3 v sigma); auto.
  destruct (CTX.E.eq_dec (v, sigma) (u, rho)).
  injection e; intros; subst.
  right; left.
  apply fresh_for_ctx_simple; auto.
  eapply partition_wf_right; eauto.
  eapply fresh_for_ctx_partition_right; eauto.

  destruct (H3 v sigma); auto.
  left.
  intro Hc.
  apply CTXFacts.add_3 in Hc; [intuition|unfold ctx_elt_as_DT.eq; intuition].
Qed.

Lemma wellformed_ctx_remove_1 :
  forall u rho G, 
    G |-wf
    ->
    CTX.remove (u, rho) G |-wf.
Proof.
  intros u rho G Hwf.
  inversion Hwf; subst.
  apply WFCtx.
  intros v sigma Hin.
  apply CTXFacts.remove_3 in Hin.
  eapply H; eauto.
  intros v sigma1 sigma2 Hin1 Hin2.
  apply (H0 v); eapply CTXFacts.remove_3; eauto.
  intros x.
  elim (H1 x);[intros Hu1|intros Hu1; destruct Hu1 as [Hu2 Hu3]].
  left; intros sigma Hin; apply CTXFacts.remove_3 in Hin; apply (Hu1 sigma); auto.
  right; split; intros sigma Hin; apply CTXFacts.remove_3 in Hin; 
    [apply (Hu2 sigma)|apply (Hu3 sigma)]; auto.
Qed.

Lemma ctx_remove_preserves_partition_left : 
  forall G GL GR u rho, 
    ~ CTX.In (u, rho) GR
    ->
    G |-part GL (+) GR 
    ->
    (CTX.remove (u, rho) G) |-part (CTX.remove (u, rho) GL) (+) GR.
Proof.
  intros G GL GR u rho Hnotin Hpart.
  inversion Hpart; subst.
  apply Partition.
  split; intros H2; destruct (CTX.E.eq_dec a (u, rho)); subst.
  contradict H2; apply CTXFacts.remove_1; intuition.
  assert (CTX.In a G).
  eapply CTXFacts.remove_3; eauto.
  elim (CTXFacts.union_1 (proj1 (H a) H3)); intros Hin.
  apply CTXFacts.union_2.
  apply CTXFacts.remove_2; eauto.
  apply CTXFacts.union_3; auto.
  elim (CTXFacts.union_1 H2); intros Hin.
  contradict Hin; apply CTXFacts.remove_1; intuition.
  contradict Hnotin; auto.
  elim (CTXFacts.union_1 H2); intros Hin.
  apply CTXFacts.remove_2; intuition.
  apply <- (H a).
  apply CTXFacts.union_2.
  eapply CTXFacts.remove_3; eauto.
  apply CTXFacts.remove_2; intuition.
  apply <- (H a).
  apply CTXFacts.union_3; auto.
  inversion H0; subst.

  apply wellformed_ctx_remove_1; auto.

  intros v sigma; elim (H1 v sigma); intuition.
  left; intros Hin.
  apply CTXFacts.remove_3 in Hin; intuition.
Qed.

Lemma ctx_remove_preserves_partition_left_2 : 
  forall G GL GR u rho, 
   CTX.In (u, rho) GR
   ->
   G |-part GL (+) GR
   ->
   G |-part CTX.remove (u, rho) GL (+) GR.
Proof.
  intros G GL GR u rho Hin Hpart.
  inversion Hpart; subst.
  apply Partition; auto.
  intros a; split; intros Hin2.
  destruct (CTX.E.eq_dec a (u, rho)); subst.
  apply CTXFacts.union_3; auto.
  assert (CTX.In a (CTX.union GL GR)).
  apply -> (H a); auto.
  destruct (CTXFacts.union_1 H2); [apply CTXFacts.union_2|apply CTXFacts.union_3; auto].
  eapply CTXFacts.remove_2; auto.
  apply <- (H a); auto.
  destruct (CTXFacts.union_1 Hin2); [apply CTXFacts.union_2|apply CTXFacts.union_3; auto].
  eapply CTXFacts.remove_3; eauto.
  intros v sigma.
  destruct (H1 v sigma) as [Hu1|Hu1]; [|destruct Hu1 as [Hu2|Hu2]]; intuition.
  left; contradict Hu1.
  eapply CTXFacts.remove_3; eauto.
Qed.

Lemma ctx_replace_case_1 : 
  forall G u sigma1 sigma2 v old new,
    CTX.In (v, old) G
    ->
    G |-wf
    ->
    CTX.In (u, sigma1) (ctx_replace v old new G)
    ->
    CTX.In (u, sigma2) (ctx_replace v old new G)
    ->
    (u = v /\ sigma1 = sigma2 /\ sigma1 = new /\ sigma2 = new) 
    \/ (u = v /\ sigma1 = sigma2 /\ sigma1 <> new /\ sigma2 <> new) 
    \/ (u <> v /\ sigma1 = sigma2 /\ CTX.In (u, sigma1) G). 
Proof.
  intros G u sigma1 sigma2 v old new Hin Hwf Hin1 Hin2.
  destruct (value_dec u v); subst; [|right;right].
  destruct (type_dec sigma1 new); 
    destruct (type_dec sigma2 new);
      subst.

  left; intuition.

  apply CTXFacts.add_3 in Hin2; 
    [|unfold ctx_elt_as_DT.eq;intros Hc; injection Hc; intros; subst; intuition].
  destruct (type_dec sigma2 old); subst.
  contradict Hin2; apply CTXFacts.remove_1; reflexivity.
  apply CTXFacts.remove_3 in Hin2.
  inversion Hwf; subst; contradict n0.
  eapply H0; eauto.

  apply CTXFacts.add_3 in Hin1; 
    [|unfold ctx_elt_as_DT.eq;intros Hc; injection Hc; intros; subst; intuition].
  destruct (type_dec sigma1 old); subst.
  contradict Hin1; apply CTXFacts.remove_1; reflexivity.
  apply CTXFacts.remove_3 in Hin1.
  inversion Hwf; subst; contradict n0.
  eapply H0; eauto.

  apply CTXFacts.add_3 in Hin1; 
    [|unfold ctx_elt_as_DT.eq;intros Hc; injection Hc; intros; subst; intuition].
  apply CTXFacts.add_3 in Hin2; 
    [|unfold ctx_elt_as_DT.eq;intros Hc; injection Hc; intros; subst; intuition].
  apply CTXFacts.remove_3 in Hin1.
  apply CTXFacts.remove_3 in Hin2.
  right; left; intuition.
  inversion Hwf; subst.
  eapply H0; eauto.
  
  apply CTXFacts.add_3 in Hin1; 
    [|unfold ctx_elt_as_DT.eq;intros Hc; injection Hc; intros; subst; intuition].
  apply CTXFacts.add_3 in Hin2; 
    [|unfold ctx_elt_as_DT.eq;intros Hc; injection Hc; intros; subst; intuition].
  apply CTXFacts.remove_3 in Hin1.
  apply CTXFacts.remove_3 in Hin2.
  intuition.
  inversion Hwf; subst.
  eapply H0; eauto.
Qed.  

Lemma ctx_replace_preserves_wf : 
  forall G u old new, 
    CTX.In (u, old) G
    ->
    G |-wf
    ->
    ctx_replace u old new G |-wf.
Proof.
  intros G u old new Hin Hwf.
  apply WFCtx.

  intros v rho Hin2.
  inversion Hwf; subst.
  destruct (value_dec u v); subst.
  eapply H; eauto.
  apply CTXFacts.add_3 in Hin2; 
    [|unfold ctx_elt_as_DT.eq;contradict n;injection n; intros; subst; intuition].
  apply CTXFacts.remove_3 in Hin2.
  eapply H; eauto.

  intros v sigma1 sigma2 Hin2 Hin3.
  elim (ctx_replace_case_1 G v sigma1 sigma2 u old new);auto; 
    [|intros Hdisj; elim Hdisj]; intros Hu1; 
      destruct Hu1 as [Hu1 Hu2];
        destruct Hu2 as [Hu2 Hu3]; 
          try (destruct Hu3 as [Hu3 Hu4]); 
            subst; auto.
  
  intros x; inversion Hwf; subst.
  elim (H1 x); intros Hu1; [|destruct Hu1 as [Hu1 Hu2]]; clear H1.
  set (v := ValVariable (Var (Free x))).
  left; intros rho Hc; apply CTXFacts.add_3 in Hc; [
    | unfold ctx_elt_as_DT.eq; intros Heq; injection Heq; intros; subst;
      specialize Hu1 with (rho:=old); contradict Hu1; intuition
  ];
  apply CTXFacts.remove_3 in Hc; specialize Hu1 with (rho:=rho); 
    contradict Hu1; intuition.
  right; split; (intros rho Hc; apply CTXFacts.add_3 in Hc; [
    | unfold ctx_elt_as_DT.eq; intros Heq; injection Heq; intros; subst
  ]); [
      apply CTXFacts.remove_3 in Hc; specialize Hu1 with (rho:=rho); 
        contradict Hu1; intuition
    | specialize Hu1 with (rho:=old); contradict Hu1; intuition
    | apply CTXFacts.remove_3 in Hc; specialize Hu2 with (rho:=rho); 
        contradict Hu2; intuition
    | specialize Hu2 with (rho:=old); contradict Hu2; intuition
  ].
Qed.

Lemma ctx_replace_preserves_partition_left : 
  forall G GL GR u old new, 
    CTX.In (u, old) GL
    ->
    (CTX.In (u, old) GR -> old = new)
    ->
    G |-part GL (+) GR 
    ->
    (ctx_replace u old new G) |-part (ctx_replace u old new GL) (+) GR.
Proof.
  intros G GL GR u old new HinGL Heq_oldnew Hpart.
  inversion Hpart; subst.
  apply Partition; auto.
  intros a; split; intros Hin2.
  destruct (CTX.E.eq_dec a (u, new)); subst.
  unfold ctx_replace in *.
  apply CTXFacts.union_2; auto.
  apply CTXFacts.add_1; intuition.
  destruct a; destruct (ctx_replace_2_stronger _ _  _ _ _ _ Hin2); subst.
  contradict n; intuition.
  destruct H2.
  assert (CTX.In (v,t) (CTX.union GL GR)).
  apply -> (H (v,t)); auto.
  destruct (CTXFacts.union_1 H4); [apply CTXFacts.union_2|apply CTXFacts.union_3; auto].
  apply CTXFacts.add_2; intuition.
  destruct (CTXFacts.union_1 Hin2).
  destruct (CTX.E.eq_dec a (u, new)); subst.
  apply CTXFacts.add_1; intuition.
  apply CTXFacts.add_2. 
  destruct a as [v t].
  pose (ctx_replace_2_stronger _ _ _ _ _ _ H2) as Hu1; destruct Hu1 as [|Hu2];
    [contradict n; intuition | destruct Hu2 as [Hu3 Hu4]].
  eapply CTXFacts.remove_2; eauto.
  apply <- (H (v,t)); auto.
  apply CTXFacts.union_2; auto.
  destruct (CTX.E.eq_dec a (u,old)); subst.
  assert (old = new); [apply Heq_oldnew; auto | subst].
  apply CTXFacts.add_1; intuition.
  apply CTXFacts.add_2.
  apply CTXFacts.remove_2; intuition.
  apply <- (H a); auto.
  apply CTXFacts.union_3; auto.

  apply ctx_replace_preserves_wf; auto.
  apply <- (H (u, old)).
  apply CTXFacts.union_2; auto.

  intros v rho.
  destruct (H1 v rho) as [Hu1|Hu1]; clear H1; [
    | destruct Hu1 as [Hu2|Hu2]]; try (solve [intuition]).
  destruct (value_dec u v); subst.
  destruct (type_dec rho new); subst.
  right.

  destruct (CTXProperties.In_dec (v, old) GR).
  inversion Hpart; subst.
  pose (H3 v old).
  destruct o; auto.
  destruct H4; auto.
  apply Heq_oldnew in i; subst; right; auto.
  destruct (type_dec new old); subst.
  contradict Hu1; intuition.
  left; contradict n0.
  inversion H0; subst.
  apply H2 with (u:=v) (rho:=new) (sigma:=old); [
    apply <- (H (v,new))
    | apply <- (H (v,old))
  ]; intuition.

  left; intros HinRepl. 
  apply CTXFacts.add_3 in HinRepl; [|contradict n; injection n; intuition].
  apply CTXFacts.remove_3 in HinRepl; intuition.

  left; intros HinRepl.
  apply CTXFacts.add_3 in HinRepl; [|contradict n; injection n; intuition].
  apply CTXFacts.remove_3 in HinRepl; intuition.
Qed.

(* ============================================================================= *)

Lemma partition_weaken_into_left_1 : 
  forall G GL GR Gu GuR,
    G |-part GL (+) GR
    ->
    Gu |-part G (+) GuR
    ->
    Gu |-part CTX.union GL (CTX.diff GuR G) (+) GR.
Proof.
  intros G GL GR Gu GuR HpartG HpartGu.
  inversion HpartG; inversion HpartGu; subst; apply Partition; auto.

  clear H1 H7; intros a; split; intros Hin.
  apply -> (H5 a) in Hin.
  apply CTXFacts.union_1 in Hin.
  destruct Hin.
  apply -> (H a) in H1.
  apply CTXFacts.union_1 in H1.
  destruct H1.
  apply CTXFacts.union_2; apply CTXFacts.union_2; auto.
  apply CTXFacts.union_3; auto.
  destruct (CTXProperties.In_dec a G); subst.
  apply -> (H a) in i.
  apply CTXFacts.union_1 in i.
  destruct i.
  apply CTXFacts.union_2; apply CTXFacts.union_2; auto.
  apply CTXFacts.union_3; auto.
  apply CTXFacts.union_2; apply CTXFacts.union_3; auto.
  apply CTXFacts.diff_3; auto.

  apply CTXFacts.union_1 in Hin.
  destruct Hin.
  apply CTXFacts.union_1 in H1.
  destruct H1.
  apply <- (H5 a).
  apply CTXFacts.union_2.
  apply <- (H a).
  apply CTXFacts.union_2; auto.
  destruct (CTXProperties.In_dec a G); subst.
  apply <- (H5 a).
  apply CTXFacts.union_2; auto.
  apply CTXFacts.diff_1 in H1.
  apply <- (H5 a).
  apply CTXFacts.union_3; auto.
  apply <- (H5 a).
  apply CTXFacts.union_2.
  apply <- (H a).
  apply CTXFacts.union_3; auto.

  intros u rho; destruct (H7 u rho) as [Hu1|Hu2]; [|destruct Hu2 as [Hu1|Hu1]]; auto.
  right; left; contradict Hu1.
  apply <- (H (u,rho)).
  apply CTXFacts.union_3; auto.
  destruct (CTXProperties.In_dec (u, rho) GL); subst.
  right.
  destruct (CTXProperties.In_dec (u, rho) GR); subst.
  destruct (H1 u rho); intuition.
  left; auto.
  left; contradict Hu1.
  apply CTXFacts.union_1 in Hu1.
  destruct Hu1.
  intuition.
  apply CTXFacts.diff_1 in H2; auto.
Qed.

Lemma ctx_weaken_case_1 : 
  forall a G1 G2 G3,
    CTX.In a (CTX.union G1 (CTX.diff G2 G3))
    ->
    (CTX.In a G1) \/ ((CTX.In a G2) /\ ~ (CTX.In a G3)).
Proof.
  intros a G1 G2 G3 Hin.
  apply CTXFacts.union_1 in Hin.
  destruct Hin; [left|right; split]; intuition.
  apply CTXFacts.diff_1 in H; auto.
  apply CTXFacts.diff_2 in H; auto.
Qed.

Lemma partition_weaken_into_left_2_wf :
  forall G GL GR Gu GuR,
    G |-part GL (+) GR
    ->
    Gu |-part G (+) GuR
    ->
    CTX.union GL (CTX.diff GuR G) |-wf.
Proof.
  intros G GL GR Gu GuR Hpart_G Hpart_Gu.
  apply WFCtx.

  intros u rho Hin.
  inversion Hpart_G; inversion Hpart_Gu; subst.
  clear H1 H7; inversion H0; inversion H6; subst.
  clear H2 H3 H8 H9.
  apply CTXFacts.union_1 in Hin.
  destruct Hin.
  apply H1 with (rho:=rho).
  apply <- (H (u,rho)).
  apply CTXFacts.union_2; auto.
  apply CTXFacts.diff_1 in H2.
  apply H7 with (rho:=rho).
  apply <- (H5 (u,rho)).
  apply CTXFacts.union_3; auto.

  intros u sigma1 sigma2 Hin1 Hin2.
  apply ctx_weaken_case_1 in Hin1; apply ctx_weaken_case_1 in Hin2.
  inversion Hpart_G; inversion Hpart_Gu; subst. clear H1 H7.
  inversion H0; inversion H6; subst. clear H1 H3 H7 H9.
  eapply H8; [destruct Hin1 | destruct Hin2].
  apply <- (H5 (u, sigma1)).
  apply CTXFacts.union_2; auto.
  apply <- (H (u, sigma1)).
  apply CTXFacts.union_2; auto.
  destruct H1.
  apply <- (H5 (u, sigma1)).
  apply CTXFacts.union_3; auto.
  apply <- (H5 (u, sigma2)).
  apply CTXFacts.union_2; auto.
  apply <- (H (u, sigma2)).
  apply CTXFacts.union_2; auto.
  destruct H1.
  apply <- (H5 (u, sigma2)).
  apply CTXFacts.union_3; auto.

  intros x.
  inversion Hpart_G; inversion Hpart_Gu; subst.
  clear H1 H7; inversion H6; subst. clear H2.
  specialize H3 with (x:=x).
  destruct H3; [left|right].
  intros rho; specialize H2 with (rho:=rho).
  intros Hc; contradict H2.
  apply CTXFacts.union_1 in Hc.
  apply <- (H5 (ValVariable (Var (Free x)), rho)).
  destruct Hc.
  apply CTXFacts.union_2.
  apply <- (H (ValVariable (Var (Free x)), rho)).
  apply CTXFacts.union_2; auto.
  apply CTXFacts.diff_1 in H2.
  apply CTXFacts.union_3; auto.
  
  destruct H2.
  split; intros rho; specialize H2 with (rho:=rho); specialize H3 with (rho:=rho).
  intros Hc; contradict H2.
  apply CTXFacts.union_1 in Hc.
  destruct Hc.
  apply <- (H5 (ValName (Nm (Free x)), rho)).
  apply CTXFacts.union_2; auto.
  apply <- (H (ValName (Nm (Free x)), rho)).
  apply CTXFacts.union_2; auto.
  apply CTXFacts.diff_1 in H2.
  apply <- (H5 (ValName (Nm (Free x)), rho)).
  apply CTXFacts.union_3; auto.
  intros Hc; contradict H3.
  apply CTXFacts.union_1 in Hc.
  destruct Hc.
  apply <- (H5 (ValName (CoNm (Free x)), rho)).
  apply CTXFacts.union_2; auto.
  apply <- (H (ValName (CoNm (Free x)), rho)).
  apply CTXFacts.union_2; auto.
  apply CTXFacts.diff_1 in H3.
  apply <- (H5 (ValName (CoNm (Free x)), rho)).
  apply CTXFacts.union_3; auto.
Qed.
  
Lemma partition_weaken_into_left_2 : 
  forall G GL GR Gu GuR,
    G |-part GL (+) GR
    ->
    Gu |-part G (+) GuR
    ->
    CTX.union GL (CTX.diff GuR G) |-part GL (+) CTX.diff GuR G.
Proof.
  intros G GL GR Gu GuR HpartG HpartGu.
  inversion HpartG; inversion HpartGu; subst; apply Partition; auto.

  clear H1 H7; intros a; split; intros Hin.
  apply CTXFacts.union_1 in Hin.
  destruct Hin.
  apply CTXFacts.union_2; auto.
  apply CTXFacts.union_3; auto.
  apply CTXFacts.union_1 in Hin.
  destruct Hin.
  apply CTXFacts.union_2; auto.
  apply CTXFacts.union_3; auto.

  eapply partition_weaken_into_left_2_wf; eauto.

  intros u rho; destruct (H7 u rho) as [Hu1|Hu2]; [|destruct Hu2 as [Hu1|Hu1]].
  left; contradict Hu1.
  apply <- (H (u,rho)).
  apply CTXFacts.union_2; auto.
  right; left.
  contradict Hu1.
  apply CTXFacts.diff_1 in Hu1; auto.
  right; right; auto.
Qed.

Lemma partition_empty : 
  forall G,
    G |-wf
    ->
    G |-part G (+) CTX.empty.
Proof.
  intros G Hpart.
  inversion Hpart; subst; apply Partition; auto.
  intros a; rewrite CTXFacts.union_iff; rewrite CTXFacts.empty_iff; intuition.
  right; left; rewrite CTXFacts.empty_iff; intuition.
Qed.

(* 
Old version - kept around for reference in case it is needed.
*)
Lemma partition_empty_old : 
  forall G GL GR,
    G |-part GL (+) GR
    ->
    GR |-part GR (+) CTX.empty.
Proof.
  intros; apply partition_empty; eapply partition_wf_right; eauto.
Qed.

(* ============================================================================= *)

Lemma ctx_remove_preserves_partition_both : 
  forall u rho G GL GR,
    ~ CTX.In (u, rho) G
    -> 
    CTX.add (u, rho) G |-part GL (+) GR
    -> 
    G |-part CTX.remove (u, rho) GL (+) CTX.remove (u, rho) GR.
Proof.
  intros u rho G GL GR Hnotin Hpart.
  inversion Hpart; subst.
  apply Partition.

  intros a; split; intros Hin.
  destruct a as [v sigma]; destruct (CTX.E.eq_dec (u, rho) (v, sigma)) as [e|n]; [
    injection e; intros; subst; intuition
    |
  ].
  apply CTXFacts.add_2 with (x:=(u,rho)) in Hin.
  apply -> (H (v, sigma)) in Hin.
  apply CTXFacts.union_1 in Hin.
  (destruct Hin; [apply CTXFacts.union_2|apply CTXFacts.union_3]);
  (apply CTXFacts.remove_2; [
      intuition
    | auto
  ]).
  
  apply CTXFacts.union_1 in Hin.
  destruct a as [v sigma]; destruct (CTX.E.eq_dec (u, rho) (v, sigma)) as [e|n]; [
    injection e; intros; subst; intuition
    |
  ]; try (apply CTXFacts.remove_1 in H2; intuition).
  destruct Hin; eapply CTXFacts.remove_3 in H2; [
    apply CTXFacts.union_2 with (s':=GR) in H2
    | apply CTXFacts.union_3  with (s:=GL) in H2
  ]; apply <- (H (v, sigma)) in H2; apply CTXFacts.add_3 in H2; auto.

  apply subset_preserves_well_formed_ctx with (G2:=G) in H0; intuition.
  
  intros v sigma.
  specialize H1 with (u:=v) (rho:=sigma).
  destruct H1; [left|right;destruct H1; [left|right]]; auto; 
    intros Hc; contradict H1; apply CTXFacts.remove_3 in Hc; auto.
Qed.

(* ============================================================================= *)

Lemma fresh_for_ctx_remove_zero_in :
  forall u rho G,
    G |-wf
    ->
    fresh_for_ctx u G
    ->
    ~ (CTX.In (u, rho) G).
Proof.
  intros u rho G Hwf Hfresh Hin; inversion Hfresh as [? ? ? U1|]; subst.
  specialize (U1 u rho); destruct u; intuition.
  inversion Hwf as [? U1 _ _]; subst; specialize (U1 k rho Hin); inversion U1.
Qed.

Lemma fresh_for_ctx_remove_zero :
  forall u rho G,
    G |-wf
    ->
    fresh_for_ctx u G
    ->
    CTX.Equal (CTX.remove (u, rho) G) G.
Proof.
  intros u rho G Hwef Hfresh a.
  rewrite CTXFacts.remove_iff.
  intuition; subst.
  revert H; apply fresh_for_ctx_remove_zero_in; auto.
Qed.

Lemma lookup_ctx_equal_wf :
  forall G1,
    G1 |-wf 
    ->
    forall G2,
      CTX.Equal G1 G2
      ->
      G2 |-wf.
Proof.
  intros G1 Hwf G2 Heq; constructor; inversion Hwf as [? U1 U2 U3]; subst; crush.
  eapply U1; rewrite Heq; eauto.
  eapply U2; rewrite Heq; eauto.
  specialize (U3 x); destruct U3 as [U4|U4].
  left; intros rho; specialize (U4 rho); rewrite <- Heq; auto.
  right; split; destruct U4 as [U5 U6]; intros rho; specialize (U5 rho); specialize (U6 rho); rewrite <- Heq; assumption.
Qed.

Lemma lookup_ctx_equal :
  forall G1 v sigma,
    G1 |-v v : sigma
    -> 
    forall G2,
      CTX.Equal G1 G2
      ->
      G2 |-v v : sigma.
Proof.
  intros G1 v sigma Hlookup; inversion Hlookup; subst; intros G2 Heq; [ apply LContext | apply LToken ];
    try (solve [eapply lookup_ctx_equal_wf; eauto]).
  rewrite <- Heq; auto.
Qed.

(*
Lemma lookup_strengthen :
  forall G v sigma,
    G |-v v : sigma
    -> 
    forall u rho, 
      fresh_for_ctx u G
      ->
      CTX.remove (u, rho) G |-v v : sigma.
NOT NEEDED AT PRESENT???
*)

(*
Lemma free_values_in_context_strengthen: 
  forall G1 G2 P,
    CTX.Subset G1 G2
    ->
    free_values_in_context G1 P 
    ->
    free_values_in_context G2 P.
NOT NEEDED AT PRESENT???
*)

Lemma remove_subset :
  forall u rho G,
    G |-wf
    ->
    fresh_for_ctx u G
    ->
    CTX.Subset G (CTX.remove (u, rho) G).
Proof.
  intros u rho G Hwf Hfresh a Hin.
  inversion Hfresh; subst.
  apply CTXFacts.remove_2; auto.
  specialize H0 with (v:=u) (sigma:=rho).
  destruct H0; [|intuition].
  intros Heq; destruct a; unfold ctx_elt_as_DT.eq in Heq; 
    injection Heq; intros; subst; intuition.
  apply CTXFacts.remove_2; auto.
  intros Heq; destruct a; unfold ctx_elt_as_DT.eq in Heq; 
    injection Heq; intros; subst.
  inversion Hwf; subst.
  specialize H with (u:=k) (rho:=t).
  pose (H Hin) as Hu1.
  inversion Hu1.
Qed.

Lemma lookup_wf_ctx :
  forall G u rho, 
    G |-v u : rho
    -> 
    G |-wf.
Proof.
  intros G u rho Hlookup; inversion Hlookup; auto.
Qed.

Lemma add_remove_comm :
  forall u v rho sigma G, 
    u <> v
    ->
    CTX.eq
      (CTX.add (v, rho) (CTX.remove (u, sigma) G))
      (CTX.remove (u, sigma) (CTX.add (v, rho) G)).
Proof.
  intros u v rho sigma G Hneq.
  intros a; destruct a as [v2 sigma2]; split; intros Hin; 
    destruct (value_dec v2 v); destruct (value_dec v2 u); subst.
  contradiction Hneq; intuition.
  apply CTXFacts.remove_2; [unfold ctx_elt_as_DT.eq; intros Heq; injection Heq; intros; subst|]; intuition.
  destruct (type_dec sigma2 rho); subst.
  intuition.
  apply CTXFacts.add_3 in Hin; [
    | unfold ctx_elt_as_DT.eq; intros Heq; injection Heq; intros; subst; intuition
  ].
  apply CTXFacts.remove_3 in Hin.
  apply CTXFacts.add_2; auto.
  apply CTXFacts.add_3 in Hin; [
    | unfold ctx_elt_as_DT.eq; intros Heq; injection Heq; intros; subst; intuition
  ].
  destruct (type_dec sigma2 sigma); subst.
  apply CTXFacts.remove_1 in Hin; [
    inversion Hin
    | unfold ctx_elt_as_DT.eq; reflexivity
  ].
  apply CTXFacts.remove_3 in Hin.
  apply CTXFacts.remove_2; [
    unfold ctx_elt_as_DT.eq; intros Heq; injection Heq; intros; subst; intuition
      |
  ].
  apply CTXFacts.add_2; auto.
  apply CTXFacts.add_3 in Hin; [
    | unfold ctx_elt_as_DT.eq; intros Heq; injection Heq; intros; subst; intuition
  ].
  apply CTXFacts.remove_3 in Hin. 
  apply CTXFacts.remove_2; [
    unfold ctx_elt_as_DT.eq; intros Heq; injection Heq; intros; subst; intuition
    |
  ].
  apply CTXFacts.add_2; auto.
  subst; intuition.
  apply CTXFacts.remove_3 in Hin. 
  destruct (type_dec sigma2 rho); subst.
  intuition.
  apply CTXFacts.add_3 in Hin; [
    | unfold ctx_elt_as_DT.eq; intros Heq; injection Heq; intros; subst; intuition
  ].
  apply CTXFacts.add_2; auto.
  apply CTXFacts.remove_2; [
    unfold ctx_elt_as_DT.eq; intros Heq; injection Heq; intros; subst; intuition
    |
  ]; auto.
  apply CTXFacts.add_2.
  destruct (type_dec sigma2 sigma); subst.
  apply CTXFacts.remove_1 in Hin; [
    inversion Hin
    | unfold ctx_elt_as_DT.eq; reflexivity
  ].
  apply CTXFacts.remove_2; [
    unfold ctx_elt_as_DT.eq; intros Heq; injection Heq; intros; subst; intuition
    |
  ]; auto.
  apply CTXFacts.remove_3 in Hin.
  apply CTXFacts.add_3 in Hin; [
    | unfold ctx_elt_as_DT.eq; intros Heq; injection Heq; intros; subst; intuition
  ]; auto.
  apply CTXFacts.remove_3 in Hin.
  apply CTXFacts.add_3 in Hin; [
    | unfold ctx_elt_as_DT.eq; intros Heq; injection Heq; intros; subst; intuition
  ].
  apply CTXFacts.add_2.
  apply CTXFacts.remove_2; [
    unfold ctx_elt_as_DT.eq; intros Heq; injection Heq; intros; subst; intuition
    |
  ]; auto.
Qed.  

Lemma add_add_comm :
  forall u v rho sigma G, 
    CTX.Equal
      (CTX.add (v, rho) (CTX.add (u, sigma) G))
      (CTX.add (u, sigma) (CTX.add (v, rho) G)).
Proof.
  intuition.
Qed.  

Lemma remove_remove_comm :
  forall u v rho sigma G, 
    CTX.Equal
      (CTX.remove (v, rho) (CTX.remove (u, sigma) G))
      (CTX.remove (u, sigma) (CTX.remove (v, rho) G)).
Proof.
  intros; intro; repeat (rewrite CTXFacts.remove_iff); intuition.
Qed.

Lemma add_cong :
  forall u sigma G1 G2, 
    CTX.Equal G1 G2
    ->
    CTX.Equal
      (CTX.add (u, sigma) G1)
      (CTX.add (u, sigma) G2).
Proof.
  intros; intro; repeat (rewrite CTXFacts.add_iff); intuition; right; intuition; 
    match goal with | [ H : CTX.Equal _ _ |- _ ] => apply H end; auto.
Qed.

Lemma remove_cong :
  forall u sigma G1 G2, 
    CTX.Equal G1 G2
    ->
    CTX.Equal
      (CTX.remove (u, sigma) G1)
      (CTX.remove (u, sigma) G2).
Proof.
  intros; intro; repeat (rewrite CTXFacts.remove_iff); intuition;
    match goal with | [ H : CTX.Equal _ _ |- _ ] => apply H end; auto.
Qed.

Lemma empty_ctx_wf : 
  CTX.empty |-wf.
Proof.
  apply WFCtx.
  intros u rho Hin; contradict Hin; apply CTXFacts.empty_1.
  intros u sigma1 sigma2 Hin1 Hin2; contradict Hin1; apply CTXFacts.empty_1.
  intros; left; intros.
  apply CTXFacts.empty_1.
Qed.

(* ============================================================================= *)

Lemma free_ids_value_neq : 
  forall u v rho G,
    G |-wf
    ->
    fresh_for_ctx u G
    ->
    CTX.In (v, rho) G
    ->
    free_ids_value u <> free_ids_value v.
Proof.
  intros u v rho G Hwf Hfresh Hin Heq.
  inversion Hfresh; subst.
  specialize (H0 v rho); destruct H0; intuition.
  inversion Hwf; subst.
  specialize (H v rho Hin).
  inversion H; subst; crush.
Qed.

Lemma free_ids_value_new_var : 
  forall u x, 
    ~ In x (free_ids_value u)
    -> 
    (ValVariable (Var (Free x))) <> u.
Proof.
  crush.
Qed.

Lemma fresh_for_ctx_name_conm : 
  forall n G,
    G |-wf 
    ->
    fresh_for_ctx (ValName (CoNm n)) G
    ->
    fresh_for_ctx (ValName (Nm n)) G.
Proof.
  intros n G Hwf Hfresh; inversion Hfresh as [? ? H1 H2 | H1 H2]; subst; constructor; inversion H1.
  constructor.
  subst.
  intros v sigma; assert (H3 := H2 v sigma); clear H2.
  destruct H3.
  left; auto.
  right; simpl in *; assumption.
Qed.

Lemma fresh_for_ctx_name_nm : 
  forall n G,
    G |-wf 
    ->
    fresh_for_ctx (ValName (Nm n)) G
    ->
    fresh_for_ctx (ValName (CoNm n)) G.
Proof.
  intros n G Hwf Hfresh; inversion Hfresh as [? ? H1 H2 | H1 H2]; subst; constructor; inversion H1.
  constructor.
  subst.
  intros v sigma; assert (H3 := H2 v sigma); clear H2.
  destruct H3.
  left; auto.
  right; simpl in *; assumption.
Qed.

Lemma fresh_for_ctx_add_var : 
  forall G u x sigma, 
    G |-wf
    ->
    free_value u 
    ->
    fresh_for_ctx u G
    -> 
    ~ In x (free_ids_value u)
    -> 
    fresh_for_ctx u (CTX.add (ValVariable (Var (Free x)), sigma) G).
Proof.
  constructor; auto.
  intros v rho.
  rewrite CTXFacts.add_iff.
  destruct (list_eq_dec string_dec (free_ids_value u) (free_ids_value v)) as [e|n].
  rewrite e in *; left; crush.
  eapply free_ids_value_neq in e; destruct e; eauto.
  right; assumption.
Qed.

Lemma wf_ctx_unique_type : 
  forall u rho sigma G, G |-wf -> CTX.In (u, rho) G -> CTX.In (u, sigma) G -> rho = sigma.
Proof.
  intros u rho sigma G Hwf Hin_rho Hin_sigma; inversion Hwf as [? _ U2 _]; subst.
  eapply U2; eauto.
Qed.

Lemma fresh_for_ctx_replace: 
  forall v G u old new,
    G |-wf
    ->
    free_value v
    ->
    fresh_for_ctx v G 
    ->
    CTX.In (u, old) G
    ->
    fresh_for_ctx v (ctx_replace u old new G).
Proof.
  constructor; auto.
  intros v' rho'.
  unfold ctx_replace.
  rewrite CTXFacts.add_iff.
  rewrite CTXFacts.remove_iff.
  destruct (list_eq_dec string_dec (free_ids_value v) (free_ids_value v')) as [e|n].
  left; crush; 
    (match goal with
    | [ H : G |-wf |- _ ] => 
      inversion H as [? U1 U2 U3]; subst      
     end; 
    match goal with
      | [ H : fresh_for_ctx _ _ |- _ ] => 
        inversion H as [? ? ? U4|]; subst; 
          [match goal with [ H : CTX.In (v', ?T) G |- _ ] => specialize (U4 v' T); destruct U4; intuition end
            | match goal with | [ H : free_value ?k |- _ ] => inversion H end]
    end).
  right; assumption.
Qed.

(* ============================================================================= *)

Lemma partition_remove_token : 
  forall G GL GR, forall (k:token), forall rho, 
    G |-part GL (+) GR
    -> 
    G |-part CTX.remove (ValToken k, rho) GL (+) GR.
Proof.
  intros G GL GR k rho Hpart; inversion Hpart; subst; constructor; auto.
  rewrite H; intros a.
  repeat (rewrite CTXFacts.union_iff).
  rewrite CTXFacts.remove_iff.
  intuition.
  left; split; auto.
  intros; subst.
  apply partition_wf_left in Hpart.
  inversion Hpart; subst.
  specialize (H2 k rho H3).
  inversion H2.
  intros u sigma.
  rewrite CTXFacts.remove_iff.
  specialize (H1 u sigma); destruct H1; intuition.
Qed.

(* ============================================================================= *)

Lemma lookup_channel_in :
  forall G u s, 
    G |-v u : TChannel s 
    -> 
    CTX.In (u, TChannel s) G.
Proof.
  intros G u s Hlookup.
  inversion Hlookup; subst; auto.
Qed.
 
(* ============================================================================= *)

Lemma in_not_fresh_for_ctx_nm_nm : 
  forall x rho G, 
    CTX.In (ValName (Nm (Free x)), rho) G
    -> 
    ~ fresh_for_ctx (Nm (Free x)) G.
Proof.
  intros x rho G Hin Hfresh_x; inversion Hfresh_x as [? ? _ U1|]; subst.
  specialize (U1 (Nm (Free x)) rho); destruct U1; subst; intuition.
Qed.  

Lemma in_not_fresh_for_ctx_conm_nm : 
  forall x rho G, 
    CTX.In (ValName (CoNm (Free x)), rho) G
    -> 
    ~ fresh_for_ctx (Nm (Free x)) G.
Proof.
  intros x rho G Hin Hfresh_x; inversion Hfresh_x as [? ? _ U1|]; subst.
  specialize (U1 (CoNm (Free x)) rho); destruct U1; subst; intuition.
Qed.  

(* ============================================================================= *)

Lemma ctx_add_wf_dual_names :
forall G x s,
    fresh_for_ctx (Nm (Free x)) G
    ->
    G |-wf
    ->
    (CTX.add (ValName (Nm (Free x)), TChannel s) (CTX.add (ValName (CoNm (Free x)), TChannel (SDual s)) G)) |-wf.
Proof.
  intros G x s Hfresh_x Hwf.
  inversion Hwf as [? U1 U2 U3]; subst.
  constructor; intros; repeat (rewrite CTXFacts.add_iff in *).
  destruct H; crush.
  constructor.
  constructor.
  eapply U1; eauto.
  repeat match goal with 
    | [ H : _ \/ _ |- _ ] => destruct H
  end; crush.
  contradict Hfresh_x; eapply in_not_fresh_for_ctx_nm_nm; eauto.
  contradict Hfresh_x; eapply in_not_fresh_for_ctx_conm_nm; eauto.
  contradict Hfresh_x; eapply in_not_fresh_for_ctx_nm_nm; eauto.
  contradict Hfresh_x; eapply in_not_fresh_for_ctx_conm_nm; eauto.
  eapply U2; eauto.
  destruct (string_dec x0 x); subst.
  left; intros rho U4; repeat (rewrite CTXFacts.add_iff in *); 
    destruct U4 as [|U5]; 
      [crush | destruct U5; [crush|]].
  inversion Hfresh_x as [? ? _ U4|]; subst.
  specialize (U4 (Var (Free x)) rho); destruct U4; intuition.
  specialize (U3 x0); destruct U3 as [U4|U4]; [left | destruct U4 as [U5 U6]; right; split];
    intros rho Hin; repeat (rewrite CTXFacts.add_iff in *);
      repeat 
        match goal with 
          | [ H : _ \/ _ |- _ ] => destruct H
          | [ H : ( _ , _ ) = ( _ , _ ) |- _ ] => discriminate H
        end.
  revert H; apply U4.
  contradict n; injection H; intros; subst; reflexivity.
  revert H; apply U5.
  contradict n; injection H; intros; subst; reflexivity.
  revert H; apply U6.
Qed.  

(* ============================================================================= *)

Lemma ctx_add_preserves_partition_left_dual_names :
  forall G GL GR x s,
    fresh_for_ctx (Nm (Free x)) G
    ->
    G |-part GL (+) GR
    ->
    (CTX.add (ValName (Nm (Free x)), TChannel s) (CTX.add (ValName (CoNm (Free x)), TChannel (SDual s)) G)) |-part 
      (CTX.add (ValName (Nm (Free x)), TChannel s) (CTX.add (ValName (CoNm (Free x)), TChannel (SDual s)) GL)) (+) GR.
Proof.
  intros G GL GR x s Hfresh_x Hpart.
  inversion Hfresh_x as [? ? _ U1| ]; subst; clear Hfresh_x.
  inversion Hpart as [? ? ? Heq Hwf U2]; subst.
  constructor.
  intros a; specialize (Heq a).
  repeat (rewrite CTXFacts.add_iff in * || rewrite CTXFacts.union_iff in *).
  rewrite Heq; clear Heq.
  intuition.
  apply ctx_add_wf_dual_names; auto.
  constructor; [constructor|]; auto.
  intros u rho; specialize (U2 u rho).
  destruct U2.
  destruct (in_dec string_dec x (free_ids_value u)).
  right; left.
  intros Hin; specialize (U1 u rho).
  destruct U1.
  contradict H0.
  eapply partition_is_subset_right; eauto.
  contradict H0.
  (repeat
    match goal with
      | [ x : value |- _ ] => destruct x
      | [ x : variable |- _ ] => destruct x
      | [ x : name |- _ ] => destruct x
      | [ x : id |- _ ] => destruct x
    end);
  simpl in *; crush.
  left.
  repeat rewrite CTXFacts.add_iff; crush.
  destruct H.
  right; left; auto.
  right; right; auto.
Qed.

(* ============================================================================= *)

Lemma typed_ctx_wf : 
  forall G P,
    G |-p P -> G |-wf.
Proof.
  intros G P Htyp; induction Htyp; try (solve [inversion H; auto]).
  inversion H1; auto.
  inversion IHHtyp1; auto.
  assert (exists x : free_id, ~ In x ((free_ids_context G) ++ L)).
  apply fresh_free_id_exists.
  destruct H1.
  apply subset_preserves_well_formed_ctx 
    with (G1:=
      CTX.add (ValName (Nm (Free x)), TChannel s) 
      (CTX.add (ValName (CoNm (Free x)), TChannel (SDual s)) 
        G)).
  apply H0 with (x:=x); intuition.
  intros a Hin.
  apply CTXFacts.add_2.
  apply CTXFacts.add_2.
  auto.
Qed.

(* ============================================================================= *)

Lemma partition_empty_typing : 
  forall G P,
    G |-p P
    ->
    G |-part G (+) CTX.empty.
Proof.
  intros G P Htyp.
  apply Partition.
  split; intros Hu1.
  apply CTXFacts.union_2; auto.
  apply CTXFacts.union_1 in Hu1; destruct Hu1; auto.
  contradict H; apply CTXFacts.empty_1.
  apply typed_ctx_wf in Htyp; auto.
  intros u rho.
  right; left.
  apply CTXFacts.empty_1.
Qed.

(* ============================================================================= *)

Lemma part_preserved_by_add_right : 
  forall x s G,
    ~ In x (free_ids_context G)
    ->
    G |-wf
    ->
    CTX.add (ValName (Nm (Free x)), TChannel s)
      (CTX.add (ValName (CoNm (Free x)), TChannel (SDual s)) G) |-part 
        G 
        (+) 
          CTX.add (ValName (Nm (Free x)), TChannel s)
          (CTX.add (ValName (CoNm (Free x)), TChannel (SDual s)) CTX.empty).
Proof.
  intros x s G Hin Hwf.
  apply partition_comm.
  apply ctx_add_preserves_partition_left_dual_names; 
    [ |
      apply partition_comm; apply partition_empty; auto
    ].
  constructor.
  constructor.
  intros v sigma.
  destruct (CTXProperties.In_dec (v, sigma) G); [right|intuition].
  simpl; intros Heq; contradict Hin.
  eapply free_ids_context_vs_context; eauto.
Qed.

(* ============================================================================= *)

(* ============================================================================= *)

(* ============================================================================= *)

(* ============================================================================= *)

Lemma free_ids_context_iff :
  forall y G,
    In y (free_ids_context G) <-> exists u, exists rho, (CTX.In (u, rho) G /\ In y (free_ids_value u)).
Proof.
  intros y G.
  unfold free_ids_context.
  rewrite in_flat_map.
  split; intros H.
  destruct H as [a H]; destruct a; destruct H as [H1 H2].
  simpl in *.
  exists v; exists t; split; auto.
  assert (SetoidList.InA CTX.E.eq (v, t) (CTX.elements G)).
  rewrite SetoidList.InA_alt.
  eexists; split; eauto; reflexivity.
  rewrite CTX.elements_spec1 in H; auto.

  destruct H as [u H]; destruct H as [t H]; destruct H as [H1 H2].
  exists (u, t); simpl; split; auto.
  apply context_in_vs_elements_in; auto.
Qed.  

(* ============================================================================= *)

Lemma free_ids_values_value :
  forall y u, 
    In y (free_ids_value u) -> In u (free_values_value u).
Proof.
  intros y u Hin.
  (repeat (match goal with
             | [ x : value |- _ ] => destruct x
             | [ x : variable |- _ ] => destruct x
             | [ x : name |- _ ] => destruct x
             | [ x : id |- _ ] => destruct x
           end; simpl in *; subst
  )); 
  try solve [intuition].
Qed.

Lemma free_ids_values_proc :
  forall P y, 
    In y (free_ids_proc P) -> exists u, In u (free_values_proc P) /\ In y (free_ids_value u).
Proof.
  intros P; induction P; intros y Hin; simpl in *; (repeat rewrite in_app_iff in *); (repeat destruct Hin as [Hin|Hin]);
    (try solve [eexists; (repeat rewrite in_app_iff); split; [left; eapply free_ids_values_value; eauto|eauto]]);
    (try solve [eexists; (repeat rewrite in_app_iff); split; [right; left; eapply free_ids_values_value; eauto|eauto]]);
    (try solve [
      apply IHP in Hin; destruct Hin as [u Hin]; destruct Hin as [Hin1 Hin2]; 
        eexists; (repeat rewrite in_app_iff); split; [right; eauto|eauto]]);
    (try solve [
      apply IHP in Hin; destruct Hin as [u Hin]; destruct Hin as [Hin1 Hin2]; 
        eexists; (repeat rewrite in_app_iff); split; eauto]);
    (try solve [
      apply IHP1 in Hin; destruct Hin as [u Hin]; destruct Hin as [Hin1 Hin2];
        eexists; (repeat rewrite in_app_iff); split; eauto]);
    (try solve [
      apply IHP2 in Hin; destruct Hin as [u Hin]; destruct Hin as [Hin1 Hin2];
        eexists; (repeat rewrite in_app_iff); split; eauto]);
    intuition.
Qed.

(* ============================================================================= *)

Lemma free_ids_proc1 :
  forall P y,
    In y (free_ids_proc P) -> exists u, (In u (free_values_proc P)  /\ In y (free_ids_value u)).
Proof.
  intros P; induction P; intros y Hin; simpl in *; try (rewrite in_app_iff in Hin);
  repeat (match goal with 
    | [ H : False |- _ ] => destruct H
    | [ H : _ \/ _ |- _ ] => destruct H
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : In _ ( _ ++ _ ) |- _ ] => rewrite in_app_iff in H
    | [ H : In _ (free_ids_value _) |- exists _ , _ ] => eexists; (repeat rewrite in_app_iff); split
    | [ IH : (forall z , In _ (free_ids_proc ?P) -> _ ) , H : In _ (free_ids_proc ?P) |- exists _ , _ ] => specialize (IH _ H)
    | [ H : exists u, _ |- _ ] => destruct H
  end); 
  try solve [eauto];
  try solve [left; eapply free_ids_values_value; eauto];
  try solve [right; left; eapply free_ids_values_value; eauto];
  try solve [right; right; eapply free_ids_values_value; eauto].
Qed.

Lemma free_ids_in_context_1 :
  forall G P x, 
    (G |-p P) 
    -> 
    In x (free_ids_proc P)
    -> 
    In x (free_ids_context G).
Proof.
  intros G P x Htyp Hin.
  apply free_values_in_context_1 in Htyp.
  rewrite free_ids_context_iff.
  apply free_ids_proc1 in Hin.
  destruct Hin as [u Hin]; destruct Hin as [Hin1 Hin2].
  apply Htyp in Hin1; destruct Hin1.
  eexists; eexists; split; eauto.
Qed.

(* ============================================================================= *)

Lemma part_typed_find_type : 
  forall u rho P G GL GR, 
    G |-part GL (+) GR 
    -> 
    GL |-p P
    -> 
    In u (free_values_proc P) 
    ->
    CTX.In (u, rho) G 
    -> 
    CTX.In (u, rho) GL.
Proof.
  intros u rho P G GL GR Hpart Htyp Hin1 Hin2.
  eapply free_values_in_context_1 in Hin1; eauto.
  destruct Hin1 as [sigma Hin1].
  replace rho with sigma; auto.
  eapply partition_is_subset_left in Hin1; eauto.
  apply partition_wf in Hpart.
  inversion Hpart; subst.
  apply (H0 u); auto.
Qed. 

(* ============================================================================= *)

Lemma free_values_insert_value1 : 
  forall u v n,
    In v (free_values_value u) -> In v (free_values_value (insert_value n u)).
Proof.
  intros u v n Hin; destruct u; 
    repeat 
      (match goal with 
         | [ n : name |- _ ] => destruct n; simpl
         | [ i : id |- _ ] => destruct i; simpl
         | [ v : variable |- _ ] => destruct v; simpl
       end); intuition.
Qed.

Lemma free_values_insert_proc1 : 
  forall P v n,
    In v (free_values_proc P) -> In v (free_values_proc (insert_proc n P)).
Proof.
  intros P; induction P; intros u n Hin; simpl in *; auto; 
    repeat 
      (match goal with 
         | [ H : _ \/ _ |- _ ] => destruct H
         | [ H : In _ ( _ ++ _ ) |- _ ] => repeat (rewrite in_app_iff in H)
         | [ |- In _ ( _ ++ _ ) ] => repeat (rewrite in_app_iff)
         | [ H : In _ (free_values_value ?v) |- In _ (free_values_value (insert_value _ ?v)) \/ _ ] => left; apply free_values_insert_value1; auto
         | [ H : In _ (free_values_value ?v) |- _ \/ _ ] => right
         | [ H : In _ (free_values_proc ?P) |- In _ (free_values_value _) \/ _ ] => right
         | [ |- In _ (free_values_proc ?P) ] => apply IHP; auto
         | [ H : In _ (free_values_proc ?P) |- In _ (free_values_proc (insert_proc _ ?P)) \/ _ ] => left; apply IHP1; auto
         | [ H : In _ (free_values_proc ?P) |- _ \/ In _ (free_values_proc (insert_proc _ ?P)) ] => right; apply IHP2; auto
       end).
Qed.
  
Lemma free_values_insert_value2 : 
  forall u v n,
    In v (free_values_value (insert_value n u)) -> In v (free_values_value u).
Proof.
  intros u v n Hin; destruct u;
    repeat 
      (match goal with 
         | [ n : name |- _ ] => destruct n; simpl in *
         | [ i : id |- _ ] => destruct i; simpl in *
         | [ v : variable |- _ ] => destruct v; simpl in *
       end); try solve [intuition];
      destruct (le_lt_dec n b); try solve [intuition].
Qed.

Lemma free_values_insert_proc2 : 
  forall P v n,
    In v (free_values_proc (insert_proc n P)) -> In v (free_values_proc P).
Proof.
  intros P; induction P; intros u n Hin; simpl in *; auto; 
    repeat 
      (match goal with 
         | [ H : _ \/ _ |- _ ] => destruct H
         | [ H : In _ ( _ ++ _ ) |- _ ] => repeat (rewrite in_app_iff in H)
         | [ |- In _ ( _ ++ _ ) ] => repeat (rewrite in_app_iff)
         | [ H : In _ (free_values_value (insert_value _ _)) |- _ ] => apply free_values_insert_value2 in H
         | [ H : In _ (free_values_value ?v) |- In _ (free_values_value ?v) \/ _ ] => left; auto
         | [ H : In _ (free_values_value ?v) |- _ \/ _ ] => right
         | [ H : In _ (free_values_proc ?P) |- In _ (free_values_value _) \/ _ ] => right
         | [ |- In _ (free_values_proc ?P) ] => eapply IHP; eauto
         | [ H : In _ (free_values_proc (insert_proc _ ?P)) |- In _ (free_values_proc ?P) \/ _ ] => left; eapply IHP1; eauto
         | [ H : In _ (free_values_proc (insert_proc _ ?P)) |- _ \/ In _ (free_values_proc ?P) ] => right; eapply IHP2; eauto
       end).
Qed.
  
(* ============================================================================= *)

Lemma free_values_open_value1 : 
  forall u v x n,
    In v (free_values_value (open_value x n u))
    -> 
    (In x (free_ids_value v) \/ In v (free_values_value u)).
Proof.
  intros u v x n Hin; destruct u.
  destruct n0; simpl in *.
  destruct i;  simpl in *.
  destruct Hin as [Hin|Hin]; [|destruct Hin].
  subst.
  right; auto.
  destruct (eq_nat_decide b n) in Hin.
  crush.
  destruct (le_lt_dec b n) in Hin.
  crush.
  crush.
  destruct i; simpl in Hin.
  destruct Hin as [Hin|Hin]; [|destruct Hin].
  subst.
  right; auto.
  crush.
  destruct (eq_nat_decide b n) in Hin.
  crush.
  destruct (le_lt_dec b n) in Hin.
  crush.
  crush.

  simpl in *.
  destruct Hin.

  destruct v0; simpl in Hin.
  destruct i; simpl in Hin.
  destruct Hin as [Hin|Hin]; [|destruct Hin].
  subst.
  right; auto.
  crush.
  destruct (eq_nat_decide b n) in Hin.
  crush.
  destruct (le_lt_dec b n) in Hin.
  crush.
  crush.
Qed.  

Lemma free_values_open_proc1 : 
  forall P v x n,
    In v (free_values_proc (open_proc x n P))
    -> 
    (In x (free_ids_value v) \/ In v (free_values_proc P)).
Proof.
  intros P; induction P; intros x u n Hin; simpl in *;
    repeat 
      (match goal with 
         | [ H : False |- _ ] => destruct H
         | [ H : _ \/ _ |- _ ] => destruct H; subst
         | [ H : In _ ( _ ++ _ ) |- _ ] => repeat (rewrite in_app_iff in H)
         | [ H : In _ (free_values_value (open_value _ _ _)) |- _ ] => apply free_values_open_value1 in H; subst
         | [ H : In _ (free_ids_value ?v) |- In _ (free_ids_value ?v) \/ _ ] => left; auto
         | [ H : In _ (free_values_proc (open_proc _ _ _)) |- _ ] => eapply IHP in H; eauto
         | [ H : In _ (free_values_proc (open_proc _ _ _)) |- _ ] => eapply IHP1 in H; eauto
         | [ H : In _ (free_values_proc (open_proc _ _ _)) |- _ ] => eapply IHP2 in H; eauto
         | [ |- context[ _ ++ _ ] ] => rewrite in_app_iff; auto
       end; (try rewrite in_app_iff)); 
      try tauto.
Qed.

(* ============================================================================= *)

Lemma free_values_open_value2 : 
  forall u v x n,
    In v (free_values_value u)
    ->
    In v (free_values_value (open_value x n u)).
Proof.
  intros u v x n Hin.
  destruct u as [nm|t|var]; [destruct nm as [i|i]; destruct i | |destruct var as [i]; destruct i]; simpl in *; auto;
    destruct (eq_nat_decide b n) in Hin; destruct (le_lt_dec b n) in Hin; crush.
Qed.

Lemma free_values_open_proc2 : 
  forall P v x n,
    In v (free_values_proc P)
    ->
    In v (free_values_proc (open_proc x n P)).
Proof.
  intros P; induction P; intros u x n Hin; simpl in *;
    repeat 
      (match goal with 
         | [ H : False |- _ ] => destruct H
         | [ H : _ \/ _ |- _ ] => destruct H; subst
         | [ H : In _ ( _ ++ _ ) |- _ ] => repeat (rewrite in_app_iff in H)
         | [ H : In _ (free_values_value ?v) |- In _ (free_values_value (open_value _ _ ?v)) \/ _ ] => left; apply free_values_open_value2; auto
         | [ H : In _ (free_values_value _) |- In _ (free_values_value (open_value _ _ _)) \/ _ ] => right
         | [ H : In _ (free_values_proc _) |- In _ (free_values_value (open_value _ _ _)) \/ _ ] => right
         | [ H : In _ (free_values_proc _) |- In _ (free_values_proc (open_proc _ _ _)) ] => apply IHP; auto
         | [ H : In _ (free_values_proc _) |- _ ] => eapply IHP1 in H; eauto
         | [ H : In _ (free_values_proc _) |- _ ] => eapply IHP2 in H; eauto
       end; (try rewrite in_app_iff));
      try tauto.
Qed.

(* ============================================================================= *)

Lemma part_is_subset_left :
  forall G GL GR, 
    G |-part GL (+) GR
    ->
    CTX.Subset GL G.
Proof.
  intros G GL GR Hpart.
  inversion Hpart; subst.
  intros a Hin; destruct a.
  rewrite H.
  rewrite CTXFacts.union_iff.
  auto.
Qed.

Lemma part_is_subset_right :
  forall G GL GR, 
    G |-part GL (+) GR
    ->
    CTX.Subset GR G.
Proof.
  intros G GL GR Hpart.
  apply partition_comm in Hpart.
  eapply part_is_subset_left; eauto.
Qed.

(* ============================================================================= *)

Lemma ctx_not_in_remove : 
  forall u sigma1 sigma2 G,
    G |-wf 
    -> 
    CTX.In (u, sigma1) G
    ->
    ~ CTX.In (u, sigma2) (CTX.remove (u, sigma1) G).
Proof.
  intros u sigma1 sigma2 G Hwf Hin.
  inversion Hwf; subst.
  rewrite CTXFacts.remove_iff.
  intros Hu; destruct Hu as [Hu1 Hu2].
  apply Hu2.
  specialize (H0 u sigma1 sigma2).
  rewrite H0; auto.
Qed.


(* ============================================================================= *)

Lemma free_ids_context_Add :
  forall y G1 G2 v t,
    CTXProperties.Add (v, t) G1 G2 
    ->
    In y (free_ids_context G1)
    -> 
    In y (free_ids_context G2).
Proof.
  intros y G1 G2 v t Hadd Hin.
  unfold free_ids_context in *.
  apply in_flat_map in Hin.
  destruct Hin as [u H1]; destruct H1 as [H1 H2]; destruct u.
  unfold free_ids_context.
  apply in_flat_map.
  exists (v0, t0); split; auto; clear H2.
  unfold CTXProperties.Add in Hadd.
  apply context_in_vs_elements_in.
  rewrite Hadd; clear Hadd.
  right.
  apply CTXFacts.elements_2.
  rewrite SetoidList.InA_alt.
  eexists; split; eauto.
Qed.  

(* ============================================================================= *)

Lemma free_ids_context_subset : 
  forall y G1 G2,
    CTX.Subset G1 G2 
    -> 
    ~ In y (free_ids_context G2)
    ->
    ~ In y (free_ids_context G1).
Proof.
  intros y G1 G2 Hsubset Hnotin.
  contradict Hnotin.
  rewrite free_ids_context_iff in *.
  destruct Hnotin as [u Hnotin]; destruct Hnotin as [rho Hnotin]; destruct Hnotin as [H1 H2].
  eexists; eexists; split; eauto.
Qed.

Lemma free_ids_value_context : 
  forall u rho G y,
    CTX.In (u, rho) G
    -> 
    In y (free_ids_value u)
    -> 
    In y (free_ids_context G).
Proof.
  intros u rho G y Hin Hin2.
  apply in_flat_map.
  exists (u, rho).
  split; auto.
  apply context_in_vs_elements_in.
  auto.
Qed.

Lemma free_ids_value_context_strong : 
  forall u rho G y,
    (G |-v u : rho)
    -> 
    In y (free_ids_value u)
    -> 
    In y (free_ids_context G).
Proof.
  intros u rho G y Htyp Hin.
  inversion Htyp; subst.
  eapply free_ids_value_context; eauto.
  contradict Hin; auto.
Qed.

Lemma free_ids_value_context_contra :
  forall (u : value) (rho : type) (G : CTX.t) (y : free_id),
  CTX.In (u, rho) G -> ~ In y (free_ids_context G) -> ~ In y (free_ids_value u).
Proof.
  intros u rho G y Hin Hnotin.
  contradict Hnotin.
  eapply free_ids_value_context; eauto.
Qed.

Lemma free_ids_value_context_lookup_contra :
  forall (u : value) (rho : type) (G : CTX.t) (y : free_id),
  (G |-v u : rho) -> ~ In y (free_ids_context G) -> ~ In y (free_ids_value u).
Proof.
  intros u rho G y Hlookup Hnotin.
  destruct rho.
  eapply free_ids_value_context_contra; eauto.
  apply lookup_channel_in; eauto.
  destruct u; inversion Hlookup; subst; try solve [eapply free_ids_value_context_contra; eauto].
  simpl.
  auto.
Qed.

Lemma free_ids_value_context_remove : 
  forall u rho G y,
    In y (free_ids_context (CTX.remove (u, rho) G))
    -> 
    In y (free_ids_context G).
Proof.
  intros u rho G y Hin.
  unfold free_ids_context in Hin.
  rewrite in_flat_map in Hin.
  destruct Hin as [a Hin]; destruct a; destruct Hin as [Hin1 Hin2].
  simpl in *.

  (* Check SetoidList.InA_alt. *)
  assert (SetoidList.InA CTX.E.eq (v, t) (CTX.elements (CTX.remove (u, rho) G))).
  rewrite SetoidList.InA_alt.
  eexists; split; [reflexivity|auto].
  rewrite CTX.elements_spec1 in H.
  rewrite CTXFacts.remove_iff in H.
  destruct H as [H _].
  clear Hin1.
  unfold free_ids_context.
  apply in_flat_map.
  exists (v, t); split; auto.
  apply context_in_vs_elements_in; auto.
Qed.  

Lemma free_ids_context_add_replace : 
  forall u s t rho y z G,
    (G |-v u : TChannel s) 
    ->
    y <> z
    ->
    ~ In y (free_ids_context G) 
    ->
    ~ In y (free_ids_context (CTX.add (ValVariable (Var (Free z)), rho) (ctx_replace u (TChannel s) (TChannel t) G))).
Proof.
  intros u s t rho y z G Hlookup Hneq Hnotin.
  contradict Hnotin.
  unfold ctx_replace in Hnotin.
  rewrite free_ids_context_iff in Hnotin.
  destruct Hnotin as [w Hnotin]; destruct Hnotin as [sigma Hnotin]; destruct Hnotin as [Hu1 Hu2].
  repeat (rewrite CTXFacts.add_iff in Hu1); repeat (rewrite CTXFacts.remove_iff in Hu1).
  repeat (destruct Hu1 as [Hu1|Hu1]); [| | destruct Hu1 as [Hu1a Hu1b]];
    try (injection Hu1; intros; subst; clear Hu1).
  contradict Hneq.
  simpl in Hu2.
  intuition.
  eapply free_ids_value_context; eauto; apply lookup_channel_in; eauto.
  eapply free_ids_value_context; eauto; apply lookup_channel_in; eauto.
Qed.

Lemma free_ids_context_replace_remove : 
  forall u s t v rho y G,
    G |-v u : TChannel s
    ->
    ~ In y (free_ids_context G)
    ->
    ~ In y (free_ids_context (ctx_replace u (TChannel s) (TChannel t) (CTX.remove (v, rho) G))).
Proof.
  intros u s t v rho y G Hlookup Hnotin.
  contradict Hnotin.
  unfold ctx_replace in Hnotin.
  rewrite free_ids_context_iff in Hnotin.
  destruct Hnotin as [w Hnotin]; destruct Hnotin as [sigma Hnotin]; destruct Hnotin as [Hu1 Hu2].
  rewrite CTXFacts.add_iff in Hu1; repeat rewrite CTXFacts.remove_iff in Hu1.
  destruct Hu1 as [Hu1|Hu1].
  injection Hu1; intros; subst; clear Hu1.
  eapply free_ids_value_context; eauto; apply lookup_channel_in; eauto.
  destruct Hu1 as [Hu1a Hu1b]; destruct Hu1a as [Hu1aa Hu1ab].
  eapply free_ids_value_context; eauto.
Qed.

Lemma free_ids_context_replace_other : 
  forall u s t y G,
    G |-v u : TChannel s
    ->
    ~ In y (free_ids_context G)
    ->
    ~ In y (free_ids_context (ctx_replace u (TChannel s) (TChannel t) G)).
Proof.
  intros u s t y G Hlookup Hnotin.
  contradict Hnotin.
  unfold ctx_replace in Hnotin.
  rewrite free_ids_context_iff in Hnotin.
  destruct Hnotin as [w Hnotin]; destruct Hnotin as [sigma Hnotin]; destruct Hnotin as [Hu1 Hu2].
 rewrite CTXFacts.add_iff in Hu1; rewrite CTXFacts.remove_iff in Hu1.
  destruct Hu1 as [Hu1|Hu1].
  injection Hu1; intros; subst; clear Hu1.
  eapply free_ids_value_context; eauto; apply lookup_channel_in; eauto.
  destruct Hu1 as [Hu1a Hu1b].
  eapply free_ids_value_context; eauto.
Qed.

Lemma free_ids_context_add : 
  forall s y z G,
    y <> z
    ->
    ~ In y (free_ids_context G) 
    ->
    ~ In y (free_ids_context (CTX.add (ValName (Nm (Free z)), TChannel s) (CTX.add (ValName (CoNm (Free z)), TChannel (SDual s)) G))).
Proof.
  intros s y z G Hneq Hnotin.
  contradict Hnotin.
  rewrite free_ids_context_iff in Hnotin.
  destruct Hnotin as [w Hnotin]; destruct Hnotin as [sigma Hnotin]; destruct Hnotin as [Hu1 Hu2].
  repeat (rewrite CTXFacts.add_iff in Hu1).
  repeat (destruct Hu1 as [Hu1|Hu1]);
    try (injection Hu1; intros; subst; clear Hu1); simpl in *; 
      try solve [contradict Hneq; intuition].
  eapply free_ids_value_context; eauto; apply lookup_channel_in; eauto.
Qed.

(* ============================================================================= *)

Lemma free_values_value_2 : forall v, free_value v -> In v (free_values_value v).
Proof.
  intros v Hfree.
  destruct Hfree as [i|i|i]; apply free_ids_values_value with (y:=i); simpl; auto.
Qed.

Definition free_values_in_context_lookup (G : CTX.t) (v : value) := (free_value v -> exists sigma, CTX.In (v, sigma) G).

Definition subset_remove_cong : 
  forall a G1 G2, CTX.Subset G1 G2 -> CTX.Subset (CTX.remove a G1) (CTX.remove a G2).
Proof.
  intros a G1 G2 Hsubset b; destruct a; destruct b; intros Hin.
  repeat (rewrite CTXFacts.remove_iff in *).
  intuition.
Qed.

(* ============================================================================= *)

Lemma part_inter : 
  forall G GL GR G',
    CTX.Subset G' G
    ->
    G |-part GL (+) GR 
    -> 
    G' |-part CTX.inter G' GL (+) CTX.inter G' GR.
Proof.
  intros G GL GR G' Hsubset Hpart.
  inversion Hpart; subst.
  constructor.
  rewrite (CTXProperties.inter_sym G' GL).
  rewrite (CTXProperties.inter_sym G' GR).
  rewrite <- CTXProperties.union_inter_1.
  rewrite <- H.
  rewrite CTXProperties.inter_sym.
  rewrite CTXProperties.inter_subset_equal; [reflexivity|auto].

  eapply subset_preserves_well_formed_ctx; eauto.

  intros u rho; specialize (H1 u rho); destruct H1 as [H1|H1]; [
    left
    | right; destruct H1 as [H1|Hstateless]; [
      left
      | right; auto
    ]
  ]; 
  rewrite CTX.inter_spec; contradict H1; intuition.
Qed.

(* ============================================================================= *)

Lemma channel_lookup_yields_free_value : 
  forall G v s,
    G |-v v : TChannel s
    -> 
    free_value v.
Proof.
  intros G v s Htyp.
  inversion Htyp; subst.
  inversion H; subst.
apply (H1 v (TChannel s)); auto.
Qed.

(* ============================================================================= *)

Lemma ctx_equal_part_2:
  forall G GL1 GL2 GR,
  (G |-part GL1 (+) GR) -> CTX.eq GL1 GL2 -> G |-part GL2 (+) GR.
Proof.
  intros G GL1 GL2 GR Hpart Heq.
  inversion Hpart; subst.
  constructor.
  rewrite <- Heq; auto.
  auto.
  intros u rho.
  rewrite <- Heq; auto.
Qed.

Lemma ctx_equal_part_3:
  forall G GL GR1 GR2,
  (G |-part GL (+) GR1) -> CTX.eq GR1 GR2 -> G |-part GL (+) GR2.
Proof.
  intros G GL GR1 GR2 Hpart Heq.
  inversion Hpart; subst.
  constructor.
  rewrite <- Heq; auto.
  auto.
  intros u rho.
  rewrite <- Heq; auto.
Qed.

Lemma ctx_equal_part:
  forall G1 G2 GL1 GL2 GR1 GR2,
  (G1 |-part GL1 (+) GR1) -> CTX.eq G1 G2 -> CTX.eq GL1 GL2 -> CTX.eq GR1 GR2 -> G2 |-part GL2 (+) GR2.
Proof.
  intros G1 G2 GL1 GL2 GR1 GR2 Hpart HeqG HeqGL HeqGR.
  apply ctx_equal_part_1 with (G1:=G1); auto.
  apply ctx_equal_part_2 with (GL1:=GL1); auto.
  apply ctx_equal_part_3 with (GR1:=GR1); auto.
Qed.

(* ============================================================================= *)
  
Lemma lookup_nm_bound : forall G b sigma, ~ (G |-v ValName (Nm (Bound b)) : sigma).
Proof.
  intros G b sigma Htyp.
  inversion Htyp; subst.
  inversion H; subst.
  pose (H1 _ _ H0) as Hu.
  inversion Hu.
Qed.

Lemma lookup_conm_bound : forall G b sigma, ~ (G |-v ValName (CoNm (Bound b)) : sigma).
Proof.
  intros G b sigma Htyp.
  inversion Htyp; subst.
  inversion H; subst.
  pose (H1 _ _ H0) as Hu.
  inversion Hu.
Qed.

Lemma lookup_var_bound : forall G b sigma, ~ (G |-v ValVariable (Var (Bound b)) : sigma).
Proof.
  intros G b sigma Htyp.
  inversion Htyp; subst.
  inversion H; subst.
  pose (H1 _ _ H0) as Hu.
  inversion Hu.
Qed.

(* ============================================================================= *)

Lemma ctx_replace_pre_union : 
  forall G GL GR u sigma1 sigma2,
    G |-part GL (+) GR
    ->
    CTX.In (u, sigma1) GL
    ->
    (CTX.In (u, sigma1) GR -> sigma1 = sigma2)
    ->
    CTX.union (ctx_replace u sigma1 sigma2 GL) GR |-part (ctx_replace u sigma1 sigma2 GL) (+) GR.
Proof.
  intros G GL GR u sigma1 sigma2 Hpart Heq Hin.
  inversion Hpart; subst.

  constructor.

  reflexivity.

  assert (CTX.eq (CTX.union (ctx_replace u sigma1 sigma2 GL) GR) (ctx_replace u sigma1 sigma2 (CTX.union GL GR))).
  unfold ctx_replace.
  rewrite CTXProperties.union_add.
  intros a; destruct a; split; intros Hin2; 
    repeat (rewrite CTXFacts.add_iff in * || rewrite CTXFacts.remove_iff in * || rewrite CTXFacts.union_iff in * ); 
  repeat (match goal with 
           | [ H : _ \/ _ |- _ ] => destruct H
           | [ H : _ = _ |- _ ] => injection H; intros; subst
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H' : CTX.In (?u, ?rho) _ |- free_value ?u ] => solve [apply (H u rho); apply H']
           | [ H : CTX.In (?u, ?rho) _ |- free_value ?u ] => solve [apply (H2 u rho); apply H]
         end; auto).  
  destruct (CTX.E.eq_dec (v, t) (u, sigma1)).
  injection e; intros; subst; clear e.
  apply Hin in H2; subst.
  left; auto.
  right; split; auto.

  eapply ctx_equal_preserves_wf; [|symmetry; apply H2].
  
  apply ctx_replace_preserves_wf.  
  rewrite CTXFacts.union_iff; left; auto.
  
  eapply ctx_equal_preserves_wf; [|eauto]; auto.

  intros v rho.
  destruct (CTXProperties.In_dec (v, rho) GR) as [i1|n1]; [|right; left; auto].
  destruct (CTXProperties.In_dec (v, rho) (ctx_replace u sigma1 sigma2 GL)) as [i2|n2]; [|left; auto].
  right; right.
  unfold ctx_replace in *; rewrite CTXFacts.add_iff in *; rewrite CTXFacts.remove_iff in *.
  destruct i2 as [Heq2|i2].
  injection Heq2; intros; subst; clear Heq2.
  assert (sigma1 = rho); [|subst].
  inversion H0; subst.
  specialize (H3 v sigma1 rho).
  rewrite H in H3.
  apply H3; rewrite CTXFacts.union_iff.
  left; auto.
  right; auto.
  specialize (H1 v rho); destruct H1.
  contradict H1; auto.
  destruct H1.
  contradict H1; auto.
  auto.

  destruct i2 as [i2 Hneq].
  specialize (H1 v rho); destruct H1.
  contradict H1; auto.
  destruct H1.
  contradict H1; auto.
  auto.
Qed.
  
(* ============================================================================= *)

Lemma add_replace_comm : 
  forall u v rho sigma1 sigma2 G, 
    u <> v
    ->
    CTX.eq
    (CTX.add (u, rho) (ctx_replace v sigma1 sigma2 G))
    (ctx_replace v sigma1 sigma2 (CTX.add (u, rho) G)).
Proof.
  intros u v rho sigma1 sigma2 G Hneq.
  intros a; destruct a; unfold ctx_replace; (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)); split; intros Hin; 
    repeat (match goal with
            | [ H : _ \/ _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ H : _ = _ |- _ ] => injection H; intros; subst; clear H
          end; auto).
  right; split; [left; auto | contradict Hneq; injection Hneq; intros; subst; auto].
Qed.
  
(* ============================================================================= *)

Inductive free_value_or_token : value -> Prop :=
| FVOTFreeValue : forall v, free_value v -> free_value_or_token v
| FVOTToken : forall k, free_value_or_token (ValToken k).

(* ============================================================================= *)

Inductive free_name_or_token : value -> Prop :=
| FNOTFreeNm : forall i, free_name_or_token (ValName (Nm (Free i)))
| FNOTFreeCoNm : forall i, free_name_or_token (ValName (CoNm (Free i)))
| FNOTToken : forall k, free_name_or_token (ValToken k).

(* ============================================================================= *)

Definition ctx_add_value (v : value) (rho : type) (G : ctx) : ctx := 
  match v with
    | ValName _ => CTX.add (v, rho) G
    | ValToken _ => G
    | ValVariable _ => CTX.add (v, rho) G
  end.

Lemma ctx_add_value_spec :
  forall u rho v sigma G,
    free_value_or_token v
    ->
    CTX.In (u, rho) (ctx_add_value v sigma G) 
    -> 
    (u = v /\ rho = sigma /\ free_value v) \/ (CTX.In (u, rho) G).
Proof.
  intros u rho v sigma G Hfvot Hin.
  destruct Hfvot.
  destruct v; simpl in Hin; try rewrite CTXFacts.add_iff in Hin;
    (repeat match goal with
              | [ H : _ \/ _ |- _ ] => destruct H
              | [ H : _ = _ |- _ ] => injection H; intros; subst; clear H
              | [ H : ?P |- _ \/ ?P ] => right; apply H
            end);
    left; (repeat split); auto.
  simpl in Hin; right; auto.
Qed.

(* ============================================================================= *)

Lemma ctx_add_value_free_value : 
  forall v rho G,
    free_value v 
    -> 
    CTX.eq (ctx_add_value v rho G) (CTX.add (v, rho) G).
Proof.
  intros v rho G Hfv.
  inversion Hfv; subst; simpl; try reflexivity.
Qed.

Lemma ctx_add_value_token : 
  forall k rho G,
    CTX.eq (ctx_add_value (ValToken k) rho G) G.
Proof.
  intros k rho G Hfv.
  simpl; reflexivity.
Qed.

(* ============================================================================= *)

Lemma partition_add_remove_swap : 
  forall G GL GR v rho,
    G |-part GL (+) GR
    ->
    CTX.In (v, rho) GR 
    ->
    G |-part CTX.add (v, rho) GL (+) CTX.remove (v, rho) GR.
Proof.
  intros G GL GR v rho Hpart Hin.
  inversion Hpart; subst.
  constructor; auto.

  rewrite CTXProperties.union_sym.
  rewrite CTXProperties.union_remove_add_2; auto.
  rewrite CTXProperties.union_sym; auto.

  intros u sigma.
  rewrite CTXFacts.add_iff; rewrite CTXFacts.remove_iff.
  specialize (H1 u sigma); destruct H1 as [H1|H1]; [|destruct H1 as [H1|H1]; [right; left; intuition | right; right; auto ]].

  destruct (CTX.E.eq_dec (v, rho) (u, sigma)).
  injection e; intros; subst; clear e.
  right; left; intuition.
  left; contradict H1; destruct H1; auto.
  contradict n; auto.
Qed.

(* ============================================================================= *)

Lemma dual_name_neq : 
  forall m, dual_name m <> m.
Proof.
  intros m; destruct m; simpl; discriminate.
Qed.

(* ============================================================================= *)

Lemma ctx_add_idem : forall u rho G, CTX.In (u, rho) G -> CTX.eq (CTX.add (u, rho) G) G.
Proof.
  intros u rho G Hin.
  intros a; destruct a; split; rewrite CTXFacts.add_iff; intros Hin2.
  destruct Hin2 as [Heq|Hin2]; auto.
  injection Heq; intros; subst; clear Heq; auto.
  right; auto.
Qed.

Lemma ctx_replace_idem : forall u rho G, CTX.In (u, rho) G -> CTX.eq (ctx_replace u rho rho G) G.
Proof.
  intros u rho G Hin.
  intros a; destruct a; split; unfold ctx_replace; rewrite CTXFacts.add_iff; rewrite CTXFacts.remove_iff; intros Hin2.
  destruct Hin2 as [Heq|Hin2]; auto.
  injection Heq; intros; subst; clear Heq; auto.
  intuition.
  destruct (CTX.E.eq_dec (v, t) (u, rho)).
  left; auto.
  right; auto.
Qed.

(* ============================================================================= *)

Lemma partition_add_idem_stateless : 
  forall G GL GR u rho,
    (G |-part GL (+) GR)
    ->
    G |-v u : rho
    ->
    free_value u
    ->
    ( |-st rho )
    ->
    (G |-part (CTX.add (u, rho) GL) (+) GR).
Proof.
  intros G GL GR u rho Hpart Hlookupu Hfree Hstateless.
  inversion Hpart; subst.
  constructor; auto.
  rewrite H.
  intros a; destruct a; (repeat rewrite CTXFacts.union_iff || rewrite CTXFacts.add_iff); split; intros Hin.
  tauto.
  destruct Hin as [Hin|Hin]; [|tauto].
  destruct Hin as [Heq|Hin]; [|tauto].
  injection Heq; intros; subst; clear Heq.
  inversion Hlookupu; subst; [|inversion Hfree].
  rewrite <- CTXFacts.union_iff.
  apply H; auto.

  intros v sigma.
  destruct (CTX.E.eq_dec (v, sigma) (u, rho)).
  injection e; intros; subst; clear e.
  right; right; auto.
  destruct (H1 v sigma) as [H2|H2]; [|destruct H2 as [H2|H2]].
  left; rewrite CTXFacts.add_iff.
  contradict n.
  destruct n as [e|n].
  injection e; intros; subst; clear e.
  reflexivity.
  contradict H2; auto.
  right; left; auto.
  right; right; auto.
Qed.

(* ============================================================================= *)

Lemma value_lookup_minimal : 
  forall G v rho,
    G |-v v : rho
    ->
    ctx_add_value v rho CTX.empty |-v v : rho.
Proof.
  intros G v rho Hlookup.
  inversion Hlookup; subst; [|apply LToken; simpl; apply empty_ctx_wf].
  assert (free_value v) as Hu.
  inversion H; eapply H1; eauto.
  inversion Hu; subst; simpl;
  (apply LContext; [
    apply wellformed_ctx_add_1; [apply empty_ctx_wf | constructor | apply FContext; constructor; rewrite CTXFacts.empty_iff; auto]
    | intuition
  ]).
Qed.

(* ============================================================================= *)

Lemma token_lookup : 
  forall G (k : token) rho,
    G |-v k : rho
    ->
    rho = TSingleton k.
Proof.
  intros G k rho Htyp.
  inversion Htyp; subst; [|auto].
  inversion H; subst.
  assert (free_value k) as Hu; [apply (H1 k rho); auto|].
  inversion Hu.
Qed.

(* ============================================================================= *)

Lemma ctx_remove_idem : 
    forall u rho GL GR,
      CTX.In (u, rho) GL
      ->
      CTX.eq (CTX.union GL (CTX.remove (u, rho) GR)) (CTX.union GL GR).
Proof.
  intros u rho GL GR Hin.
  intros a; destruct a; split; (repeat rewrite CTXFacts.union_iff || rewrite CTXFacts.remove_iff); intros Hin2.
  intuition.
  destruct Hin2.
  intuition.
  destruct (CTX.E.eq_dec (u, rho) (v, t)).
  injection e; intros; subst; clear e.
  intuition.
  intuition.
Qed.

(* ============================================================================= *)

Lemma ctx_remove_not_in : forall v rho G, ~ CTX.In (v, rho) G -> CTX.eq (CTX.remove (v, rho) G) G.
Proof.
  intros v rho G Hin a; rewrite CTXFacts.remove_iff; destruct a; split; intros Hin2.
  tauto.
  split; [auto|].
  intros e; injection e; intros; subst; clear e.
  tauto.
Qed.

(* ============================================================================= *)

Lemma dual_name_dual_name : 
  forall nm, 
    dual_name (dual_name nm) = nm.
Proof.
  intros nm; destruct nm; intuition.
Qed.

Lemma sdual_sdual_neq : 
  forall s,
     s <> SDual (SDual s).
Proof.
  intros s; induction s; intros Heq; try solve [discriminate Heq].
  injection Heq; intros; contradict IHs; auto.
Qed.

Lemma sdual_neq : 
  forall s,
     s <> SDual s.
Proof.
  intros s; induction s; intros Heq; try solve [discriminate Heq].
  injection Heq; intros; contradict IHs; auto.
Qed.

(* ============================================================================= *)

Lemma replace_cong
     : forall u sigma rho G1 G2,
       CTX.Equal G1 G2 ->
       CTX.Equal (ctx_replace u sigma rho G1) (ctx_replace u sigma rho G2).
Proof.
  intros u sigma rho G1 G2 Heq.
  intros a; destruct a; split; 
    unfold ctx_replace; (repeat rewrite CTXFacts.add_iff); (repeat rewrite CTXFacts.remove_iff); 
      rewrite Heq; intros Hin; tauto.
Qed.

(* ============================================================================= *)

