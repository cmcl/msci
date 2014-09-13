Require Export Arith.EqNat.
Require Export Arith.Lt.
Require Export Arith.Compare_dec.
Require Export List.
Require Export ListLocal.
Require Import String.
Require Import TypeAssignmentPoly.
Require Import ResultOpenClose.
Require Import ResultBasics.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import TacticsLocal.

(* ============================================================================= *)

Lemma lookup_strengthen :
  forall G2 u rho,
    G2 |-v u : rho
    -> 
    forall G1,
      CTX.Subset G1 G2
      ->
      free_values_in_context_lookup G1 u
      ->
      G1 |-v u : rho.
Proof.
  intros G2 u rho Hlookup G1 Hsubset Hfvicl.
  inversion Hlookup; subst; [|apply LToken; eapply subset_preserves_well_formed_ctx; eauto].
  assert (free_value u) as Hfv; [inversion H; eapply H1; eauto|].
  apply LContext; [eapply subset_preserves_well_formed_ctx; eauto|].
  specialize (Hfvicl Hfv).
  destruct Hfvicl as [sigma Hin].
  assert (rho = sigma); [|subst].
  apply Hsubset in Hin.
  inversion H as [? _ Heqtypes _]; subst.
  apply (Heqtypes u rho sigma); auto.
  auto.
Qed.

(* ============================================================================= *)

Lemma typed_strengthen :
  forall G2 P,
    G2 |-p P
    -> 
    forall G1,
      CTX.Subset G1 G2
      ->
      free_values_in_context G1 P
      ->
      G1 |-p P.
Proof.
  intros G2 P Htyp; induction Htyp; intros G1 Hsubseteq Hfvic.
  
  SCase "u ? ; P"%string.
  apply TypPrefixInput with (L:=free_ids_context G ++ L) (s:=s).
  eapply lookup_strengthen; eauto.

  intros Hfree; apply Hfvic; simpl; rewrite in_app_iff; left.
  apply free_values_value_2; auto.

  intros v Hin; apply Hfvic; simpl; rewrite in_app_iff; right; auto.

  intros G' rho t x Hnotin Htrans Heq; subst.
  assert (~ In x L) as HnotinL; [rewrite in_app_iff in Hnotin; contradict Hnotin; right; auto|].
  assert (~ In x (free_ids_context G)) as HnotinG; [rewrite in_app_iff in Hnotin; contradict Hnotin; left; auto|].
  clear Hnotin.
  eapply H2; eauto.

  apply CTXProperties.subset_add_3; [intuition|].
  apply CTXProperties.subset_add_2.
  unfold ctx_replace.
  apply CTXProperties.subset_add_3; [intuition|].
  apply CTXProperties.subset_add_2.
  apply subset_remove_cong; auto.

  assert (free_values_in_context G1 P) as Hfvic2.
  intros v Hin; apply Hfvic; simpl; rewrite in_app_iff; right; auto.
  intros v Hin.
  unfold free_values_in_context in Hfvic2.

  pose (free_values_open_proc1 _ _ _ _ Hin) as Hin2; destruct Hin2.

  pose (H1 _ rho t x HnotinL Htrans eq_refl) as Htyp.
  eapply free_values_in_context_1 in Htyp.
  destruct (Htyp _ Hin) as [sigma Hin2].
  rewrite CTXFacts.add_iff in Hin2.
  destruct Hin2 as [Heq|Hin2].
  injection Heq; intros; subst; clear Heq.
  eexists; rewrite CTXFacts.add_iff; left; auto.

  contradict HnotinG.
  apply free_ids_context_iff.
  unfold ctx_replace in Hin2.
  rewrite CTXFacts.add_iff in Hin2; rewrite CTXFacts.remove_iff in Hin2.
  destruct Hin2 as [Heq|Hin2].
  injection Heq; intros; subst; clear Heq.
  apply lookup_channel_in in H.
  exists v; exists (TChannel s); split; auto.

  destruct Hin2 as [Hin2 Hneq].
  exists v; exists sigma; split; auto.

  specialize (Hfvic2 v H3).
  destruct Hfvic2 as [sigma Hfvic2].
  destruct (CTX.E.eq_dec (v, sigma) (u, TChannel s)); [injection e; intros; subst; clear e|]; 
    eexists; unfold ctx_replace; (repeat rewrite CTXFacts.add_iff); rewrite CTXFacts.remove_iff.
  right; left; reflexivity.
  right; right; split; eauto.


  SCase "u ! v ; P"%string.
  destruct H3.
  
  SSCase "v removed"%string.
  eapply TypPrefixOutput with (s:=s) (rho:=rho) (t:=t); [auto|auto| | |left| |].
  eapply lookup_strengthen; eauto; intros Hin; apply free_values_value_2 in Hin; apply Hfvic; auto; simpl; (repeat rewrite in_app_iff); auto.
  eapply lookup_strengthen; eauto; intros Hin; apply free_values_value_2 in Hin; apply Hfvic; auto; simpl; (repeat rewrite in_app_iff); auto.
  eauto; subst.
  eauto; subst.
  apply IHHtyp.

  SSSCase "subset - removed"%string.
  subst.
  intros a; destruct a as [w sigma1].
  unfold ctx_replace; (repeat rewrite CTXFacts.add_iff); (repeat rewrite CTXFacts.remove_iff).
  intros Hin; destruct Hin as [Heq|Hin]; [injection Heq; intros; subst; clear Heq; auto|].
  destruct Hin as [Hin Hneq1]; destruct Hin as [Hin Hneq2]; auto.

  SSSCase "free_values_in_context - removed"%string.
  subst.
  intros w Hin.
  assert (In w (free_values_proc (u ! v ; P))) as Hin2; [simpl; (repeat rewrite in_app_iff); auto|].
  specialize (Hfvic w Hin2); destruct Hfvic as [sigma Hfvic].
  eapply free_values_in_context_1 in Htyp.
  destruct (Htyp _ Hin) as [sigma2 Hin3].
  unfold ctx_replace in Hin3; rewrite CTXFacts.add_iff in Hin3; (repeat rewrite CTXFacts.remove_iff in Hin3).
  destruct Hin3 as [Heq | Hin3]; [injection Heq; intros; subst; clear Heq|destruct Hin3 as [Hin3 Hneq]; destruct Hin3 as [Hin3 Hneq2]].
  exists (TChannel t); unfold ctx_replace; rewrite CTXFacts.add_iff; (repeat rewrite CTXFacts.remove_iff); left; auto.
  exists sigma2; unfold ctx_replace; rewrite CTXFacts.add_iff; (repeat rewrite CTXFacts.remove_iff); right; (repeat (split; auto)).
  assert (sigma = sigma2); [|subst; auto].
  apply Hsubseteq in Hfvic.
  inversion H1 as [? ? ? Hwf|]; subst.
  inversion Hwf as [? ? Huniq _]; subst.
  apply (Huniq w); auto.

  SSCase "v not removed"%string.
  eapply TypPrefixOutput with (s:=s) (rho:=rho) (t:=t); [auto|auto| | |right| |].
  eapply lookup_strengthen; eauto; intros Hin; apply free_values_value_2 in Hin; apply Hfvic; auto; simpl; (repeat rewrite in_app_iff); auto.
  eapply lookup_strengthen; eauto; intros Hin; apply free_values_value_2 in Hin; apply Hfvic; auto; simpl; (repeat rewrite in_app_iff); auto.
  destruct H3; subst; eauto.
  eauto.
  destruct H3 as [Heq Hst]; subst.
  apply IHHtyp.

  SSSCase "subset - not removed - stateless"%string.
  intros a; destruct a as [w sigma1].
  unfold ctx_replace; (repeat rewrite CTXFacts.add_iff); (repeat rewrite CTXFacts.remove_iff).
  intros Hin; destruct Hin as [Heq|Hin]; [injection Heq; intros; subst; clear Heq; left; auto|right].
  destruct Hin as [Hin Hneq1]; auto.

  SSSCase "free_values_in_context - not removed - stateless"%string.
  intros w Hin.
  assert (In w (free_values_proc (u ! v ; P))) as Hin2; [simpl; (repeat rewrite in_app_iff); auto|].
  specialize (Hfvic w Hin2); destruct Hfvic as [sigma Hfvic].
  eapply free_values_in_context_1 in Htyp.
  destruct (Htyp _ Hin) as [sigma2 Hin3].
  unfold ctx_replace in Hin3; rewrite CTXFacts.add_iff in Hin3; (repeat rewrite CTXFacts.remove_iff in Hin3).
  destruct Hin3 as [Heq | Hin3]; [injection Heq; intros; subst; clear Heq|destruct Hin3 as [Hin3 Hneq]].
  exists (TChannel t); unfold ctx_replace; rewrite CTXFacts.add_iff; (repeat rewrite CTXFacts.remove_iff); left; auto.
  exists sigma2; unfold ctx_replace; rewrite CTXFacts.add_iff; (repeat rewrite CTXFacts.remove_iff); right; (repeat (split; auto)).
  assert (sigma = sigma2); [|subst; auto].
  apply Hsubseteq in Hfvic.
  inversion H1 as [? ? ? Hwf|]; subst.
  inversion Hwf as [? ? Huniq _]; subst.
  apply (Huniq w); auto.


  SCase "P ||| Q"%string.
  inversion H as [? ? ? _ Hwf _]; subst.
  inversion Hwf as [? _ Heqtypes _]; subst.
  apply TypPar with (GL:=CTX.inter G1 GL) (GR:=CTX.inter G1 GR).
  eapply part_inter; eauto.

  apply IHHtyp1; [intuition|].
  unfold free_values_in_context in Hfvic.
  intros u Hin.
  apply free_values_in_context_1 in Htyp1.
  specialize (Htyp1 u Hin); destruct Htyp1 as [sigma1 Hu1].
  assert (In u (free_values_proc (P|||Q))) as Hin2; [simpl; rewrite in_app_iff; left; auto|].
  specialize (Hfvic u Hin2); destruct Hfvic as [sigma2 Hu2].
  assert (sigma1 = sigma2).
  apply (Heqtypes u sigma1 sigma2); intuition.
  eapply partition_is_subset_left; eauto.
  subst. 
  exists sigma2; rewrite CTX.inter_spec; auto.

  apply IHHtyp2; [intuition|].
  unfold free_values_in_context in Hfvic.
  intros u Hin.
  apply free_values_in_context_1 in Htyp2.
  specialize (Htyp2 u Hin); destruct Htyp2 as [sigma1 Hu1].
  assert (In u (free_values_proc (P|||Q))) as Hin2; [simpl; rewrite in_app_iff; right; auto|].
  specialize (Hfvic u Hin2); destruct Hfvic as [sigma2 Hu2].
  assert (sigma1 = sigma2).
  apply (Heqtypes u sigma1 sigma2); intuition.
  eapply partition_is_subset_right; eauto.
  subst. 
  exists sigma2; rewrite CTX.inter_spec; auto.


  SCase "P +++ Q"%string.
  unfold free_values_in_context in Hfvic.
  apply TypSum; (apply IHHtyp1 || apply IHHtyp2); auto; intros u Hin; apply Hfvic; simpl; rewrite in_app_iff; auto.


  SCase "IsEq u v P"%string.
  apply TypIsEq with (K:=K) (L:=L); 
    try solve [
      eapply lookup_strengthen; eauto; intros Hin; apply free_values_value_2 in Hin; 
      apply Hfvic; auto; simpl; (repeat rewrite in_app_iff); auto].
  intros w Hin; apply Hfvic; simpl; (repeat rewrite in_app_iff); auto.
  intros Heq; apply H3; auto.
  intros w Hin; apply Hfvic; simpl; (repeat rewrite in_app_iff); auto.

  SCase "IsNotEq u v P"%string.
  apply TypIsNotEq with (K:=K) (L:=L); 
    try solve [
      eapply lookup_strengthen; eauto; intros Hin; apply free_values_value_2 in Hin; 
      apply Hfvic; auto; simpl; (repeat rewrite in_app_iff); auto].
  intros w Hin; apply Hfvic; simpl; (repeat rewrite in_app_iff); auto.
  intros Hneq; apply H3; auto.
  intros w Hin; apply Hfvic; simpl; (repeat rewrite in_app_iff); auto.


  SCase "New P"%string.
  apply TypNew with (L:=free_ids_context G ++ L) (s:=s).
  intros x G' Hnotin Heq; subst.
  eapply H0; [intuition|reflexivity| |].

  apply CTXProperties.subset_add_3; [intuition|].
  apply CTXProperties.subset_add_2.
  apply CTXProperties.subset_add_3; [intuition|].
  apply CTXProperties.subset_add_2.
  auto.


  assert (~ In x L) as HnotinL; [rewrite in_app_iff in Hnotin; contradict Hnotin; right; auto|].
  assert (~ In x (free_ids_context G)) as HnotinG; [rewrite in_app_iff in Hnotin; contradict Hnotin; left; auto|].

  assert (free_values_in_context G1 P) as Hfvic2; [intros v Hin; apply Hfvic; auto|].
  intros v Hin.
  unfold free_values_in_context in Hfvic2.

  pose (free_values_open_proc1 _ _ _ _ Hin) as Hin2; destruct Hin2.

  pose (H x _ HnotinL eq_refl) as Htyp.
  eapply free_values_in_context_1 in Htyp.
  destruct (Htyp _ Hin) as [sigma Hin2].
  repeat (rewrite CTXFacts.add_iff in Hin2).
  destruct Hin2 as [Heq|Hin2].
  injection Heq; intros; subst; clear Heq.
  eexists; rewrite CTXFacts.add_iff; left; auto.
  destruct Hin2 as [Heq|Hin2].
  injection Heq; intros; subst; clear Heq.
  exists (TChannel (SDual s)); (repeat rewrite CTXFacts.add_iff); right; left; auto.
  exists sigma; (repeat rewrite CTXFacts.add_iff); right; right; auto.

  contradict HnotinG.
  apply free_ids_context_iff.
  exists v; exists sigma; split; auto.

  specialize (Hfvic2 v H1).
  destruct Hfvic2 as [sigma Hfvic2].
  exists sigma; (repeat rewrite CTXFacts.add_iff); right; right; auto.


  SCase "! P"%string.
  assert (free_values_in_context G1 P); [apply Hfvic|].
  apply TypRep with (G':=CTX.inter G1 G'); intuition.
  eapply subset_preserves_well_formed_ctx; eauto.
  apply (H1 u).
  rewrite CTX.inter_spec in H3; intuition.
  apply IHHtyp.
  intuition.
  apply free_values_in_context_1 in Htyp.
  intros u Hin.
  specialize (Htyp u Hin); destruct Htyp as [sigma1 Hu1].
  specialize (H2 u Hin); destruct H2 as [sigma2 Hu2].
  assert (sigma1 = sigma2); [|subst].
  inversion H; subst.
  apply (H3 u sigma1 sigma2); intuition.
  eexists; rewrite CTX.inter_spec; split; eauto.


  SCase "Zero"%string.
  apply TypZero.
  eapply subset_preserves_well_formed_ctx; eauto.

Qed.

(* ============================================================================= *)

Lemma strengthening : 
  forall (G1 G2 : ctx) (P : proc),
    (G2 |-p P) ->
    CTX.Subset G1 G2 -> 
    free_values_in_context G1 P -> 
    G1 |-p P.
Proof.
  intros G1 G2 P Htyp Hsubset Hfvic.
  eapply typed_strengthen; eauto.
Qed.

(* ============================================================================= *)

