Require Export Arith.EqNat.
Require Export Arith.Lt.
Require Export Arith.Compare_dec.
Require Export List.
Require Export ListLocal.
Require Import String.
Require Import TypeAssignmentPoly.
Require Import ResultOpenClose.
Require Import ResultBasics.
Require Import ResultWeaken.
Require Import ResultRename.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import TacticsLocal.
Require Import ResultStrengthen.
Require Import ResultStructTyped.
Require Import ResultSubst.
Require Import ResultSubjectReduction.

Lemma ctx_preservation_in : 
  forall f1 f2 G1 G2 v vo s,
    f1 <> f2 ->
    ctx_preservation G1 G2 (VOInteract v f2 vo) ->
    CTX.In (ValName (Nm (Free f1)), TChannel s) G1 ->
    CTX.In (ValName (Nm (Free f1)), TChannel s) G2.
Proof.
  intros f1 f2 G1 G2 v vo s Hneq Hpres Hin.
  
  inversion Hpres; subst.
  rewrite H3; clear H3.

  assert (ValName (Nm (Free f1)) <> nm1) as Hneq1.
  inversion H4; subst; 
    (try solve [discriminate]);
    (try solve [contradict Hneq; injection Hneq; intros; subst; auto]).

  assert (ValName (Nm (Free f1)) <> (dual_name nm1)) as Hneq2.
  inversion H4; subst; 
    (try solve [discriminate]);
    (try solve [contradict Hneq; injection Hneq; intros; subst; auto]).

  repeat unfold ctx_replace in *.
  repeat (rewrite CTXFacts.add_iff in * || rewrite CTXFacts.remove_iff in *).
  right; split.
  right; split; auto.
  contradict Hneq2; injection Hneq2; intros; subst; clear Hneq2; symmetry.
  destruct nm1; simpl in *.
  discriminate H3.
  injection H3; intros; subst; auto.

  contradict Hneq1; injection Hneq1; intros; subst; clear Hneq1; auto.
Qed.

Lemma lookup_functional : 
  forall G u sigma1 sigma2, 
    G |-wf 
    ->
    CTX.In (u, sigma1) G
    ->
    CTX.In (u, sigma2) G
    ->
    sigma1 = sigma2.
Proof.
  intros G u sigma1 sigma2 Hwf Hinu1 Hinu2.
  inversion Hwf; subst.
  eapply H0; eauto.
Qed.

(* ============================================================================= *)

Theorem conformance : 
  forall G P Q f s alphas,
    reductions P Q alphas
    -> 
    G |-p P
    ->
    balanced G
    ->
    CTX.In (ValName (Nm (Free f)), TChannel s) G
    ->
    traces f (project f alphas) s.
Proof.
  intros G P Q f s alphas Hredns; generalize G f s; induction Hredns; intros G' f' s' Htyp Hpre Hin; [ simpl; constructor | ].
  clear G; rename G' into G; clear f; rename f' into f; clear s; rename s' into s.
  assert (G |-wf) as HwfG.
  eapply typed_ctx_wf; eauto.

  apply subject_reduction with (G1:=G) in H; auto.
  destruct H as [G2 Hconj]; destruct Hconj as [Htyp2 Hpres].

  destruct vo. 
  unfold project; simpl.
  eapply IHHredns; eauto.

  inversion Hpres; subst; [
    eapply balanced_equals; eauto
    | inversion H4
  ].
  inversion Hpres; subst; [
    rewrite H; auto
    | inversion H4
  ].

  simpl; destruct (string_dec f f0); subst.
  inversion Hpres; subst.
  inversion H4; subst; simpl in *; 
    (eapply lookup_functional in Hin; [ | apply typed_ctx_wf in Htyp; eauto | eauto ]).

  injection Hin; intros; subst; clear Hin; 
    eapply TRCCons; eauto; eapply IHHredns; eauto; [
      eapply ctx_preservation_preserves_balanced; eauto
      | auto
    ].
  rewrite H3; unfold ctx_replace; rewrite CTXFacts.add_iff; auto.

  injection Hin; intros; subst; clear Hin; 
    eapply TRCCons; eauto; eapply IHHredns; eauto; [
      eapply ctx_preservation_preserves_balanced; eauto
      | auto
    ].
  rewrite H3; unfold ctx_replace; rewrite CTXFacts.add_iff; auto.

  injection Hin; intros; subst; clear Hin; 
    eapply TRCCons; eauto.
  constructor; eauto.
  simpl.
  constructor.
  eapply IHHredns; eauto; [
      eapply ctx_preservation_preserves_balanced; eauto
      | auto
    ].
  rewrite H3; unfold ctx_replace; (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)); auto.
  right; split; auto; discriminate.

  injection Hin; intros; subst; clear Hin; 
    eapply TRCCons; eauto.
  constructor; eauto.
  simpl.
  constructor.
  eapply IHHredns; eauto; [
      eapply ctx_preservation_preserves_balanced; eauto
      | auto
    ].
  rewrite H3; unfold ctx_replace; (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)); auto.
  right; split; auto; discriminate.

  eapply IHHredns; eauto; [
    eapply ctx_preservation_preserves_balanced; eauto
    | eapply ctx_preservation_in; eauto
  ].
Qed.
