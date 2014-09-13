Require Export Arith.EqNat.
Require Export Arith.Lt.
Require Export Arith.Compare_dec.
Require Export List.
Require Import String.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Export Process.
Require Import Bool.
Require Import TypeAssignmentPoly.
Require Import ResultOpenClose.
Require Import ResultBasics.
Require Import ResultSubjectReduction.

Lemma free_name_is_name : 
  forall v, is_free_name v -> is_name v.
Proof.
  intros v Hisfn; destruct Hisfn; constructor.
Qed.  

Lemma is_name_open_value : 
  forall x n v, is_name (open_value x n v) -> is_name v.
Proof.
  intros x n v Hisn.
  destruct v as [nm | k | var]; [
    destruct nm; constructor
    | auto
    | inversion Hisn
  ].
Qed.

Lemma is_not_token_open_value :
  forall x n v, is_not_token v -> is_not_token (open_value x n v).
Proof.
  intros x n v Hisnt.
  unfold is_not_token in *; intros k; specialize (Hisnt k).
  destruct v as [nm | | var]; [
    | auto
    | 
  ]; discriminate.
Qed.

Lemma singleton_is_token :
  forall G v K,
    G |-v v : TSingleton K 
    -> 
    balanced G
    -> 
    ~ is_not_token v.
Proof.
  intros G v K Htyp Hpre.
  inversion Htyp; subst; [| intros Hisnt; specialize (Hisnt K); auto].
  destruct Hpre as [_ Hpre]; destruct Hpre as [Hallfreenames Hnct].
  apply Hnct in H0; destruct H0; discriminate.
Qed.

Lemma error_open_proc_inv : forall P x n, error P -> error (open_proc x n P).
Proof.
  intros P; induction P; intros x n Herror; simpl in *; 
    (try solve [inversion Herror]);
    (try solve [inversion Herror; subst; simpl; constructor; contradict H0; apply is_name_open_value in H0; assumption]);
    (try solve [inversion_clear Herror; constructor; destruct H; eapply is_not_token_open_value in H; eauto]).
  inversion_clear Herror; constructor; apply IHP; auto.
  inversion_clear Herror; [ apply EParLeft; apply IHP1 | apply EParRight; apply IHP2 ]; assumption.
  inversion_clear Herror; [ apply ESumLeft; apply IHP1 | apply ESumRight; apply IHP2 ]; assumption.
  inversion_clear Herror; constructor; apply IHP; auto.
Qed.

Lemma balanced_subset : 
  forall G1 G2,
    CTX.Subset G1 G2
    ->
    balanced G2
    ->
    balanced G1.
Proof.
  intros G1 G2 Hsubset Hprespre.
  inversion Hprespre.
  constructor; unfold ctx_matched_names in *; unfold all_free_names in *.
  intros nm1 nm2 rho sigma Heq Hin1 Hin2; apply (H nm1 nm2); auto.
  split.
  destruct H0 as [H0 H1].
  intros u rho Hin; apply (H0 u rho); auto.

  destruct H0 as [H0 H1].
  intros v rho Hin; apply (H1 v rho); auto.
Qed.
  
(* ============================================================================= *)

Theorem runtime_safety_immediate : 
  forall G P,
    G |-p P
    ->
    balanced G
    -> 
    ~ error P.
Proof.
  intros G P Htyp; induction Htyp; intros Hpre; try solve [intros Herror; inversion Herror].

  rename H into Hu; clear H0 H1 H2.
  destruct Hpre as [_ Hpre]; destruct Hpre as [Hallfreenames _].
  apply lookup_channel_in in Hu.
  apply Hallfreenames in Hu.
  intros Herror; inversion Herror; subst; contradict H0; apply free_name_is_name; assumption.

  rename H1 into Hu; clear H0 H2 H3 H4.
  destruct Hpre as [_ Hpre]; destruct Hpre as [Hallfreenames _].
  apply lookup_channel_in in Hu.
  apply Hallfreenames in Hu.
  intros Herror; inversion Herror; subst; contradict H1; apply free_name_is_name; assumption.

  intros Herror; inversion_clear Herror.
  apply IHHtyp1; [ apply balanced_partition in H | ]; auto.
  apply IHHtyp2; [ apply partition_comm in H; apply balanced_partition in H | ]; auto.

  intros Herror; inversion_clear Herror.
  apply IHHtyp1; auto.
  apply IHHtyp2; auto.

  intros Herror; inversion_clear Herror.
  destruct H4; contradict H4; [ apply singleton_is_token in H | apply singleton_is_token in H0 ]; auto.

  intros Herror; inversion_clear Herror.
  destruct H4; contradict H4; [ apply singleton_is_token in H | apply singleton_is_token in H0 ]; auto.

  intros Herror; inversion_clear Herror.
  clear H; rename H0 into Hind; rename H1 into Herror.
  destruct (fresh_free_id_exists ((free_ids_context G) ++ L)).
  rewrite in_app_iff in H.
  eapply (Hind x); auto.
  apply ctx_preservation_extension; auto.
  apply error_open_proc_inv; assumption.

  intros Herror; inversion_clear Herror.
  apply IHHtyp; [|assumption].
  apply balanced_subset in H0; auto.
Qed.

(* ============================================================================= *)

Lemma runtime_safety_aux : 
  forall (P Q : proc) (alphas : list obs),
    reductions P Q alphas 
    ->
    forall  (G : ctx),
      G |-p P
      ->
      balanced G
      -> 
      ~ error Q.
Proof.
  intros P Q alphas Hredns.
  induction Hredns; intros G Htyp Hpre; [ eapply runtime_safety_immediate; eauto | ].

  destruct (subject_reduction _ _ _ _ H Htyp Hpre) as [G2 Hconj]; destruct Hconj as [Htyp2 Hpres].
  apply (IHHredns G2); auto.
  apply ctx_preservation_preserves_balanced in Hpres; auto.
  apply typed_ctx_wf in Htyp; auto.
Qed.

(* ============================================================================= *)

Theorem runtime_safety : 
  forall (G : ctx) (P Q : proc) (alphas : list obs),
    G |-p P
    ->
    balanced G
    -> 
    reductions P Q alphas 
    ->
    ~ error Q.
Proof.
  intros G P Q alphas Htyp Hpre Hredns.
  eapply runtime_safety_aux; eauto.
Qed.

(* ============================================================================= *)

