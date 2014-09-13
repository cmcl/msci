Require Export Arith.EqNat.
Require Export Arith.Lt.
Require Export Arith.Compare_dec.
Require Export List.
Require Export ListLocal.
Require Import String.
Require Import Omega.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import TacticsLocal.
Require Import Process.
Require Import ResultOpenClose.

(* ============================================================================= *)

Theorem struct_equiv_open : forall P Q x, 
  P == Q -> forall n, (open_proc x n P) == (open_proc x n Q).
Proof.
  intros P Q x Hequiv.
  induction Hequiv; intros n; simpl; 
    try (eapply StrRefl || eapply StrParZeroRight || eapply StrSumZeroRight 
      || eapply StrParComm || eapply StrSumComm
      || eapply StrParAssoc || eapply StrSumAssoc
      || eapply StrRep
      || eapply StrParCongRight || eapply StrSumCongRight); eauto.
  apply StrSym; auto.
  eapply StrTrans; eauto.

  rewrite <- insert_open_proc; [apply StrNewParRight|intuition].
  rewrite <- insert_open_proc; [apply StrNewSumRight|intuition].
  eapply StrNewCong.
  intros i Hfresh_i_open_P Hfresh_i_open_Q.

  destruct (string_dec i x) as [e1|n1].
  rewrite -> e1 in *.

  erewrite -> open_open_eq_proc; intuition.
  erewrite -> open_open_eq_proc; intuition.
  eapply H0.
  contradict Hfresh_i_open_P; apply free_ids_open_proc2; intuition.
  contradict Hfresh_i_open_Q; apply free_ids_open_proc2; intuition.

  erewrite -> open_open_proc; [|omega|auto].
  erewrite -> open_open_proc; [|omega|auto].
  eapply H0.

  contradict Hfresh_i_open_P; apply free_ids_open_proc2; auto.
  contradict Hfresh_i_open_Q; apply free_ids_open_proc2; auto.
Qed.

(* ============================================================================= *)

Lemma StrParZeroLeft : forall P, P == (Zero ||| P).
Proof.
  intros P; eapply StrTrans; [|eapply StrParComm]; apply StrParZeroRight.
Qed.

Lemma StrSumZeroLeft : forall P, P == (Zero +++ P).
Proof.
  intros P; eapply StrTrans; [|eapply StrSumComm]; apply StrSumZeroRight.
Qed.

Lemma StrParCongLeft : forall P Q1 Q2, Q1 == Q2 -> (Q1 ||| P) == (Q2 ||| P).
Proof.
  intros P Q1 Q2 H.
  eapply StrTrans; [eapply StrParComm|].
  eapply StrTrans; [|eapply StrParComm].
  eapply StrParCongRight; auto.
Qed.

Lemma StrSumCongLeft : forall P Q1 Q2, Q1 == Q2 -> (Q1 +++ P) == (Q2 +++ P).
  intros P Q1 Q2 H.
  eapply StrTrans; [eapply StrSumComm|].
  eapply StrTrans; [|eapply StrSumComm].
  eapply StrSumCongRight; auto.
Qed.

Lemma StrNewParLeft : forall P Q, ((New Q) ||| P) == (New (Q ||| (insert_proc 0 P))).
Proof.
  intros P Q; eapply StrTrans.
  eapply StrParComm.
  eapply StrTrans. 
  eapply StrNewParRight.
  apply StrNewCong.
  intros i Hfresh_i_open1 Hfresh_i_open2.
  cbv beta delta [open_proc] iota zeta; fold open_proc.
  rewrite <- open_insert_proc.
  apply StrParComm.
Qed.

Lemma StrNewSumLeft : forall P Q, ((New Q) +++ P) == (New (Q +++ (insert_proc 0 P))).
Proof.
  intros P Q; eapply StrTrans.
  eapply StrSumComm.
  eapply StrTrans. 
  eapply StrNewSumRight.
  apply StrNewCong.
  intros i Hfresh_i_open1 Hfresh_i_open2.
  cbv beta delta [open_proc] iota zeta; fold open_proc.
  rewrite <- open_insert_proc.
  apply StrSumComm.
Qed.

(* ============================================================================= *)

Lemma struct_equiv_par_cong : 
  forall P1 Q1 P2 Q2, P1 == Q1 -> P2 == Q2 -> P1 ||| P2 == Q1 ||| Q2.
Proof.
  intros P1 Q1 P2 Q2 H1 H2.
  eapply StrTrans; 
    [eapply StrParCongLeft
      | eapply StrSym; apply StrParCongRight;apply StrSym];
    auto.
Qed.

Lemma struct_equiv_sum_cong : 
  forall P1 Q1 P2 Q2, P1 == Q1 -> P2 == Q2 -> P1 +++ P2 == Q1 +++ Q2.
Proof.
  intros P1 Q1 P2 Q2 H1 H2.
  eapply StrTrans; 
    [eapply StrSumCongLeft
      | eapply StrSym; apply StrSumCongRight; apply StrSym ];
    auto.
Qed.

Lemma struct_equiv_par_zero_cong : 
  forall P Q, P == Q -> P == Q ||| Zero.
Proof.
  intros P Q H.
  eapply StrTrans; [apply H|apply StrParZeroRight].
Qed.

Lemma struct_equiv_sum_zero_cong : 
  forall P Q, P == Q -> P == Q +++ Zero.
Proof.
  intros P Q H.
  eapply StrTrans; [apply H|apply StrSumZeroRight].
Qed.

