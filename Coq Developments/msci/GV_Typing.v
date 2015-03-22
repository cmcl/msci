(** Beginning of the file for GV typing lemmas. *)
Require Import Metatheory.
Require Import GV_Definitions GV_Infrastructure.
Set Implicit Arguments.

(* Destruct compound well-formed type assumptions. *)
Ltac des_wfs :=
  match goal with
    | [H: wf_typ (! _ # _) _ |- _] => inverts H
    | [H: wf_typ (? _ # _) _ |- _] => inverts H
    | [H: wf_typ (_ <+> _) _ |- _] => inverts H
    | [H: wf_typ (_ <&> _) _ |- _] => inverts H
    | [H: wf_typ (_ <x> _) _ |- _] => inverts H
    | [H: wf_typ (_ ⊸ _) _ |- _] => inverts H
    | [H: wf_typ (_ → _) _ |- _] => inverts H
    | |- _ => idtac
  end.

Lemma duals_are_sessions:
  forall S dS (DU: are_dual S dS),
    is_session S /\ is_session dS.
Proof. ii; induction DU; des; split; auto. Qed.

Lemma duals_are_wf:
  forall S dS (DU: are_dual S dS),
    wf_typ S lin /\ wf_typ dS lin.
Proof.
  ii; induction DU; des; split; auto; econstructor; eauto
  ; by repeat match goal with
                | [H: are_dual ?S ?dS |- _] =>
                  apply duals_are_sessions in H; des; auto
              end.
Qed.

Lemma wt_tm_is_lc : forall Φ t T
    (WT: Φ ⊢ t ∈ T),
  lc t.
Proof.
  ii; induction WT; des_wfs; match goal with
                               | [H: are_dual ?S ?dS |- _] =>
                                 apply duals_are_wf in H; des
                               | |- _ => idtac
                             end; eauto using subst_lc.
Qed.