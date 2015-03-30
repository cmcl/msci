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

Lemma wt_tm_is_lc:
  forall Φ t T
         (WT: Φ ⊢ t ∈ T),
    lc t.
Proof.
  ii; induction WT; des_wfs; match goal with
                               | [H: are_dual ?S ?dS |- _] =>
                                 apply duals_are_wf in H; des
                               | |- _ => idtac
                             end; eauto using subst_lc.
Qed.

Lemma gv_in_env_fv_1:
  forall Φ M T x
         (WT: Φ ⊢ M ∈ T)
         (IN: x `in` dom Φ),
    x `in` GVFV M.
Proof.
  ii; induction WT; try (by s; simpl_env in *; destruct_in; auto).
  - pick fresh y; destruct_notin; find_specializes; s; des.
    simpl_env in *; destruct_in; apply open_fv_proc_1 in H; auto.
  - pick fresh y; pick fresh z; destruct_notin.
    apply notin_singleton_2 in NotInTac1.
    forwards NIN: notin_union_3 Fr0 NotInTac1.
    specializes H Fr NIN.
    simpl_env in *; destruct_in; s; [fsetdec|].
    do 2 !apply open_fv_proc_1 in H; auto.
  - pick fresh y; destruct_notin; find_specializes; s.
    simpl_env in *; destruct_in; auto.
    apply open_fv_proc_1 in H; auto.
  - pick fresh y; destruct_notin; find_specializes; s.
    simpl_env in *; destruct_in; solve [apply open_fv_proc_1 in H; auto
                                       |apply open_fv_proc_1 in H0; auto].
Qed.
