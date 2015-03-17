(** Beginning of the file for GV typing lemmas. *)
Require Import Metatheory.
Require Import GV_Definitions GV_Infrastructure.
Set Implicit Arguments.

Lemma elab_inl: forall (T: typ lin), ⟪T⟫ = inl T.
Proof. auto. Qed.

Lemma elab_inr: forall (T: typ un), ⟪T⟫ = inr T.
Proof. auto. Qed.

Lemma unlimited_env_typing:
  forall Φ t (T: typ un)
         (WT: Φ ⊢ t ∈ T),
    un_env Φ.
Proof.
  ii; inversion WT; repeat simpl_existT; substs; auto; unfold un_env; i
  ; simpl_env in *.
  - rewrite elab_inr in *; destruct_in; substs; eauto.
  - fsetdec.
  - destruct_in. admit (* analyze_in x0 IN0 *). substs; eauto.
  - destruct_in. admit (* analyze_in x IN0 *). admit (*analyze_in x IN1*).
Admitted.

Lemma typing_subst:
  forall Φ Ψ k (T: typ k) (U: typ un) z t u
         (WTT: Φ ++ (z ~ inr U) ++ Ψ ⊢ t ∈ T)
         (WTU: Φ ⊢ u ∈ U),
    Φ ++ Ψ ⊢ [z ~> u]t ∈ T.
Proof.
  ii; assert (UNENV: un_env Φ) by eauto using unlimited_env_typing.
  induction WTT.
Admitted.

Lemma wt_tm_is_lc : forall Φ t k (T: typ k)
    (WT: Φ ⊢ t ∈ T),
  lc t.
Proof.
  ii; induction WT; eauto using subst_lc.
Qed.