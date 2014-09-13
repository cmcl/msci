Require Import String.
Require Import TypeAssignmentPoly.
Require Import ResultBasics.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import List.
Require Import ExampleCommon.

Require String. Open Scope string_scope.

Lemma ctx_G'_wf :
  forall l s,
  ~ In l ("d" :: "c" :: nil)
  -> (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
    (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
    (CTX.add (namec, TChannel s)
    (CTX.add (named, TChannel (SDual s)) CTX.empty)))) |-wf.
Proof.
  intros l s Hnin.
  apply ctx_add_wf_dual_names.
  x_fresh_for_ctx.
  apply ctx_add_namec_s_add_named_SDual_s_well_formed.
Qed.

Lemma ctx_GL_GR_partition_G' :
  forall l s,
    ~ In l ("d" :: "c" :: nil) ->
    (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
      (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
      (CTX.add (namec, TChannel s)
      (CTX.add (named, TChannel (SDual s)) CTX.empty)))) |-part
    (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
      (CTX.add (namec, TChannel s)
      (CTX.add (named, TChannel (SDual s)) CTX.empty))) (+)
    (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
      (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
      CTX.empty)).
Proof.
  intros l s Hnin.
  apply Partition.
  Case "CTX.eq G' (CTX.union GL GR)".
    unfold CTX.eq; unfold CTX.Equal.
    induction a as (u,rho).
    split; intros H0.
    SCase "forall (u,rho), CTX.In (u,rho) G'".
      x_in_G; try solve [apply CTXFacts.union_3; x_in_G];
        apply CTXFacts.union_2; x_in_G.
    SCase "forall (u,rho), CTX.In (u,rho) (CTX.union GL GR)".
      x_in_G; assumption.
    SCase "G'|-wf".
      apply ctx_G'_wf; assumption.
    SCase "forall u,rho, ~In (u,rho) GL \/ ~In (u,rho) GR \/ (|-st rho)".
      intros u rho.
      (repeat
        match goal with
          | |- context [CTX.In (u,rho) (CTX.add ?y _)] =>
              edestruct CTXProperties.In_dec with (x:=(u,rho));
                [right | left; eauto]
          | H: CTX.In (u,rho) _ |- _ => x_in_G
          | H: ?x = (u,rho) |- _ =>
              inversion H; subst; clear H; constructor; intros
          | H : SDual (SFwd SInOut) -- _ --> _ |- _ => inversion H; clear H
          | H : SFwd SInOut -- _ --> _ |- _ => inversion H; clear H
          | |- ?x = ?x => reflexivity
        end);
        (repeat
          match goal with
            | H : ~ In ?x ?L1 |- _ => contradict H
            | H: (?x, ?y) = (?x',?y') |- _ => inversion H; clear H
            | |- In ?x _ => red
            | |- ?x = ?x \/ _ => left; reflexivity
            | |- ?x = ?y \/ _ => right
          end).
Qed.

Lemma ctx_conm_l_sdual_sfwd_namec_s_named_sdual_s_wf :
  forall l s,
    ~ In l ("d" :: "c" :: nil)
    -> CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
         (CTX.add (namec, TChannel s)
           (CTX.add (named, TChannel (SDual s)) CTX.empty)) |-wf.
Proof.
  intros l s Hnin.
  apply wellformed_ctx_add_1; try solve [constructor]; [|x_fresh_for_ctx].
  apply ctx_add_namec_s_add_named_SDual_s_well_formed.
Qed.

Lemma ctx_conm_m_x_conm_l_sfwd_namec_s_named_sdual_s_wf :
  forall m l s x,
    ~ In l ("d" :: "c" :: nil)
    -> ~ In m (l :: "d" :: "c" :: nil)
    -> CTX.add (ValName (CoNm (Free m)), TChannel x)
         (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
           (CTX.add (namec, TChannel s)
             (CTX.add (named, TChannel (SDual s)) CTX.empty))) |-wf.
Proof.
  intros m l s x Hnin Hnin'.
  apply wellformed_ctx_add_1; try solve [constructor]; [|x_fresh_for_ctx].
  apply ctx_conm_l_sdual_sfwd_namec_s_named_sdual_s_wf; assumption.
Qed.

Lemma ctx_nm_l_sfwd_conm_l_sdual_sfwd_namec_s_named_sdual_s_wf :
  forall l s,
    ~ In l ("d" :: "c" :: nil)
    -> CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
         (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
           (CTX.add (namec, TChannel s)
             (CTX.add (named, TChannel (SDual s)) CTX.empty))) |-wf.
Proof.
  intros l s Hnin.
  apply ctx_add_wf_dual_names.
  x_fresh_for_ctx.
  apply ctx_add_namec_s_add_named_SDual_s_well_formed.
Qed.

Lemma ctx_conm_m_x_nm_l_sfwd_conm_l_sfwd_namec_s_named_sdual_s_wf :
  forall m l s x,
    ~ In l ("d" :: "c" :: nil)
    -> ~ In m (l :: "d" :: "c" :: nil)
    -> CTX.add (ValName (CoNm (Free m)), TChannel x)
        (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
          (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
            (CTX.add (namec, TChannel s)
              (CTX.add (named, TChannel (SDual s)) CTX.empty)))) |-wf.
Proof.
  intros m l s x Hnin Hnin'.
  apply wellformed_ctx_add_1; [| constructor | x_fresh_for_ctx].
  apply ctx_add_wf_dual_names.
  x_fresh_for_ctx.

  apply ctx_add_namec_t_add_named_SDual_s_well_formed.
Qed.

Lemma ctx_nm_m_SInOut_conm_m_sdual_SInOut_conm_l_sfwd_namec_s_named_sdual_s_wf :
  forall m l s,
    ~ In l ("d" :: "c" :: nil)
    -> ~ In m (l :: "d" :: "c" :: nil)
    -> CTX.add (ValName (Nm (Free m)), TChannel SInOut)
      (CTX.add (ValName (CoNm (Free m)), TChannel (SDual SInOut))
        (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
          (CTX.add (namec, TChannel s)
            (CTX.add (named, TChannel (SDual s)) CTX.empty)))) |-wf.
Proof.
  intros m l s Hnin Hnin'.
  apply ctx_add_wf_dual_names.
  x_fresh_for_ctx.

  apply ctx_conm_l_sdual_sfwd_namec_s_named_sdual_s_wf; assumption.
Qed.

Lemma ctx_nm_m_SInOut_conm_m_sdual_SInOut_nm_l_sfwd_conm_l_sfwd_namec_s_named_sdual_s_wf :
  forall m l s,
    ~ In l ("d" :: "c" :: nil)
    -> ~ In m (l :: "d" :: "c" :: nil)
    -> CTX.add (ValName (Nm (Free m)), TChannel SInOut)
      (CTX.add (ValName (CoNm (Free m)), TChannel (SDual SInOut))
        (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
          (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
            (CTX.add (namec, TChannel s)
              (CTX.add (named, TChannel (SDual s)) CTX.empty))))) |-wf.
Proof.
  intros m l s Hnin Hnin'.
  apply ctx_add_wf_dual_names; [x_fresh_for_ctx|].
  apply ctx_add_wf_dual_names; [x_fresh_for_ctx|].

  apply ctx_add_namec_t_add_named_SDual_s_well_formed.
Qed.

Lemma ctx_conm_l_sfwd_named_sdual_s_wf :
  forall l s,
    ~ In l ("d" :: "c" :: nil)
    -> CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
         (CTX.add (named, TChannel (SDual s)) CTX.empty) |-wf.
Proof.
  intros l s Hnin.
  apply wellformed_ctx_add_1; try solve [constructor]; [|x_fresh_for_ctx].
  apply ctx_add_named_SDual_s_well_formed.
Qed.

Lemma ctx_conm_m_x_conm_l_sdual_sfwd_named_sdual_s_wf :
  forall m l s x,
    ~ In l ("d" :: "c" :: nil)
    -> ~ In m (l :: "d" :: "c" :: nil)
    -> CTX.add (ValName (CoNm (Free m)), TChannel x)
         (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
           (CTX.add (named, TChannel (SDual s)) CTX.empty)) |-wf.
Proof.
  intros m l s x Hnin Hnin'.
  apply wellformed_ctx_add_1; try solve [constructor]; [|x_fresh_for_ctx].
  apply ctx_conm_l_sfwd_named_sdual_s_wf; assumption.
Qed.

Lemma ctx_conm_m_x_nm_l_sfwd_conm_l_sfwd_named_sdual_s_wf :
  forall m l s x,
    ~ In l ("d" :: "c" :: nil)
    -> ~ In m (l :: "d" :: "c" :: nil)
    -> CTX.add (ValName (CoNm (Free m)), TChannel x)
        (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
          (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
            (CTX.add (named, TChannel (SDual s)) CTX.empty))) |-wf.
Proof.
  intros m l s x Hnin Hnin'.
  apply wellformed_ctx_add_1; [|constructor|x_fresh_for_ctx].
  apply ctx_add_wf_dual_names; [x_fresh_for_ctx|].

  apply ctx_add_named_SDual_s_well_formed.
Qed.

Lemma ctx_conm_m_sdual_sepsilon_conm_l_sfwd_wf :
  forall m l,
    ~ In m (l :: "d" :: "c" :: nil)
    -> CTX.add (ValName (CoNm (Free m)), TChannel (SDual SEpsilon))
     (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
       CTX.empty) |-wf.
Proof.
  intros m l Hnin.
  apply wellformed_ctx_add_1; [|constructor|x_fresh_for_ctx].
  apply wellformed_ctx_add_1; [|constructor|x_fresh_for_ctx].
  apply empty_ctx_wf.
Qed.

(* GL|-(New params) (/l!params; /params!c; /params!d; 0) *)
Lemma GL_types_forwarder_bootstrap :
  forall (s:session) (l:free_id),
  ~ In l ("d" :: "c" :: nil)
  -> CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
       (CTX.add (namec, TChannel s)
         (CTX.add (named, TChannel (SDual s)) CTX.empty))
     |-p New
       (CoNm (Free l) ! Nm (Bound 0);
         (CoNm (Bound 0) ! Nm (Free "c");
           (CoNm (Bound 0) ! Nm (Free "d"); Zero))).
Proof.
  intros s l Hnin.
  apply TypNew with (s:=SInOut) (L:=l::("d":free_id)::("c" : free_id)::nil).
  intros m G'' Hnin' G''def; subst; simpl.
  eapply TypPrefixOutput with (s:=SDual (SFwd SInOut))
      (t:=SDual (SFwd SInOut)) (rho:=TChannel SInOut);
    [(apply trdual_w_mdual_involution; apply TRFwd) | left; discriminate | | | (left;auto) | auto | ];
    try constructor; try solve [x_in_G]; try solve [
      apply ctx_nm_m_SInOut_conm_m_sdual_SInOut_conm_l_sfwd_namec_s_named_sdual_s_wf;
      assumption].

  apply ctx_equal_preserves_typed with
    (G1:=CTX.add (ValName (CoNm (Free m)), TChannel (SDual SInOut))
      (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
        (CTX.add (namec, TChannel s)
          (CTX.add (named, TChannel (SDual s)) CTX.empty)))); [ |
    symmetry; apply ctx_replace_nothing_eq_stronger; [x_in_G |
      rewrite -> CTXProperties.remove_add; [reflexivity|
        x_nin_G; contradict Hnin'; inversion H; right; right; left;
        reflexivity]]].

  eapply TypPrefixOutput with (s:=SDual SInOut) (t:=SDual (SInOut1 s));
    try solve [(apply trdual_w_mdual_involution; constructor) || left; discriminate || (left;auto) ||
      reflexivity]; try constructor; try solve [x_in_G ||
        (apply ctx_conm_m_x_conm_l_sfwd_namec_s_named_sdual_s_wf;
          assumption)].

  unfold ctx_replace.
  apply ctx_equal_preserves_typed with
    (G1:=CTX.add (ValName (CoNm (Free m)), TChannel (SDual (SInOut1 s)))
      (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
          (CTX.add (named, TChannel (SDual s)) CTX.empty))); [|
      apply ctx_add_1; [reflexivity|]; symmetry;
      rewrite <- CTXProperties.add_add with
        (s:=(CTX.add (named, TChannel (SDual s)) CTX.empty));
      rewrite <- CTXProperties.add_add with
        (s:=(CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
          (CTX.add (named, TChannel (SDual s)) CTX.empty)));
      rewrite -> CTXProperties.remove_add; [|x_nin_G; inversion H; subst;
        contradict Hnin; right; left; reflexivity];
      rewrite -> CTXProperties.remove_add; [|x_nin_G; inversion H; subst;
        contradict Hnin; right; left; reflexivity];
      reflexivity].

  eapply TypPrefixOutput with (s:=SDual (SInOut1 s)) (t:=(SDual SEpsilon))
      (rho:=TChannel (SDual s));
    try (constructor || apply trdual_mdual_with_trInOut1 || discriminate); x_in_G;
    try (reflexivity); try solve [
      apply ctx_conm_m_x_conm_l_sdual_sfwd_named_sdual_s_wf; assumption].
  discriminate.

  apply ctx_equal_preserves_wf with
    (G1:=CTX.add (ValName (CoNm (Free m)), TChannel (SDual SEpsilon))
      (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
        CTX.empty)).

  apply ctx_conm_m_sdual_sepsilon_conm_l_sfwd_wf; assumption.

  apply ctx_add_1; [reflexivity|]; symmetry.
  rewrite <- CTXProperties.add_add with (s:=CTX.empty);
    rewrite <- CTXProperties.add_add with
      (s:=(CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
        CTX.empty));
    rewrite -> CTXProperties.remove_add; try x_nin_G;
    rewrite -> CTXProperties.remove_add; try x_nin_G; reflexivity.
Qed.

Lemma ctx_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf :
  forall x_params rho l,
    ~ In l ("d" :: "c" :: nil)
    -> ~ In x_params (l :: "d" :: "c" :: nil)
    -> CTX.add (ValVariable (Var (Free x_params)), TChannel rho)
        (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
          (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
            CTX.empty)) |-wf.
Proof.
  intros x_params rho l Hnin Hnin'.
  apply wellformed_ctx_add_1; try solve [constructor]; [|x_fresh_for_ctx].
  apply ctx_term_dual_term_wf; assumption.
Qed.

Lemma ctx_var_xin_s0_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf :
  forall x_in s0 x_params rho l,
    ~ In l ("d" :: "c" :: nil)
    -> ~ In x_params (l :: "d" :: "c" :: nil)
    -> ~ In x_in (x_params :: l :: "d" :: "c" :: nil)
    -> CTX.add (ValVariable (Var (Free x_in)), TChannel s0)
        (CTX.add (ValVariable (Var (Free x_params)), TChannel rho)
        (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
        (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
        CTX.empty))) |-wf.
Proof.
  intros x_in s0 x_params rho l Hnin Hnin' Hnin''.
  apply wellformed_ctx_add_1; try solve [constructor]; [|x_fresh_for_ctx].
  apply ctx_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf; assumption.
Qed.

Lemma ctx_var_xout_sdual_s0_var_xin_t_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf :
  forall x_out s0 x_in t x_params rho l,
    ~ In l ("d" :: "c" :: nil)
    -> ~ In x_params (l :: "d" :: "c" :: nil)
    -> ~ In x_in (x_params :: l :: "d" :: "c" :: nil)
    -> ~ In x_out (x_in :: x_params :: l :: "d" :: "c" :: nil)
    -> CTX.add (ValVariable (Var (Free x_out)), TChannel (SDual s0))
        (CTX.add (ValVariable (Var (Free x_in)), TChannel t)
        (CTX.add (ValVariable (Var (Free x_params)), TChannel rho)
        (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
        (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
        CTX.empty)))) |-wf.
Proof.
  intros x_out s0 x_in t x_params rho l Hnin Hnin' Hnin'' Hnin'''.
  apply wellformed_ctx_add_1; try solve [constructor]; [|x_fresh_for_ctx].
  apply ctx_var_xin_s0_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf;
    assumption.
Qed.

Lemma ctx_var_x_rho'_var_xout_sdual_s0_var_xin_t_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf :
  forall x rho' x_out s0 x_in t x_params rho l,
    ~ In l ("d" :: "c" :: nil)
    -> ~ In x_params (l :: "d" :: "c" :: nil)
    -> ~ In x_in (x_params :: l :: "d" :: "c" :: nil)
    -> ~ In x_out (x_in :: x_params :: l :: "d" :: "c" :: nil)
    -> ~ In x (x_out :: x_in :: x_params :: l :: "d" :: "c" :: nil)
    -> 
       (CTX.add (ValVariable (Var (Free x)), rho')
       (CTX.add (ValVariable (Var (Free x_out)), TChannel (SDual s0))
       (CTX.add (ValVariable (Var (Free x_in)), TChannel t)
       (CTX.add (ValVariable (Var (Free x_params)), TChannel rho)
       (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
       (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
       CTX.empty)))))) |-wf.
Proof.
  intros x rho' x_out s0 x_in t x_params rho l Hnin Hnin' Hnin'' Hnin''' Hnin4.
  apply wellformed_ctx_add_1; try solve [constructor]; [|x_fresh_for_ctx].
  apply ctx_var_xout_sdual_s0_var_xin_t_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf;
    assumption.
Qed.

Lemma ctx_nm_m_rho'_conm_m_sdual_rho'_var_xout_sdual_t_var_xin_t_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf :
  forall m rho' x_out t x_in x_params rho l,
    ~ In l ("d" :: "c" :: nil)
    -> ~ In x_params (l :: "d" :: "c" :: nil)
    -> ~ In x_in (x_params :: l :: "d" :: "c" :: nil)
    -> ~ In x_out (x_in :: x_params :: l :: "d" :: "c" :: nil)
    -> ~ In m (x_out :: x_in :: x_params :: l :: "d" :: "c" :: nil)
    -> 
       (CTX.add (ValName (Nm (Free m)), TChannel rho')
       (CTX.add (ValName (CoNm (Free m)), TChannel (SDual rho'))
       (CTX.add (ValVariable (Var (Free x_out)), TChannel (SDual t))
       (CTX.add (ValVariable (Var (Free x_in)), TChannel t)
       (CTX.add (ValVariable (Var (Free x_params)), TChannel rho)
       (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
       (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
       CTX.empty))))))) |-wf.
Proof.
  intros m rho' x_out t x_in x_params rho l Hnin Hnin' Hnin'' Hnin''' Hnin4.
  apply ctx_add_wf_dual_names. 
  x_fresh_for_ctx.
  apply ctx_var_xout_sdual_s0_var_xin_t_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf;
    assumption.
Qed.

Lemma ctx_conm_m_sdual_rho'_var_xout_sdual_t_var_xin_t_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf :
  forall m rho' x_out t x_in x_params rho l,
    ~ In l ("d" :: "c" :: nil)
    -> ~ In x_params (l :: "d" :: "c" :: nil)
    -> ~ In x_in (x_params :: l :: "d" :: "c" :: nil)
    -> ~ In x_out (x_in :: x_params :: l :: "d" :: "c" :: nil)
    -> ~ In m (x_out :: x_in :: x_params :: l :: "d" :: "c" :: nil)
    ->
       (CTX.add (ValName (CoNm (Free m)), TChannel (SDual rho'))
       (CTX.add (ValVariable (Var (Free x_out)), TChannel (SDual t))
       (CTX.add (ValVariable (Var (Free x_in)), TChannel t)
       (CTX.add (ValVariable (Var (Free x_params)), TChannel rho)
       (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
       (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
       CTX.empty)))))) |-wf.
Proof.
  intros m rho' x_out t x_in x_params rho l Hnin Hnin' Hnin'' Hnin''' Hnin4.
  apply wellformed_ctx_add_1; try solve [constructor]; [|x_fresh_for_ctx].
  apply ctx_var_xout_sdual_s0_var_xin_t_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf;
    assumption.
Qed.

(* GR|-p l?x_params; x_params?x_in; x_params?x_out; x_in?x; x_out!x;
           new m; co-l!m; co-m!x_in; co-m!x_out; 0 *)
Lemma GR_types_forwarder_main_non_repeated :
  forall l,
    ~ In l ("d" :: "c" :: nil)
    ->
    CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
      (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
      CTX.empty)
    |-p Nm (Free l) ? ; (Var (Bound 0) ? ; (Var (Bound 1) ? ;
      (Var (Bound 1) ? ; (Var (Bound 1) ! Var (Bound 0); New
      (CoNm (Free l) ! Nm (Bound 0); (CoNm (Bound 0) ! Var (Bound 3);
      (CoNm (Bound 0) ! Var (Bound 2); Zero))))))).
Proof.
  intros l Hnin.
  (* GR|-p l?x_params; x_params?x_in; x_params?x_out; x_in?x; x_out!x;
           new m; co-l!m; co-m!x_in; co-m!x_out; 0 *)
  apply TypPrefixInput with (s:=SFwd SInOut)
    (L:=l::("d":free_id)::("c" : free_id)::nil).
  (*GR |-v Nm(Free l) : TChannel (SFwd SInOut)*)
  constructor; [apply ctx_term_dual_term_wf | x_in_G].

  (*free_values_in_context*)
  free_vals_in_ctx.

  (*GR'|-p x_params?x_in; rest*)
  intros GR' rho t x_params Hnin' Htrans GR'def; compute.
  (*first some cleanup...*)
  inversion Htrans; subst; clear Htrans.
  apply ctx_equal_preserves_typed with
    (G1:=CTX.add (ValVariable (Var (Free x_params)), TChannel SInOut)
      (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
        (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
          CTX.empty)));
    [| apply ctx_add_1; [reflexivity|]; symmetry;
      apply ctx_replace_nothing_eq; x_in_G].
  (*now the main course: GR'|-p x_params?x_in; rest*)
  apply TypPrefixInput with (s:=SInOut)
    (L:=x_params::l::("d":free_id)::("c" : free_id)::nil).

  (*GR' |-v Var(Free x_params) : TChannel SInOut*)
  constructor; [apply ctx_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf;
    assumption | x_in_G].

  (*free_values_in_context*)
  free_vals_in_ctx.

  (*GR''|-p x_params?x_out; rest*)
  intros GR'' rho t x_in Hnin'' Htrans GR''def; compute.
  (*first some cleanup...*)
  inversion Htrans; subst; clear Htrans.
  unfold ctx_replace.
  apply ctx_equal_preserves_typed with
    (G1:=CTX.add (ValVariable (Var (Free x_in)), TChannel s)
      (CTX.add (ValVariable (Var (Free x_params)), TChannel (SInOut1 s))
      (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
        (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
          CTX.empty))));
    [|repeat (apply ctx_add_1; [reflexivity|]); symmetry;
      apply CTXProperties.remove_add with
        (s:=CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
          (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
            CTX.empty)); x_nin_G].
  (*now the main course: GR''|-p x_params?x_out; rest*)
  apply TypPrefixInput with (s:=SInOut1 s)
    (L:=x_in::x_params::l::("d":free_id)::("c" : free_id)::nil).

  (*GR'' |-v Var(Free x_in) : TChannel s*)
  constructor;
    [apply ctx_var_xin_s0_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf;
      assumption | x_in_G].

  (*free_values_in_context*)
  free_vals_in_ctx.

  (*GR'''|-p x_in?x; rest*)
  intros GR''' rho t x_out Hnin''' Htrans GR'''def; compute.
  (*first some cleanup...*)
  inversion Htrans; subst; clear Htrans.
  unfold ctx_replace.
  apply ctx_equal_preserves_typed with
    (G1:=CTX.add (ValVariable (Var (Free x_out)), TChannel (SDual s))
      (CTX.add (ValVariable (Var (Free x_params)), TChannel (SEpsilon))
      (CTX.add (ValVariable (Var (Free x_in)), TChannel s)
      (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
      (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
      CTX.empty)))));
    [|repeat (apply ctx_add_1; [reflexivity|]);
      rewrite -> CTXProperties.add_add with
        (s:=CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
          (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
            CTX.empty));
      rewrite -> CTXProperties.remove_add with
        (s:= CTX.add (ValVariable (Var (Free x_in)), TChannel s)
          (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
          (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
          CTX.empty)));
      [reflexivity|x_nin_G; inversion H; contradict Hnin''; left; symmetry;
        assumption]].
  apply ctx_equal_preserves_typed with
    (G1:=CTX.add (ValVariable (Var (Free x_out)), TChannel (SDual s))
      (CTX.add (ValVariable (Var (Free x_in)), TChannel s)
      (CTX.add (ValVariable (Var (Free x_params)), TChannel (SEpsilon))
      (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
      (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
      CTX.empty)))));
    [|rewrite -> CTXProperties.add_add with
        (s:=CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
          (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
            CTX.empty));
      reflexivity].

  (*now the main course: GR'''|-p x_in?x; rest*)
  eapply TypPrefixInput with (s:=s)
    (L:=x_out::x_in::x_params::l::("d":free_id)::("c" : free_id)::nil).

  (*GR''' |-v Var(Free x_in) : TChannel s*)
  constructor;
    [apply ctx_var_xout_sdual_s0_var_xin_t_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf;
      assumption | x_in_G].

  (*free_values_in_context*)
  free_vals_in_ctx.

  (*stuff -> GR4|-p x_out!x; rest*)
  intros GR4 rho t x Hnin4 Htrans GR4def; compute.
  (*first some cleanup...*)
  subst; unfold ctx_replace.
  apply ctx_equal_preserves_typed with
    (G1:=CTX.add (ValVariable (Var (Free x)), rho)
      (CTX.add (ValVariable (Var (Free x_in)), TChannel t)
      (CTX.add (ValVariable (Var (Free x_out)), TChannel (SDual s))
      (CTX.add (ValVariable (Var (Free x_params)), TChannel (SEpsilon))
      (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
      (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
      CTX.empty))))));
    [|repeat (apply ctx_add_1; [reflexivity|]);
      rewrite -> CTXProperties.add_add with
        (s:=
          (CTX.add (ValVariable (Var (Free x_params)), TChannel (SEpsilon))
          (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
          (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
          CTX.empty))));
      rewrite -> CTXProperties.remove_add with
        (s:=
          (CTX.add (ValVariable (Var (Free x_out)), TChannel (SDual s))
          (CTX.add (ValVariable (Var (Free x_params)), TChannel (SEpsilon))
          (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
          (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
          CTX.empty)))));
      [reflexivity|x_nin_G; inversion H; [contradict Hnin'''|contradict Hnin''];
      left; [symmetry|]; assumption]].
  apply ctx_equal_preserves_typed with
    (G1:=
      (CTX.add (ValVariable (Var (Free x)), rho)
      (CTX.add (ValVariable (Var (Free x_out)), TChannel (SDual s))
      (CTX.add (ValVariable (Var (Free x_in)), TChannel t)
      (CTX.add (ValVariable (Var (Free x_params)), TChannel (SEpsilon))
      (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
      (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
      CTX.empty)))))));
    [|rewrite -> CTXProperties.add_add with
        (s:=
          (CTX.add (ValVariable (Var (Free x_params)), TChannel (SEpsilon))
          (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
          (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
          CTX.empty))));
      reflexivity].

  (*now the main course: GR4|-p x_out!x;rest*)
  eapply TypPrefixOutput with (rho:=rho) (s:=SDual s) (t:=SDual t);
    try solve [
      constructor;
        [apply ctx_var_x_rho'_var_xout_sdual_s0_var_xin_t_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf; 
          assumption
        | x_in_G]].

  apply trdual_w_mdual_involution; simpl; assumption.
  left; contradict Hnin4; left; inversion Hnin4; reflexivity.

  left; reflexivity.
  reflexivity.

  (*first some cleanup...*)
  unfold ctx_replace.
  apply ctx_equal_preserves_typed with
    (G1:=
          (CTX.add (ValVariable (Var (Free x_out)), TChannel (SDual t))
          (CTX.remove (ValVariable (Var (Free x_out)), TChannel (SDual s))
          (CTX.add (ValVariable (Var (Free x_out)), TChannel (SDual s))
          (CTX.add (ValVariable (Var (Free x_in)), TChannel t)
          (CTX.add (ValVariable (Var (Free x_params)), TChannel (SEpsilon))
          (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
          (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
          CTX.empty))))))));
    [|apply ctx_add_1; [reflexivity|];
    rewrite -> CTXProperties.Equal_remove with (s':=
          (CTX.remove (ValVariable (Var (Free x)), rho)
          (CTX.add (ValVariable (Var (Free x)), rho)
          (CTX.add (ValVariable (Var (Free x_out)), TChannel (SDual s))
          (CTX.add (ValVariable (Var (Free x_in)), TChannel t)
          (CTX.add (ValVariable (Var (Free x_params)), TChannel (SEpsilon))
          (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
          (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
          CTX.empty))))))));
    [reflexivity|];
    rewrite -> CTXProperties.remove_add with (s:=
          (CTX.add (ValVariable (Var (Free x_out)), TChannel (SDual s))
          (CTX.add (ValVariable (Var (Free x_in)), TChannel t)
          (CTX.add (ValVariable (Var (Free x_params)), TChannel (SEpsilon))
          (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
          (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
          CTX.empty))))));
    [reflexivity|x_nin_G; inversion H; subst; contradict Hnin4;
      [left|right; left|right;right;left]; reflexivity]].
  apply ctx_equal_preserves_typed with
    (G1:=
        (CTX.add (ValVariable (Var (Free x_out)), TChannel (SDual t))
        (CTX.add (ValVariable (Var (Free x_in)), TChannel t)
        (CTX.add (ValVariable (Var (Free x_params)), TChannel (SEpsilon))
        (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
        (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
        CTX.empty))))));
    [|apply ctx_add_1; [reflexivity|];
    rewrite -> CTXProperties.remove_add with (s:=
          (CTX.add (ValVariable (Var (Free x_in)), TChannel t)
          (CTX.add (ValVariable (Var (Free x_params)), TChannel (SEpsilon))
          (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
          (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
          CTX.empty)))));
    [reflexivity|x_nin_G; inversion H; subst; contradict Hnin'''; left;
      reflexivity]].

  (*now the main course: GR5|-p New m;rest*)
  apply TypNew with (s:=SInOut)
    (L:=x_out::x_in::x_params::l::("d":free_id)::("c" : free_id)::nil).
  intros m GR5 Hnin5 GR5def; compute; subst.

  (*now the main course: GR6|-p conm_l!nm_x;rest*)
  eapply TypPrefixOutput with (rho:=TChannel SInOut)
      (s:=SDual (SFwd SInOut)) (t:=SDual (SFwd SInOut));
    try solve [
      constructor; [|x_in_G];
      apply ctx_nm_m_rho'_conm_m_sdual_rho'_var_xout_sdual_t_var_xin_t_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf;
      assumption].

  apply trdual_w_mdual_involution; simpl; constructor.
  left; discriminate.

  left; reflexivity.

  reflexivity.

  (*cleanup the context*)
  apply ctx_equal_preserves_typed with
    (G1:=
      (CTX.add (ValName (CoNm (Free m)), TChannel (SDual SInOut))
      (CTX.add (ValVariable (Var (Free x_out)), TChannel (SDual t))
      (CTX.add (ValVariable (Var (Free x_in)), TChannel t)
      (CTX.add (ValVariable (Var (Free x_params)), TChannel (SEpsilon))
      (CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
      (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
      CTX.empty)))))));
    [|rewrite -> ctx_replace_nothing_eq; x_in_G;
      rewrite -> CTXProperties.remove_add; [reflexivity|]; x_nin_G;
      contradict Hnin5; inversion H; right; right; right; right; right;
      left; reflexivity].
  (*now the main course: GR7|-p conm_m!var_xin;rest*)
  eapply TypPrefixOutput with (rho:=TChannel t) (s:=SDual SInOut)
      (t:=SDual (SInOut1 t));
    try solve [ constructor; [|x_in_G];
      apply ctx_conm_m_sdual_rho'_var_xout_sdual_t_var_xin_t_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf;
      assumption].

  apply trdual_w_mdual_involution; simpl; constructor.
  left; discriminate.

  left; reflexivity.

  reflexivity.

  (*now the main course: GR8|-p conm_m!var_xout;Zero*)
  eapply TypPrefixOutput with (rho:=TChannel (SDual t))
      (s:=SDual (SInOut1 t)) (t:=SDual (SEpsilon));
    try solve [
      constructor; [|x_in_G]; apply ctx_replace_preserves_wf; x_in_G;
      apply wellformed_ctx_remove_1;
      apply ctx_conm_m_sdual_rho'_var_xout_sdual_t_var_xin_t_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf;
      assumption].

  apply trdual_w_mdual_involution; simpl; constructor.
  left; discriminate.

  left; reflexivity.

  reflexivity.

  (*now the main course: GR9|-p Zero*)
  apply TypZero; apply ctx_replace_preserves_wf; x_in_G;
    apply wellformed_ctx_remove_1;
    apply wellformed_ctx_add_1; [|constructor|x_fresh_for_ctx];
    repeat apply wellformed_ctx_remove_1;
    apply ctx_conm_m_sdual_rho'_var_xout_sdual_t_var_xin_t_var_xparams_rho_nm_l_sfwd_conm_l_sdual_sfwd_wf;
    assumption.
Qed.

(* =============== forwarder definitions and main lemma =============== *)

Definition uni_forwarder_aux_init ARGS i o :=
  New (ARGS ! ((Nm (Bound 0))); (((CoNm (Bound 0))) ! i;
    ((CoNm (Bound 0))!o; Zero))).

Definition uni_forwarder_aux_rep :=
  Nm (Bound 0) ? ; (Var (Bound 0) ?; (Var (Bound 1) ?; (Var (Bound 1) ?;
    (Var (Bound 1) ! (Var (Bound 0));
      uni_forwarder_aux_init (CoNm (Bound 5)) (Var (Bound 3))
        (Var (Bound 2)))))).

(* Def fwd(in,out) = in?z; out!z; fwd(in,out) *)
Definition uni_forwarder_multi_step i o :=
  New ((uni_forwarder_aux_init (CoNm (Bound 1)) i o)
    ||| (Rep (uni_forwarder_aux_rep))).

Lemma uni_forwarder_multi_step_zero_typing : 
  forall s : session,
    (CTX.add (namec, TChannel s) (CTX.add (named, TChannel (SDual s)) CTX.empty))
    |-p
      (uni_forwarder_multi_step namec named).
Proof.
  intros.
  pose (CTX.add (namec, TChannel s)
    (CTX.add (named, TChannel (SDual s)) CTX.empty)) as G.
  apply TypNew with (s:=SFwd SInOut) (L:=("d":free_id)::("c" : free_id)::nil).
  intros l G' Hnin G'def; subst; simpl.
  apply TypPar with
    (GL:=CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
      (CTX.add (namec, TChannel s)
        (CTX.add (named, TChannel (SDual s)) CTX.empty)))
    (GR:=CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
      (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
        CTX.empty)).

  apply ctx_GL_GR_partition_G'; assumption.

  (* Let GL := CTX.add (CoNm (Free l), TChannel (SDual (SFwd SInOut)))
     (CTX.add (namec, TChannel s)
     (CTX.add (named, TChannel (SDual s)) CTX.empty)) *)

  (* GL |-p forwarder_bootstrap *)
  apply GL_types_forwarder_bootstrap; assumption.

  (* Let GR := CTX.add (Nm (Free l), TChannel (SFwd SInOut))
     (CTX.add (CoNm (Free l), TChannel (SDual (SFwd SInOut))) CTX.empty) *)

  (* GR |-p ! (forwarder_aux_rep) *)
  eapply TypRep with (G:=
    CTX.add (ValName (Nm (Free l)), TChannel (SFwd SInOut))
      (CTX.add (ValName (CoNm (Free l)), TChannel (SDual (SFwd SInOut)))
        CTX.empty));
    [apply ctx_term_dual_term_wf | reflexivity | |].

  (* forall (u,rho) in GR, |-st rho *)
  intros u rho Hin; x_in_G; inversion H; constructor; intros m t Htrans;
    inversion Htrans; try inversion H3; reflexivity.

  (* GR |-p forwarder_aux_rep *)
  apply GR_types_forwarder_main_non_repeated; assumption.
Qed.
