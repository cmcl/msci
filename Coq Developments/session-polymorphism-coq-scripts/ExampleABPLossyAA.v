Require Export Arith.EqNat.
Require Export Arith.Lt.
Require Export Arith.Compare_dec.
Require Export List.
Require Import String.
Open Scope string_scope.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import Process.
Require Import List.
Require Import PrettyPrinter.
Require Import TypeAssignmentPoly.
Require Import ResultBasics.
Require Import ExampleCommon.
Require Import ExampleRecursion.


Lemma abp_lossyAA_procR_typing :
  forall xc xerr1 xerr2 i r s t,
  ~ In xc ("lossy" :: nil)
  ->
  ~ In xerr1 (xc :: "lossy" :: nil)
  ->
  ~ In xerr2 (xerr1 :: xc :: "lossy" :: nil)
  ->
  ((s = (SAck r (token_of_bool i)) /\ t = (SAck r (token_of_bool i))))
  ->
  CTX.add (ValVariable (Var (Free xerr2)), TChannel t)
    (CTX.add (ValVariable (Var (Free xc)), TChannel SEpsilon)
    (CTX.add (ValVariable (Var (Free xerr1)), TChannel (SDual s))
    (CTX.add (ValName (Nm (Free "lossy")), TChannel (SFwd SLossy))
    (CTX.add (ValName (CoNm (Free "lossy")), TChannel (SDual (SFwd SLossy)))
    CTX.empty))))
  |-p Var (Free xerr1) ? ;
    (Var (Free xerr1) ? ;
      (New
        (CoNm (Free "lossy") ! Nm (Bound 0);
          (CoNm (Bound 0) ! Var (Free xerr1);
            (CoNm (Bound 0) ! Var (Free xerr2); Zero))) +++
      Var (Free xerr2) ! Var (Bound 1);
        (Var (Free xerr2) ! Var (Bound 0);
          New
            (CoNm (Free "lossy") ! Nm (Bound 0);
              (CoNm (Bound 0) ! Var (Free xerr1);
                (CoNm (Bound 0) ! Var (Free xerr2); Zero)))))).
Proof.
  intros xc xerr1 xerr2 i r s t H_xc_nin H_xerr1_nin H_xerr2_nin Hst.
  destruct Hst; subst.
  (* err1?i; rest *)
  apply TypPrefixInput with (s:=SDual (SAck r (token_of_bool i)))
      (L:=xerr2 :: xerr1 :: xc :: "lossy" :: nil);
    [constructor; [ctx_wf; discriminate_w_list | x_in_G]
      | free_vals_in_ctx |].
  intros G' rho t xi H_xi_nin Htrans G'def; compute; subst G'.
  inversion Htrans; subst;
    inversion H1; subst;
    inversion H0; subst.
  Case "H1 = TRAckA".
    (* err1?x; rest *)
    apply TypPrefixInput with (s:=SDual (SAck1 r (token_of_bool i)))
        (L:=xi :: xerr2 :: xerr1 :: xc :: "lossy" :: nil);
      [constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | free_vals_in_ctx |];
      try instantiate (1:=TSingleton (Token ""));
      try solve [contradiction].
    intros G' rho t x H_x_nin Htrans1 G'def; compute; subst G'.
    inversion Htrans1; subst;
      inversion H3; subst;
      inversion H2; subst.
    (* (lossy(err1, err2) + err2!i; err2!x; lossy(err1, err2)) *)
    apply TypSum.

    (* (lossy(err1, err2), i.e. New d *)
    SCase "lossy(err1,err2)".
      apply TypNew with (s:=SLossy)
          (L:=x :: xi :: xerr2 :: xerr1 :: xc :: "lossy" :: nil);
        intros d G' H_d_nin G'def;
        compute;
        subst G'.
      (* /lossy!d; rest *)
      eapply TypPrefixOutput with (s:=SDual (SFwd SLossy))
          (rho:=TChannel SLossy) (t:=SDual (SFwd SLossy));
        [apply trdual_w_mdual_involution; constructor
          | left; discriminate
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* /d!err1; rest *)
      eapply TypPrefixOutput with (s:=SDual SLossy)
          (rho:=TChannel (SDual (SAck r (token_of_bool i))))
          (t:=SDual (SLossy1 (SAck r (token_of_bool i))
            (SAck r (token_of_bool i))));
        [apply trdual_w_mdual_involution; apply TRLossyA with (i:=i) (r:=r);
            reflexivity
          | left; discriminate
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* /d!err2; rest *)
      eapply TypPrefixOutput with
          (s:=SDual (SLossy1 (SAck r (token_of_bool i))
            (SAck r (token_of_bool i))))
          (rho:=TChannel (SAck r (token_of_bool i)))
          (t:=SDual SEpsilon);
        [apply trdual_w_mdual_involution; constructor
          | left; discriminate
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* 0 *)
      apply TypZero;
        destruct i;
        ctx_wf;
        discriminate_w_list.

    (* + err2!i; err2!x; lossy(err1, err2)) *)
    SCase "+ err2!i; err2!x; lossy(err1,err2)".
      (* err2!i; rest *)
      eapply TypPrefixOutput with (s:=SAck r (token_of_bool i))
          (rho:=TSingleton (token_of_bool i)) (t:=SAck1 r (token_of_bool i));
        [constructor
          | left; contradict H_xi_nin; discriminate_w_list
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* err2!x; rest *)
      eapply TypPrefixOutput with (s:=SAck1 r (token_of_bool i))
          (rho:=TSingleton tok) (t:=SAck r (token_of_bool i));
        [constructor
          | left; contradict H_x_nin; discriminate_w_list
          | constructor; [ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* (lossy(err1, err2), i.e. New d *)
      apply TypNew with (s:=SLossy)
          (L:=x :: xi :: xerr2 :: xerr1 :: xc :: "lossy" :: nil);
        intros d G' H_d_nin G'def;
        compute;
        subst G'.
      (* /lossy!d; rest *)
      eapply TypPrefixOutput with (s:=SDual (SFwd SLossy))
          (rho:=TChannel SLossy) (t:=SDual (SFwd SLossy));
        [apply trdual_w_mdual_involution; constructor
          | left; discriminate
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* /d!err1; rest *)
      eapply TypPrefixOutput with (s:=SDual SLossy)
          (rho:=TChannel (SDual (SAck r (token_of_bool i))))
          (t:=SDual (SLossy1 (SAck r (token_of_bool i))
            (SAck r (token_of_bool i))));
        [apply trdual_w_mdual_involution; apply TRLossyA with (i:=i) (r:=r);
            reflexivity
          | left; discriminate
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* /d!err2; rest *)
      eapply TypPrefixOutput with
          (s:=SDual (SLossy1 (SAck r (token_of_bool i))
            (SAck r (token_of_bool i))))
          (rho:=TChannel (SAck r (token_of_bool i)))
          (t:=SDual SEpsilon);
        [apply trdual_w_mdual_involution; constructor
          | left; discriminate
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* 0 *)
      apply TypZero;
        destruct i;
        ctx_wf;
        discriminate_w_list.

    Case "H1 = TRAckC".
    (* err1?x; rest *)
    apply TypPrefixInput with (s:=SDual (SAck2 r (token_of_bool i)))
        (L:=xi :: xerr2 :: xerr1 :: xc :: "lossy" :: nil);
      [constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | free_vals_in_ctx |];
      try instantiate (1:=TSingleton (Token ""));
      try solve [contradiction].
    intros G' rho t x H_x_nin Htrans1 G'def; compute; subst G'.
    inversion Htrans1; subst;
      inversion H3; subst;
      inversion H2; subst.
    (* (lossy(err1, err2) + err2!i; err2!x; lossy(err1, err2)) *)
     apply TypSum.

    (* (lossy(err1, err2), i.e. New d *)
    SCase "lossy(err1,err2)".
      apply TypNew with (s:=SLossy)
          (L:=x :: xi :: xerr2 :: xerr1 :: xc :: "lossy" :: nil);
        intros d G' H_d_nin G'def;
        compute;
        subst G'.
      (* /lossy!d; rest *)
      eapply TypPrefixOutput with (s:=SDual (SFwd SLossy))
          (rho:=TChannel SLossy) (t:=SDual (SFwd SLossy));
        [apply trdual_w_mdual_involution; constructor
          | left; discriminate
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* /d!err1; rest *)
      eapply TypPrefixOutput with (s:=SDual SLossy)
          (rho:=TChannel (SDual (SNack r tok0 s'0 (token_of_negb_token
            (token_of_bool i)))))
          (t:=SDual (SLossy1 (SNack r tok0 s'0 (token_of_negb_token
            (token_of_bool i))) (SAck r (token_of_bool i))));
        [apply trdual_w_mdual_involution;
            apply TRLossyC with (i:=i) (r:=r) (k:=tok0) (r':=s'0);
            destruct i; reflexivity
          | left; discriminate
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* /d!err2; rest *)
      eapply TypPrefixOutput with
          (s:=SDual (SLossy1 (SNack r tok0 s'0 (token_of_negb_token
            (token_of_bool i))) (SAck r (token_of_bool i))))
          (rho:=TChannel (SAck r (token_of_bool i)))
          (t:=SDual SEpsilon);
        [apply trdual_w_mdual_involution; constructor
          | left; discriminate
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* 0 *)
      apply TypZero;
        destruct i;
        ctx_wf;
        discriminate_w_list.

    (* + err2!i; err2!x; lossy(err1, err2)) *)
    SCase "+ err2!i; err2!x; lossy(err1,err2)".
      (* err2!i; rest *)
      eapply TypPrefixOutput with (s:=SAck r (token_of_bool i))
          (rho:=TSingleton (token_of_negb_token (token_of_bool i)))
          (t:=SAck2 r (token_of_bool i));
        [apply TRAckC with (tok:=tok0) (s':=s'0); assumption
          | left; contradict H_xi_nin; discriminate_w_list
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* err2!x; rest *)
      eapply TypPrefixOutput with (s:=SAck2 r (token_of_bool i))
          (rho:=TSingleton tok0)
          (t:=SNack r tok0 s'0 (token_of_negb_token (token_of_bool i)));
        [constructor; assumption
          | left; contradict H_x_nin; discriminate_w_list
          | constructor; [ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* (lossy(err1, err2), i.e. New d *)
      apply TypNew with (s:=SLossy)
          (L:=x :: xi :: xerr2 :: xerr1 :: xc :: "lossy" :: nil);
        intros d G' H_d_nin G'def;
        compute;
        subst G'.
      (* /lossy!d; rest *)
      eapply TypPrefixOutput with (s:=SDual (SFwd SLossy))
          (rho:=TChannel SLossy) (t:=SDual (SFwd SLossy));
        [apply trdual_w_mdual_involution; constructor
          | left; discriminate
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* /d!err1; rest *)
      eapply TypPrefixOutput with (s:=SDual SLossy)
          (rho:=TChannel (SDual (SNack r tok0 s'0 (token_of_negb_token
            (token_of_bool i)))))
          (t:=SDual (SLossy1 (SNack r tok0 s'0 (token_of_negb_token
            (token_of_bool i))) (SNack r tok0 s'0 (token_of_negb_token
            (token_of_bool i)))));
        [apply trdual_w_mdual_involution;
            apply TRLossyB with (i:=negb i) (r:=r) (k:=tok0) (r':=s'0);
            destruct i; reflexivity
          | left; discriminate
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* /d!err2; rest *)
      eapply TypPrefixOutput with
          (s:=SDual (SLossy1 (SNack r tok0 s'0 (token_of_negb_token
            (token_of_bool i))) (SNack r tok0 s'0 (token_of_negb_token
            (token_of_bool i)))))
          (rho:=TChannel (SNack r tok0 s'0 (token_of_negb_token
            (token_of_bool i))))
          (t:=SDual SEpsilon);
        [apply trdual_w_mdual_involution; constructor
          | left; discriminate
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* 0 *)
      apply TypZero;
        destruct i;
        ctx_wf;
        discriminate_w_list.
Qed.
