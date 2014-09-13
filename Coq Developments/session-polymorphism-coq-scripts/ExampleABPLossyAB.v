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


Lemma abp_lossyAB_procR_typing :
  forall xc xerr1 xerr2 i r k r' s t,
  ~ In xc ("lossy" :: nil)
  ->
  ~ In xerr1 (xc :: "lossy" :: nil)
  ->
  ~ In xerr2 (xerr1 :: xc :: "lossy" :: nil)
  ->
  ((s = (SNack r k r' (token_of_bool i)))
    /\  (t = (SNack r k r' (token_of_bool i))))
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
  intros xc xerr1 xerr2 i r k r' s t H_xc_nin H_xerr1_nin H_xerr2_nin Hst.
  destruct Hst; subst.
  (* err1?i; rest *)
  apply TypPrefixInput with (s:=SDual (SNack r k r' (token_of_bool i)))
      (L:=xerr2 :: xerr1 :: xc :: "lossy" :: nil);
    [constructor; [ctx_wf; discriminate_w_list | x_in_G]
      | free_vals_in_ctx |].
  intros G' rho t xi H_xi_nin Htrans G'def; compute; subst G'.
  inversion Htrans; subst;
    inversion H1; subst;
    inversion H0; subst.
  (* err1?x; rest *)
  apply TypPrefixInput with (s:=SDual (SNack1 r k r' (token_of_bool i)))
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
  Case "lossy(err1,err2)".
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
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity
        | ].
    (* /d!err1; rest *)
    eapply TypPrefixOutput with (s:=SDual SLossy)
        (rho:=TChannel (SDual (SNack r k r' (token_of_bool i))))
        (t:=SDual (SLossy1 (SNack r k r' (token_of_bool i))
          (SNack r k r' (token_of_bool i))));
      [apply trdual_w_mdual_involution;
          apply TRLossyB with (i:=i) (r:=r) (k:=k) (r':=r');
          reflexivity
        | left; discriminate
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity
        | ].
    (* /d!err2; rest *)
    eapply TypPrefixOutput with
        (s:=SDual (SLossy1 (SNack r k r' (token_of_bool i))
          (SNack r k r' (token_of_bool i))))
        (rho:=TChannel (SNack r k r' (token_of_bool i)))
          (t:=SDual SEpsilon);
      [apply trdual_w_mdual_involution; constructor
        | left; discriminate
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity
        | ].
    (* 0 *)
    apply TypZero;
      ctx_wf;
      discriminate_w_list.

  (* + err2!i; err2!x; lossy(err1, err2)) *)
  Case "+ err2!i; err2!x; lossy(err1,err2)".
    (* err2!i; rest *)
    eapply TypPrefixOutput with (s:=SNack r k r' (token_of_bool i))
        (rho:=TSingleton (token_of_bool i))
        (t:=SNack1 r k r' (token_of_bool i));
      [constructor; assumption
        | left; contradict H_xi_nin; discriminate_w_list
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity
        | ].
    (* err2!x; rest *)
    eapply TypPrefixOutput with (s:=SNack1 r k r' (token_of_bool i))
        (rho:=TSingleton k) (t:=SNack r k r' (token_of_bool i));
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
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity
        | ].
    (* /d!err1; rest *)
    eapply TypPrefixOutput with (s:=SDual SLossy)
        (rho:=TChannel (SDual (SNack r k r' (token_of_bool i))))
        (t:=SDual (SLossy1 (SNack r k r' (token_of_bool i))
          (SNack r k r' (token_of_bool i))));
      [apply trdual_w_mdual_involution;
          apply TRLossyB with (i:=i) (r:=r) (k:=k) (r':=r');
          reflexivity
        | left; discriminate
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity
        | ].
    (* /d!err2; rest *)
    eapply TypPrefixOutput with
        (s:=SDual (SLossy1 (SNack r k r' (token_of_bool i))
          (SNack r k r' (token_of_bool i))))
        (rho:=TChannel (SNack r k r' (token_of_bool i)))
        (t:=SDual SEpsilon);
      [apply trdual_w_mdual_involution; constructor
        | left; discriminate
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity
        | ].
    (* 0 *)
    apply TypZero;
      destruct i;
      ctx_wf;
      discriminate_w_list.
Qed.
