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


Lemma abp_lossyBA_procR_typing :
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
  |-p Var (Free xerr2) ? ;
    (New
      (CoNm (Free "lossy") ! Nm (Bound 0);
        (CoNm (Bound 0) ! Var (Free xerr1);
          (CoNm (Bound 0) ! Var (Free xerr2); Zero))) +++
    (Var (Free xerr1) ! Var (Bound 0);
      (New
        (CoNm (Free "lossy") ! Nm (Bound 0);
          (CoNm (Bound 0) ! Var (Free xerr1);
            (CoNm (Bound 0) ! Var (Free xerr2); Zero)))))).
Proof.
  intros xc xerr1 xerr2 i r s t H_xc_nin H_xerr1_nin H_xerr2_nin Hst.
  destruct Hst; subst.
  (* err2?i; rest *)
  apply TypPrefixInput with (s:=SAck r (token_of_bool i))
      (L:=xerr2 :: xerr1 :: xc :: "lossy" :: nil);
    [constructor; [ctx_wf; discriminate_w_list | x_in_G]
      | free_vals_in_ctx |].
  intros G' rho t xi H_xi_nin Htrans G'def; compute; subst G'.
  inversion Htrans; subst.
  (* (lossy(err1, err2) + err1!i;lossy(err1, err2)) *)
  apply TypSum.

  (* (lossy(err1, err2), i.e. New d *)
  Case "lossy(err1, err2)".
    apply TypNew with (s:=SLossy)
        (L:=xi :: xerr2 :: xerr1 :: xc :: "lossy" :: nil);
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
        (rho:=TChannel (SDual (SAck r (token_of_bool i))))
        (t:=SDual (SLossy1 (SAck r (token_of_bool i))
          (SAck r (token_of_bool i))));
      [apply trdual_w_mdual_involution; apply TRLossyA with (i:=i) (r:=r);
          reflexivity
        | left; discriminate
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
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
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity
        | ].
    (* 0 *)
    apply TypZero;
      ctx_wf;
      discriminate_w_list.

  (* + err1!i;lossy(err1, err2)) *)
  Case "+ err1!i; lossy(err1,err2)".
    (* err1!i; rest *)
    eapply TypPrefixOutput with (s:=SDual (SAck r (token_of_bool i)))
        (rho:=TSingleton (token_of_bool i))
        (t:=SDual (SAck r (token_of_bool i)));
      [apply trdual_w_mdual_involution; constructor
        | left; contradict H_xi_nin; discriminate_w_list
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity
        | ].
    (* (lossy(err1, err2), i.e. New d *)
    apply TypNew with (s:=SLossy)
        (L:=xi :: xerr2 :: xerr1 :: xc :: "lossy" :: nil);
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
        (rho:=TChannel (SDual (SAck r (token_of_bool i))))
        (t:=SDual (SLossy1 (SAck r (token_of_bool i))
          (SAck r (token_of_bool i))));
      [apply trdual_w_mdual_involution; apply TRLossyA with (i:=i) (r:=r);
          reflexivity
        | left; discriminate
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
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
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity
        | ].
    (* 0 *)
    apply TypZero;
      ctx_wf;
      discriminate_w_list.
Qed.
