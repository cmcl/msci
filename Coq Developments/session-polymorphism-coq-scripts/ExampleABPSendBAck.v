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

Lemma abp_sendB_Ack_procR_typing :
  forall i k r r' (xc:free_id) (xerr1:free_id) (x:free_id) (xin:free_id),
    r --(MInp (TSingleton k))--> r'
    ->
    ~ In xc ("send_true" :: "send_false" :: nil)
    ->
    ~ In x (xc :: "send_true" :: "send_false" :: nil)
    ->
    ~ In xin (x :: xc :: "send_true" :: "send_false" :: nil)
    ->
    ~ In xerr1 (xin :: x :: xc :: "send_true" :: "send_false" :: nil)
    ->
    (CTX.add(ValVariable (Var (Free xerr1)),
        TChannel (SAck r (token_of_bool (negb i))))
      (CTX.add(ValVariable (Var (Free xc)), TChannel SEpsilon)
      (CTX.add(ValVariable (Var (Free xin)), TChannel (SToks (r')))
      (CTX.add(ValVariable (Var (Free x)), TSingleton k)
      (CTX.add(ValName (Nm (Free (String.append "send_" (string_of_bool i)))),
        (TChannel (SFwd (SSend i))))
      (CTX.add(ValName(CoNm (Free (String.append "send_" (string_of_bool i)))),
        (TChannel (SDual (SFwd (SSend i)))))
      (CTX.add(ValName (CoNm (Free (String.append "send_"
        (string_of_bool (negb i))))),
        (TChannel (SDual (SFwd (SSend (negb i))))))
      CTX.empty)))))))
    |-p Var (Free xerr1) ? ;
      (IsEq (Var (Bound 0))
        (Token (if if i then false else true then "true" else "false"))
      (New
      (CoNm (Free (String.append "send_" (if i then "true" else "false")))
        ! Nm (Bound 0);
      (CoNm (Bound 0) ! Var (Free x);
      (CoNm (Bound 0) ! Var (Free xin);
      (CoNm (Bound 0) ! Var (Free xerr1);
      Zero)))))).
Proof.
  intros i k r r' xc xerr1 x xin Htrans Hxc_nin Hx_nin Hxin_nin Hxerr1_nin.
  compute.
  apply TypPrefixInput  with (s:=SAck r (token_of_bool (negb i)))
      (L:=xc :: xerr1 :: xin :: x :: "send_true" :: "send_false" :: nil);
    [constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
      | free_vals_in_ctx |].
  intros G' rho t z H_z_nin Htrans4 G'def; compute; subst G'.
  inversion Htrans4; subst.
  Case "Htrans4 : TRNackB".
    apply TypIsEq with (K:=token_of_bool (negb i)) (L:=token_of_bool (negb i));
      [constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | apply LToken; destruct i; ctx_wf; discriminate_w_list
        | free_vals_in_ctx |].
    intro H_i_tok_eq.
    apply TypNew  with (s:=SSend i)
        (L:=z :: xc :: xerr1 :: xin :: x :: "send_true" :: "send_false"
          :: nil).
    intros d G' H_d_nin G'def; compute; subst G'.
    eapply TypPrefixOutput with (s:=SDual (SFwd (SSend i)))
        (rho:=TChannel (SSend i)) (t:=SDual (SFwd (SSend i)));
      [apply trdual_w_mdual_involution; constructor
        | left; discriminate
        | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity | ].
    eapply TypPrefixOutput with (s:=SDual (SSend i))
        (rho:=TSingleton k)
        (t:=SDual (SSend1 i r' (SAck r (token_of_bool (negb i)))));
      [apply trdual_w_mdual_involution; constructor; assumption
        | left; discriminate
        | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | right; split; [reflexivity | constructor]
        | reflexivity | ].
    eapply TypPrefixOutput with
        (s:=SDual (SSend1 i r' (SAck r (token_of_bool (negb i)))))
        (rho:=TChannel (SToks r'))
        (t:=SDual (SSend2 i (SAck r (token_of_bool (negb i)))));
      [apply trdual_w_mdual_involution; constructor; assumption
        | left; discriminate
        | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity | ].
    eapply TypPrefixOutput with
        (s:=SDual (SSend2 i (SAck r (token_of_bool (negb i)))))
        (rho:=TChannel (SAck r (token_of_bool (negb i))))
        (t:=SDual SEpsilon);
      [apply trdual_w_mdual_involution; constructor; assumption
        | left; discriminate
        | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity | ].
    apply TypZero;
      destruct i;
      ctx_wf;
      discriminate_w_list.
Qed.
