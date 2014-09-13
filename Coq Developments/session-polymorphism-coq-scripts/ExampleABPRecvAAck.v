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

Lemma abp_recvA_Ack_procR_typing :
  forall i t (xc:free_id) (xerr2:free_id) (xout:free_id),
    ~ In xc ("recv_true" :: "recv_false" :: nil)
    ->
    ~ In xerr2 (xc :: "recv_true" :: "recv_false" :: nil)
    ->
    ~ In xout (xerr2 :: xc :: "recv_true" :: "recv_false" :: nil)
    ->
    (CTX.add (ValVariable (Var (Free xout)), TChannel (SDual (SToks t)))
      (CTX.add (ValVariable (Var (Free xc)), TChannel SEpsilon)
      (CTX.add (ValVariable (Var (Free xerr2)),
        TChannel (SDual (SAck t (token_of_bool (negb i)))))
      (CTX.add (ValName (Nm (Free ("recv_" ++ string_of_bool i))),
        TChannel (SFwd (SRecv i)))
      (CTX.add (ValName (CoNm (Free ("recv_" ++ string_of_bool i))),
        TChannel (SDual (SFwd (SRecv i))))
      (CTX.add (ValName (CoNm (Free ("recv_" ++ string_of_bool (negb i)))),
        TChannel (SDual (SFwd (SRecv (negb i)))))
      CTX.empty))))))
    |-p Var (Free xerr2) !
          Token (if if i then false else true then "true" else "false");
        (New
        (CoNm (Free (String.append "recv_" (if i then "true" else "false")))
          ! Nm (Bound 0);
        (CoNm (Bound 0) ! Var (Free xerr2);
        (CoNm (Bound 0) ! Var (Free xout);
        Zero)))).
Proof.
  intros i t xc xerr2 xout Hxc_nin Hxerr2_nin Hxout_nin.
  (* err2!(1-i); rest *)
  eapply TypPrefixOutput with
      (s:=SDual (SAck t (token_of_bool (negb i))))
      (rho:=TSingleton (token_of_bool (negb i)))
      (t:=SDual (SAck t (token_of_bool (negb i))));
    [apply trdual_w_mdual_involution; constructor; assumption
      | left; discriminate
      | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
      | apply LToken; destruct i; ctx_wf; discriminate_w_list
      | right; split; [reflexivity | constructor]
      | reflexivity
      | ].
  (* recv_i(err2, out), i.e. New d *)
  apply TypNew with (s:=SRecv i)
      (L:=xc :: xerr2 :: xout :: "recv_true" :: "recv_false" :: nil);
    intros d G' H_d_nin G'def; compute; subst G'.
  (* d!"recv_i"; rest *)
  eapply TypPrefixOutput with (s:=SDual (SFwd (SRecv i)))
      (rho:=TChannel (SRecv i)) (t:=SDual (SFwd (SRecv i)));
    [apply trdual_w_mdual_involution; constructor
      | left; discriminate
      | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
      | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
      | left; reflexivity
      | reflexivity
      | ].
  (* d!err2; rest *)
  eapply TypPrefixOutput with (s:=SDual (SRecv i))
      (rho:=TChannel (SDual (SAck t (token_of_bool (negb i)))))
      (t:=SDual (SRecv1 i (SAck t (token_of_bool (negb i))) t));
    [apply trdual_w_mdual_involution; constructor; reflexivity
      | left; discriminate
      | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
      | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
      | left; reflexivity
      | reflexivity
      | ].
  (* d!out; rest *)
  eapply TypPrefixOutput with
      (s:=SDual (SRecv1 i (SAck t (token_of_bool (negb i))) t))
      (rho:=TChannel (SDual (SToks t)))
      (t:=SDual SEpsilon);
    [apply trdual_w_mdual_involution; constructor; reflexivity
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
