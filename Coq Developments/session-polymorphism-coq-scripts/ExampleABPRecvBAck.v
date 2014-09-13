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

Lemma abp_recvB_Ack_procR_typing :
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
    |-p Var (Free xerr2) ? ;
        (IsEq (Var (Bound 0))
          (Token (if if i then false else true then "true" else "false"))
        (Var (Free xerr2) ? ;
        (New
        (CoNm (Free (String.append "recv_" (if i then "true" else "false")))
          ! Nm (Bound 0);
        (CoNm (Bound 0) ! Var (Free xerr2);
        (CoNm (Bound 0) ! Var (Free xout);
        Zero)))))).
Proof.
  intros i t xc xerr2 xout Hxc_nin Hxerr2_nin Hxout_nin.
  (* err2?z; rest *)
  apply TypPrefixInput with (s:=SDual (SAck t (token_of_bool (negb i))))
      (L:=xc :: xerr2 :: xout :: "recv_true" :: "recv_false" :: nil);
    [constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
      | free_vals_in_ctx |].
  intros G' rho t' z H_z_nin Htrans G'def; compute; subst G'.
  inversion Htrans; subst; inversion H1; subst; inversion H0; subst.

  Case "Htrans = TRAckA".
    (* [z=(1−i)]; rest *)
    apply TypIsEq with (K:=token_of_bool (negb i))
        (L:=token_of_bool (negb i));
      [constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | apply LToken; destruct i; ctx_wf; discriminate_w_list
        | free_vals_in_ctx; try instantiate (1:=TSingleton (token_of_bool i));
            contradiction
        | intro H_i_tok_eq; clear H_i_tok_eq].
    (* err2?y; rest *)
    apply TypPrefixInput with (s:=SDual (SAck1 t (token_of_bool (negb i))))
        (L:=z :: xc :: xerr2 :: xout :: "recv_true" :: "recv_false" :: nil);
      [constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | free_vals_in_ctx; try instantiate (1:=TSingleton (token_of_bool i));
          contradiction
        |].
    intros G' rho t' y H_y_nin Htrans1 G'def; compute; subst G'.
    inversion Htrans1; subst; inversion H3; subst; inversion H2; subst.
    (* recv_i(err2, out), i.e. New d *)
    apply TypNew with (s:=SRecv i)
        (L:=y :: z :: xc :: xerr2 :: xout :: "recv_true" :: "recv_false"
          :: nil);
      intros d G' H_d_nin G'def; compute; subst G'.
    (* d!"recv_i";rest *)
    eapply TypPrefixOutput with (s:=SDual (SFwd (SRecv i)))
        (rho:=TChannel (SRecv i)) (t:=SDual (SFwd (SRecv i)));
      [apply trdual_w_mdual_involution; constructor
        | left; discriminate
        | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity
        | ].
    (* d!err2;rest *)
    eapply TypPrefixOutput with (s:=SDual (SRecv i))
        (rho:=TChannel (SDual (SAck t (token_of_bool (negb i)))))
        (t:=SDual (SRecv1 i (SAck t (token_of_bool (negb i))) t));
      [apply trdual_w_mdual_involution; apply TRRecvB; reflexivity
        | left; discriminate
        | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity
        | ].
    (* d!out;rest *)
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

  Case "Htrans = TRAckC".
    (* [z=(1−i)]; rest *)
    apply TypIsEq with
        (K:=Token (string_of_negb_string (string_of_bool (negb i))))
        (L:=token_of_bool (negb i));
      [constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
        | apply LToken; destruct i; ctx_wf; discriminate_w_list
        | free_vals_in_ctx; try instantiate (1:=TSingleton (token_of_bool i));
            contradiction
        |];
      intro H_bad;
      destruct i in H_bad;
      contradict H_bad;
      discriminate.
Qed.
