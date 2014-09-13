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

Lemma abp_recvC_Nack_procR_typing :
  forall i k r t (xc:free_id) (xerr2:free_id) (xout:free_id),
    ~ In xc ("recv_true" :: "recv_false" :: nil)
    ->
    ~ In xerr2 (xc :: "recv_true" :: "recv_false" :: nil)
    ->
    ~ In xout (xerr2 :: xc :: "recv_true" :: "recv_false" :: nil)
    ->
    (CTX.add (ValVariable (Var (Free xout)), TChannel (SDual (SToks t)))
      (CTX.add (ValVariable (Var (Free xc)), TChannel SEpsilon)
      (CTX.add (ValVariable (Var (Free xerr2)),
        TChannel (SDual (SNack r k t (token_of_bool (negb i)))))
      (CTX.add (ValName (Nm (Free ("recv_" ++ string_of_bool i))),
        TChannel (SFwd (SRecv i)))
      (CTX.add (ValName (CoNm (Free ("recv_" ++ string_of_bool i))),
        TChannel (SDual (SFwd (SRecv i))))
      (CTX.add (ValName (CoNm (Free ("recv_" ++ string_of_bool (negb i)))),
        TChannel (SDual (SFwd (SRecv (negb i)))))
      CTX.empty))))))
    |-p Var (Free xerr2) ? ;
        (IsEq (Var (Bound 0)) (Token (if i then "true" else "false"))
        (Var (Free xerr2) ? ;
        (Var (Free xout) ! Var (Bound 0);
        (New
        (CoNm (Free (String.append "recv_"
            (if if i then false else true then "true" else "false")))
          ! Nm (Bound 0);
        (CoNm (Bound 0) ! Var (Free xerr2);
        (CoNm (Bound 0) ! Var (Free xout);
        Zero))))))).
Proof.
  intros i k r t xc xerr2 xout Hxc_nin Hxerr2_nin Hxout_nin.
  (* err2?z; rest *)
  apply TypPrefixInput with (s:=SDual (SNack r k t (token_of_bool (negb i))))
      (L:=xc :: xerr2 :: xout :: "recv_true" :: "recv_false" :: nil);
    [constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
      | free_vals_in_ctx |].
  intros G' rho t' z H_z_nin Htrans G'def; compute; subst G'.
  inversion Htrans; subst; inversion H1; subst; inversion H0; subst.
  (* [z=i]; rest *)
  apply TypIsEq with (K:=token_of_bool (negb i))
      (L:=token_of_bool i);
    [constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G]
      | apply LToken; destruct i; ctx_wf; discriminate_w_list
      | free_vals_in_ctx; try instantiate (1:=TSingleton (token_of_bool i));
          contradiction
      | ];
  intro H_bad;
    destruct i in H_bad;
    contradict H_bad;
    discriminate.
Qed.