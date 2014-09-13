Require Import String.
Require Import TypeAssignmentPoly.
Require Import ResultBasics.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import List.
Require Import ExampleCommon.

Require String. Open Scope string_scope.

Lemma ctx_G'_wf : 
  forall x s t rho, 
    x <> "c" 
    ->
    x <> "d" 
    ->
    CTX.add (ValVariable (Var (Free x)), rho)
    (ctx_replace namec (TChannel s) (TChannel t)
      (CTX.add (namec, TChannel s)
        (CTX.add (named, TChannel (SDual s)) CTX.empty))) |-wf .
Proof with (try (solve [apply FNm|apply FCoNm|apply FVariable])).
  intros x s t rho Hneqc Hneqd.
  ctx_wf.
Qed.

Definition uni_forwarder_one_step (c d : value) (p : proc) : proc := 
  c ? ; (d ! var0; p).

Lemma uni_forwarder_one_step_zero_typing_long :
  forall s : session,
    (CTX.add (namec, TChannel s) (CTX.add (named, TChannel (SDual s)) CTX.empty))
    |-p
      (uni_forwarder_one_step namec named Zero).
Proof.
  intros.
  unfold uni_forwarder_one_step.
  apply TypPrefixInput with (s:=s) (L:=(("c" : free_id) :: ("d":free_id) :: nil)).

  Case "Let G=(namec,s)(named,SDual s). G |-v u : TChannel s".
    apply LContext.
    SCase "G well formed".
      apply ctx_add_namec_s_add_named_SDual_s_well_formed.

    SCase "Is (namec,?) in ((namec,s),(named,SDual s))?".
      x_in_G.

  Case "free_values_in_context G P".
    free_vals_in_ctx.

  Case "G' |-p (open_proc x 0 P)".
    intros. subst.
    simpl.
    eapply TypPrefixOutput with (s := (SDual s)).
    apply trdual_w_mdual_involution. eauto.
    left; discriminate.

    apply LContext.
    SCase "((x,rho),replace(namec,s,t) (namec,s),(named,SDual s))|-wf".
      apply ctx_G'_wf.
        SSCase "x<>c".
          contradict H. rewrite -> H. apply in_eq.
        SSCase "x<>d".
          contradict H. rewrite -> H.  apply in_cons. apply in_eq.

    SCase "Is (named,SDual s) in (Var x,rho)replace(namec,s,t)((namec,s)(named,SDual s))".
      x_in_G.

    SCase "(Var x,rho)(replace(namec,s,t)((namec,s)(named,SDual s)))|-v open_value x 0 var0:rho".
      apply LContext.
      SSCase "((x,rho),replace(namec,s,t) (namec,s),(named,SDual s))|-wf".
        apply ctx_G'_wf.
        SSSCase "x<>c".
          contradict H. rewrite -> H. apply in_eq.
        SSSCase "x<>d".
          contradict H. rewrite -> H.  apply in_cons. apply in_eq.
      SSCase "Is (open_value x 0 var0, rho) in (Var x,rho)(replace(namec,s,t)((namec,s)(named,SDual s)))".
        x_in_G.

    SCase "?733=remove(open_value x 0 var0,rho)(Var x, rho)(replace(namec,s,t)(namec,s)(named,SDual)) \/ ?733=(Var x,rho)(replace(namec,s,t)((namec,s)(named,SDual s))) /\ |-st rho".
      left.
      reflexivity.

    SCase "?734=replace(open_value x 0 named,SDual s,SDual t)(remove(open_value x 0 var0, rho) ((Var x, rho)(replace(namec,s,t)((namec,s)(named,SDual s)))))".
      reflexivity.
      apply TypZero.

    SCase "replace(open_value x 0 named,SDual s,SDual t)(remove(open_value x 0 var0, rho) ((Var x, rho)(replace(namec,s,t)((namec,s)(named,SDual s)))))|-wf".
      apply ctx_replace_preserves_wf; [x_in_G|].
      SSCase "(remove(open_value x 0 var0, rho) ((Var x, rho)(replace(namec,s,t)((namec,s)(named,SDual s)))))|-wf". 
        apply wellformed_ctx_remove_1.
        apply ctx_G'_wf.
        SSSCase "x<>c".
          contradict H. rewrite -> H. apply in_eq.
        SSSCase "x<>d".
          contradict H. rewrite -> H.  apply in_cons. apply in_eq.
Qed.

(* This proves the same theorem as the previous lemma.  It just shows how
   to prove it using some of the tactics found in ExampleCommon.v. *)
Lemma uni_forwarder_one_step_zero_typing :
  forall s : session,
    (CTX.add (namec, TChannel s) (CTX.add (named, TChannel (SDual s)) CTX.empty))
    |-p
      (uni_forwarder_one_step namec named Zero).
Proof.
  intros.
  unfold uni_forwarder_one_step.
  apply TypPrefixInput with (s:=s)
      (L:=(("c" : free_id) :: ("d":free_id) :: nil));
    [apply LContext; [ctx_wf|x_in_G] | free_vals_in_ctx|].

  Case "G' |-p (open_proc x 0 P)".
    intros; subst; simpl.
    eapply TypPrefixOutput with (s := (SDual s));
      [apply trdual_w_mdual_involution; eauto | left; discriminate | constructor; [ctx_wf|x_in_G]
        | constructor; [ctx_wf|x_in_G] | left; reflexivity | reflexivity | ].

  apply TypZero; ctx_wf.
Qed.
