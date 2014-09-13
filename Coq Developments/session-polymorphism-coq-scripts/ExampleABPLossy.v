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
Require Import ExampleABPLossyBase.
Require Import ExampleABPLossyAA.
Require Import ExampleABPLossyAB.
Require Import ExampleABPLossyAC.
Require Import ExampleABPLossyAD.
Require Import ExampleABPLossyBA.
Require Import ExampleABPLossyBB.
Require Import ExampleABPLossyBC.
Require Import ExampleABPLossyBD.


Lemma abp_lossy_procR_typing :
  CTX.add(ValName (Nm (Free "lossy")), TChannel (SFwd SLossy))
    (CTX.add(ValName (CoNm (Free "lossy")), TChannel (SDual (SFwd SLossy)))
    CTX.empty)
  |-p recv_args "lossy" ("err1" :: "err2" :: nil)
    (transformProcR abp_lossy_procR).
Proof.
  compute.
  (* lossy?xc; rest *)
  apply TypPrefixInput with (s:=SFwd SLossy) (L:="lossy" :: nil);
    [constructor; [ctx_wf | x_in_G]
      | free_vals_in_ctx |].
  intros G' rho t xc H_xc_nin Htrans G'def; compute; subst G'.
  inversion Htrans; subst.
  (* clean up context *)
  apply ctx_equal_preserves_typed with (G1:=
      (CTX.add (ValVariable (Var (Free xc)), TChannel SLossy)
      (CTX.add (ValName (Nm (Free "lossy")), TChannel (SFwd SLossy))
      (CTX.add (ValName (CoNm (Free "lossy")), TChannel (SDual (SFwd SLossy)))
      CTX.empty))));
    [|apply ctx_add_1; [reflexivity|];
      symmetry;
      apply ctx_replace_nothing_eq_stronger;
      [x_in_G|reflexivity]].
  (* xc?err1; rest *)
  apply TypPrefixInput with (s:=SLossy) (L:=xc :: "lossy" :: nil);
    [constructor; [ctx_wf | x_in_G]
      | free_vals_in_ctx |].
  intros G' rho t xerr1 H_xerr1_nin Htrans1 G'def; compute; subst G'.
  (* clean up context *)
  apply ctx_equal_preserves_typed with (G1:=
      (CTX.add (ValVariable (Var (Free xerr1)), rho)
      (CTX.add (ValVariable (Var (Free xc)), TChannel t)
      (CTX.add (ValName (Nm (Free "lossy")), TChannel (SFwd SLossy))
      (CTX.add (ValName (CoNm (Free "lossy")), TChannel (SDual (SFwd SLossy)))
      CTX.empty)))));
    [|apply ctx_add_1;
      [reflexivity|];
      symmetry;
      unfold ctx_replace;
      rewrite -> CTXProperties.remove_add;
      [reflexivity|x_nin_G]].
  (* xc?err2; rest *)
  apply TypPrefixInput with (s:=t) (L:=xerr1 :: xc :: "lossy" :: nil);
    [constructor; [ctx_wf | x_in_G]
      | free_vals_in_ctx |].
  intros G' rho' t' xerr2 H_xerr2_nin Htrans2 G'def; compute; subst G'.
  (* clean up context *)
  apply ctx_equal_preserves_typed with (G1:=
      (CTX.add (ValVariable (Var (Free xerr2)), rho')
      (CTX.add (ValVariable (Var (Free xc)), TChannel t')
      (CTX.add (ValVariable (Var (Free xerr1)), rho)
      (CTX.add (ValName (Nm (Free "lossy")), TChannel (SFwd SLossy))
      (CTX.add (ValName (CoNm (Free "lossy")), TChannel (SDual (SFwd SLossy)))
      CTX.empty))))));
    [|unfold ctx_replace;
      apply ctx_add_1;
      [reflexivity|];
      apply ctx_add_1;
      [reflexivity|];
      symmetry;
      rewrite <- CTXProperties.add_add with (s:=
      (CTX.add (ValName (Nm (Free "lossy")), TChannel (SFwd SLossy))
      (CTX.add (ValName (CoNm (Free "lossy")), TChannel (SDual (SFwd SLossy)))
      CTX.empty)));
      rewrite -> CTXProperties.remove_add;
      [reflexivity|x_nin_G; discriminate_w_list]].
  (* abp_lossyA_procR ++ abp_lossyB_procR *)
  apply TypSum;
    inversion Htrans1; subst;
    inversion Htrans2; subst.
  Case "Htrans1 = TRLossyA, abp_lossyA_procR".
    apply abp_lossyAA_procR_typing with (i:=i) (r:=r);
      try assumption;
      split;
      reflexivity.
  Case "Htrans1 = TRLossyB, abp_lossyA_procR".
    apply abp_lossyAB_procR_typing with (i:=i) (r:=r) (k:=k) (r':=r');
      try assumption;
      split;
      reflexivity.
  Case "Htrans1 = TRLossyC, abp_lossyA_procR".
    apply abp_lossyAC_procR_typing with (i:=i) (r:=r) (k:=k) (r':=r');
      try assumption;
      split;
      reflexivity.
  Case "Htrans1 = TRLossyD, abp_lossyA_procR".
    apply abp_lossyAD_procR_typing with (i:=i) (r:=r) (k:=k) (r':=r');
      try assumption;
      split;
      reflexivity.
  Case "Htrans1 = TRLossyA, abp_lossyB_procR".
    eapply abp_lossyBA_procR_typing with (i:=i) (r:=r);
      try assumption;
      split;
      reflexivity.
  Case "Htrans1 = TRLossyB, abp_lossyB_procR".
    eapply abp_lossyBB_procR_typing with (i:=i) (r:=r);
      try assumption;
      split;
      reflexivity.
  Case "Htrans1 = TRLossyC, abp_lossyB_procR".
    eapply abp_lossyBC_procR_typing with (i:=i) (r:=r);
      try assumption;
      split;
      reflexivity.
  Case "Htrans1 = TRLossyD, abp_lossyB_procR".
    eapply abp_lossyBD_procR_typing with (i:=i) (r:=r);
      try assumption;
      split;
      reflexivity.
Qed.



Require Import ResultRename.

Lemma abp_lossy_typing :
  forall s t i r k r',
  ((s = (SAck r (token_of_bool i)) /\ t = (SAck r (token_of_bool i))))
  \/ ((s = (SNack r k r' (token_of_bool i)))
    /\ (t = (SNack r k r' (token_of_bool i))))
  \/ ((s = (SNack r k r' (token_of_bool (negb i))))
    /\ (t = (SAck r (token_of_bool i))))
  \/ ((s = (SNack r k r' (token_of_bool i)))
    /\ (t = (SAck r' (token_of_bool i))))
  ->
  CTX.add(ValName (CoNm (Free "err1")), TChannel (SDual s))
    (CTX.add(ValName (Nm (Free "err2")), TChannel t)
    CTX.empty)
  |-p abp_lossy (ValName (CoNm (Free "err1"))) (ValName (Nm (Free "err2"))).
Proof.
  intros s t i r k r' Hst.
  compute.
  apply TypNew with (s:=SFwd SLossy) (L:="lossy" :: "err1" :: "err2" ::nil).
  intros lossy G' H_lossy_nin G'def; compute; subst.

  pose (typed_rename _ _ abp_lossy_procR_typing "lossy" lossy) as Hu.
  simpl in Hu.
  eapply TypPar; [
    |eapply TypPar;
      [apply partition_empty; ctx_wf
        |apply Hu
        |apply TypZero; ctx_wf]
    |].
  Case "G |-part freeid_rename_ctx 'lossy' lossy GL (+) GR".
    Focus 1.
    instantiate (1:=
      (CTX.add(ValName (CoNm (Free lossy)), TChannel (SDual (SFwd SLossy)))
      (CTX.add(ValName (CoNm (Free "err1")), TChannel (SDual s))
      (CTX.add(ValName (Nm (Free "err2")), TChannel t)
      CTX.empty)))).

    (* get rid of the freeid_rename_ctx *)
    clear Hu.
    eapply ctx_equal_part_2;
      [| (repeat rewrite freeid_rename_ctx_add ||
       rewrite freeid_rename_ctx_empty); [reflexivity | x_nin_G | x_nin_G]].
    simpl.
    (* now the paritition *)
    apply Partition.
    SCase "CTX.eq G' (CTX.union GL GR)".
      unfold CTX.eq; unfold CTX.Equal.
      induction a as (u,rho).
      split; intros H0.
      SSCase "forall (u,rho), CTX.In (u,rho) G'".
        x_in_G;
        inversion H; subst;
        rewrite CTXFacts.union_iff;
        try solve [left; x_in_G];
        try solve [right; x_in_G].
      SSCase "forall (u,rho), CTX.In (u,rho) (CTX.union GL GR)".
        x_in_G; assumption.
    SCase "G'|-wf".
      ctx_wf.
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
          | H : SDual (SFwd _) -- _ --> _ |- _ => inversion H; clear H
          | H : SFwd _ -- _ --> _ |- _ => inversion H; clear H
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

  Case "freeid_rename_ctx 'lossy' lossy ((Nm 'lossy',) (CoNm 'lossy',) empty)".
    apply typed_rename_wf; [ctx_wf|].
    rewrite free_ids_context_iff.
    red.
    intros.
    repeat destruct H.
    x_in_G;
      inversion H;
      subst;
      simpl in H0;
      contradict H_lossy_nin;
      destruct H0;
      try solve [left; assumption];
      contradiction.

  Case "~In lossy (free_ids_context ((Nm 'lossy',) (CoNm 'lossy',) empty))".
    rewrite free_ids_context_iff.
    red.
    intros.
    repeat destruct H.
    x_in_G;
      inversion H;
      subst;
      simpl in H0;
      contradict H_lossy_nin;
      destruct H0;
      try solve [left; assumption];
      contradiction.

  Case "(/lossy,SDual SFwd SLossy) (/'err1', SDual s) ('err2',t)
      |-p bootstrap".
    apply TypNew with (s:=SLossy)
      (L:=lossy :: "lossy" :: "err1" :: "err2" ::nil).
    intros d G' H_d_nin G'def; compute; subst.
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
    SCase "Hst = TRLossyA".
      destruct Hst; (destruct H; subst).
      (* /d!err1; rest *)
      eapply TypPrefixOutput with (s:=SDual SLossy)
          (rho:=TChannel (SDual (SAck r (token_of_bool i))))
          (t:=SDual (SLossy1 (SAck r (token_of_bool i))
            (SAck r (token_of_bool i))));
        [apply trdual_w_mdual_involution; apply TRLossyA with (i:=i) (r:=r);
              reflexivity
          | left; contradict H_d_nin; inversion H_d_nin; subst;
              discriminate_w_list
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

    SSCase "Hst = TRLossyB".
      destruct H; subst.
      (* /d!err1; rest *)
      eapply TypPrefixOutput with (s:=SDual SLossy)
          (rho:=TChannel (SDual (SNack r k r' (token_of_bool i))))
          (t:=SDual (SLossy1 (SNack r k r' (token_of_bool i))
            (SNack r k r' (token_of_bool i))));
        [apply trdual_w_mdual_involution;
              apply TRLossyB with (i:=i) (r:=r) (k:=k) (r':=r');
              reflexivity
          | left; contradict H_d_nin; inversion H_d_nin; subst;
              discriminate_w_list
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

    SSCase "Hst = TRLossyC".
      destruct H; destruct H; subst.
      (* /d!err1; rest *)
      eapply TypPrefixOutput with (s:=SDual SLossy)
          (rho:=TChannel (SDual (SNack r k r' (token_of_bool (negb i)))))
          (t:=SDual (SLossy1 (SNack r k r' (token_of_bool (negb i)))
            (SAck r (token_of_bool i))));
        [apply trdual_w_mdual_involution;
              apply TRLossyC with (i:=i) (r:=r) (k:=k) (r':=r');
              reflexivity
          | left; contradict H_d_nin; inversion H_d_nin; subst;
              discriminate_w_list
          | constructor; [ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* /d!err2; rest *)
      eapply TypPrefixOutput with
          (s:=SDual (SLossy1 (SNack r k r' (token_of_bool (negb i)))
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

    SSSCase "Hst = TRLossyD".
      (* /d!err1; rest *)
      eapply TypPrefixOutput with (s:=SDual SLossy)
          (rho:=TChannel (SDual (SNack r k r' (token_of_bool i))))
          (t:=SDual (SLossy1 (SNack r k r' (token_of_bool i))
            (SAck r' (token_of_bool i))));
        [apply trdual_w_mdual_involution;
              apply TRLossyD with (i:=i) (r:=r) (k:=k) (r':=r');
              reflexivity
          | left; contradict H_d_nin; inversion H_d_nin; subst;
              discriminate_w_list
          | constructor; [ctx_wf; discriminate_w_list | x_in_G]
          | constructor; [ctx_wf; discriminate_w_list | x_in_G]
          | left; reflexivity
          | reflexivity
          | ].
      (* /d!err2; rest *)
      eapply TypPrefixOutput with
          (s:=SDual (SLossy1 (SNack r k r' (token_of_bool i))
            (SAck r' (token_of_bool i))))
          (rho:=TChannel (SAck r' (token_of_bool i)))
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

Lemma abp_lossy_typing_corr i r :
  CTX.add(ValName (CoNm (Free "err1")),
      TChannel (SDual (SAck r (token_of_bool i))))
    (CTX.add(ValName (Nm (Free "err2")), TChannel (SAck r (token_of_bool i)))
    CTX.empty)
  |-p abp_lossy (ValName (CoNm (Free "err1"))) (ValName (Nm (Free "err2"))).
Proof.
  eapply abp_lossy_typing with (i:=i) (r:=r) (k:=Token "") (r':=r);
    left; split; reflexivity.
Qed.
