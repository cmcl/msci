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
Require Import TypeAssignmentPoly.
Require Import ResultBasics.
Require Import ExampleCommon.
Require Import ExampleRecursion.
Require Import ExampleABPRecvBase.
Require Import ExampleABPRecvANack.
Require Import ExampleABPRecvBNack.
Require Import ExampleABPRecvCNack.
Require Import ExampleABPRecvAAck.
Require Import ExampleABPRecvBAck.
Require Import ExampleABPRecvCAck.

Lemma abp_recv_procR_typing i :
    CTX.add(ValName (Nm (Free ((String.append "recv_" (string_of_bool i))))),
        (TChannel (SFwd (SRecv i))))
      (CTX.add(ValName
          (CoNm (Free (String.append "recv_" (string_of_bool i)))),
        (TChannel (SDual (SFwd (SRecv i)))))
      (CTX.add(ValName
          (CoNm (Free (String.append "recv_" (string_of_bool (negb i))))),
        (TChannel (SDual (SFwd (SRecv (negb i))))))
      CTX.empty))
    |-p recv_args (String.append "recv_" (string_of_bool i))
      ("err2" :: "out" :: nil)
      (transformProcR (abp_recv_procR i)).
Proof.
  apply TypPrefixInput with (s:=SFwd (SRecv i))
      (L:="recv_true" :: "recv_false" :: nil);
    [ constructor; [apply ctx_add_wf_dual_names | x_in_G];
        [destruct i; x_fresh_for_ctx | ctx_wf]
      | free_vals_in_ctx |].
  intros G' rho t xc H_xc_nin Htrans G'def; compute; subst G'.
  inversion Htrans; subst.
  (* clean up context *)
  apply ctx_equal_preserves_typed with (G1:=
      (CTX.add (ValVariable (Var (Free xc)), TChannel (SRecv i))
      (CTX.add (ValName (Nm (Free ("recv_" ++ (string_of_bool i)))),
        TChannel (SFwd (SRecv i)))
      (CTX.add (ValName (CoNm (Free ("recv_" ++ (string_of_bool i)))),
        TChannel (SDual (SFwd (SRecv i))))
      (CTX.add (ValName (CoNm (Free ("recv_" ++ (string_of_bool (negb i))))),
        TChannel (SDual (SFwd (SRecv (negb i)))))
      CTX.empty)))));
    [|apply ctx_add_1; [reflexivity|];
      symmetry;
      apply ctx_replace_nothing_eq_stronger;
      [x_in_G|reflexivity]].
  (* main event *)
  apply TypPrefixInput with (s:=SRecv i)
      (L:=xc :: "recv_true" :: "recv_false" :: nil);
    [constructor; [destruct i; ctx_wf | x_in_G]
      | free_vals_in_ctx |].
  intros G' rho t' xerr2 H_xerr2_nin Htrans1 G'def; compute; subst G'.
  inversion Htrans1; subst.
  Case "Htrans1 = TRRecvA".
    (* clean up context *)
    apply ctx_equal_preserves_typed with (G1:=
        (CTX.add (ValVariable (Var (Free xerr2)),
          TChannel (SDual (SNack r k t (token_of_bool (negb i)))))
        (CTX.add (ValVariable (Var (Free xc)),
          TChannel (SRecv1 i (SNack r k t (token_of_bool (negb i))) t))
        (CTX.add (ValName (Nm (Free ("recv_" ++ (string_of_bool i)))),
          TChannel (SFwd (SRecv i)))
        (CTX.add (ValName (CoNm (Free ("recv_" ++ (string_of_bool i)))),
          TChannel (SDual (SFwd (SRecv i))))
        (CTX.add (ValName (CoNm (Free ("recv_" ++ (string_of_bool (negb i))))),
          TChannel (SDual (SFwd (SRecv (negb i)))))
        CTX.empty))))));
      [|unfold ctx_replace;
        apply ctx_add_1;
        [reflexivity|];
        symmetry;
        rewrite -> CTXProperties.remove_add;
        [reflexivity|x_nin_G]].
    (* main event *)
    apply TypPrefixInput with
        (s:=SRecv1 i (SNack r k t (token_of_bool (negb i))) t)
        (L:=xerr2 :: xc :: "recv_true" :: "recv_false" :: nil);
      [constructor; [destruct i; ctx_wf | x_in_G]
        | free_vals_in_ctx |].
    intros G' rho t' xout H_xout_nin Htrans2 G'def; compute; subst G'.
    inversion Htrans2; subst.
    (* clean up context *)
    apply ctx_equal_preserves_typed with (G1:=
        (CTX.add (ValVariable (Var (Free xout)), TChannel (SDual (SToks t)))
        (CTX.add (ValVariable (Var (Free xc)), TChannel SEpsilon)
        (CTX.add (ValVariable (Var (Free xerr2)),
          TChannel (SDual (SNack r k t (token_of_bool (negb i)))))
        (CTX.add (ValName (Nm (Free ("recv_" ++ (string_of_bool i)))),
          TChannel (SFwd (SRecv i)))
        (CTX.add (ValName (CoNm (Free ("recv_" ++ (string_of_bool i)))),
          TChannel (SDual (SFwd (SRecv i))))
        (CTX.add (ValName (CoNm (Free ("recv_" ++ (string_of_bool (negb i))))),
          TChannel (SDual (SFwd (SRecv (negb i)))))
        CTX.empty)))))));
      [|unfold ctx_replace;
        apply ctx_add_1;
        [reflexivity|];
        apply ctx_add_1;
        [reflexivity|];
        symmetry;
        rewrite <- CTXProperties.add_add with (s:=
          (CTX.add (ValName (Nm (Free ("recv_" ++ (string_of_bool i)))),
            TChannel (SFwd (SRecv i)))
          (CTX.add (ValName (CoNm (Free ("recv_" ++ (string_of_bool i)))),
            TChannel (SDual (SFwd (SRecv i))))
          (CTX.add (ValName (CoNm (Free ("recv_" ++
              (string_of_bool (negb i))))),
            TChannel (SDual (SFwd (SRecv (negb i)))))
          CTX.empty))));
        rewrite -> CTXProperties.remove_add;
        [reflexivity|x_nin_G]].
    apply TypSum; [|apply TypSum].
    apply abp_recvA_Nack_procR_typing; assumption.
    apply abp_recvB_Nack_procR_typing; assumption.
    apply abp_recvC_Nack_procR_typing; assumption.

  Case "Htrans1 = TRRecvB".
    (* clean up context *)
    apply ctx_equal_preserves_typed with (G1:=
        (CTX.add (ValVariable (Var (Free xerr2)),
          TChannel (SDual (SAck t (token_of_bool (negb i)))))
        (CTX.add (ValVariable (Var (Free xc)),
          TChannel (SRecv1 i (SAck t (token_of_bool (negb i))) t))
        (CTX.add (ValName (Nm (Free ("recv_" ++ (string_of_bool i)))),
          TChannel (SFwd (SRecv i)))
        (CTX.add (ValName (CoNm (Free ("recv_" ++ (string_of_bool i)))),
          TChannel (SDual (SFwd (SRecv i))))
        (CTX.add (ValName (CoNm (Free ("recv_" ++ (string_of_bool (negb i))))),
          TChannel (SDual (SFwd (SRecv (negb i)))))
        CTX.empty))))));
      [|unfold ctx_replace;
        apply ctx_add_1;
        [reflexivity|];
        symmetry;
        rewrite -> CTXProperties.remove_add;
        [reflexivity|x_nin_G]].
    (* main event *)
    apply TypPrefixInput with
        (s:=SRecv1 i (SAck t (token_of_bool (negb i))) t)
        (L:=xerr2 :: xc :: "recv_true" :: "recv_false" :: nil);
      [constructor; [destruct i; ctx_wf | x_in_G]
        | free_vals_in_ctx |].
    intros G' rho t' xout H_xout_nin Htrans2 G'def; compute; subst G'.
    inversion Htrans2; subst.
    (* clean up context *)
    apply ctx_equal_preserves_typed with (G1:=
        (CTX.add (ValVariable (Var (Free xout)), TChannel (SDual (SToks t)))
        (CTX.add (ValVariable (Var (Free xc)), TChannel SEpsilon)
        (CTX.add (ValVariable (Var (Free xerr2)),
          TChannel (SDual (SAck t (token_of_bool (negb i)))))
        (CTX.add (ValName (Nm (Free ("recv_" ++ (string_of_bool i)))),
          TChannel (SFwd (SRecv i)))
        (CTX.add (ValName (CoNm (Free ("recv_" ++ (string_of_bool i)))),
          TChannel (SDual (SFwd (SRecv i))))
        (CTX.add (ValName (CoNm (Free ("recv_" ++ (string_of_bool (negb i))))),
          TChannel (SDual (SFwd (SRecv (negb i)))))
        CTX.empty)))))));
      [|unfold ctx_replace;
        apply ctx_add_1;
        [reflexivity|];
        apply ctx_add_1;
        [reflexivity|];
        symmetry;
        rewrite <- CTXProperties.add_add with (s:=
          (CTX.add (ValName (Nm (Free ("recv_" ++ (string_of_bool i)))),
            TChannel (SFwd (SRecv i)))
          (CTX.add (ValName (CoNm (Free ("recv_" ++ (string_of_bool i)))),
            TChannel (SDual (SFwd (SRecv i))))
          (CTX.add (ValName (CoNm (Free ("recv_" ++
              (string_of_bool (negb i))))),
            TChannel (SDual (SFwd (SRecv (negb i)))))
          CTX.empty))));
        rewrite -> CTXProperties.remove_add;
        [reflexivity|x_nin_G]].
    apply TypSum; [|apply TypSum].
    apply abp_recvA_Ack_procR_typing; assumption.
    apply abp_recvB_Ack_procR_typing; assumption.
    apply abp_recvC_Ack_procR_typing; assumption.
Qed.


Require Import ResultRename.


Lemma abp_recv_typing r :
  (CTX.add(ValName (CoNm (Free "err2")),
      TChannel (SDual (SAck r (token_of_bool true))))
    (CTX.add (ValName (Nm (Free "out")), TChannel (SDual (SToks r)))
    CTX.empty))
  |-p abp_recv (ValName (CoNm (Free "err2"))) (ValName (Nm (Free "out"))).
Proof.
  compute.
  apply TypNew with (s:=SFwd (SRecv false))
    (L:="recv_false" :: "recv_true" :: "err2" :: "out" :: nil).
  intros recvF G' H_recvF_nin G'def; compute; subst.
  apply TypNew with (s:=SFwd (SRecv true))
    (L:=recvF :: "recv_false" :: "recv_true" :: "err2" :: "out" :: nil).
  intros recvT G' H_recvT_nin G'def; compute; subst.
  apply TypPar with (GL:=
      (CTX.add(ValName (Nm (Free recvT)), TChannel (SFwd (SRecv true)))
        (CTX.add(ValName (CoNm (Free recvT)),
          TChannel (SDual (SFwd (SRecv true))))
        (CTX.add(ValName (Nm (Free recvF)), TChannel (SFwd (SRecv false)))
        (CTX.add(ValName (CoNm (Free recvF)),
          TChannel (SDual (SFwd (SRecv false))))
        CTX.empty)))))
    (GR:=
      (CTX.add(ValName (CoNm (Free recvF)),
        TChannel (SDual (SFwd (SRecv false))))
      (CTX.add(ValName (CoNm (Free "err2")),
        TChannel (SDual (SAck r (token_of_bool true))))
      (CTX.add (ValName (Nm (Free "out")), TChannel (SDual (SToks r)))
      CTX.empty)))).

  (* paritition ok *)
  Case "G |-part GL (+) GR".
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

  (* recv processes ok *)
  eapply TypPar.

  (* use Focus 2 here so that we don't instantiate the context too early
     which breaks the tactic. *)
  Focus 2.
  (* abp_recv_procR false *)
  Case "GL'|-p abp_recv_procR false".
    pose (typed_rename _ _ (abp_recv_procR_typing false) "recv_false" recvF)
      as Hu.
    simpl in Hu.
    assert (~ In recvF
      (free_ids_context
        (CTX.add(ValName (Nm (Free "recv_false")),
            TChannel (SFwd (SRecv false)))
          (CTX.add(ValName (CoNm (Free "recv_false")),
            TChannel (SDual (SFwd (SRecv false))))
          (CTX.add(ValName (CoNm (Free "recv_true")),
            TChannel (SDual (SFwd (SRecv true))))
          CTX.empty))))).

    SCase "~In recvF (free_ids_context GL')".
      rewrite free_ids_context_iff;
        red;
        intros;
        repeat destruct H;
        x_in_G;
        inversion H;
        subst;
        simpl in H0;
        contradict H_recvF_nin;
        destruct H0;
        try solve [contradiction];
        subst;
        discriminate_w_list.

    pose (typed_rename _ _ (Hu H) "recv_true" recvT) as Hu'.
    unfold Hu in Hu'.
    simpl in Hu'.
    replace ((if string_dec recvF "recv_true" then Free recvT else Free recvF))
        with (Free recvF) in *;
      [apply Hu'
        | clear Hu Hu'; destruct (string_dec recvF "recv_true");
          [subst; contradict H_recvF_nin; intuition
            | reflexivity
          ]
      ].

    SCase "~In recvT (free_ids_context GL')".
      rewrite free_ids_context_iff;
        red;
        intros;
        repeat destruct H0;
        repeat (rewrite freeid_rename_ctx_add in H0; [|x_nin_G]);
        rewrite freeid_rename_ctx_empty in H0;
        x_in_G;
        inversion H0;
        subst;
        simpl in H1;
        x_in_G;
        try solve [contradiction];
        contradict H_recvT_nin;
        subst;
        discriminate_w_list.

  (* partition ok *)
  Case "GL |-part GL' (+) GR'".
    instantiate (1:=
      (CTX.add(ValName (Nm (Free recvT)), TChannel (SFwd (SRecv true)))
        (CTX.add(ValName (CoNm (Free recvT)),
          TChannel (SDual (SFwd (SRecv true))))
        (CTX.add(ValName (CoNm (Free recvF)),
          TChannel (SDual (SFwd (SRecv false))))
        CTX.empty)))).
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
        left.
        assert (CTX.Equal (freeid_rename_ctx "recv_true" recvT
          (freeid_rename_ctx "recv_false" recvF
            (CTX.add(ValName (Nm (Free "recv_false")),
              TChannel (SFwd (SRecv false)))
            (CTX.add(ValName (CoNm (Free "recv_false")),
              TChannel (SDual (SFwd (SRecv false))))
            (CTX.add(ValName (CoNm (Free "recv_true")),
              TChannel (SDual (SFwd (SRecv true))))
             CTX.empty)))))
          (freeid_rename_ctx "recv_true" recvT
            (CTX.add(ValName (Nm (Free recvF)), TChannel (SFwd (SRecv false)))
              (CTX.add(ValName (CoNm (Free recvF)),
                TChannel (SDual (SFwd (SRecv false))))
              (CTX.add(ValName (CoNm (Free "recv_true")),
                TChannel (SDual (SFwd (SRecv true))))
              CTX.empty)))));
          [apply freeid_rename_ctx_well_defined;
            repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
            rewrite freeid_rename_ctx_empty;
            simpl;
            reflexivity|].
        rewrite H0.
        repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
          rewrite freeid_rename_ctx_empty;
          simpl.
       replace
           ((if string_dec recvF "recv_true" then Free recvT else Free recvF))
           with (Free recvF) in *;
         [x_in_G
           | destruct (string_dec recvF "recv_true");
             [subst; contradict H_recvT_nin; intuition
               | reflexivity
             ]
         ].

      SSCase "forall (u,rho), CTX.In (u,rho) (CTX.union GL GR)".
        assert (CTX.Equal (freeid_rename_ctx "recv_true" recvT
          (freeid_rename_ctx "recv_false" recvF
            (CTX.add(ValName (Nm (Free "recv_false")),
              TChannel (SFwd (SRecv false)))
            (CTX.add(ValName (CoNm (Free "recv_false")),
              TChannel (SDual (SFwd (SRecv false))))
            (CTX.add(ValName (CoNm (Free "recv_true")),
              TChannel (SDual (SFwd (SRecv true))))
            CTX.empty)))))
          (freeid_rename_ctx "recv_true" recvT
            (CTX.add(ValName (Nm (Free recvF)), TChannel (SFwd (SRecv false)))
            (CTX.add(ValName (CoNm (Free recvF)),
              TChannel (SDual (SFwd (SRecv false))))
            (CTX.add(ValName (CoNm (Free "recv_true")),
              TChannel (SDual (SFwd (SRecv true))))
            CTX.empty)))));
          [apply freeid_rename_ctx_well_defined;
            repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
            rewrite freeid_rename_ctx_empty;
            simpl;
            reflexivity|].
        rewrite H in H0.
        repeat (rewrite freeid_rename_ctx_add in H0; [|x_nin_G]);
          rewrite freeid_rename_ctx_empty in H0;
          simpl in H0.
        replace
            ((if string_dec recvF "recv_true" then Free recvT else Free recvF))
            with (Free recvF) in *;
          [x_in_G
            | destruct (string_dec recvF "recv_true");
              [subst; contradict H_recvT_nin; intuition
                | reflexivity
              ]
          ].

    SCase "G'|-wf".
      ctx_wf.

    SCase "forall u,rho, ~In (u,rho) GL \/ ~In (u,rho) GR \/ (|-st rho)".
      intros u rho.
      assert (CTX.Equal (freeid_rename_ctx "recv_true" recvT
        (freeid_rename_ctx "recv_false" recvF
          (CTX.add(ValName (Nm (Free "recv_false")),
            TChannel (SFwd (SRecv false)))
          (CTX.add(ValName (CoNm (Free "recv_false")),
            TChannel (SDual (SFwd (SRecv false))))
          (CTX.add(ValName (CoNm (Free "recv_true")),
            TChannel (SDual (SFwd (SRecv true))))
          CTX.empty)))))
        (freeid_rename_ctx "recv_true" recvT
          (CTX.add(ValName (Nm (Free recvF)), TChannel (SFwd (SRecv false)))
          (CTX.add(ValName (CoNm (Free recvF)),
            TChannel (SDual (SFwd (SRecv false))))
          (CTX.add(ValName (CoNm (Free "recv_true")),
            TChannel (SDual (SFwd (SRecv true))))
          CTX.empty)))));
        [apply freeid_rename_ctx_well_defined;
          repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
          rewrite freeid_rename_ctx_empty;
          simpl;
          reflexivity|].
      rewrite H.
      repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
        rewrite freeid_rename_ctx_empty;
        simpl.
      replace
          ((if string_dec recvF "recv_true" then Free recvT else Free recvF))
          with (Free recvF) in *;
        [| destruct (string_dec recvF "recv_true");
          [subst; contradict H_recvT_nin; intuition
            | reflexivity
          ]
        ].
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

  eapply TypPar;
    [(* partition ok *) apply partition_empty; ctx_wf
      |(* abp_recv_procR true *)
      | apply TypZero; ctx_wf].

  (* abp_recv_procR true *)
  Case "GL''|-p abp_recv_procR true".
    pose (typed_rename _ _ (abp_recv_procR_typing true) "recv_true" recvT)
      as Hu.
    simpl in Hu.
    assert (~ In recvT
      (free_ids_context
        (CTX.add(ValName (Nm (Free "recv_true")),
            TChannel (SFwd (SRecv true)))
          (CTX.add(ValName (CoNm (Free "recv_true")),
            TChannel (SDual (SFwd (SRecv true))))
          (CTX.add(ValName (CoNm (Free "recv_false")),
            TChannel (SDual (SFwd (SRecv false))))
          CTX.empty))))).

    SCase "~In recvT (free_ids_context GL'')".
      rewrite free_ids_context_iff;
        red;
        intros;
        repeat destruct H;
        x_in_G;
        inversion H;
        subst;
        simpl in H0;
        contradict H_recvT_nin;
        destruct H0;
        try solve [contradiction];
        subst;
        discriminate_w_list.

    pose (typed_rename _ _ (Hu H) "recv_false" recvF) as Hu'.
    unfold Hu in Hu'.
    simpl in Hu'.
    replace
      ((if string_dec recvT "recv_false" then Free recvF else Free recvT))
        with (Free recvT) in *;
      [(*apply Hu'*)
        | clear Hu Hu'; destruct (string_dec recvT "recv_false");
          [subst; contradict H_recvT_nin; intuition
            | reflexivity
          ]
      ].
    assert (CTX.Equal (freeid_rename_ctx "recv_false" recvF
      (freeid_rename_ctx "recv_true" recvT
        (CTX.add(ValName (Nm (Free "recv_true")), TChannel (SFwd (SRecv true)))
        (CTX.add(ValName (CoNm (Free "recv_true")),
          TChannel (SDual (SFwd (SRecv true))))
        (CTX.add(ValName (CoNm (Free "recv_false")),
          TChannel (SDual (SFwd (SRecv false))))
        CTX.empty)))))
      (freeid_rename_ctx "recv_false" recvF
        (CTX.add(ValName (Nm (Free recvT)), TChannel (SFwd (SRecv true)))
        (CTX.add(ValName (CoNm (Free recvT)),
          TChannel (SDual (SFwd (SRecv true))))
        (CTX.add(ValName (CoNm (Free "recv_false")),
          TChannel (SDual (SFwd (SRecv false))))
        CTX.empty)))));
      [apply freeid_rename_ctx_well_defined;
        repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
        rewrite freeid_rename_ctx_empty;
        simpl;
        reflexivity|].

    assert (~ In recvF
      (free_ids_context
        (freeid_rename_ctx "recv_true" recvT
        (CTX.add(ValName (Nm (Free "recv_true")),
          TChannel (SFwd (SRecv true)))
        (CTX.add(ValName (CoNm (Free "recv_true")),
          TChannel (SDual (SFwd (SRecv true))))
        (CTX.add(ValName (CoNm (Free "recv_false")),
          TChannel (SDual (SFwd (SRecv false))))
        CTX.empty)))))).
    SCase "~In recvF (free_ids_context GL'')".
      rewrite free_ids_context_iff;
        red;
        intros;
        repeat destruct H1;
        repeat (rewrite freeid_rename_ctx_add in H1; [|x_nin_G]);
        rewrite freeid_rename_ctx_empty in H1;
        x_in_G;
        inversion H1; subst;
        simpl in H2;
        x_in_G;
        try solve [contradiction];
        contradict H_recvT_nin;
        try solve [subst; discriminate_w_list];
        contradict H_recvF_nin; 
        subst; discriminate_w_list.
    unfold token_value_of_bool in Hu'; unfold token_of_bool in Hu'.
    simpl in Hu'.
    eapply ctx_equal_preserves_typed.
    apply Hu'.

    assumption.
    rewrite H0.
    repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
      rewrite freeid_rename_ctx_empty;
      simpl;
      replace
          ((if string_dec recvT "recv_false" then Free recvF else Free recvT))
          with (Free recvT) in *;
        [| destruct (string_dec recvT "recv_false");
           [subst; contradict H_recvT_nin; intuition
             | reflexivity
           ]
        ];
      reflexivity.

  (* bootstrap ok *)
  Case "GR |-p abp_revc_bootstrap".
    apply TypNew with (s:=SRecv false)
      (L:=recvT :: recvF :: "recv_false" :: "recv_true" :: "err2" :: "out"
        :: nil).
    intros d G' H_d_nin G'def; compute; subst.
    (* /recvF!d; rest *)
    eapply TypPrefixOutput with (s:=SDual (SFwd (SRecv false)))
        (rho:=TChannel (SRecv false)) (t:=SDual (SFwd (SRecv false)));
      [apply trdual_w_mdual_involution; constructor
        | left; discriminate
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity
        | ].
    (* /d!/err2; rest *)
    eapply TypPrefixOutput with (s:=SDual (SRecv false))
        (rho:=TChannel (SDual (SAck r (token_of_bool true))))
        (t:=SDual (SRecv1 false (SAck r (token_of_bool true)) r));
      [apply trdual_w_mdual_involution; constructor; reflexivity
        | left; contradict H_d_nin; inversion H_d_nin; subst;
          discriminate_w_list
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity
        | ].
    (* /d!out; rest *)
    eapply TypPrefixOutput with
        (s:=SDual (SRecv1 false (SAck r (token_of_bool true)) r))
        (rho:=TChannel (SDual (SToks r)))
        (t:=SDual SEpsilon);
      [apply trdual_w_mdual_involution; constructor; reflexivity
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
