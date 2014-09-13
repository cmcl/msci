Require Export Arith.EqNat.
Require Export Arith.Lt.
Require Export Arith.Compare_dec.
Require Export List.
Require Import String.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import Process.
Require Import List.
Require Import PrettyPrinter.
Require Import TypeAssignmentPoly.
Require Import ResultBasics.
Require Import ExampleCommon.
Require Import ExampleRecursion.
Require Import ExampleABPSendBase.
Require Import ExampleABPSendANack.
Require Import ExampleABPSendBNack.
Require Import ExampleABPSendCNack.
Require Import ExampleABPSendAAck.
Require Import ExampleABPSendBAck.
Require Import ExampleABPSendCAck.


Lemma abp_send_procR_typing :
  forall i,
    CTX.add(ValName (Nm (Free ((String.append "send_" (string_of_bool i))))),
        (TChannel (SFwd (SSend i))))
    (CTX.add(ValName (CoNm (Free (String.append "send_" (string_of_bool i)))),
        (TChannel (SDual (SFwd (SSend i)))))
    (CTX.add(ValName (CoNm (Free (String.append "send_" (string_of_bool (negb i))))),
        (TChannel (SDual (SFwd (SSend (negb i))))))
    CTX.empty))
    |-p recv_args (String.append "send_" (string_of_bool i)) ("x" :: "in" :: "err1" :: nil) (transformProcR (abp_send_procR i)).
Proof.
  intros i.
  unfold string_of_bool; unfold negb.
  apply TypPrefixInput with (s:=SFwd (SSend i))
      (L:="send_true" :: "send_false" :: nil);
    [| free_vals_in_ctx |].
  constructor; [apply ctx_add_wf_dual_names | x_in_G];
    [destruct i; x_fresh_for_ctx | ctx_wf].
  intros G' rho t xc H_xc_nin Htrans G'def; compute; subst G'.
  inversion Htrans; subst.
  (* clean up context *)
  apply ctx_equal_preserves_typed with (G1:=
      (CTX.add (ValVariable (Var (Free xc)), (TChannel (SSend i)))
      (CTX.add (ValName (Nm (Free ("send_" ++ (if i then "true" else "false")))),
        TChannel (SFwd (SSend i)))
      (CTX.add (ValName (CoNm (Free ("send_" ++ (if i then "true" else "false")))),
        TChannel (SDual (SFwd (SSend i))))
      (CTX.add (ValName (CoNm (Free
        ("send_" ++ (if if i then false else true then "true" else "false")))),
        TChannel (SDual (SFwd (SSend (negb i)))))
      CTX.empty)))));
    [|apply ctx_add_1; [reflexivity|];
      symmetry;
      apply ctx_replace_nothing_eq_stronger;
      [x_in_G|reflexivity]].
  (* main event *)
  apply TypPrefixInput with (s:=SSend i)
      (L:=xc :: "send_true" :: "send_false" :: nil);
    [constructor; [destruct i; ctx_wf | x_in_G]
      | free_vals_in_ctx |].
  intros G' rho t x H_x_nin Htrans1 G'def; compute; subst G'.
  inversion Htrans1; subst.
  (* clean up context *)
  apply ctx_equal_preserves_typed with (G1:=
      (CTX.add (ValVariable (Var (Free x)), (TSingleton k))
      (CTX.add (ValVariable (Var (Free xc)),
        (TChannel (SSend1 i r' (SNack r k r' (token_of_bool i)))))
      (CTX.add (ValName (Nm (Free ("send_" ++ (if i then "true" else "false")))),
        TChannel (SFwd (SSend i)))
      (CTX.add (ValName (CoNm (Free ("send_" ++ (if i then "true" else "false")))),
        TChannel (SDual (SFwd (SSend i))))
      (CTX.add (ValName (CoNm (Free
        ("send_" ++ (if if i then false else true then "true" else "false")))),
        TChannel (SDual (SFwd (SSend (negb i)))))
      CTX.empty))))));
    [| unfold ctx_replace;
      repeat (apply ctx_add_1; [reflexivity|]);
      rewrite -> CTXProperties.remove_add;
      x_nin_G;
      reflexivity].
  (* main event *)
  Case "SSend i --MInp TSingleton k--> SSend1 i r' (SNack r k r' (token_of_bool i))".
Focus 1.
    apply TypPrefixInput with (s:=SSend1 i r' (SNack r k r' (token_of_bool i)))
        (L:=x :: xc :: "send_true" :: "send_false" :: nil);
      [constructor; [destruct i; ctx_wf | x_in_G]
        | free_vals_in_ctx |].
    intros G' rho t xin H_xin_nin Htrans2 G'def; compute; subst G'.
    inversion Htrans2; subst.
    (* clean up context *)
    apply ctx_equal_preserves_typed with (G1:=
        (CTX.add (ValVariable (Var (Free xin)), (TChannel (SToks r')))
        (CTX.add (ValVariable (Var (Free xc)),
          (TChannel (SSend2 i (SNack r k r' (token_of_bool i)))))
        (CTX.add (ValVariable (Var (Free x)), (TSingleton k))
        (CTX.add (ValName (Nm (Free ("send_" ++ (if i then "true" else "false")))),
          TChannel (SFwd (SSend i)))
        (CTX.add (ValName (CoNm (Free ("send_" ++ (if i then "true" else "false")))),
          TChannel (SDual (SFwd (SSend i))))
        (CTX.add (ValName (CoNm (Free
          ("send_" ++ (if if i then false else true then "true" else "false")))),
          TChannel (SDual (SFwd (SSend (negb i)))))
        CTX.empty)))))));
      [| unfold ctx_replace;
        repeat (apply ctx_add_1; [reflexivity|]);
        rewrite <- CTXProperties.add_add with (s:=
          (CTX.add (ValName (Nm (Free ("send_" ++ (if i then "true" else "false")))),
            TChannel (SFwd (SSend i)))
          (CTX.add (ValName (CoNm (Free ("send_" ++ (if i then "true" else "false")))),
            TChannel (SDual (SFwd (SSend i))))
          (CTX.add (ValName (CoNm (Free
            ("send_" ++ (if if i then false else true then "true" else "false")))),
            TChannel (SDual (SFwd (SSend (negb i)))))
          CTX.empty))));
        rewrite -> CTXProperties.remove_add;
        [reflexivity | x_nin_G]].
    (* main event *)
    apply TypPrefixInput with (s:=SSend2 i (SNack r k r' (token_of_bool i)))
        (L:=xin :: x :: xc :: "send_true" :: "send_false" :: nil);
      [| free_vals_in_ctx |].
    constructor; [destruct i; ctx_wf; contradict H_x_nin; left; reflexivity | x_in_G].
    intros G' rho t xerr1 H_xerr1_nin Htrans3 G'def; compute; subst G'.
    inversion Htrans3; subst.
    (* context cleanup *)
    apply ctx_equal_preserves_typed with (G1:=
        (CTX.add (ValVariable (Var (Free xerr1)),
          (TChannel (SNack r k r' (token_of_bool i))))
        (CTX.add (ValVariable (Var (Free xc)),
          (TChannel (SEpsilon)))
        (CTX.add (ValVariable (Var (Free xin)), (TChannel (SToks r')))
        (CTX.add (ValVariable (Var (Free x)), (TSingleton k))
        (CTX.add (ValName (Nm (Free ("send_" ++ (if i then "true" else "false")))),
          TChannel (SFwd (SSend i)))
        (CTX.add (ValName (CoNm (Free ("send_" ++ (if i then "true" else "false")))),
          TChannel (SDual (SFwd (SSend i))))
        (CTX.add (ValName (CoNm (Free
          ("send_" ++ (if if i then false else true then "true" else "false")))),
          TChannel (SDual (SFwd (SSend (negb i)))))
        CTX.empty))))))));
      [| unfold ctx_replace;
        repeat (apply ctx_add_1; [reflexivity|]);
        rewrite <- CTXProperties.add_add with (s:=
          (CTX.add (ValVariable (Var (Free x)), (TSingleton k))
          (CTX.add (ValName (Nm (Free ("send_" ++ (if i then "true" else "false")))),
            TChannel (SFwd (SSend i)))
          (CTX.add (ValName (CoNm (Free ("send_" ++ (if i then "true" else "false")))),
            TChannel (SDual (SFwd (SSend i))))
          (CTX.add (ValName (CoNm (Free
            ("send_" ++ (if if i then false else true then "true" else "false")))),
            TChannel (SDual (SFwd (SSend (negb i)))))
          CTX.empty)))));
        rewrite -> CTXProperties.remove_add;
        [reflexivity | x_nin_G];
        contradict H_xin_nin; inversion H; right; left; reflexivity].
    apply TypSum; [|apply TypSum].
    apply abp_sendA_Nack_procR_typing; assumption.
    apply abp_sendB_Nack_procR_typing; assumption.
    apply abp_sendC_Nack_procR_typing; assumption.

  Case "SSend i --MInp TSingleton k--> SSend1 i r' (SAck r (token_of_bool negb i))".
    (* clean up context *)
    apply ctx_equal_preserves_typed with (G1:=
        (CTX.add (ValVariable (Var (Free x)), (TSingleton k))
        (CTX.add (ValVariable (Var (Free xc)),
          (TChannel (SSend1 i r' (SAck r (token_of_bool (negb i))))))
        (CTX.add (ValName (Nm (Free ("send_" ++ (if i then "true" else "false")))),
          TChannel (SFwd (SSend i)))
        (CTX.add (ValName (CoNm (Free ("send_" ++ (if i then "true" else "false")))),
          TChannel (SDual (SFwd (SSend i))))
        (CTX.add (ValName (CoNm (Free
          ("send_" ++ (if if i then false else true then "true" else "false")))),
          TChannel (SDual (SFwd (SSend (negb i)))))
        CTX.empty))))));
      [| unfold ctx_replace;
        repeat (apply ctx_add_1; [reflexivity|]);
        rewrite -> CTXProperties.remove_add;
        [reflexivity | x_nin_G]].
    apply TypPrefixInput with
        (s:=SSend1 i r' (SAck r (token_of_bool (negb i))))
        (L:=x :: xc :: "send_true" :: "send_false" :: nil);
      [constructor; [destruct i; ctx_wf | x_in_G]
        | free_vals_in_ctx |].
    intros G' rho t xin H_xin_nin Htrans2 G'def; compute; subst G'.
    inversion Htrans2; subst.
    (* clean up context *)
    apply ctx_equal_preserves_typed with (G1:=
        (CTX.add (ValVariable (Var (Free xin)), (TChannel (SToks r')))
        (CTX.add (ValVariable (Var (Free xc)),
          (TChannel (SSend2 i (SAck r (token_of_bool (negb i))))))
        (CTX.add (ValVariable (Var (Free x)), (TSingleton k))
        (CTX.add (ValName (Nm (Free ("send_" ++ (if i then "true" else "false")))),
          TChannel (SFwd (SSend i)))
        (CTX.add (ValName (CoNm (Free ("send_" ++ (if i then "true" else "false")))),
          TChannel (SDual (SFwd (SSend i))))
        (CTX.add (ValName (CoNm (Free
          ("send_" ++ (if if i then false else true then "true" else "false")))),
          TChannel (SDual (SFwd (SSend (negb i)))))
        CTX.empty)))))));
      [| unfold ctx_replace;
        repeat (apply ctx_add_1; [reflexivity|]);
        rewrite <- CTXProperties.add_add with (s:=
          (CTX.add (ValName (Nm (Free ("send_" ++ (if i then "true" else "false")))),
            TChannel (SFwd (SSend i)))
          (CTX.add (ValName (CoNm (Free ("send_" ++ (if i then "true" else "false")))),
            TChannel (SDual (SFwd (SSend i))))
          (CTX.add (ValName (CoNm (Free
            ("send_" ++ (if if i then false else true then "true" else "false")))),
            TChannel (SDual (SFwd (SSend (negb i)))))
          CTX.empty))));
        symmetry; rewrite -> CTXProperties.remove_add;
        [reflexivity | x_nin_G]].
    (* main event *)
    apply TypPrefixInput with (s:=SSend2 i (SAck r (token_of_bool (negb i))))
        (L:=xin :: x :: xc :: "send_true" :: "send_false" :: nil);
      [| free_vals_in_ctx |].
    constructor; [destruct i; ctx_wf; discriminate_w_list | x_in_G].
    intros G' rho t xerr1 H_xerr1_nin Htrans3 G'def; compute; subst G'.
    inversion Htrans3; subst.
    (* context cleanup *)
    apply ctx_equal_preserves_typed with (G1:=
        (CTX.add (ValVariable (Var (Free xerr1)),
          (TChannel (SAck r (token_of_bool (negb i)))))
        (CTX.add (ValVariable (Var (Free xc)), (TChannel (SEpsilon)))
        (CTX.add (ValVariable (Var (Free xin)), (TChannel (SToks r')))
        (CTX.add (ValVariable (Var (Free x)), (TSingleton k))
        (CTX.add (ValName (Nm (Free ("send_" ++ (if i then "true" else "false")))),
          TChannel (SFwd (SSend i)))
        (CTX.add (ValName (CoNm (Free ("send_" ++ (if i then "true" else "false")))),
          TChannel (SDual (SFwd (SSend i))))
        (CTX.add (ValName (CoNm (Free
          ("send_" ++ (if if i then false else true then "true" else "false")))),
          TChannel (SDual (SFwd (SSend (negb i)))))
        CTX.empty))))))));
      [| unfold ctx_replace;
        repeat (apply ctx_add_1; [reflexivity|]);
        rewrite <- CTXProperties.add_add with (s:=
          (CTX.add (ValVariable (Var (Free x)), (TSingleton k))
          (CTX.add (ValName (Nm (Free ("send_" ++ (if i then "true" else "false")))),
            TChannel (SFwd (SSend i)))
          (CTX.add (ValName (CoNm (Free ("send_" ++ (if i then "true" else "false")))),
            TChannel (SDual (SFwd (SSend i))))
          (CTX.add (ValName (CoNm (Free
            ("send_" ++ (if if i then false else true then "true" else "false")))),
            TChannel (SDual (SFwd (SSend (negb i)))))
          CTX.empty)))));
        rewrite -> CTXProperties.remove_add;
        [reflexivity | x_nin_G]; discriminate_w_list].
    apply TypSum; [|apply TypSum].
    apply abp_sendA_Ack_procR_typing; assumption.
    apply abp_sendB_Ack_procR_typing; assumption.
    apply abp_sendC_Ack_procR_typing; assumption.
Qed.


Require Import ResultRename.


Lemma abp_send_typing r :
  (CTX.add(ValName (Nm (Free "err1")),
      TChannel (SAck r (token_of_bool true)))
    (CTX.add (ValName (Nm (Free "in")), TChannel (SToks r))
    CTX.empty))
  |-p (ValName (Nm (Free "in"))) ? ;
    abp_send (ValVariable (Var (Bound 0))) (ValName (Nm (Free "in")))
      (ValName (Nm (Free "err1"))).
Proof.
  compute.
  apply TypPrefixInput with (s:=SToks r) (L:="err1" :: "in" ::nil);
    [constructor; [ctx_wf | x_in_G]
      | free_vals_in_ctx |].
  intros G' rho t x H_x_nin Htrans G'def; compute; subst G'.
  inversion Htrans; subst.
  (* clean up context *)
  apply ctx_equal_preserves_typed with (G1:=
  (CTX.add(ValVariable (Var (Free x)), TSingleton tok)
    (CTX.add(ValName (Nm (Free "in")), TChannel (SToks s'))
    (CTX.add(ValName (Nm (Free "err1")),
      TChannel (SAck r (token_of_bool true)))
    CTX.empty))));
    [|unfold ctx_replace;
      repeat (apply ctx_add_1; [reflexivity|]);
      symmetry;
      rewrite CTXProperties.add_add with (s:=CTX.empty);
      apply CTXProperties.remove_add;
      x_nin_G].
  apply TypNew with (s:=SFwd (SSend false))
    (L:=x :: "send_false" :: "send_true" :: "err1" :: "in" :: nil).
  intros sendF G' H_sendF_nin G'def; compute; subst.
  apply TypNew with (s:=SFwd (SSend true)) 
    (L:=sendF :: x :: "send_false" :: "send_true" :: "err1" :: "in" :: nil).
  intros sendT G' H_sendT_nin G'def; compute; subst.
  apply TypPar with (GL:=
      (CTX.add(ValName (Nm (Free sendT)), TChannel (SFwd (SSend true)))
        (CTX.add(ValName (CoNm (Free sendT)),
          TChannel (SDual (SFwd (SSend true))))
        (CTX.add(ValName (Nm (Free sendF)), TChannel (SFwd (SSend false)))
        (CTX.add(ValName (CoNm (Free sendF)),
          TChannel (SDual (SFwd (SSend false))))
        CTX.empty)))))
    (GR:=
      (CTX.add(ValName (CoNm (Free sendF)),
          TChannel (SDual (SFwd (SSend false))))
        (CTX.add(ValName (Nm (Free "err1")),
          TChannel (SAck r (token_of_bool true)))
        (CTX.add (ValName (Nm (Free "in")), TChannel (SToks s'))
        (CTX.add(ValVariable (Var (Free x)), TSingleton tok)
        CTX.empty))))).

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

  Focus 2.
  (* bootstrap ok *)
  Case "GR |-p abp_send_bootstrap".
    apply TypNew with (s:=SSend false)
      (L:=sendT :: sendF :: x :: "send_false" :: "send_true" :: "err1" :: "in"
      :: nil).
    intros d G' H_d_nin G'def; compute; subst.
    eapply TypPrefixOutput with (s:=SDual (SFwd (SSend false)))
        (rho:=TChannel (SSend false))
        (t:=SDual (SFwd (SSend false)));
      [apply trdual_w_mdual_involution; constructor; assumption
        | left; discriminate
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity | ].
    eapply TypPrefixOutput with
        (s:=SDual (SSend false))
        (rho:=TSingleton tok)
        (t:=SDual (SSend1 false s' (SAck r (token_of_bool true))));
      [apply trdual_w_mdual_involution; constructor; assumption
        | left; discriminate
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; ctx_wf; x_in_G
        | right; split; [reflexivity | constructor]
        | reflexivity | ].
    eapply TypPrefixOutput with
        (s:=SDual (SSend1 false s' (SAck r (token_of_bool true))))
        (rho:=TChannel (SToks s'))
        (t:=SDual (SSend2 false (SAck r (token_of_bool true))));
      [apply trdual_w_mdual_involution; constructor; assumption
        | left; discriminate
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity | ].
    eapply TypPrefixOutput with
        (s:=SDual (SSend2 false (SAck r (token_of_bool true))))
        (rho:=TChannel (SAck r (token_of_bool true)))
        (t:=SDual SEpsilon);
      [apply trdual_w_mdual_involution; constructor; assumption
        | left; discriminate
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | constructor; [ctx_wf; discriminate_w_list | x_in_G]
        | left; reflexivity
        | reflexivity | ].
    apply TypZero;
      ctx_wf.

  (* send processes ok *)
  eapply TypPar.

  (* use Focus 2 here so that we don't instantiate the context too early
     which breaks the tactic. *)
  Focus 2.
  (* abp_send_procR false *)
  Case "GL'|-p abp_send_procR false".
    pose (typed_rename _ _ (abp_send_procR_typing false) "send_false" sendF)
      as Hu.
    simpl in Hu.
    assert (~ In sendF
      (free_ids_context
        (CTX.add(ValName (Nm (Free "send_false")),
            TChannel (SFwd (SSend false)))
          (CTX.add(ValName (CoNm (Free "send_false")),
            TChannel (SDual (SFwd (SSend false))))
          (CTX.add(ValName (CoNm (Free "send_true")),
            TChannel (SDual (SFwd (SSend true))))
          CTX.empty))))) as Hf_nin.
    SCase "~In sendF (free_ids_context GL')".
      rewrite free_ids_context_iff;
        red;
        intros;
        repeat destruct H;
        x_in_G;
        inversion H;
        subst;
        simpl in H0;
        contradict H_sendF_nin;
        destruct H0;
        try solve [contradiction];
        subst;
        discriminate_w_list.
    pose (typed_rename _ _ (Hu Hf_nin) "send_true" sendT) as Hu'.
    unfold Hu in Hu'.
    simpl in Hu'.
    replace
      ((if string_dec sendF "send_true" then Free sendT else Free sendF))
        with (Free sendF) in *;
      [apply Hu'
        | clear Hu Hu'; destruct (string_dec sendF "send_true");
          [subst; contradict H_sendT_nin; intuition
            | reflexivity
          ]
      ].

    SCase "~In sendT (free_ids_context GL')".
      rewrite free_ids_context_iff;
        red;
        intros;
        repeat destruct H;
        repeat (rewrite freeid_rename_ctx_add in H; [|x_nin_G]);
        rewrite freeid_rename_ctx_empty in H;
        simpl in H;
        x_in_G;
        inversion H;
        subst;
        simpl in H;
        contradict H_sendT_nin;
        destruct H0;
        try solve [contradiction];
        subst;
        discriminate_w_list.

  (* use Focus 2 here so that we don't instantiate the context too early
     which breaks the tactic. *)
  Focus 2.
  eapply TypPar;
    [apply partition_empty (* partition ok *)
      |(* abp_send_procR true *)
      |apply TypZero; ctx_wf].

  Focus 2.
  (* abp_send_procR true *)
  Case "GL''|-p abp_send_procR true".
    pose (typed_rename _ _ (abp_send_procR_typing true) "send_true" sendT)
      as Hu.
    simpl in Hu.
    assert (~ In sendT
      (free_ids_context
        (CTX.add(ValName (Nm (Free "send_true")),
            TChannel (SFwd (SSend true)))
          (CTX.add(ValName (CoNm (Free "send_true")),
            TChannel (SDual (SFwd (SSend true))))
          (CTX.add(ValName (CoNm (Free "send_false")),
            TChannel (SDual (SFwd (SSend false))))
          CTX.empty))))) as Ht_nin.
    SCase "~In sendT (free_ids_context GL')".
      rewrite free_ids_context_iff;
        red;
        intros;
        repeat destruct H;
        x_in_G;
        inversion H;
        subst;
        simpl in H0;
        contradict H_sendT_nin;
        destruct H0;
        try solve [contradiction];
        subst;
        discriminate_w_list.
    pose (typed_rename _ _ (Hu Ht_nin) "send_false" sendF) as Hu'.
    unfold Hu in Hu'.
    simpl in Hu'.
    replace
      ((if string_dec sendT "send_false" then Free sendF else Free sendT))
        with (Free sendT) in *;
      [apply Hu'
        | clear Hu Hu'; destruct (string_dec sendT "send_false");
          [subst; contradict H_sendF_nin; intuition
            | reflexivity
          ]
      ].

    SCase "~In sendF (free_ids_context GL'')".
      rewrite free_ids_context_iff;
        red;
        intros;
        repeat destruct H;
        repeat (rewrite freeid_rename_ctx_add in H; [|x_nin_G]);
        rewrite freeid_rename_ctx_empty in H;
        simpl in H;
        x_in_G;
        inversion H;
        subst;
        simpl in H0;
        destruct H0;
        try solve [contradiction];
        contradict H_sendT_nin;
        try solve [contradiction];
        subst;
        discriminate_w_list;
        contradict H_sendF_nin;
        discriminate_w_list.

  Focus 2.
  Case "GL''|-wf".
    apply typed_rename_wf;
      [apply typed_rename_wf; [ctx_wf|]|].
    SCase "~In sendT (free_ids_context GL')".
      rewrite free_ids_context_iff;
        red;
        intros;
        repeat destruct H;
        x_in_G;
        inversion H;
        subst;
        simpl in H0;
        contradict H_sendT_nin;
        destruct H0;
        try solve [contradiction];
        subst;
        discriminate_w_list.
    SCase "~In sendF (free_ids_context GL'')".
      rewrite free_ids_context_iff;
        red;
        intros;
        repeat destruct H;
        repeat (rewrite freeid_rename_ctx_add in H; [|x_nin_G]);
        rewrite freeid_rename_ctx_empty in H;
        simpl in H;
        x_in_G;
        inversion H;
        subst;
        simpl in H0;
        destruct H0;
        try solve [contradiction];
        contradict H_sendT_nin;
        try solve [contradiction];
        subst;
        discriminate_w_list;
        contradict H_sendF_nin;
        discriminate_w_list.

  (* partition ok *)
  Case "GL |-part GL' (+) GR'".
    assert (CTX.Equal
      (freeid_rename_ctx "send_false" sendF
        (CTX.add(ValName (Nm (Free sendT)),
          TChannel (SFwd (SSend true)))
        (CTX.add(ValName (CoNm (Free sendT)),
          TChannel (SDual (SFwd (SSend true))))
        (CTX.add(ValName (CoNm (Free "send_false")),
          TChannel (SDual (SFwd (SSend false))))
        CTX.empty))))
      (freeid_rename_ctx "send_false" sendF
        (freeid_rename_ctx "send_true" sendT
        (CTX.add(ValName (Nm (Free "send_true")),
          TChannel (SFwd (SSend true)))
        (CTX.add(ValName (CoNm (Free "send_true")),
          TChannel (SDual (SFwd (SSend true))))
        (CTX.add(ValName (CoNm (Free "send_false")),
          TChannel (SDual (SFwd (SSend false))))
        CTX.empty)))))) as HeqFT;
[apply freeid_rename_ctx_well_defined;
repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
rewrite freeid_rename_ctx_empty;
simpl;
replace
          ((if string_dec sendT "send_false" then Free sendF else Free sendT))
            with (Free sendT) in *;
          [| destruct (string_dec sendT "send_false");
            [subst; contradict H_sendT_nin; intuition
              | reflexivity]]; reflexivity|
].

    assert (CTX.Equal
      (freeid_rename_ctx "send_true" sendT
        (CTX.add(ValName (Nm (Free sendF)),
          TChannel (SFwd (SSend false)))
        (CTX.add(ValName (CoNm (Free sendF)),
          TChannel (SDual (SFwd (SSend false))))
        (CTX.add(ValName (CoNm (Free "send_true")),
          TChannel (SDual (SFwd (SSend true))))
        CTX.empty))))
      (freeid_rename_ctx "send_true" sendT
        (freeid_rename_ctx "send_false" sendF
        (CTX.add(ValName (Nm (Free "send_false")),
          TChannel (SFwd (SSend false)))
        (CTX.add(ValName (CoNm (Free "send_false")),
          TChannel (SDual (SFwd (SSend false))))
        (CTX.add(ValName (CoNm (Free "send_true")),
          TChannel (SDual (SFwd (SSend true))))
        CTX.empty)))))) as HeqTF;
[apply freeid_rename_ctx_well_defined;
repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
rewrite freeid_rename_ctx_empty;
simpl;
replace
          ((if string_dec sendF "send_true" then Free sendT else Free sendF))
            with (Free sendF) in *;
          [| destruct (string_dec sendF "send_true");
            [subst; contradict H_sendF_nin; intuition
              | reflexivity]];
reflexivity|].

    apply Partition; [|ctx_wf|].
    SCase "CTX.eq G' (CTX.union GL GR)".
      unfold CTX.eq; unfold CTX.Equal.
      induction a as (u,rho).
      split; intros H0.
      SSCase "forall (u,rho), CTX.In (u,rho) G'".
        x_in_G;
        inversion H; subst;
        rewrite CTXFacts.union_iff;
        try solve [left;
          rewrite <- HeqTF;
          repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
          rewrite freeid_rename_ctx_empty;
          simpl;
          replace
          ((if string_dec sendF "send_true" then Free sendT else Free sendF))
            with (Free sendF) in *;
          [| destruct (string_dec sendF "send_true");
            [subst; contradict H_sendF_nin; intuition
              | reflexivity]];
          x_in_G];
        try solve [right;
          rewrite <- HeqFT;
          repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
          rewrite freeid_rename_ctx_empty;
          simpl;
          replace
          ((if string_dec sendT "send_false" then Free sendF else Free sendT))
            with (Free sendT) in *;
          [| destruct (string_dec sendT "send_false");
            [subst; contradict H_sendT_nin; intuition
              | reflexivity]];
          x_in_G].

      SSCase "forall (u,rho), CTX.In (u,rho) (CTX.union GL GR)".
        rewrite <- HeqTF in H0;
        rewrite <- HeqFT in H0.
          repeat (rewrite freeid_rename_ctx_add in H0; [|x_nin_G]);
          rewrite freeid_rename_ctx_empty in H0;
          simpl in H0;
          replace
          ((if string_dec sendT "send_false" then Free sendF else Free sendT))
            with (Free sendT) in *;
          [| destruct (string_dec sendT "send_false");
            [subst; contradict H_sendT_nin; intuition
              | reflexivity]];
          repeat (rewrite freeid_rename_ctx_add in H0; [|x_nin_G]);
          rewrite freeid_rename_ctx_empty in H0;
          simpl in H0;
          replace
          ((if string_dec sendF "send_true" then Free sendT else Free sendF))
            with (Free sendF) in *;
          [| destruct (string_dec sendF "send_true");
            [subst; contradict H_sendF_nin; intuition
              | reflexivity]].
        x_in_G; assumption.

    SCase "forall u,rho, ~In (u,rho) GL \/ ~In (u,rho) GR \/ (|-st rho)".
      intros u rho.
      repeat (match goal with
        | |- context[freeid_rename_ctx "send_true" sendT _] =>
          rewrite <- HeqTF;
          repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
          rewrite freeid_rename_ctx_empty;
          simpl;
          replace
          ((if string_dec sendF "send_true" then Free sendT else Free sendF))
            with (Free sendF) in *;
          [| destruct (string_dec sendF "send_true");
            [subst; contradict H_sendF_nin; intuition
              | reflexivity]]
        | |- context[freeid_rename_ctx "send_false" sendF _] =>
          rewrite <- HeqFT;
          repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
          rewrite freeid_rename_ctx_empty;
          simpl;
          replace
          ((if string_dec sendT "send_false" then Free sendF else Free sendT))
            with (Free sendT) in *;
          [| destruct (string_dec sendT "send_false");
            [subst; contradict H_sendT_nin; intuition
              | reflexivity]]
        end).
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
Qed.
