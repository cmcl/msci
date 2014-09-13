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
Require Import ExampleABPSendBase.
Require Import ExampleABPSend.
Require Import ExampleABPRecvBase.
Require Import ExampleABPRecv.
Require Import ExampleABPLossyBase.
Require Import ExampleABPLossy.


(* ------------ abp definitions ------------------*)
(* proc abp(in, out) = (New err1, err2)
     ((in?x; send_false(x, in, err1))
     |lossy(co err1, err2)
     |recv_false(co err2, out))
*)
Definition abp inp out :=
  New (New (
    (inp? ; (abp_send (ValVariable (Var (Bound 0))) inp
      (ValName (Nm (Bound 2)))
    ))
    ||| (abp_lossy (ValName (CoNm (Bound 1))) (ValName (Nm (Bound 0))))
    ||| (abp_recv (ValName (CoNm (Bound 0))) out))).

Definition abp_test : proc :=
  abp (var_value_of_string "qin") (var_value_of_string "qout").

(*
Eval compute in abp_test.
*)


(* ------------------- lemmas ------------------ *)


(*
  proc send_i(x, in, err1)
  proc lossy(err1, err2)
  proc recv_i(err2, out)
*)

(* proc abp(in, out) = (New err1, err2)
     ((in?x; send_false(x, in, err1))
     |lossy(co err1, err2)
     |recv_false(co err2, out))
*)

Require Import ResultRename.

Lemma abp_typing : 
  forall s : session,
    (CTX.add (ValName (Nm (Free "in")), TChannel (SToks s))
      (CTX.add (ValName (Nm (Free "out")), TChannel (SDual (SToks s)))
      CTX.empty))
    |-p
      (abp (ValName (Nm (Free "in"))) (ValName (Nm (Free "out")))).
Proof.
  intros s.
  compute.
  apply TypNew with (s:=SAck s (token_of_bool true))
    (L:="err1" :: "err2" :: "in" :: "out" ::nil).
  intros xerr1 G' H_xerr1_nin G'def; compute; subst.
  apply TypNew with (s:=SAck s (token_of_bool true))
    (L:=xerr1 :: "err1" :: "err2" :: "in" :: "out" ::nil).
  intros xerr2 G' H_xerr2_nin G'def; compute; subst.
  eapply TypPar.

Focus 3.
  Case "G|-p abp_recv(/xerr2,out)".
    pose (typed_rename _ _ (abp_recv_typing s) "err2" xerr2) as Hu.
    apply Hu.
    SCase "~In xerr2 (free_ids_context G)".
      rewrite free_ids_context_iff;
        red;
        intros;
        repeat destruct H;
        x_in_G;
        inversion H;
        subst;
        simpl in H0;
        contradict H_xerr2_nin;
        destruct H0;
        try solve [contradiction];
        subst;
        discriminate_w_list.

Focus 2.
  eapply TypPar.

Focus 3.
  Case "G|-p abp_lossy (/err1, err2)".
    pose (typed_rename _ _ (abp_lossy_typing_corr true s) "err1" xerr1) as Hu.
    assert (~ In xerr1
      (free_ids_context
        (CTX.add (ValName (CoNm (Free "err1")),
            TChannel (SDual (SAck s (token_of_bool true))))
          (CTX.add (ValName (Nm (Free "err2")),
            TChannel (SAck s (token_of_bool true)))
          CTX.empty)))).

    SCase "~In xerr1 (free_ids_context G)".
      rewrite free_ids_context_iff;
        red;
        intros;
        repeat destruct H;
        x_in_G;
        inversion H;
        subst;
        simpl in H0;
        contradict H_xerr1_nin;
        destruct H0;
        try solve [contradiction];
        subst;
        discriminate_w_list.

    simpl in Hu.
    pose (typed_rename _ _ (Hu H) "err2" xerr2) as Hu'.
    unfold Hu in Hu'.
    simpl in Hu'.
    replace ((if string_dec xerr1 "err2" then Free xerr2 else Free xerr1))
        with (Free xerr1) in *;
      [apply Hu'
        | clear Hu Hu'; destruct (string_dec xerr1 "err2");
          [subst; contradict H_xerr1_nin; intuition
            | reflexivity
          ]
      ].

    SCase "~In xerr1 (free_ids_context G)".
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
        contradict H_xerr2_nin;
        subst;
        discriminate_w_list.

  Focus 3.
  Case "G|-p in?x; abp_send (x, in, err1)".
    pose (typed_rename _ _ (abp_send_typing s) "err1" xerr1) as Hu.
    apply Hu.
    SCase "~In xerr1 (free_ids_context G)".
      rewrite free_ids_context_iff;
        red;
        intros;
        repeat destruct H;
        x_in_G;
        contradict H_xerr1_nin;
        inversion H;
        subst;
        simpl in H0;
        destruct H0;
        subst;
        discriminate_w_list;
        try solve [contradiction].

  instantiate (1:=
      (CTX.add(ValName (Nm (Free xerr2)),
        TChannel (SAck s (token_of_bool true)))
      (CTX.add(ValName (Nm (Free "in")), TChannel (SToks s))
      (CTX.add(ValName (Nm (Free xerr1)),
        TChannel (SAck s (token_of_bool true)))
      (CTX.add(ValName (CoNm (Free xerr1)),
        TChannel (SDual (SAck s (token_of_bool true))))
      CTX.empty))))).

  assert (CTX.Equal
    (freeid_rename_ctx "err2" xerr2
      (CTX.add(ValName (Nm (Free "err2")),
        TChannel (SAck s (token_of_bool true)))
      (CTX.add(ValName (Nm (Free "out")),
        TChannel (SDual (SToks s)))
      CTX.empty)))
    (CTX.add(ValName (Nm (Free xerr2)),
        TChannel (SAck s (token_of_bool true)))
      (CTX.add(ValName (Nm (Free "out")),
        TChannel (SDual (SToks s)))
      CTX.empty))
    ) as Heq_xerr2.
  repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
    rewrite freeid_rename_ctx_empty;
    simpl;
    reflexivity.

  assert (CTX.Equal
    (freeid_rename_ctx "err2" xerr2
      (CTX.add(ValName (CoNm (Free "err2")),
        TChannel (SDual (SAck s (token_of_bool true))))
      (CTX.add(ValName (Nm (Free "out")),
        TChannel (SDual (SToks s)))
      CTX.empty)))
    (CTX.add(ValName (CoNm (Free xerr2)),
        TChannel (SDual (SAck s (token_of_bool true))))
      (CTX.add(ValName (Nm (Free "out")),
        TChannel (SDual (SToks s)))
      CTX.empty))
    ) as Heq_co_xerr2.
  repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
    rewrite freeid_rename_ctx_empty;
    simpl;
    reflexivity.

  Case "GL|-p GL' (+) GR'".
  apply Partition; [|ctx_wf|].
  SCase "CTX.eq G' (CTX.union GL GR)".
    unfold CTX.eq; unfold CTX.Equal.
    induction a as (u,rho).
    split; intros H0.
    SSCase "forall (u,rho), CTX.In (u,rho) G'".
      x_in_G;
      inversion H; subst;
      rewrite CTXFacts.union_iff;
      try solve [left; x_in_G];
      right;
      rewrite Heq_co_xerr2;
      x_in_G.

     SSCase "forall (u,rho), CTX.In (u,rho) (CTX.union GL GR)".
      rewrite Heq_co_xerr2 in H0;
        x_in_G.

    SCase "forall u,rho, ~In (u,rho) GL \/ ~In (u,rho) GR \/ (|-st rho)".
      intros u rho.
      match goal with
        | |- context[freeid_rename_ctx "err2" xerr2 _] =>
          rewrite Heq_co_xerr2
      end.
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
        end); try solve [
        (repeat
          match goal with
            | H : ~ In ?x ?L1 |- _ => contradict H
            | H: (?x, ?y) = (?x',?y') |- _ => inversion H; clear H
            | |- In ?x _ => red
            | |- ?x = ?x \/ _ => left; reflexivity
            | |- ?x = ?y \/ _ => right
          end)];
        contradict H_xerr2_nin;
        inversion H0;
        left;
        reflexivity.

  Case "GL'|-p GL'' (+) GR''".
  assert (CTX.Equal
    (freeid_rename_ctx "err1" xerr1
      (CTX.add(ValName (Nm (Free "err1")),
        TChannel (SAck s (token_of_bool true)))
      (CTX.add(ValName (Nm (Free "in")), TChannel (SToks s))
      CTX.empty)))
    (CTX.add(ValName (Nm (Free xerr1)),
        TChannel (SAck s (token_of_bool true)))
      (CTX.add(ValName (Nm (Free "in")), TChannel (SToks s))
      CTX.empty)))as Heq_xerr1.
  repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
    rewrite freeid_rename_ctx_empty;
    simpl;
    reflexivity.

  assert (CTX.Equal
    (freeid_rename_ctx "err2" xerr2
      (freeid_rename_ctx "err1" xerr1
      (CTX.add(ValName (CoNm (Free "err1")),
        TChannel (SDual (SAck s (token_of_bool true))))
      (CTX.add(ValName (Nm (Free "err2")),
        TChannel (SAck s (token_of_bool true)))
      CTX.empty))))
    (CTX.add(ValName (CoNm (Free xerr1)),
        TChannel (SDual (SAck s (token_of_bool true))))
      (CTX.add(ValName (Nm (Free xerr2)),
        TChannel (SAck s (token_of_bool true)))
      CTX.empty))) as Heq_xerr2_xerr1.

  assert (CTX.Equal
    (freeid_rename_ctx "err2" xerr2
      (CTX.add(ValName (CoNm (Free xerr1)),
        TChannel (SDual (SAck s (token_of_bool true))))
      (CTX.add(ValName (Nm (Free "err2")),
        TChannel (SAck s (token_of_bool true)))
      CTX.empty)))
    (CTX.add(ValName (CoNm (Free xerr1)),
        TChannel (SDual (SAck s (token_of_bool true))))
      (CTX.add(ValName (Nm (Free xerr2)),
        TChannel (SAck s (token_of_bool true)))
      CTX.empty))) as Heq_xerr2_xerr1_part.
  repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
    rewrite freeid_rename_ctx_empty;
    simpl;
    replace
          ((if string_dec xerr1 "err2" then Free xerr2 else Free xerr1))
            with (Free xerr1) in *;
          [| destruct (string_dec xerr1 "err2");
            [subst; contradict H_xerr1_nin; intuition
              | reflexivity]]; reflexivity.
  rewrite <- Heq_xerr2_xerr1_part;
    apply freeid_rename_ctx_well_defined;
    repeat (rewrite freeid_rename_ctx_add; [|x_nin_G]);
    rewrite freeid_rename_ctx_empty;
    simpl;
    reflexivity.

  apply Partition; [|ctx_wf|].
  SCase "CTX.eq G' (CTX.union GL GR)".
    unfold CTX.eq; unfold CTX.Equal.
    induction a as (u,rho).
    split; intros H0.
    SSCase "forall (u,rho), CTX.In (u,rho) G'".
      x_in_G;
      inversion H; subst;
      rewrite CTXFacts.union_iff;
      try solve [left; rewrite Heq_xerr1; x_in_G];
      right;
      rewrite Heq_xerr2_xerr1;
      x_in_G.

    SSCase "forall (u,rho), CTX.In (u,rho) (CTX.union GL GR)".
      rewrite Heq_xerr1 in H0;
      rewrite Heq_xerr2_xerr1 in H0;
      x_in_G.

    SCase "forall u,rho, ~In (u,rho) GL \/ ~In (u,rho) GR \/ (|-st rho)".
      intros u rho.
      repeat (match goal with
        | |- context[freeid_rename_ctx "err2" xerr2 _] =>
          rewrite Heq_xerr2_xerr1
        | |- context[freeid_rename_ctx "err1" xerr1 _] =>
          rewrite Heq_xerr1
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
        end); try solve [
        (repeat
          match goal with
            | H : ~ In ?x ?L1 |- _ => contradict H
            | H: (?x, ?y) = (?x',?y') |- _ => inversion H; clear H
            | |- In ?x _ => red
            | |- ?x = ?x \/ _ => left; reflexivity
            | |- ?x = ?y \/ _ => right
          end)];
        contradict H_xerr2_nin;
        inversion H0;
        left;
        reflexivity.
Qed.
