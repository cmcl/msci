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
Require Import ResultSubjectReduction.
Require Import ExampleCommon.
Require Import ExampleRecursion.


(* ------------ bifwd definitions ------------------*)
(* proc bifwd(right, left) = 
     (left?x.right!x.bifwd(left, right))
     +(right?x.left!x.bifwd(left, right)) in bifwd(left, right)
*)
Definition bifwd_procR :=
SumR
(InputR (var_value_of_string "left")
  (OutputR (var_value_of_string "right") (ValVariable (Var (Bound 0)))
          (RecurseR "bifwd" ((var_value_of_string "left")
            :: (var_value_of_string "right") :: nil))))
(InputR (var_value_of_string "right")
  (OutputR (var_value_of_string "left") (ValVariable (Var (Bound 0)))
          (RecurseR "bifwd" ((var_value_of_string "left")
            :: (var_value_of_string "right") :: nil)))).

Definition bifwd left right : proc :=
  let mkTriple := ("bifwd", "left" :: "right" :: nil, bifwd_procR) in
  createRecProc (mkTriple :: nil) "bifwd" (left :: right :: nil).

Definition bifwd_test : proc :=
  bifwd (var_value_of_string "qleft") (var_value_of_string "qright").

(*
Eval compute in bifwd_test.
     = New
         (Nm (Bound 0) ? ;
          (Var (Bound 0) ? ;
           (Var (Bound 1) ? ;
            (Var (Bound 1) ? ;
             (Var (Bound 1) ! Var (Bound 0);
              New
                (CoNm (Bound 5) ! Nm (Bound 0);
                 (CoNm (Bound 0) ! Var (Bound 3);
                  (CoNm (Bound 0) ! Var (Bound 2); Zero)))) +++
             Var (Bound 0) ? ;
             (Var (Bound 2) ! Var (Bound 0);
              New
                (CoNm (Bound 5) ! Nm (Bound 0);
                 (CoNm (Bound 0) ! Var (Bound 3);
                  (CoNm (Bound 0) ! Var (Bound 2); Zero))))))) ||| Zero
          ||| New
                (CoNm (Bound 1) ! Nm (Bound 0);
                 (CoNm (Bound 0) ! Var (Free "qleft");
                  (CoNm (Bound 0) ! Var (Free "qright"); Zero))))
     : proc
*)


Lemma bifwd_typing :
  forall s,
  CTX.add(ValName (Nm (Free "left")), TChannel s)
    (CTX.add(ValName (CoNm (Free "right")), TChannel (SDual s))
    CTX.empty)
  |-p bifwd (ValName (Nm (Free "left"))) (ValName (CoNm (Free "right"))).
Proof.
  intros s.
  compute.
  apply TypNew with (s:=SFwd SInOut) (L:="bifwd" :: "left" :: "right" :: nil).
  intros bifwd G' H_bifwd_nin G'def; compute; subst.

  eapply TypPar with
    (GL:=
      (CTX.add(ValName (Nm (Free bifwd)), TChannel (SFwd SInOut))
        (CTX.add(ValName (CoNm (Free bifwd)), TChannel (SDual (SFwd SInOut)))
        CTX.empty)))
    (GR:=
      (CTX.add(ValName (CoNm (Free bifwd)), TChannel (SDual (SFwd SInOut)))
        (CTX.add(ValName (Nm (Free "left")), TChannel s)
        (CTX.add(ValName (CoNm (Free "right")), TChannel (SDual s))
        CTX.empty)))).

  (* Partition ok *)
  Case "G |-part GL (+) GR".
  apply Partition; [| ctx_wf |].
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
  (* bootstrap *)
  Case "G|-p bootstrap".
    (* GL |-p New d; rest *)
    apply TypNew with (s:=SInOut)
      (L:=bifwd :: "bifwd" :: "left" :: "right" :: nil).
    intros d G' H_d_nin G'def; compute; subst.

    (* GL' |-p /bifwd!d; rest *)
    eapply TypPrefixOutput with (s:=SDual (SFwd SInOut))
        (rho:=TChannel SInOut)
        (t:=SDual (SFwd SInOut));
      [apply trdual_w_mdual_involution; constructor
        | left; discriminate
        | constructor; [ctx_wf | x_in_G]
        | constructor; [ctx_wf | x_in_G]
        | left; reflexivity
        | reflexivity
        |].
    (* GL' |-p /d!left; rest *)
    eapply TypPrefixOutput with (s:=SDual SInOut)
        (rho:=TChannel s)
        (t:=SDual (SInOut1 s));
      [apply trdual_w_mdual_involution; constructor
        | left; discriminate
        | constructor; [ctx_wf | x_in_G]
        | constructor; [ctx_wf | x_in_G]
        | left; reflexivity
        | reflexivity
        |].
    (* GL' |-p /d!right; rest *)
    eapply TypPrefixOutput with (s:=SDual (SInOut1 s))
        (rho:=TChannel (SDual s))
        (t:=SDual SEpsilon);
      [apply trdual_mdual_with_trInOut1
        | left; discriminate_w_list
        | constructor; [ctx_wf | x_in_G]
        | constructor; [ctx_wf | x_in_G]
        | left; reflexivity
        | reflexivity
        |].
    (* GL' |-p Zero *)
    apply TypZero;
      ctx_wf.

  (* GR |-p rest ||| Zero *)
  eapply TypPar;
    [apply partition_empty; ctx_wf
      | | apply TypZero; ctx_wf].

  (* GR |-p bifwd ? d ; rest *)
  Case "GR |-p bifwd?d; rest".
    (* GR |-p bifwd ? d ; rest *)
    apply TypPrefixInput with (s:=SFwd SInOut)
        (L:=bifwd :: "bifwd" :: "left" :: "right" :: nil);
      [constructor; [ctx_wf | x_in_G]
        | free_vals_in_ctx |].
    intros G' rho t d H_d_nin Htrans G'def; compute; subst G'.
    inversion Htrans; subst; clear Htrans.
    (* GR' |-p d ? left ; rest *)
    apply TypPrefixInput with (s:=SInOut)
        (L:=d :: bifwd :: "bifwd" :: "left" :: "right" :: nil);
      [constructor; [ctx_wf | x_in_G]
        | free_vals_in_ctx |].
    intros G' rho t left H_left_nin Htrans G'def; compute; subst G'.
    inversion Htrans; subst; clear Htrans.
    (* GR' |-p d ? right ; rest *)
    apply TypPrefixInput with (s:=SInOut1 s0)
        (L:=left :: d :: bifwd :: "bifwd" :: "left" :: "right" :: nil);
      [constructor; [ctx_wf | x_in_G]
        | free_vals_in_ctx |].
    intros G' rho t right H_right_nin Htrans G'def; compute; subst G'.
    inversion Htrans; subst; clear Htrans.

    (* GR' |-p bifwd_left +++ bifwd_right *)
    apply TypSum.
    SCase "GR' |-p left ? x ; rest ".
      (* GR' |-p left ? x ; rest *)
      apply TypPrefixInput with (s:=s0)
          (L:=right :: left :: d :: bifwd :: "bifwd" :: "left" :: "right"
            :: nil);
        [constructor; [ctx_wf | x_in_G]
          | free_vals_in_ctx |].
      intros G' rho t x H_x_nin Htrans G'def; compute; subst G'.
      (* GR' |-p right!x; rest *)
      eapply TypPrefixOutput with (s:=SDual s0)
          (rho:=rho)
          (t:=SDual t);
        [apply trdual_w_mdual_involution; assumption
          | left; contradict H_x_nin; discriminate_w_list
          | constructor; [ctx_wf | x_in_G]
          | constructor; [ctx_wf | x_in_G]
          | left; reflexivity
          | reflexivity
          |].

      (* GR' |-p New e; rest *)
      apply TypNew with (s:=SInOut)
        (L:=right :: left :: d :: bifwd :: "bifwd" :: "left" :: "right"
          :: nil).
      intros e G' H_e_nin G'def; compute; subst.
      (* GR' |-p /bifwd!e; rest *)
      eapply TypPrefixOutput with (s:=SDual (SFwd SInOut))
          (rho:=TChannel SInOut)
          (t:=SDual (SFwd SInOut));
        [apply trdual_w_mdual_involution; constructor
          | left; discriminate
          | constructor; [ctx_wf | x_in_G]
          | constructor; [ctx_wf | x_in_G]
          | left; reflexivity
          | reflexivity
          |].
      (* GR' |-p /e!left; rest *)
      eapply TypPrefixOutput with (s:=SDual SInOut)
          (rho:=TChannel t)
          (t:=SDual (SInOut1 t));
        [apply trdual_w_mdual_involution; constructor
          | left; discriminate
          | constructor; [ctx_wf | x_in_G]
          | constructor; [ctx_wf | x_in_G]
          | left; reflexivity
          | reflexivity
          |].
      (* GR' |-p /e!right; rest *)
      eapply TypPrefixOutput with (s:=SDual (SInOut1 t))
          (rho:=TChannel (SDual t))
          (t:=SDual SEpsilon);
        [apply trdual_mdual_with_trInOut1
          | left; discriminate_w_list
          | constructor; [ctx_wf | x_in_G]
          | constructor; [ctx_wf | x_in_G]
          | left; reflexivity
          | reflexivity
          |].
      (* GR' |-p Zero *)
      apply TypZero;
        ctx_wf.

    SCase "GR' |-p right ? x ; rest ".
      (* GR' |-p right ? x ; rest *)
      apply TypPrefixInput with (s:=SDual s0)
          (L:=right :: left :: d :: bifwd :: "bifwd" :: "left" :: "right"
            :: nil);
        [constructor; [ctx_wf | x_in_G]
          | free_vals_in_ctx |].
      intros G' rho t x H_x_nin Htrans G'def; compute; subst G'.

      (* get Htrans in the proper form *)
      apply sdual_transition in Htrans;
        destruct Htrans as [t' Htrans];
        destruct Htrans as [Htrans Ht_eq]; subst.

      (* GR' |-p left!x; rest *)
      eapply TypPrefixOutput with (s:=s0)
          (rho:=rho)
          (t:=t');
        [assumption
          | left; contradict H_x_nin; discriminate_w_list
          | constructor; [ctx_wf | x_in_G]
          | constructor; [ctx_wf | x_in_G]
          | left; reflexivity
          | reflexivity
          |].
      (* GR' |-p New e; rest *)
      apply TypNew with (s:=SInOut)
        (L:=right :: left :: d :: bifwd :: "bifwd" :: "left" :: "right"
          :: nil).
      intros e G' H_e_nin G'def; compute; subst.
      (* GR' |-p /bifwd!e; rest *)
      eapply TypPrefixOutput with (s:=SDual (SFwd SInOut))
          (rho:=TChannel SInOut)
          (t:=SDual (SFwd SInOut));
        [apply trdual_w_mdual_involution; constructor
          | left; discriminate
          | constructor; [ctx_wf | x_in_G]
          | constructor; [ctx_wf | x_in_G]
          | left; reflexivity
          | reflexivity
          |].
      (* GR' |-p /e!left; rest *)
      eapply TypPrefixOutput with (s:=SDual SInOut)
          (rho:=TChannel t')
          (t:=SDual (SInOut1 t'));
        [apply trdual_w_mdual_involution; constructor
          | left; discriminate
          | constructor; [ctx_wf | x_in_G]
          | constructor; [ctx_wf | x_in_G]
          | left; reflexivity
          | reflexivity
          |].
      (* GR' |-p /e!right; rest *)
      eapply TypPrefixOutput with (s:=SDual (SInOut1 t'))
          (rho:=TChannel (SDual t'))
          (t:=SDual SEpsilon);
        [apply trdual_mdual_with_trInOut1
          | left; discriminate_w_list
          | constructor; [ctx_wf | x_in_G]
          | constructor; [ctx_wf | x_in_G]
          | left; reflexivity
          | reflexivity
          |].
      (* GR' |-p Zero *)
      apply TypZero;
        ctx_wf.
Qed.
