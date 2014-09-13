Require Import String.
Require Import TypeAssignmentPoly.
Require Import ResultBasics.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import List.
Require Import ExampleCommon.

Require String. Open Scope string_scope.

Lemma Hneq :
  forall d s,
    ((ValName (Nm (Free d))), TChannel SSink) = (namec, TChannel s)
  -> In d ("c" :: nil).
Proof.
  intros.
  inversion H; left; reflexivity.
Qed.

Lemma ctx_GL_wf :
  forall s d,
    ~ In d ("c" :: nil) ->
  CTX.add (ValName (CoNm (Free d)), TChannel (SDual SSink))
    (CTX.add (namec, TChannel (s)) CTX.empty)|-wf.
Proof.
  intros.
  ctx_wf.
Qed.

Lemma ctx_GR_wf :
  forall d,
    CTX.add (ValName (Nm (Free d)), TChannel SSink)
      (CTX.add (ValName (CoNm (Free d)), TChannel (SDual SSink))
        CTX.empty)|-wf. 
Proof.
  intros d.
  ctx_wf.
Qed.

Lemma ctx_var_x_s_nm_d_ssink_conm_d_sdual_ssink_empty_wf :
  forall x s d,
    ~ In x (d :: "c" :: nil) ->
  CTX.add (ValVariable (Var (Free x)), TChannel s)
    (CTX.add (ValName (Nm (Free d)), TChannel SSink)
      (CTX.add (ValName (CoNm (Free d)), TChannel (SDual SSink))
        CTX.empty)) |-wf.
Proof.
  intros x s d HxnIn.
  ctx_wf.
Qed.

Lemma ctx_y_rho_replace_x_s_t_x_s_d_ssink_cod_sdual_ssink_wf :
  forall y rho x s t d,
    ~ In y (x :: d :: "c" :: nil) ->
    ~ In x (d :: "c" :: nil) ->
  CTX.add (ValVariable (Var (Free y)), rho)
    (ctx_replace (ValVariable (Var (Free x))) (TChannel s) (TChannel t)
      (CTX.add (ValVariable (Var (Free x)), TChannel s)
        (CTX.add ((ValName (Nm (Free d))), TChannel SSink)
          (CTX.add ((ValName (CoNm (Free d))), TChannel (SDual SSink))
            CTX.empty))))|-wf.
Proof.
  intros y rho x s t d Hu HxnIn.
  ctx_wf.
Qed.

Lemma ctx_G'_wf :
  forall d s,
    ~ In d ("c" :: nil)
    -> CTX.add (ValName (Nm (Free d)), TChannel SSink)
      (CTX.add (ValName (CoNm (Free d)), TChannel (SDual SSink))
        (CTX.add (namec, TChannel s) CTX.empty))|-wf.
Proof.
  intros d s H.
  ctx_wf.
Qed.

Lemma logic_1 : forall P Q, ~ P -> ~Q -> ~ (P \/ Q).
  intuition.
Qed.

Lemma logic_2 : forall P Q R, ~ P -> ~Q \/ R -> ~ (P \/ Q) \/ R.
  intuition.
Qed.

Lemma ctx_GL_GR_parition_G' :
  forall d s,
    ~ In d ("c" :: nil)
    -> CTX.add (ValName (Nm (Free d)), TChannel SSink)
      (CTX.add (ValName (CoNm (Free d)), TChannel (SDual SSink))
        (CTX.add (namec, TChannel s) CTX.empty))
    |-part CTX.add (ValName (CoNm (Free d)), TChannel (SDual SSink))
         (CTX.add (namec, TChannel s) CTX.empty)
      (+) CTX.add (ValName (Nm (Free d)), TChannel SSink)
        (CTX.add (ValName (CoNm (Free d)), TChannel (SDual SSink)) CTX.empty).
Proof.
  intros d s H.
  pose (nm_d := ValName (Nm (Free d))).
  pose (conm_d := ValName (CoNm (Free d))).
  fold nm_d; fold conm_d.
  pose (G':=CTX.add (nm_d,TChannel SSink)
    (CTX.add(conm_d,TChannel (SDual SSink))
      (CTX.add(namec,TChannel s) CTX.empty))).
  pose (GL := CTX.add (conm_d, TChannel (SDual SSink))
    (CTX.add (namec, TChannel (s)) CTX.empty)).
  pose (GR :=CTX.add (nm_d,TChannel SSink)
    (CTX.add(conm_d,TChannel (SDual SSink)) CTX.empty)).

  apply Partition.
  Case "CTX.eq G' (CTX.union GL GR)".
    unfold CTX.eq; unfold CTX.Equal.
      induction a as (u,rho).
      split; intros H0.
      SSSCase "forall (u,rho), CTX.In (u,rho) G'".
        x_in_G; try solve [apply CTXFacts.union_3; x_in_G].
        apply CTXFacts.union_2; x_in_G.
      SSSCase "forall (u,rho), CTX.In (u,rho) (CTX.union GL GR)".
        x_in_G; assumption.
    SSCase "G'|-wf".
      apply ctx_G'_wf; assumption.
    SSCase "forall u,rho, ~In (u,rho) GL \/ ~In (u,rho) GR \/ (|-st rho)".
      intros.
      (repeat
        match goal with
          | |- context [CTX.In ?x (CTX.add ?y _)] =>
            rewrite -> CTXFacts.add_iff;
            let Heq := fresh "Heq" in
              let Hneq := fresh "Hneq" in
                destruct (CTX.E.eq_dec y x) as [Heq | Hneq];
                [inversion Heq | apply logic_2; [assumption|]]
          | |- ~ CTX.In ?x (CTX.empty) \/ _ =>
            rewrite CTXFacts.empty_iff; intuition
          | |- context [|-st TChannel (SDual SSink)] =>
            right; right; constructor; intros
          | H : SDual SSink -- _ --> _ |- _ => inversion H; clear H
          | H : SSink -- _ --> _ |- _ => inversion H; clear H
          | |- ?x = ?x => reflexivity
        end).
      right; left; x_nin_G; contradict H; inversion H0; left; reflexivity.
Qed.

Lemma ctx_GL_types_coname_d_write_c :
  forall d s,
    ~ In d ("c" :: nil)
    ->
      CTX.add (ValName (CoNm (Free d)), TChannel (SDual SSink))
       (CTX.add (namec, TChannel s) CTX.empty) |-p
       CoNm (Free d) ! namec; Zero.
Proof.
  intros d s H.
  eapply TypPrefixOutput with (s:=SDual SSink) (t:= SDual SSink) 
      (rho:=TChannel s);
  [ apply TRDual with (m:=MInp (TChannel s)) (s:=SSink) (t:=SSink); apply TRSink
    | unfold namec; left; discriminate
    | 
    | 
    | auto
    | auto
    | constructor; ctx_wf
  ]; (constructor; [ ctx_wf | x_in_G ]).

Qed.

Lemma ctx_GR_types_rep_name_d_read_x_x_read_y_coname_d_write_x :
  forall d,
    ~ In d ("c" :: nil) ->
    CTX.add (ValName (Nm (Free d)), TChannel SSink)
     (CTX.add (ValName (CoNm (Free d)), TChannel (SDual SSink)) CTX.empty)
    |-p !Nm (Free d) ? ;
     (Var (Bound 0) ? ; (CoNm (Free d) ! Var (Bound 1); Zero)).
Proof.
  intros d H.
  pose (GR:=CTX.add (ValName (Nm (Free d)),TChannel SSink)
    (CTX.add(ValName (CoNm (Free d)),TChannel (SDual SSink)) CTX.empty)).
  apply TypRep with (G':=GR); try (apply ctx_GR_wf || reflexivity).

  Case "forall (u,rho), In(u,rho) GR -> |-st rho".
    intros u rho.
    unfold GR; intros Hin.
    x_in_G; try (inversion H0; constructor; intros m t H1; inversion H1);
      [reflexivity | (inversion H5; reflexivity)].

  Case "GR |-p d?x;x?y;co d!x;0".
    apply TypPrefixInput with (s:=SSink) (L:=d::("c" : free_id)::nil).
    SCase "GR|-v d : TChannel SSink".
      apply LContext; [apply ctx_GR_wf | unfold GR; x_in_G].

    SCase "free_values_in_context GR (x?y;co d!x;0)".
      free_vals_in_ctx.

    SCase "GR'= (Var x,rho) GR,
      GR'|-p open_proc x y (x?y;cd d!x;0)".
      intros GR' rho t x HxnIn Htrans GR'def; subst.
      inversion Htrans; subst.
      simpl.
      pose (nm_d := ValName (Nm (Free d))).
      pose (conm_d := ValName (CoNm (Free d))).
      unfold GR.
      apply TypPrefixInput with (s:=s) (L:=x::d::("c":free_id)::nil).

      SSCase "GR'|-v Var (Free x) y (x?y;co d!x;0)".
        constructor; [ctx_wf|x_in_G].

      SSCase "free_values_in_context GR' (CoNm (Free d) ! Var (Free x); Zero)".
        free_vals_in_ctx.

      intros G' rho t y Hu Htrans2 Heq2; subst.
      simpl.
      SSCase "CTX.add (Var (Free y), rho)
        (ctx_replace (Var (Free x)) (TChannel s) (TChannel t)
          (CTX.add (Var (Free x), TChannel s) GR))
        |-p CoNm (Free d) ! Var (Free x); Zero".
        (* don't care about the transition of the input channel in sink. *)
        clear Htrans2.
        clear GR.
        eapply TypPrefixOutput with (s:=(SDual SSink)) (t:=(SDual SSink))
            (rho:=TChannel t); try solve [constructor; [ctx_wf|x_in_G]];
          [ | left; discriminate | left; reflexivity | reflexivity
            | apply TypZero].

        SSSCase "SDual SSink -- MOut (TChannel t) --> SDual SSink".
          rewrite <- (m_dual_is_dual (MOut (TChannel t)));
            apply TRDual; apply TRSink.
        ctx_wf.
Qed.

(* new d; ( (co d)!c; 0 | rep (d?x; x?y; (co d)!x; 0) ) *)
Definition sink : proc := 
  New (((CoNm (Bound 0)) ! namec ; Zero)
        |||
       (Rep (Nm (Bound 0) ? ; ((Var (Bound 0)) ? ; 
              ((CoNm (Bound 2)) ! (Var (Bound 1)); Zero))))).

Lemma sink_typing : 
    forall s,
    (CTX.add (namec, TChannel (s)) CTX.empty) |-p sink.
Proof.
  intros s.
  unfold sink.
  eapply TypNew with (s:=SSink) (L:= ("c" : free_id)::nil).
  intros d G' H Heq.
  (* this does a limited compute just on stuff in brackets.
  cbv beta delta [open_proc open_value open_name open_id] iota zeta.*)
  compute; fold namec.
  subst.
  pose (nm_d := ValName (Nm (Free d))).
  pose (conm_d := ValName (CoNm (Free d))).
  fold nm_d; fold conm_d.
  Case "Let G'=(d,SSink)(co d,dual SSink)(c,s). G' |-p co d!c ||| !(d?x;x?y;co d!x).".
  pose ( GL := CTX.add (conm_d, TChannel (SDual SSink)) 
         (CTX.add (namec, TChannel (s)) CTX.empty) ).
  pose (GR :=CTX.add (nm_d,TChannel SSink)
    (CTX.add(conm_d,TChannel (SDual SSink)) CTX.empty)).
  eapply TypPar with (GL:=GL) (GR:=GR).
  SCase "G' |-part GL (+) GR.".
    apply ctx_GL_GR_parition_G'; assumption.

  SCase "GL |-p co d!c.".
    apply ctx_GL_types_coname_d_write_c; assumption.

  SCase "GR |-p rep(d?x;x?y;co d!x;0).".
    clear GL.
    unfold GR; unfold nm_d; unfold conm_d.
    apply ctx_GR_types_rep_name_d_read_x_x_read_y_coname_d_write_x;
      assumption.
Qed.