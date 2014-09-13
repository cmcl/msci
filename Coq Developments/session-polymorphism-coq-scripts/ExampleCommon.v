Require Import String.
Require Import TypeAssignmentPoly.
Require Import ResultBasics.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import List.

Require String. Open Scope string_scope.

Ltac x_in_G_aux H1 H2 :=
  let H':= fresh "H" in
    inversion H1 as [H']; rewrite -> H' in H2; contradict H2; red.

Ltac x_in_G :=
  (repeat
    match goal with
      | |- context [ctx_replace _ _ _ _] => unfold ctx_replace
      | [ H : context [ctx_replace _ _ _ _] |- _ ] => unfold ctx_replace in H
      | [ H : CTX.In _ (CTX.add _ _) |- _ ] =>
        try solve [apply CTXFacts.add_1 in H];
          rewrite CTXFacts.add_iff in H
      | [ H : CTX.In _ (CTX.union _ _) |- _ ] =>
        rewrite CTXFacts.union_iff in H
      | [ H : CTX.In _ (CTX.remove _ _) |- _ ] =>
        rewrite CTXFacts.remove_iff in H
      | [ H : CTX.In _ CTX.empty |- _ ] =>
        rewrite CTXFacts.empty_iff in H; contradiction
      | [ H : _ \/ _ |- _ ] => destruct H
      | [ H : _ /\ _ |- _ ] => destruct H
      | [ |- CTX.In _ (CTX.add _ _) ] =>
        try solve [apply CTXFacts.add_1; (reflexivity||assumption)];
          rewrite CTXFacts.add_iff; right
      | [ |- CTX.In _ (CTX.remove _ _) ] =>
        rewrite CTXFacts.remove_iff; split; [| try solve [discriminate];
          try solve [
            repeat (match goal with
              | [ |- (?x, _) <> (?y, _) ] => intro
              | [ H1: ~ In ?x _ ,  H2 : (?x :: _) = (?x :: _) |- False ] =>
                 contradict H1; red
              | [ H1 : (ValName (Nm (Free ?x)), _) = (_, _),
                  H2 : ~ In ?x _ |- False ] => x_in_G_aux H1 H2
              | [ H1 : (_, _) = (ValName (Nm (Free ?x)), _),
                  H2 : ~ In ?x _ |- False ] => x_in_G_aux H1 H2
              | [ H1 : (ValName (CoNm (Free ?x)), _) = (_, _),
                  H2 : ~ In ?x _ |- False ] => x_in_G_aux H1 H2
              | [ H1 : (_, _) = (ValName (CoNm (Free ?x)), _),
                  H2 : ~ In ?x _ |- False ] => x_in_G_aux H1 H2
              | [ H1 : (ValVariable (Var (Free ?x)), _) = (_, _),
                  H2 : ~ In ?x _ |- False ] => x_in_G_aux H1 H2
              | [ H1 : (_, _) = (ValVariable (Var (Free ?x)), _),
                  H2 : ~ In ?x _ |- False ] => x_in_G_aux H1 H2
              | |- ?x = ?x \/ _ => left; reflexivity
              | |- ?x = ?y \/ _ => try right
            end)
          ] ]
    end).
Ltac x_nin_G :=
  (repeat
    match goal with
      | [ H : ctx_replace _ _ _ _ |- _ ] => unfold ctx_replace in H
      | [ |- ~ CTX.In _ _ ] => compute; intros
      | [ H : CTX.In _ (CTX.add _ _) |- _ ] => rewrite CTXFacts.add_iff in H
      | [ H : CTX.In _ (CTX.remove _ _) |- _ ] =>
        rewrite CTXFacts.remove_iff in H; destruct H
      | [ H : CTX.In _ CTX.empty |- _ ] =>
        rewrite CTXFacts.empty_iff in H; contradiction
      | [ H : _ \/ _ |- _ ] => destruct H; [try solve [contradiction]|]
      | [ H : _ = _ |- _ ] => try solve
        [(contradiction||symmetry in H;contradiction||discriminate)]
    end).

Ltac x_fresh_for_ctx :=
  constructor;
  [(constructor||assumption)|];
  let v:=fresh "v" in
    let sigma:=fresh "sigma" in
      intros v sigma;
  match goal with
    | |- ~ CTX.In (v,sigma) ?G \/ _ =>
      destruct CTXProperties.In_dec with (x:=(v,sigma)) (s:=G)
  end;
  [right | left; eauto ];
  x_in_G;
  (contradiction ||
    (repeat
      match goal with
        | [ H : (?x, _) = (?y, _) |- _] =>
          inversion H; simpl; clear H
        | [ H : (?x, ?rho) = (?x, ?rho') |- _] =>
          inversion H; simpl; clear H
        | [ H : ~ In ?x ?L1 |- ?x :: ?L2 <> ?y :: ?L3 ] =>
          try solve [let Heq:= fresh "H" in intros Heq; inversion Heq];
            injection; let Heq:= fresh "H" in intro Heq; subst; contradict H
        | [ H : ~ In ?y ?L1 |- ?x :: ?L2 <> ?y :: ?L3 ] =>
          try solve [let Heq:= fresh "H" in intros Heq; inversion Heq];
            injection; let Heq:= fresh "H" in intro Heq; subst; contradict H
        | |- ?x :: ?L2 <> ?y :: ?L3 =>
          try solve [let Hn:= fresh "H" in intros Hn; inversion Hn;
            contradiction]
        | |- In ?x _ => red
        | |- ?x = ?x \/ _ => left; reflexivity
        | |- ?x = ?y \/ _ => right
      end)).

Ltac free_vals_in_ctx :=
  compute;
  intros u Hin;
  (repeat
    match goal with
      | [ H : _ \/ _ |- _ ] => destruct H
      | [ H : _ = _ |- _ ] => subst
      | [ H : False |- _ ] => contradiction
    end);
  eexists;
  x_in_G.

Ltac ctx_wf :=
  (repeat match goal with
    | |- CTX.empty |-wf => apply empty_ctx_wf
    | |- CTX.add (?x,_) (CTX.add (?y,_) _) |-wf => unfold x; unfold y
    | |- CTX.add (ValName (Nm (Free ?l)), TChannel (?x))
         (CTX.add (ValName (CoNm (Free ?l)), TChannel (SDual (?x)))
         _) |-wf
         => apply ctx_add_wf_dual_names
    | |- CTX.add _ _ |-wf => apply wellformed_ctx_add_1
    | |- ctx_replace _ _ _ _ |-wf =>
         apply ctx_replace_preserves_wf; [x_in_G|]
    | |- CTX.remove _ _ |-wf => apply wellformed_ctx_remove_1
    | |- free_value _ => try solve [constructor]
    | |- fresh_for_ctx _ _ => x_fresh_for_ctx
    end).

Definition name0 : value := (Nm (Bound 0)).
Definition var0 : value := (Var (Bound 0)).

Definition namec : value := (Nm (Free "c")).
Definition named : value := (Nm (Free "d")).

Lemma m_dual_involution : forall m, m = m_dual(m_dual m).
Proof.
  induction m.
  Case "m = MInp t".
    simpl; reflexivity.
  Case "m = MOut t".
    simpl; reflexivity.
Qed.

Lemma trdual_w_mdual_involution :
  forall s t m, s --(m_dual m)--> t -> (SDual s) --m--> (SDual t).
Proof.
  intros.
  apply TRDual in H.
  rewrite m_dual_involution with m.
  assumption.
Qed.

(* spell out the proof for one wf case for an example of how to prove
   well-formedness without the ctx_wf tactic. *)
Lemma ctx_free_nm_sess_wf :
  forall s x, ((CTX.add (ValName (Nm (Free x)), TChannel s) CTX.empty)|-wf).
Proof.
  intros.
  apply wellformed_ctx_add_1.
  apply empty_ctx_wf.
  apply FNm.
  x_fresh_for_ctx.
Qed.

Lemma ctx_free_conm_sess_wf :
  forall s x, ((CTX.add (ValName (CoNm (Free x)), TChannel s) CTX.empty)|-wf).
Proof.
  intros.
  ctx_wf.
Qed.

Lemma ctx_add_named_SDual_s_well_formed :
  forall s, ((CTX.add (named, TChannel (SDual s)) CTX.empty)|-wf).
Proof.
  intros.
  ctx_wf.
Qed.

Lemma ctx_add_namec_t_add_named_SDual_s_well_formed :
  forall s t, ((CTX.add(namec, TChannel t)(CTX.add (named, TChannel (SDual s)) CTX.empty))|-wf).
Proof.
  intros.
  ctx_wf.
Qed.

Lemma ctx_add_namec_s_add_named_SDual_s_well_formed :
  forall s, ((CTX.add(namec, TChannel s)(CTX.add (named, TChannel (SDual s)) CTX.empty))|-wf).
Proof.
  intros.
  ctx_wf.
Qed.

Lemma TypNew_context_wf :
   forall s G G', G |-wf ->
      forall x,
      ~ (In x (free_ids_context G))
      ->
      G' = (CTX.add (ValName (Nm (Free x)), TChannel s)
             (CTX.add (ValName (CoNm (Free x)), TChannel (SDual s))
               G))
      -> G' |-wf.
Proof.
  intros s G G' Gwf x H G'def.
  subst.
  apply WFCtx.

  Case "forall u rho, In(u,rho) G' -> free_value u".
    intros.
    x_in_G; try solve [inversion H0; constructor].
    inversion Gwf; apply H1 with (u:=u) (rho:=rho); assumption.

  Case "forall u rho sigma, In(u,rho) G' -> In(u,sigma) G' -> rho = sigma".
    intros u rho sigma Hin_rho Hin_sigma.
    x_in_G; try (inversion H1); try (inversion H0); subst;
      try solve [(reflexivity || discriminate)];
      try solve [destruct Gwf as [? ? Hu]; eapply Hu; eauto];
      contradict H; try solve [eapply free_ids_context_vs_context_name;
        eauto]; eapply free_ids_context_vs_context_coname; eauto.

  Case "forall x0, (forall rho, ~In(Var x0,rho) G') \/
    ((forall rho, ~In(Nm x0,rho) G') /\ (forall rho, ~In(CoNm x0,rho) G'))".
    destruct Gwf as [? _ _ Hu].
    intros y.
    specialize (Hu y).
    destruct Hu as [Hu|Hu].
    left; intros rho.
    specialize (Hu rho).
    x_nin_G; contradiction.

    destruct (string_dec x y); subst.
    SCase "x = y".
      left; intros rho; destruct Hu as [Hu1 Hu2]; specialize (Hu1 rho);
        specialize (Hu2 rho).
      x_nin_G.
      contradict H; eapply free_ids_context_vs_context_var; eauto.
    SCase "x <> y".
      right.
      destruct Hu as [Hu1 Hu2].
      split; intros rho; specialize (Hu1 rho); specialize (Hu2 rho);
        [contradict Hu1|contradict Hu2].
      x_in_G; try ((inversion H0; contradiction) || assumption).
      x_nin_G; ((inversion H0; contradiction) || assumption).
Qed.

Lemma in_not_fresh_for_ctx_nm_nm : 
  forall x rho G, 
    CTX.In (ValName (Nm (Free x)), rho) G
    -> 
    ~ fresh_for_ctx (Nm (Free x)) G.
Proof.
  intros x rho G Hin Hfresh_x; inversion Hfresh_x as [? ? _ U1|]; subst.
  specialize (U1 (Nm (Free x)) rho); destruct U1; subst; intuition.
Qed.

Lemma in_not_fresh_for_ctx_conm_nm : 
  forall x rho G, 
    CTX.In (ValName (CoNm (Free x)), rho) G
    -> 
    ~ fresh_for_ctx (Nm (Free x)) G.
Proof.
  intros x rho G Hin Hfresh_x; inversion Hfresh_x as [? ? _ U1|]; subst.
  specialize (U1 (CoNm (Free x)) rho); destruct U1; subst; intuition.
Qed.

Lemma ctx_add_wf_dual_names :
forall G x s,
    fresh_for_ctx (Nm (Free x)) G
    ->
    G |-wf
    ->
    (CTX.add (ValName (Nm (Free x)), TChannel s) (CTX.add (ValName (CoNm (Free x)), TChannel (SDual s)) G)) |-wf.
Proof.
  intros G x s Hfresh_x Hwf.
  inversion Hwf as [? U1 U2 U3]; subst.
  constructor; intros; repeat (rewrite CTXFacts.add_iff in *).
  destruct H; crush.
  constructor.
  constructor.
  eapply U1; eauto.
  repeat match goal with 
    | [ H : _ \/ _ |- _ ] => destruct H
  end; crush.
  contradict Hfresh_x; eapply in_not_fresh_for_ctx_nm_nm; eauto.
  contradict Hfresh_x; eapply in_not_fresh_for_ctx_conm_nm; eauto.
  contradict Hfresh_x; eapply in_not_fresh_for_ctx_nm_nm; eauto.
  contradict Hfresh_x; eapply in_not_fresh_for_ctx_conm_nm; eauto.
  eapply U2; eauto.
  destruct (string_dec x0 x); subst.
  left; intros rho U4.
  x_in_G; try discriminate.
  inversion Hfresh_x as [? ? _ U4|]; subst.
  specialize (U4 (Var (Free x)) rho); destruct U4; intuition.

  specialize (U3 x0); destruct U3 as [U4|U4];
    [left; intros rho Hin; specialize (U4 rho)
      | destruct U4 as [U5 U6]; right; split; intros rho Hin;
        [specialize (U5 rho)|specialize (U6 rho)]];
      x_nin_G; (contradiction || inversion H; symmetry in H1; contradiction).
Qed.

Lemma ctx_replace_nothing_eq :
   forall v old G ,
     CTX.In (v,old) G ->
     CTX.eq (ctx_replace v old old G) G.
Proof.
  intros.
  unfold ctx_replace.
  apply CTXProperties.add_remove.
  assumption.
Qed.

Lemma ctx_replace_nothing_eq_stronger :
   forall v old G G',
     CTX.In (v,old) G ->
     CTX.eq G G' ->
     CTX.eq (ctx_replace v old old G) G'.
Proof.
  intros.
  unfold ctx_replace.
  rewrite -> CTXProperties.add_remove; assumption.
Qed.

Lemma ctx_remove_x_replace_nothing_G_eq_ctx_remove_x_G :
  forall x u rho G,
    CTX.In (u,rho) G ->
  CTX.eq (CTX.remove x (ctx_replace u rho rho G)) (CTX.remove x G).
Proof.
  intros.
  apply ctx_remove_1; [reflexivity|].
  apply ctx_replace_nothing_eq.
  assumption.
Qed.

Lemma ctx_add_x_replace_nothing_G_eq_ctx_add_x_G :
  forall x u rho G,
    CTX.In (u,rho) G ->
  CTX.eq (CTX.add x (ctx_replace u rho rho G)) (CTX.add x G).
Proof.
  intros.
  apply ctx_add_1; [reflexivity|].
  apply ctx_replace_nothing_eq.
  assumption.
Qed.

Lemma ctx_term_dual_term_wf :
  forall d s,
    CTX.add (ValName (Nm (Free d)), TChannel s)
      (CTX.add (ValName (CoNm (Free d)), TChannel (SDual s))
        CTX.empty)|-wf. 
Proof.
  intros d s.
  apply TypNew_context_wf with (s:=s) (G:= CTX.empty) (x:=d).
  apply empty_ctx_wf.
  unfold free_ids_context.
  rewrite CTXProperties.elements_empty.
  auto.
  reflexivity.
Qed.

Lemma trdual_mdual_with_trInOut1 : 
  forall s, 
    SDual (SInOut1 s) --(MOut (TChannel (SDual s)))--> SDual (SEpsilon).
Proof.
  intros s.
  rewrite <- (m_dual_is_dual (MOut (TChannel (SDual s)))).
  apply TRDual.
  unfold m_dual.
  apply TRInOut1.
Qed.

