Require Export Arith.EqNat.
Require Export Arith.Lt.
Require Export Arith.Compare_dec.
Require Export List.
Require Export ListLocal.
Require Import String.
Require Import TypeAssignmentPoly.
Require Import ResultOpenClose.
Require Import ResultBasics.
Require Import ResultWeaken.
Require Import ResultRename.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import TacticsLocal.
Require Import ResultStrengthen.
Require Import ResultStructTyped.
Require Import ResultSubst.

Lemma mk_obs_imp_obs_msg_nm : 
  forall G nm v a vo,
    balanced G
    ->
    G |-v v : a
    ->
    mk_obs nm v vo
    ->
    mk_obs_msg nm (MInp a) vo.
Proof.
  intros G nm v a vo Hprespre Hlookup Hvo.
  inversion Hlookup; subst.
  destruct Hprespre as [_ Hprespre]; destruct Hprespre as [Hallfreenames Hnameschanneltypes].
  specialize (Hallfreenames _ _ H0).
  specialize (Hnameschanneltypes _ _ H0); destruct Hnameschanneltypes as [s Hnameschanneltypes]; simpl in *; subst; 
    inversion Hallfreenames; subst; inversion Hvo; subst; 
      inversion H1; subst; 
        try constructor; 
          subst. 

  simpl in *; subst.
  inversion Hvo; subst; 
    inversion H0; subst; 
      constructor.
Qed.

Lemma mk_obs_imp_obs_msg_conm : 
  forall G nm v a vo,
    balanced G
    ->
    G |-v v : a
    ->
    mk_obs nm v vo
    ->
    mk_obs_msg (dual_name nm) (MOut a) vo.
Proof.
  intros G nm v a vo Hprespre Hlookup Hvo.
  inversion Hlookup; subst.
  destruct Hprespre as [_ Hprespre]; destruct Hprespre as [Hallfreenames Hnameschanneltypes].
  specialize (Hallfreenames _ _ H0).
  specialize (Hnameschanneltypes _ _ H0); destruct Hnameschanneltypes as [s Hnameschanneltypes]; simpl in *; subst; 
    inversion Hallfreenames; subst; inversion Hvo; subst; 
      inversion H1; subst; 
        try constructor; 
          subst. 

  simpl in *; subst.
  inversion Hvo; subst; 
    inversion H0; subst; 
      constructor.
Qed.

(* ============================================================================= *)

Lemma partition_interaction1 : 
  forall G GL GR m v rho s1 sigma2 s1d sigma4,
    G |-part GL (+) GR
    ->
    ValName (m) <> v
    ->
    ValName (dual_name m) <> v
    ->
    GL |-v m : TChannel s1
    ->
    GR |-v (dual_name m) : TChannel s1d 
    ->
    GR |-v v : rho
    ->
    free_value v
    ->
    (CTX.In (ValName m, TChannel s1) GR -> TChannel s1 = sigma2)
    ->
    (CTX.In (ValName (dual_name m), TChannel s1d) GL -> TChannel s1d = sigma4)
    ->
    (CTX.union
      (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL))
      (ctx_replace (dual_name m) (TChannel s1d) sigma4 (CTX.remove (v, rho) GR) ))
    |-part (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL)) (+) (ctx_replace (dual_name m) (TChannel s1d) sigma4 (CTX.remove (v, rho) GR) ).
Proof.
  intros G GL GR m v rho s1 sigma2 s1d sigma4 Hpart Hneqm Hneqdm Hlookupm Hlookupdm Hlookupv Hfv Hineqm Hineqdm.
  eapply ctx_equal_part; [
    | rewrite ctx_add_value_free_value; [
      rewrite add_replace_comm; [
        reflexivity
        | auto
      ]
      | auto]
    | rewrite ctx_add_value_free_value; [
      rewrite add_replace_comm; [
        reflexivity
        | auto
      ]
      | auto]
    | reflexivity 
  ].
  eapply ctx_replace_pre_union.
  apply partition_comm.
  eapply ctx_replace_pre_union .
  apply partition_comm.
  apply partition_add_remove_swap.
  eauto.

  inversion Hlookupv; subst; [|inversion Hfv]; auto.

  rewrite CTXFacts.remove_iff.
  split.
  inversion Hlookupdm; subst; auto.
  intros Hu; injection Hu; intros; subst.
  contradict Hneqdm; auto.

  rewrite CTXFacts.add_iff.
  intros Hin.
  destruct Hin as [Heq|Hin].
  injection Heq; intros; subst; contradict Hneqdm; auto.
  apply Hineqdm; auto.
  
  rewrite CTXFacts.add_iff.
  right.
  inversion Hlookupm; subst; auto.

  unfold ctx_replace.
  (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)).
  intros Hin.
  destruct Hin as [Hin|Hin].
  injection Hin; intros; contradict H0.
  apply dual_name_neq.

  destruct Hin as [Hin Hneq1]; destruct Hin as [Hin Hneq2].
  apply Hineqm; auto.
Qed.

(* ============================================================================= *)

Lemma partition_interaction2 : 
  forall G GL GR m v rho s1 sigma2 s1d sigma4,
    G |-part GL (+) GR
    ->
    ValName (m) <> v
    ->
    ValName (dual_name m) <> v
    ->
    GL |-v m : TChannel s1
    ->
    GR |-v (dual_name m) : TChannel s1d 
    ->
    (exists k, v = ValToken k)
    ->
    (CTX.In (ValName m, TChannel s1) GR -> TChannel s1 = sigma2)
    ->
    (CTX.In (ValName (dual_name m), TChannel s1d) GL -> TChannel s1d = sigma4)
    ->
    (CTX.union
      (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL))
      (ctx_replace (dual_name m) (TChannel s1d) sigma4 (CTX.remove (v, rho) GR) ))
    |-part (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL)) (+) (ctx_replace (dual_name m) (TChannel s1d) sigma4 (CTX.remove (v, rho) GR) ).
Proof.
  intros G GL GR m v rho s1 sigma2 s1d sigma4 Hpart Hneqm Hneqdm Hlookupm Hlookupdm Htok Hineqm Hineqdm.
  destruct Htok as [k Heq]; subst.
  eapply ctx_equal_part; [
    | rewrite ctx_add_value_token; reflexivity
    | rewrite ctx_add_value_token; reflexivity
    | reflexivity 
  ].
  eapply ctx_replace_pre_union.
  apply partition_comm.
  eapply ctx_replace_pre_union .
  apply partition_remove_token.
  apply partition_comm.
  eauto.

  rewrite CTXFacts.remove_iff.
  split.
  inversion Hlookupdm; subst; auto.

  discriminate.

  assumption.

  inversion Hlookupm; subst; auto.

  unfold ctx_replace.
  (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)).
  intros Hin.
  destruct Hin as [Hin|Hin].
  injection Hin; intros; contradict H0.
  apply dual_name_neq.

  destruct Hin as [Hin Hneq1]; destruct Hin as [Hin Hneq2].
  apply Hineqm; auto.
Qed.

(* ============================================================================= *)

Lemma partition_interaction3 : 
  forall G GL GR m v rho s1 sigma2 s1d sigma4,
    G |-part GL (+) GR
    ->
    ValName (m) = v
    ->
    ValName (dual_name m) <> v
    ->
    GL |-v m : TChannel s1
    ->
    GR |-v (dual_name m) : TChannel s1d 
    ->
    GR |-v v : rho
    ->
    free_value v
    ->
    (CTX.In (ValName m, TChannel s1) GR -> TChannel s1 = sigma2)
    ->
    (CTX.In (ValName (dual_name m), TChannel s1d) GL -> TChannel s1d = sigma4)
    ->
    (CTX.union
      (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL))
      (ctx_replace (dual_name m) (TChannel s1d) sigma4 (CTX.remove (v, rho) GR) ))
    |-part (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL)) (+) (ctx_replace (dual_name m) (TChannel s1d) sigma4 (CTX.remove (v, rho) GR) ).
Proof.
  intros G GL GR m v rho s1 sigma2 s1d sigma4 Hpart Hneqm Hneqdm Hlookupm Hlookupdm Hlookupv Hfv Hineqm Hineqdm.
  subst.
  assert (rho = TChannel s1 /\ |-st TChannel s1).
  inversion Hpart; subst.
  inversion Hlookupm; subst.
  inversion Hlookupv; subst.
  assert (rho = TChannel s1).
  inversion H0; subst.
  
  rewrite (H7 m (TChannel s1) rho); auto; rewrite H; rewrite CTXFacts.union_iff; [left|right]; auto.

  split; auto; subst.
  destruct (H1 m (TChannel s1)) as [Hu|Hu]; [contradict Hu; auto | destruct Hu as [Hu|Hu]; [contradict Hu; auto | auto] ].

  destruct H as [Heq Hstateless]; subst.

  assert (TChannel s1 = sigma2).
  apply Hineqm.
  inversion Hlookupv; subst; auto.

  subst.
  
  inversion Hlookupm; subst.
  
  eapply ctx_equal_part; [
    | rewrite ctx_add_value_free_value; [rewrite ctx_add_idem; [rewrite ctx_replace_idem; [rewrite CTXProperties.union_sym; reflexivity|auto] | rewrite ctx_replace_idem; auto] | auto]
    | rewrite ctx_add_value_free_value; [rewrite ctx_add_idem; [rewrite ctx_replace_idem; [reflexivity|auto] | rewrite ctx_replace_idem; auto] | auto]
    | reflexivity 
  ].
  apply partition_comm.
  eapply ctx_replace_pre_union.
  apply ctx_remove_preserves_partition_left_2; auto.
  apply partition_comm.
  eauto.

  rewrite CTXFacts.remove_iff.
  split.
  inversion Hlookupdm; subst; auto.
  intros Hu; injection Hu; intros.
  symmetry in H2.
  contradict H2.
  apply dual_name_neq.

  apply Hineqdm.
Qed.

(* ============================================================================= *)

Lemma partition_interaction : 
  forall G GL GR m v rho s1 sigma2 s1d sigma4,
    G |-part GL (+) GR
    ->
    ValName (dual_name m) <> v
    ->
    GL |-v m : TChannel s1
    ->
    GR |-v (dual_name m) : TChannel s1d 
    ->
    GR |-v v : rho
    ->
    free_value_or_token v
    ->
    (CTX.In (ValName m, TChannel s1) GR -> TChannel s1 = sigma2)
    ->
    (CTX.In (ValName (dual_name m), TChannel s1d) GL -> TChannel s1d = sigma4)
    ->
    (CTX.union
      (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL))
      (ctx_replace (dual_name m) (TChannel s1d) sigma4 (CTX.remove (v, rho) GR) ))
    |-part (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL)) (+) (ctx_replace (dual_name m) (TChannel s1d) sigma4 (CTX.remove (v, rho) GR) ).
Proof.
  intros G GL GR m v rho s1 sigma2 s1d sigma4 Hpart Hneqdm Hlookupm Hlookupdm Hlookupv Hfvot Hineqm Hineqdm.
  destruct (value_dec (ValName m) v); [
    subst; apply partition_interaction3 with (G:=G); auto; eapply channel_lookup_yields_free_value; eauto
    | destruct Hfvot; [
      apply partition_interaction1 with (G:=G); auto
      | apply partition_interaction2 with (G:=G); eauto
    ]
  ].
Qed.

(* ============================================================================= *)

Lemma partition_interaction_stateless1 : 
  forall G GL GR m v rho s1 sigma2 s1d sigma4,
    G |-part GL (+) GR
    ->
    ValName (m) <> v
    ->
    ValName (dual_name m) <> v
    ->
    GL |-v m : TChannel s1
    ->
    GR |-v (dual_name m) : TChannel s1d 
    ->
    GR |-v v : rho
    ->
    free_value v
    ->
    (CTX.In (ValName m, TChannel s1) GR -> TChannel s1 = sigma2)
    ->
    (CTX.In (ValName (dual_name m), TChannel s1d) GL -> TChannel s1d = sigma4)
    ->
    |-st rho
    -> 
    (CTX.union
      (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL))
      (ctx_replace (dual_name m) (TChannel s1d) sigma4 GR ))
    |-part (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL)) (+) (ctx_replace (dual_name m) (TChannel s1d) sigma4 GR).
Proof.
  intros G GL GR m v rho s1 sigma2 s1d sigma4 Hpart Hneqmv Hneqdm Hlookupm Hlookupdm Hlookupv Hfv Hineqm Hineqdm Hstateless; subst.
  eapply ctx_equal_part; [
    | rewrite ctx_add_value_free_value; [
      rewrite add_replace_comm; [
        reflexivity
        | auto
      ]
      | auto]
    | rewrite ctx_add_value_free_value; [
      rewrite add_replace_comm; [
        reflexivity
        | auto
      ]
      | auto]
    | reflexivity
  ].
  eapply ctx_replace_pre_union.
  apply partition_comm.
  eapply ctx_replace_pre_union .
  apply partition_comm.

  apply partition_add_idem_stateless; eauto.
  eapply partition_lookup_left. 
  apply partition_comm; eauto.
  auto.

  inversion Hlookupdm; subst; auto.

  rewrite CTXFacts.add_iff.
  intros Hin.
  destruct Hin as [Heq|Hin].
  injection Heq; intros; subst; contradict Hneqdm; auto.
  apply Hineqdm; auto.

  rewrite CTXFacts.add_iff.
  right.
  inversion Hlookupm; subst; auto.

  unfold ctx_replace.
  (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)).
  intros Hin.
  destruct Hin as [Hin|Hin].
  injection Hin; intros; contradict H0.
  apply dual_name_neq.

  destruct Hin as [Hin Hneq].
  apply Hineqm; auto.
Qed.

(* ============================================================================= *)

Lemma partition_interaction_stateless2 : 
  forall G GL GR m v rho s1 sigma2 s1d sigma4,
    G |-part GL (+) GR
    ->
    ValName (m) <> v
    ->
    ValName (dual_name m) <> v
    ->
    GL |-v m : TChannel s1
    ->
    GR |-v (dual_name m) : TChannel s1d 
    ->
    (exists k, v = ValToken k)
    ->
    (CTX.In (ValName m, TChannel s1) GR -> TChannel s1 = sigma2)
    ->
    (CTX.In (ValName (dual_name m), TChannel s1d) GL -> TChannel s1d = sigma4)
    ->
    (CTX.union
      (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL))
      (ctx_replace (dual_name m) (TChannel s1d) sigma4 GR ))
    |-part (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL)) (+) (ctx_replace (dual_name m) (TChannel s1d) sigma4 GR).
Proof.
  intros G GL GR m v rho s1 sigma2 s1d sigma4 Hpart Hneqmv Hneqdm Hlookupm Hlookupdm Htok Hineqm Hineqdm; subst.
  destruct Htok as [k Heq]; subst.
  eapply ctx_equal_part; [
    | rewrite ctx_add_value_token; reflexivity
    | rewrite ctx_add_value_token; reflexivity
    | reflexivity
  ].
  eapply ctx_replace_pre_union.
  apply partition_comm.
  eapply ctx_replace_pre_union .
  apply partition_comm.
  eauto.

  inversion Hlookupdm; subst; auto.
  assumption.
  inversion Hlookupm; subst; auto.

  unfold ctx_replace.
  (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)).
  intros Hin.
  destruct Hin as [Hin|Hin].
  injection Hin; intros; contradict H0.
  apply dual_name_neq.

  destruct Hin as [Hin Hneq].
  apply Hineqm; auto.
Qed.

(* ============================================================================= *)

Lemma partition_interaction_stateless3 : 
  forall G GL GR m v rho s1 sigma2 s1d sigma4,
    G |-part GL (+) GR
    ->
    ValName (m) = v
    ->
    ValName (dual_name m) <> v
    ->
    GL |-v m : TChannel s1
    ->
    GR |-v (dual_name m) : TChannel s1d 
    ->
    GR |-v v : rho
    ->
    free_value_or_token v
    ->
    (CTX.In (ValName m, TChannel s1) GR -> TChannel s1 = sigma2)
    ->
    (CTX.In (ValName (dual_name m), TChannel s1d) GL -> TChannel s1d = sigma4)
    ->
    |-st rho
    -> 
    (CTX.union
      (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL))
      (ctx_replace (dual_name m) (TChannel s1d) sigma4 GR ))
    |-part (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL)) (+) (ctx_replace (dual_name m) (TChannel s1d) sigma4 GR).
Proof.
  intros G GL GR m v rho s1 sigma2 s1d sigma4 Hpart Heqmv Hneqdm Hlookupm Hlookupdm Hlookupv Hfvot Hineqm Hineqdm Hstateless; subst.
  assert (rho = TChannel s1); [|subst].
  inversion Hpart; subst.
  inversion Hlookupm; subst.
  inversion Hlookupv; subst.
  inversion H0; subst.

  rewrite (H7 m (TChannel s1) rho); auto; rewrite H; rewrite CTXFacts.union_iff; [left|right]; auto.

  assert (TChannel s1 = sigma2).
  apply Hineqm.
  inversion Hlookupv; subst; auto.

  subst.

  inversion Hlookupm; subst.

  assert (free_value m).
  eapply channel_lookup_yields_free_value; eauto.

  eapply ctx_equal_part; [
    | rewrite ctx_add_value_free_value; [rewrite ctx_add_idem; [rewrite ctx_replace_idem; [rewrite CTXProperties.union_sym; reflexivity|auto] | rewrite ctx_replace_idem; auto] | auto]
    | rewrite ctx_add_value_free_value; [rewrite ctx_add_idem; [rewrite ctx_replace_idem; [reflexivity|auto] | rewrite ctx_replace_idem; auto] | auto]
    | reflexivity
  ].
  apply partition_comm.
  eapply ctx_replace_pre_union.
  apply partition_comm.
  eauto.

  inversion Hlookupdm; subst; auto.
  auto.
Qed.

(* ============================================================================= *)

Lemma partition_interaction_stateless : 
  forall G GL GR m v rho s1 sigma2 s1d sigma4,
    G |-part GL (+) GR
    ->
    ValName (dual_name m) <> v
    ->
    GL |-v m : TChannel s1
    ->
    GR |-v (dual_name m) : TChannel s1d 
    ->
    GR |-v v : rho
    ->
    free_value_or_token v
    ->
    (CTX.In (ValName m, TChannel s1) GR -> TChannel s1 = sigma2)
    ->
    (CTX.In (ValName (dual_name m), TChannel s1d) GL -> TChannel s1d = sigma4)
    ->
    |-st rho
    -> 
    (CTX.union
      (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL))
      (ctx_replace (dual_name m) (TChannel s1d) sigma4 GR ))
    |-part (ctx_add_value v rho (ctx_replace m (TChannel s1) sigma2 GL)) (+) (ctx_replace (dual_name m) (TChannel s1d) sigma4 GR).
Proof.
  intros G GL GR m v rho s1 sigma2 s1d sigma4 Hpart Hneqdm Hlookupm Hlookupdm Hlookupv Hfvot Hineqm Hineqdm Hstateless.
  destruct (value_dec (ValName m) v); [
    subst; apply partition_interaction_stateless3 with (G:=G); auto; eapply channel_lookup_yields_free_value; eauto
    | destruct Hfvot; [
      apply partition_interaction_stateless1 with (G:=G); auto
      | apply partition_interaction_stateless2 with (G:=G); eauto
    ]
  ].
Qed.

(* ============================================================================= *)

Lemma balanced_partition :
  forall G GL GR,
    G |-part GL (+) GR
    -> 
    balanced G
    ->
    balanced GL.
Proof.
  intros G GL GR Hpart Hprespre.
  pose (part_is_subset_left _ _ _ Hpart) as Hsubseteq.
  inversion Hprespre.
  constructor; unfold ctx_matched_names in *; unfold all_free_names in *.
  intros nm1 nm2 rho sigma Heq Hin1 Hin2; apply (H nm1 nm2); auto.
  split.
  destruct H0 as [H0 H1].
  intros u rho Hin; apply (H0 u rho); auto.

  destruct H0 as [H0 H1].
  intros v rho Hin; apply (H1 v rho); auto.
Qed.

(* ============================================================================= *)

Lemma ctx_preservation_partition : 
  forall G GL GL' GR vv,
    G |-part GL (+) GR
    ->
    ctx_preservation GL GL' vv
    ->
    ((CTX.union GL' GR) |-part GL' (+) GR) /\ ctx_preservation G (CTX.union GL' GR) vv.
Proof.
  intros G GL GL' GR vv Hpart Hpres.
  inversion Hpart; subst.
  inversion Hpres; subst.

  split.
  eapply ctx_equal_part; eauto ; [rewrite H2|symmetry|reflexivity]; auto.
  apply CPNoInteraction; rewrite H2; symmetry; auto.

  split.
  eapply ctx_equal_part; [ | rewrite H6; reflexivity | rewrite H6; reflexivity | reflexivity ].
  eapply ctx_replace_pre_union.
  eapply ctx_replace_pre_union.
  eauto.
  auto.
  intros Hin.
  destruct (H1 (dual_name nm1) (TChannel (SDual s))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]]; try solve [contradict Hu; auto].
  inversion Hu; subst; rewrite (H8 _ _ (TRDual _ _ _ H5)); auto.
  unfold ctx_replace.
  apply CTXFacts.add_2; apply CTXFacts.remove_2; auto.
  destruct nm1; discriminate.
  intros Hin.
  destruct (H1 nm1 (TChannel s)) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]]; try solve [contradict Hu; auto].
  inversion Hu; subst; rewrite (H8 _ _ H5); auto.
  
  pose (part_is_subset_left _ _ _ Hpart) as Hsubseteq1.
  pose (part_is_subset_right _ _ _ Hpart) as Hsubseteq2.
  apply (CPInteraction _ _ nm1 (dual_name nm1) s m t vv eq_refl); auto.
  rewrite H6.

  intros a; destruct a.
  unfold ctx_replace.
  (repeat (rewrite CTXFacts.union_iff || rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)).
  split; intros Hin;
  repeat (match goal with
            | [ H : _ \/ _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ |- _ /\ _ ] => split
            | [ H : (_, _) = (_, _) |- _ ] => injection H; intros; subst; clear H
            | [ H : ?X <> ?Y |- (?X, _) = (?Y, _) \/ _ ] => right
            | [ H : ?X <> ?Y |- (?X, _) <> (?Y, _) ] => contradict H; injection H; intros; subst; clear H
          end);
  try solve [tauto].

  right; split; [right; split; auto|auto].

  destruct (CTX.E.eq_dec (ValName (nm1), TChannel (s)) (v, t0)).
  injection e; intros; subst; clear e.
  left; auto.
  assert (|-st TChannel (s)).
  inversion Hpart; subst.
  destruct (H10 nm1 (TChannel (s))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H8; subst.
  rewrite (H10 _ _ H5); auto.

  right; split; auto.
  destruct (CTX.E.eq_dec (ValName (dual_name nm1), TChannel (SDual s)) (v, t0)).
  injection e; intros; subst; clear e.
  left; auto.
  assert (|-st TChannel (SDual s)).
  inversion Hpart; subst.
  destruct (H10 (dual_name nm1) (TChannel (SDual s))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H8; subst.
  rewrite (H10 _ _ (TRDual _ _ _ H5)); auto.
  right; split; auto.

  rewrite H in H2.
  rewrite CTXFacts.union_iff in H2; destruct H2 as [Hu|Hu]; [|right; auto].
  left; right; split; auto.
Qed.

(* ============================================================================= *)

(* This is the only part of the subject reduction result that depends on knowing all transitions for SDual. *)
Lemma sdual_transition : 
  forall s m t,
    (SDual s -- m --> t)
    -> 
    exists t2,
      ((s -- m_dual m --> t2) /\ (t = SDual t2)).
Proof.
  intros s m t Htrans.
  inversion Htrans; subst.
  destruct m0; simpl in *; exists t0; split; auto.
Qed.

(* ============================================================================= *)

Lemma ctx_preservation_stateful : 
  forall G GL GR nm1 nm2 s1 t1 s2 t2 a v rho vo,
    dual_name nm1 = nm2
    ->
    ValName nm2 <> v
    ->
    G |-part GL (+) GR
    ->
    CTX.In (ValName nm1, TChannel s1) GL
    ->
    CTX.In (ValName nm2, TChannel s2) GR
    ->
    GR |-v v : rho
    ->
    dual_types_transition2 (TChannel s1) (TChannel s2) a (TChannel t1) (TChannel t2)   
    ->
    mk_obs nm1 v vo
    ->
    rho = a
    ->
    balanced G
    ->
    ctx_preservation 
      (CTX.union GL GR)
      (CTX.union 
        (ctx_add_value v rho
          (ctx_replace nm1 (TChannel s1) (TChannel t1) 
            GL))
        (ctx_replace nm2 (TChannel s2) (TChannel t2)
          (CTX.remove (v, rho) 
            GR)))
      vo.
Proof.
  intros G GL GR nm1 nm2 s1 t1 s2 t2 a v rho vo Heqn Hneqmv Hpart Hin1 Hin2 Hlookupv Hdualtt Hvo Heqrho HprespreG; subst.
  inversion Hdualtt; subst.

  Case "dual 1"%string.
  apply (CPInteraction _ _ nm1 (dual_name nm1) s1 (MInp a) t1); auto; try rewrite CTXFacts.union_iff.
  left; auto.
  right; auto.

  inversion Hlookupv; subst.

  SCase "v is in G"%string.
  destruct (value_dec nm1 v); [subst|].

  SSCase "v = nm1"%string.
  assert (a = TChannel s1) as Hm1eq; [|rewrite Hm1eq in *].
  inversion Hpart; subst.
  inversion H2; subst.
  apply (H6 nm1 a (TChannel s1)); auto; rewrite H1; rewrite CTXFacts.union_iff; [right; auto | left; auto].
  assert (TChannel s1 = TChannel t1) as Hu; [|injection Hu; intros; subst; clear Hu].
  assert (|-st TChannel s1).
  inversion Hpart; subst.
  destruct (H3 nm1 (TChannel s1)) as [Hu|Hu]; [contradict Hu|destruct Hu as [Hu|Hu]; [contradict Hu|]]; auto.
  inversion H1; subst.
  rewrite (H3 _ _ H4); auto.
  simpl.
  rewrite ctx_add_idem.
  rewrite ctx_replace_idem; auto.
  rewrite ctx_replace_idem; auto.
  rewrite ctx_replace_idem; auto.
  rewrite ctx_replace_idem; auto.
  rewrite ctx_remove_idem; auto.
  reflexivity.
  rewrite CTXFacts.union_iff; tauto.
  rewrite ctx_replace_idem; auto.
  rewrite CTXFacts.union_iff; tauto.
  rewrite CTXFacts.union_iff; tauto.
  rewrite CTXFacts.remove_iff; split; auto.
  intros e; injection e; intros.
  destruct nm1; discriminate H2.
  rewrite ctx_replace_idem; auto.

  SSCase "v <> nm1"%string.
  eapply CTX_eq_trans; [
    rewrite ctx_add_value_free_value; [
      rewrite add_replace_comm; [reflexivity|auto]
      | inversion H; eapply H1; eauto
    ]
    |
  ].
  intros a'; destruct a'.
  unfold ctx_replace.
  (repeat (rewrite CTXFacts.union_iff || rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)).
  split; intros Hin;
  repeat (match goal with
            | [ H : _ \/ _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ |- _ /\ _ ] => split
            | [ H : (_, _) = (_, _) |- _ ] => injection H; intros; subst; clear H
            | [ H : ?X <> ?Y |- (?X, _) = (?Y, _) \/ _ ] => right
            | [ H : ?X <> ?Y |- (?X, _) <> (?Y, _) ] => contradict H; injection H; intros; subst; clear H
          end);
  try solve [tauto].

  right; split; auto.
  destruct (CTX.E.eq_dec (ValName (dual_name nm1), TChannel (SDual s1)) (v0, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel (SDual s1)).
  inversion Hpart; subst.
  destruct (H6 (dual_name nm1) (TChannel (SDual s1))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H3; subst.
  rewrite (H6 _ _ (TRDual _ _ _ H4)); auto.

  right; split; [left; auto|].

  contradict n; injection n; intros; destruct nm1; simpl in H2; discriminate H2. 

  destruct (CTX.E.eq_dec (ValName (nm1), TChannel (s1)) (v0, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel (s1)).
  inversion Hpart; subst.
  destruct (H7 nm1 (TChannel (s1))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H5; subst.
  rewrite (H7 _ _ H4); auto.

  destruct (CTX.E.eq_dec (v, a) (v0, t)).
  injection e; intros; subst; clear e.
  left; right; split; [left; auto|].
  contradict n; injection n; intros; subst; auto.
  tauto.

  SCase "v is a token"%string.
  eapply CTX_eq_trans; [
    rewrite ctx_add_value_token; reflexivity
    |
  ].
  intros a; destruct a.
  unfold ctx_replace.
  (repeat (rewrite CTXFacts.union_iff || rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)).
  split; intros Hin; 
  repeat (match goal with
            | [ H : _ \/ _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ |- _ /\ _ ] => split
            | [ H : (_, _) = (_, _) |- _ ] => injection H; intros; subst; clear H
            | [ H : ?X <> ?Y |- (?X, _) = (?Y, _) \/ _ ] => right
            | [ H : ?X <> ?Y |- (?X, _) <> (?Y, _) ] => contradict H; injection H; intros; subst; clear H
          end);
  try solve [tauto].

  right; split; auto.
  destruct (CTX.E.eq_dec (ValName (dual_name nm1), TChannel (SDual s1)) (v, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel (SDual s1)).
  inversion Hpart; subst.
  destruct (H5 (dual_name nm1) (TChannel (SDual s1))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H2; subst.
  rewrite (H5 _ _ (TRDual _ _ _ H4)); auto.

  right; split; [left; auto|].
  intros Hu; injection Hu; intros; destruct nm1; simpl in H1; discriminate H1.

  destruct (CTX.E.eq_dec (ValName (nm1), TChannel (s1)) (v, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel (s1)).
  inversion Hpart; subst.
  destruct (H6 nm1 (TChannel (s1))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H3; subst.
  rewrite (H6 _ _ H4); auto.

  right; right; split; [split|]; auto.
  inversion H; subst.
  specialize (H3 v t H0); destruct H3; discriminate.

  eapply mk_obs_imp_obs_msg_nm; eauto.
  simpl.
  apply partition_comm in Hpart.
  apply partition_lookup_left with (1:=Hpart); auto.



  Case "dual 2"%string.
  apply (CPInteraction _ _ (dual_name nm1) nm1 s2 (MOut a) t2); auto; try rewrite CTXFacts.union_iff.
  destruct nm1; simpl; reflexivity.
  right; auto.
  left; auto.

  inversion Hlookupv; subst.

  SCase "v is in G"%string.
  destruct (value_dec nm1 v); [subst|].

  SSCase "v = nm1"%string.
  assert (a = TChannel (SDual s2)); [|subst].
  inversion Hpart; subst.
  inversion H2; subst.
  apply (H6 nm1 a (TChannel (SDual s2))); auto; rewrite H1; rewrite CTXFacts.union_iff; [right; auto | left; auto].
  assert (TChannel (SDual s2) = TChannel (SDual t2)) as Hu; [|injection Hu; intros; subst; clear Hu].
  assert (|-st TChannel (SDual s2)).
  inversion Hpart; subst.
  destruct (H3 nm1 (TChannel (SDual s2))) as [Hu|Hu]; [contradict Hu|destruct Hu as [Hu|Hu]; [contradict Hu|]]; auto.
  inversion H1; subst.
  rewrite (H3 _ _ (TRDual _ _ _ H4)); auto.
  simpl.
  rewrite ctx_add_idem.
  rewrite ctx_replace_idem; auto.
  rewrite ctx_replace_idem; auto.
  rewrite ctx_replace_idem; auto.
  rewrite ctx_replace_idem; auto.
  rewrite ctx_remove_idem; auto.
  reflexivity.
  rewrite CTXFacts.union_iff; tauto.
  rewrite ctx_replace_idem; auto.
  rewrite CTXFacts.union_iff; tauto.
  rewrite CTXFacts.union_iff; tauto.
  rewrite CTXFacts.remove_iff; split; auto.
  intros e; injection e; intros.
  destruct nm1; discriminate H2.
  rewrite ctx_replace_idem; auto.

  SSCase "v <> nm1"%string.
  eapply CTX_eq_trans; [
    rewrite ctx_add_value_free_value; [
      rewrite add_replace_comm; [reflexivity|auto]
      | inversion H; eapply H1; eauto
    ]
    |
  ].
  intros a'; destruct a'.
  unfold ctx_replace.
  (repeat (rewrite CTXFacts.union_iff || rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)).
  split; intros Hin;
  repeat (match goal with
            | [ H : _ \/ _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ |- _ /\ _ ] => split
            | [ H : (_, _) = (_, _) |- _ ] => injection H; intros; subst; clear H
            | [ H : ?X <> ?Y |- (?X, _) = (?Y, _) \/ _ ] => right
            | [ H : ?X <> ?Y |- (?X, _) <> (?Y, _) ] => contradict H; injection H; intros; subst; clear H
          end);
  try solve [tauto].

  right; split; [left; auto|].
  contradict n; injection n; intros; destruct nm1; discriminate H2.

  destruct (CTX.E.eq_dec (ValName (dual_name nm1), TChannel (s2)) (v0, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel (s2)).
  inversion Hpart; subst.
  destruct (H6 (dual_name nm1) (TChannel (s2))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H3; subst.
  rewrite (H6 _ _ H4); auto.

  right; split; auto.
  destruct (CTX.E.eq_dec (ValName (nm1), TChannel (SDual s2)) (v0, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel (SDual s2)).
  inversion Hpart; subst.
  destruct (H7 (nm1) (TChannel (SDual s2))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H5; subst.
  rewrite (H7 _ _ (TRDual _ _ _ H4)); auto.

  destruct (CTX.E.eq_dec (v, a) (v0, t)).
  injection e; intros; subst; clear e.
  left; right; split; [left; auto|].
  contradict n; injection n; intros; subst; auto.
  tauto.


  SCase "v is a token"%string.
  eapply CTX_eq_trans; [
    rewrite ctx_add_value_token; reflexivity
    |
  ].
  intros a; destruct a.
  unfold ctx_replace.
  (repeat (rewrite CTXFacts.union_iff || rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)).
  split; intros Hin; 
  repeat (match goal with
            | [ H : _ \/ _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ |- _ /\ _ ] => split
            | [ H : (_, _) = (_, _) |- _ ] => injection H; intros; subst; clear H
            | [ H : ?X <> ?Y |- (?X, _) = (?Y, _) \/ _ ] => right
            | [ H : ?X <> ?Y |- (?X, _) <> (?Y, _) ] => contradict H; injection H; intros; subst; clear H
          end);
  try solve [tauto].

  right; split; [left; auto|].
  intros Hu; injection Hu; intros; destruct nm1; simpl in H1; discriminate H1.

  destruct (CTX.E.eq_dec (ValName (dual_name nm1), TChannel s2) (v, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel s2).
  inversion Hpart; subst.
  destruct (H5 (dual_name nm1) (TChannel (s2))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H2; subst.
  rewrite (H5 _ _ H4); auto.

  right; split; auto.
  destruct (CTX.E.eq_dec (ValName (nm1), TChannel (SDual s2)) (v, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel (SDual s2)).
  inversion Hpart; subst.
  destruct (H6 nm1 (TChannel (SDual s2))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H3; subst.
  rewrite (H6 _ _ (TRDual _ _ _ H4)); auto.

  right; right; split; [split|]; auto.
  inversion H; subst.
  specialize (H3 v t H0); destruct H3; discriminate.


  eapply mk_obs_imp_obs_msg_conm; eauto.
  simpl.
  apply partition_comm in Hpart.
  apply partition_lookup_left with (1:=Hpart); auto.


Qed.

(* ============================================================================= *)

Lemma ctx_preservation_stateless : 
  forall G GL GR nm1 nm2 s1 t1 s2 t2 a v rho vo,
    dual_name nm1 = nm2
    ->
    ValName nm2 <> v
    ->
    G |-part GL (+) GR
    ->
    CTX.In (ValName nm1, TChannel s1) GL
    ->
    CTX.In (ValName nm2, TChannel s2) GR
    ->
    GR |-v v : rho
    ->
    dual_types_transition2 (TChannel s1) (TChannel s2) a (TChannel t1) (TChannel t2)
    ->
    mk_obs nm1 v vo
    ->
    rho = a
    ->
    balanced G
    ->
    ctx_preservation 
      (CTX.union GL GR)
      (CTX.union 
        (ctx_add_value v rho
          (ctx_replace nm1 (TChannel s1) (TChannel t1) 
            GL))
        (ctx_replace nm2 (TChannel s2) (TChannel t2)
          GR))
      vo.
Proof.
  intros G GL GR nm1 nm2 s1 t1 s2 t2 a v rho vo Heqn Hneqmv Hpart Hin1 Hin2 Hlookupv Hdualtt Hvo Heqrho HprespreG; subst.
  inversion Hdualtt; subst.

  Case "dual 1"%string.
  apply (CPInteraction _ _ nm1 (dual_name nm1) s1 (MInp a) t1); auto; try rewrite CTXFacts.union_iff.
  left; auto.
  right; auto.

  inversion Hlookupv; subst.

  SCase "v is in G"%string.
  destruct (value_dec nm1 v); [subst|].

  SSCase "v = nm1"%string.
  assert (a = TChannel s1); [|subst].
  inversion Hpart; subst.
  inversion H2; subst.
  apply (H6 nm1 a (TChannel s1)); auto; rewrite H1; rewrite CTXFacts.union_iff; [right; auto | left; auto].
  assert (TChannel s1 = TChannel t1) as Hu; [|injection Hu; intros; subst; clear Hu].
  assert (|-st TChannel s1).
  inversion Hpart; subst.
  destruct (H3 nm1 (TChannel s1)) as [Hu|Hu]; [contradict Hu|destruct Hu as [Hu|Hu]; [contradict Hu|]]; auto.
  inversion H1; subst.
  rewrite (H3 _ _ H4); auto.
  simpl.
  rewrite ctx_add_idem.
  rewrite ctx_replace_idem; auto.
  rewrite ctx_replace_idem; auto.
  rewrite ctx_replace_idem; auto.
  rewrite ctx_replace_idem; auto.
  reflexivity.
  rewrite CTXFacts.union_iff; tauto.
  rewrite ctx_replace_idem; auto.
  rewrite CTXFacts.union_iff; tauto.
  rewrite CTXFacts.union_iff; tauto.
  apply CTXFacts.add_1; reflexivity.

  SSCase "v <> nm1"%string.
  eapply CTX_eq_trans; [
    rewrite ctx_add_value_free_value; [
      rewrite add_replace_comm; [reflexivity|auto]
      | inversion H; eapply H1; eauto
    ]
    |
  ].
  intros a'; destruct a'.
  unfold ctx_replace.
  (repeat (rewrite CTXFacts.union_iff || rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)).
  split; intros Hin;
  repeat (match goal with
            | [ H : _ \/ _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ |- _ /\ _ ] => split
            | [ H : (_, _) = (_, _) |- _ ] => injection H; intros; subst; clear H
            | [ H : ?X <> ?Y |- (?X, _) = (?Y, _) \/ _ ] => right
            | [ H : ?X <> ?Y |- (?X, _) <> (?Y, _) ] => contradict H; injection H; intros; subst; clear H
          end);
  try solve [tauto].

  right; split; auto.
  destruct (CTX.E.eq_dec (ValName (dual_name nm1), TChannel (SDual s1)) (v0, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel (SDual s1)).
  inversion Hpart; subst.
  destruct (H6 (dual_name nm1) (TChannel (SDual s1))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H3; subst.
  rewrite (H6 _ _ (TRDual _ _ _ H4)); auto.

  right; split; [left; auto|].

  contradict n; injection n; intros; destruct nm1; simpl in H2; discriminate H2.

  destruct (CTX.E.eq_dec (ValName (nm1), TChannel (s1)) (v0, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel (s1)).
  inversion Hpart; subst.
  destruct (H6 nm1 (TChannel (s1))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H3; subst.
  rewrite (H6 _ _ H4); auto.

  SCase "v is a token"%string.
  eapply CTX_eq_trans; [
    rewrite ctx_add_value_token; reflexivity
    |
  ].
  intros a; destruct a.
  unfold ctx_replace.
  (repeat (rewrite CTXFacts.union_iff || rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)).
  split; intros Hin;
  repeat (match goal with
            | [ H : _ \/ _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ |- _ /\ _ ] => split
            | [ H : (_, _) = (_, _) |- _ ] => injection H; intros; subst; clear H
            | [ H : ?X <> ?Y |- (?X, _) = (?Y, _) \/ _ ] => right
            | [ H : ?X <> ?Y |- (?X, _) <> (?Y, _) ] => contradict H; injection H; intros; subst; clear H
          end);
  try solve [tauto].

  right; split; auto.
  destruct (CTX.E.eq_dec (ValName (dual_name nm1), TChannel (SDual s1)) (v, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel (SDual s1)).
  inversion Hpart; subst.
  destruct (H5 (dual_name nm1) (TChannel (SDual s1))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H2; subst.
  rewrite (H5 _ _ (TRDual _ _ _ H4)); auto.

  right; split; [left; auto|].
  intros Hu; injection Hu; intros; destruct nm1; simpl in H1; discriminate H1.

  destruct (CTX.E.eq_dec (ValName (nm1), TChannel (s1)) (v, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel (s1)).
  inversion Hpart; subst.
  destruct (H5 nm1 (TChannel (s1))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H2; subst.
  rewrite (H5 _ _ H4); auto.

  eapply mk_obs_imp_obs_msg_nm; eauto.
  apply partition_comm in Hpart.
  apply partition_lookup_left with (1:=Hpart); auto.


  Case "dual 2"%string.
  apply (CPInteraction _ _ (dual_name nm1) nm1 s2 (MOut a) t2); auto; try rewrite CTXFacts.union_iff.
  destruct nm1; simpl; reflexivity.
  right; auto.
  left; auto.

  inversion Hlookupv; subst.

  SCase "v is in G"%string.
  destruct (value_dec nm1 v); [subst|].

  SSCase "v = nm1"%string.
  assert (a = TChannel (SDual s2)); [|subst].
  inversion Hpart; subst.
  inversion H2; subst.
  apply (H6 nm1 a (TChannel (SDual s2))); auto; rewrite H1; rewrite CTXFacts.union_iff; [right; auto | left; auto].
  assert (TChannel (SDual s2) = TChannel (SDual t2)) as Hu; [|injection Hu; intros; subst; clear Hu].
  assert (|-st TChannel (SDual s2)).
  inversion Hpart; subst.
  destruct (H3 nm1 (TChannel (SDual s2))) as [Hu|Hu]; [contradict Hu|destruct Hu as [Hu|Hu]; [contradict Hu|]]; auto.
  inversion H1; subst.
  rewrite (H3 _ _ (TRDual _ _ _ H4)); auto.
  simpl.
  rewrite ctx_add_idem.
  rewrite ctx_replace_idem; auto.
  rewrite ctx_replace_idem; auto.
  rewrite ctx_replace_idem; auto.
  rewrite ctx_replace_idem; auto.
  reflexivity.
  rewrite CTXFacts.union_iff; tauto.
  rewrite ctx_replace_idem; auto.
  rewrite CTXFacts.union_iff; tauto.
  rewrite CTXFacts.union_iff; tauto.
  apply CTXFacts.add_1; reflexivity.

  SSCase "v <> nm1"%string.
  eapply CTX_eq_trans; [
    rewrite ctx_add_value_free_value; [
      rewrite add_replace_comm; [reflexivity|auto]
      | inversion H; eapply H1; eauto
    ]
    |
  ].
  intros a'; destruct a'.
  unfold ctx_replace.
  (repeat (rewrite CTXFacts.union_iff || rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)).
  split; intros Hin;
  repeat (match goal with
            | [ H : _ \/ _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ |- _ /\ _ ] => split
            | [ H : (_, _) = (_, _) |- _ ] => injection H; intros; subst; clear H
            | [ H : ?X <> ?Y |- (?X, _) = (?Y, _) \/ _ ] => right
            | [ H : ?X <> ?Y |- (?X, _) <> (?Y, _) ] => contradict H; injection H; intros; subst; clear H
          end);
  try solve [tauto].

  right; split; [left; auto|].
  contradict n; injection n; intros; destruct nm1; discriminate H2.

  destruct (CTX.E.eq_dec (ValName (dual_name nm1), TChannel (s2)) (v0, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel (s2)).
  inversion Hpart; subst.
  destruct (H6 (dual_name nm1) (TChannel (s2))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H3; subst.
  rewrite (H6 _ _ H4); auto.

  right; split; auto.
  destruct (CTX.E.eq_dec (ValName (nm1), TChannel (SDual s2)) (v0, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel (SDual s2)).
  inversion Hpart; subst.
  destruct (H6 (nm1) (TChannel (SDual s2))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H3; subst.
  rewrite (H6 _ _ (TRDual _ _ _ H4)); auto.

  SCase "v is a token"%string.
  eapply CTX_eq_trans; [
    rewrite ctx_add_value_token; reflexivity
    |
  ].
  intros a; destruct a.
  unfold ctx_replace.
  (repeat (rewrite CTXFacts.union_iff || rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)).
  split; intros Hin;
  repeat (match goal with
            | [ H : _ \/ _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ |- _ /\ _ ] => split
            | [ H : (_, _) = (_, _) |- _ ] => injection H; intros; subst; clear H
            | [ H : ?X <> ?Y |- (?X, _) = (?Y, _) \/ _ ] => right
            | [ H : ?X <> ?Y |- (?X, _) <> (?Y, _) ] => contradict H; injection H; intros; subst; clear H
          end);
  try solve [tauto].

  right; split; [left; auto|].
  intros Hu; injection Hu; intros; destruct nm1; simpl in H1; discriminate H1.

  destruct (CTX.E.eq_dec (ValName (dual_name nm1), TChannel s2) (v, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel s2).
  inversion Hpart; subst.
  destruct (H5 (dual_name nm1) (TChannel (s2))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H2; subst.
  rewrite (H5 _ _ H4); auto.

  right; split; auto.
  destruct (CTX.E.eq_dec (ValName (nm1), TChannel (SDual s2)) (v, t)); [left|right;tauto].
  injection e; intros; subst; clear e.
  assert (|-st TChannel (SDual s2)).
  inversion Hpart; subst.
  destruct (H5 nm1 (TChannel (SDual s2))) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; auto]; contradict Hu; auto.
  inversion H2; subst.
  rewrite (H5 _ _ (TRDual _ _ _ H4)); auto.


  eapply mk_obs_imp_obs_msg_conm; eauto.
  simpl.
  apply partition_comm in Hpart.
  apply partition_lookup_left with (1:=Hpart); auto.

Qed.

(* ============================================================================= *)
  
Lemma ctx_preservation_eq : 
  forall G1a G1b G2b G2a vo,
    CTX.eq G1a G1b
    ->
    ctx_preservation G1b G2b vo
    ->
    CTX.eq G2b G2a
    ->
    ctx_preservation G1a G2a vo.
Proof.
  intros G1a G1b G2b G2a vo Heq1 Hpres Heq2.
  inversion Hpres; subst; clear Hpres.
  apply CPNoInteraction; rewrite Heq1; rewrite <- Heq2; auto.
  apply (CPInteraction _ _ nm1 (dual_name nm1) s m t); auto.
  rewrite Heq1; auto.
  rewrite Heq1; auto.
  rewrite <- Heq2; auto.
  rewrite H3; auto.
  unfold ctx_replace.
  apply add_cong.
  apply remove_cong.
  apply add_cong.
  apply remove_cong.
  symmetry; auto.
Qed.

(* ============================================================================= *)

Lemma dual_types_spec : 
  forall s1 s2 m t2,
    dual_types (TChannel s1) (TChannel s2)
    ->
    transition s2 m t2
    -> 
    exists t1, transition s1 (m_dual m) t1 /\ dual_types (TChannel t1) (TChannel t2).
Proof.
  intros s1 s2 m t2 Hdual Htrans.
  inversion Hdual; subst.
  apply sdual_transition in Htrans.
  destruct Htrans as [t1 Htrans]; destruct Htrans as [Htrans Heq]; subst.
  exists t1; split; auto.
  constructor.
  apply TRDual in Htrans.
  exists (SDual t2); split; auto.
  constructor.
Qed.

(* ============================================================================= *)

Lemma dual_types_transition2_spec
     : forall (s1 s2 : session) (a : type) (t1 t2 : session),
       dual_types_transition2 (TChannel s1) (TChannel s2) a (TChannel t1) (TChannel t2)
       ->
       (transition s2 (MOut a) t2) 
       ->
       (s1 -- (MInp a) --> t1) /\ dual_types (TChannel t1) (TChannel t2).
Proof.
  intros s1 s2 a t1 t2 Hdtt Htrans.
  inversion Hdtt; subst; split; auto; try constructor.
  replace (MInp a) with (m_dual (m_dual (MInp a))); [|reflexivity].
  apply TRDual; auto.
Qed.

(* ============================================================================= *)

Lemma ctx_preservation_extension : 
  forall G1 i s,
    ~ In i (free_ids_context G1)
    ->
    balanced G1
    ->
    balanced (CTX.add (ValName (Nm (Free i)), TChannel s) (CTX.add (ValName (CoNm (Free i)), TChannel (SDual s)) G1)).
Proof.
  intros G1 i s Hin Hprespre; split; [|split].

  intros nm1 nm2 rho sigma Heq Hin1 Hin2; subst.
  (repeat rewrite CTXFacts.add_iff in *); 
  (destruct Hin1 as [Hin1|Hin1]; [|destruct Hin1 as [Hin1|Hin1]]);
  (destruct Hin2 as [Hin2|Hin2]; [|destruct Hin2 as [Hin2|Hin2]]);
  (try (injection Hin1; intros));
  (try (injection Hin2; intros));
  (try solve [subst; constructor]);
  (try solve [subst; contradict Hin; rewrite free_ids_context_iff; eexists; eexists; split; eauto; simpl; auto]);
  (try solve [rewrite <- H0 in H2; discriminate H2]);
  (try solve
    [subst; contradict Hin; rewrite free_ids_context_iff; eexists; eexists; split; eauto; simpl; auto;
     destruct nm1; try solve [injection H0; intros; subst; simpl; auto]; try solve [simpl in *; discriminate H0]] ).
  inversion Hprespre.
  unfold ctx_matched_names in H.
  apply (H _ _ _ _ eq_refl Hin1 Hin2).

  
  intros u rho Hin1.
  (repeat rewrite CTXFacts.add_iff in *).
  destruct Hin1 as [Hin1|Hin1]; [|destruct Hin1 as [Hin1|Hin1]];
    try solve [injection Hin1; intros; subst; constructor].
  inversion Hprespre.
  destruct H0 as [H0 _].
  unfold all_free_names in H0.
  apply (H0 u rho); auto.


  intros u rho Hin1.
  (repeat rewrite CTXFacts.add_iff in *).
  destruct Hin1 as [Hin1|Hin1]; [|destruct Hin1 as [Hin1|Hin1]];
    try solve [injection Hin1; intros; subst; eexists; reflexivity].
  destruct Hprespre as [_ Hprespre]; destruct Hprespre as [_ Hchans].
  apply (Hchans u rho Hin1).
Qed.


(* ============================================================================= *)

Lemma ctx_preservation_free_ids_context :
  forall i G1 G2 vo,
    ctx_preservation G1 G2 vo
    -> 
    ~ In i (free_ids_context G1)
    ->
    ~ In i (free_ids_context G2).
Proof.
  intros i G1 G2 vo Hpres Hnotini.
  destruct Hpres.
  contradict Hnotini.
  rewrite free_ids_context_iff in *.
  destruct Hnotini as [u Hnotini]; destruct Hnotini as [rho Hin]; destruct Hin as [Hin1 Hin2].
  exists u; exists rho; split; auto; rewrite <- H; auto.
  contradict Hnotini.
  rewrite free_ids_context_iff in *.
  destruct Hnotini as [u Hnotini]; destruct Hnotini as [rho Hnotini]; destruct Hnotini as [Hin1 Hin2].
  rewrite H3 in Hin1.
  unfold ctx_replace in Hin1.
  (repeat rewrite CTXFacts.add_iff in Hin1 || rewrite CTXFacts.remove_iff in Hin1).
  (repeat match goal with
            | [ H : _ \/ _ |- _ ] => destruct H
            | [ H : _ /\ _ |- _ ] => destruct H
            | [ H : (_, _) = (_, _) |- _ ] => injection H; intros; subst; clear H
          end); 
  eexists; eexists; split; eauto.  
  destruct nm1; eauto.
Qed.

(* ============================================================================= *)

Lemma ctx_preservation_extension_inverse :
  forall x nm1 nm2 s G1 G2 vo, 
    In x (free_ids_value (ValName nm1))
    ->
    ~ In x (free_ids_context G1)
    ->
    nm2 = dual_name nm1
    ->
    ctx_preservation
      (CTX.add (ValName nm1, TChannel s)
        (CTX.add (ValName nm2, TChannel (SDual s)) G1))
      G2 vo
    -> 
    exists G2', exists t,
      CTX.eq G2 (CTX.add (ValName nm1, TChannel t) (CTX.add (ValName nm2, TChannel (SDual t)) G2'))
      /\ 
      ( (s = t /\ ctx_preservation G1 G2' vo)
        \/ 
        (exists m, (transition s m t) /\ CTX.eq G1 G2' /\ mk_obs_msg nm1 m vo)
      ).
Proof.
  intros x nm1 nm2 s G1 G2 vo Hinxnm1 HnotinxG1 Heq Hpres; subst.
  inversion Hpres; subst; clear Hpres.
  exists G1; exists s; split; [auto | left].
  split; [auto | apply CPNoInteraction; reflexivity].

  assert (
    (nm0 = nm1 /\ s0 = s) \/
    (CTX.In (ValName nm0, TChannel s0) G1 /\ CTX.In (ValName (dual_name nm0), TChannel (SDual s0)) G1)
  ).
  (repeat rewrite CTXFacts.add_iff in H0 || rewrite CTXFacts.remove_iff in H0 ).
  destruct H0 as [Heq|H0]; [|destruct H0 as [Heq|Hu]]; try (injection Heq; intros; subst; clear Heq).
  left; tauto.
  rewrite dual_name_dual_name in H1.
  (repeat rewrite CTXFacts.add_iff in H1 || rewrite CTXFacts.remove_iff in H1 ).
  destruct H1 as [Heq|H1]; [|destruct H1 as [Heq|Hu]]; try (injection Heq; intros; clear Heq).
  contradict H; apply sdual_sdual_neq.
  contradict H; apply sdual_neq.
  contradict HnotinxG1; rewrite free_ids_context_iff.
  eexists; eexists; split; eauto.
  (repeat rewrite CTXFacts.add_iff in H1 || rewrite CTXFacts.remove_iff in H1 ).
  destruct H1 as [Heq|H1]; [|destruct H1 as [Heq|Hu2]]; try (injection Heq; intros; clear Heq).
  subst.
  contradict HnotinxG1; rewrite free_ids_context_iff.
  eexists; eexists; split; [apply Hu|destruct nm0; auto].
  assert (nm0 = nm1); [destruct nm1; destruct nm0; simpl in H0; try solve [injection H0; intros; subst; auto]; try solve [discriminate H0] | ].
  subst.
  left; tauto.
  right; tauto.

  destruct H as [Heq|Hin]; [destruct Heq; subst | destruct Hin as [Hin1 Hin2]].
  clear H0; clear H1.
  exists G1; exists t; split.
  rewrite H3.
  apply add_cong.
  unfold ctx_replace.
  eapply CTX_eq_trans; [
    rewrite <- add_remove_comm; [| destruct nm1; simpl; discriminate]
    | reflexivity
  ].
  apply add_cong.
  eapply CTX_eq_trans; [
    rewrite <- remove_remove_comm
    | reflexivity
  ].
  intros a; destruct a; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff ); split; intros Hin; try solve [tauto].
  split; [split; [right; right; auto | ] | ].
  intros Heq; injection Heq; intros; subst; contradict HnotinxG1; rewrite free_ids_context_iff; eexists; eexists; split; eauto.
  intros Heq; injection Heq; intros; subst; contradict HnotinxG1; rewrite free_ids_context_iff; eexists; eexists; split; eauto.
  destruct nm1; simpl in *; auto.
  right; exists m; split; [auto|]; split; [reflexivity | assumption].


  exists (ctx_replace nm0 (TChannel s0) (TChannel t) (ctx_replace (dual_name nm0) (TChannel (SDual s0)) (TChannel (SDual t)) G1)); exists s; split.
  rewrite H3.


  eapply CTX_eq_trans; [reflexivity | rewrite add_replace_comm].
  eapply CTX_eq_trans; [reflexivity | rewrite add_replace_comm].
  apply replace_cong.
  eapply CTX_eq_trans; [reflexivity | rewrite add_replace_comm].
  eapply CTX_eq_trans; [reflexivity | rewrite add_replace_comm].
  reflexivity.
  
  intros Heq; injection Heq; intros; subst; contradict HnotinxG1; rewrite free_ids_context_iff; eexists; eexists; split; eauto. 

  intros Heq; contradict HnotinxG1; rewrite free_ids_context_iff; subst; eexists; eexists; split; eauto.
  rewrite <- Heq; auto.
  destruct nm1; simpl; auto.

  intros Heq; injection Heq; intros; subst; contradict HnotinxG1; rewrite free_ids_context_iff; eexists; eexists; split; eauto. 
  destruct nm0; simpl; auto.

  intros Heq; injection Heq; intros; subst; contradict HnotinxG1; rewrite free_ids_context_iff; eexists; eexists; split; eauto. 
  destruct nm1; simpl; auto.

  left; split; auto.
  apply (CPInteraction _ _ nm0 (dual_name nm0) s0 m t); auto; reflexivity.
Qed.

(* ============================================================================= *)

Lemma balanced_equals : 
  forall G1 G2, CTX.eq G1 G2 -> balanced G2 -> balanced G1.
Proof.
  intros G1 G2 Heq Hpre.
  unfold balanced in *.
  destruct Hpre as [Ha Hb] ; destruct Hb as [Hb Hc] .
  repeat split.

  unfold ctx_matched_names in *.
  intros; eapply Ha; simpl in *; eauto; try rewrite <- Heq; auto.

  unfold all_free_names in *.
  intros; eapply Hb; simpl in *; eauto; try rewrite <- Heq; eauto.

  unfold names_channel_types in *.
  intros; eapply Hc; simpl in *; eauto; try rewrite <- Heq; eauto.
Qed.

Lemma ctx_replace_cases : 
  forall G u v rho sigma1 sigma2, 
    G |-wf 
    ->
    CTX.In (v, sigma1) G
    ->
    CTX.In (u, rho) (ctx_replace v sigma1 sigma2 G)  
    ->
    (u = v /\ rho = sigma2) \/ (u <> v /\ CTX.In (u, rho) G).
Proof.
  intros G u v rho sigma1 sigma2 Hwf Hinv Hinu.
  unfold ctx_replace in *.
  repeat (rewrite CTXFacts.add_iff in * || rewrite CTXFacts.remove_iff in *).
  destruct Hinu as [Hinu | Hinu].
  injection Hinu; intros; subst; clear Hinu; auto.
  destruct Hinu as [Hinu Hneq].
  right; split; auto.
  contradict Hneq; subst.
  assert (sigma1 = rho); [| subst; auto].
  inversion Hwf; eapply H0; eauto.
Qed.

Lemma ctx_replace_cases_channel_two : 
  forall G u v1 v2 rho s1 s2 t1 t2, 
    G |-wf 
    ->
    CTX.In (v1, TChannel s1) G
    ->
    CTX.In (v2, TChannel s2) G
    ->
    v1 <> v2
    ->
    CTX.In (u, rho)
    (ctx_replace v1 (TChannel s1) (TChannel t1) 
      (ctx_replace v2 (TChannel s2) (TChannel t2) 
        G))  
    ->
    (u = v1 /\ rho = TChannel t1)
    \/ (u <> v1 /\ u = v2 /\ rho = TChannel t2)
    \/ (u <> v1 /\ u <> v2 /\ CTX.In (u, rho) G).
Proof.
  intros G u v1 v2 rho s1 s2 t1 t2 Hwf Hin1 Hin2 Hneq Hinu.

  assert ((ctx_replace v2 (TChannel s2) (TChannel t2) G) |-wf ).
  apply ctx_replace_preserves_wf; auto.

  apply ctx_replace_cases in Hinu; auto.
  destruct Hinu as [Hinu | Hinu].
  left; auto.
  destruct Hinu as [Hneq2 Hinu]; apply ctx_replace_cases in Hinu; auto.
  right; destruct Hinu as [Hinu | Hinu]; auto.

  unfold ctx_replace.
  apply CTXFacts.add_2.
  apply CTXFacts.remove_2.
  contradict Hneq; injection Hneq; auto.
  auto.
Qed.


Lemma ctx_preservation_preserves_balanced : 
  forall G1 G2 vo,
    G1 |-wf 
    ->
    ctx_preservation G1 G2 vo
    -> 
    balanced G1
    ->
    balanced G2.
Proof.
  intros G1 G2 vo Hwf Hpres Hpre.

  inversion Hpres; subst.
  eapply balanced_equals; eauto.

  unfold balanced in *.
  destruct Hpre as [Ha Hb] ; destruct Hb as [Hb Hc] .
  repeat split.

  unfold ctx_matched_names in *.
  intros.
  subst.
  rewrite H3 in H5.
  rewrite H3 in H6.

  assert (ValName nm1 <> ValName (dual_name nm1)) as Hneq; [destruct nm1; simpl; discriminate|].
  (destruct (ctx_replace_cases_channel_two G1 _ _ _ _ _ _ _ _ Hwf H0 H1 Hneq H5); auto; clear H5);
  (destruct (ctx_replace_cases_channel_two G1 _ _ _ _ _ _ _ _ Hwf H0 H1 Hneq H6); auto; clear H6);
  repeat match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : _ \/ _ |- _ ] => destruct H
         end;
  subst; 
    (try solve [destruct nm0; destruct nm1; simpl in *; discriminate]);
    (try solve [constructor]).
  injection H; intros; subst; clear H.
  destruct nm1; simpl in *; contradict H7; reflexivity.
  injection H5; intros; subst; clear H5.
  destruct nm0; simpl in *; contradict H7; reflexivity.
  destruct nm0; destruct nm1; simpl in *; 
    (try solve [injection H6; intros; subst; clear H6; tauto]);
    (try solve [discriminate H6]).
  contradict H5.
  destruct nm0; destruct nm1; simpl in *;
    (try solve [injection H8; intros; subst; clear H8; tauto]);
    (try solve [discriminate H8]).

  eapply Ha; eauto.


  unfold all_free_names in *; intros u rho Hin.
  rewrite H3 in Hin.
  repeat unfold ctx_replace in *.
  repeat (rewrite CTXFacts.add_iff in * || rewrite CTXFacts.remove_iff in *).
  repeat match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : _ \/ _ |- _ ] => destruct H
         end.
  injection H; intros; subst; clear H; eapply Hb; apply H0.
  injection H; intros; subst; clear H; eapply Hb; apply H1.
  eapply Hb; eauto; apply CTXFacts.remove_2.
  
  unfold names_channel_types in *; intros v rho Hin.
  rewrite H3 in Hin.
  repeat unfold ctx_replace in *.
  repeat (rewrite CTXFacts.add_iff in * || rewrite CTXFacts.remove_iff in *).
  repeat match goal with
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : _ \/ _ |- _ ] => destruct H
         end.
  injection H; intros; subst; clear H; eexists; auto.
  injection H; intros; subst; clear H; eexists; auto.
  eapply Hc; apply H.
Qed.

(* ============================================================================= *)

Lemma freeid_rename_idem_value : forall i v, freeid_rename_value i i v = v.
Proof.
  intros i v.
  repeat (match goal with
           | [ v : value |- _ ] => destruct v
           | [ n : name |- _ ] => destruct n
           | [ i : id |- _ ] => destruct i
           | [ v : variable |- _ ] => destruct v
           | [ |- ?X = ?X ] => reflexivity
           | [ |- context[if ?X then _ else _ ] ] => destruct X; subst
         end; simpl).
Qed.

(* ============================================================================= *)

Lemma freeid_rename_idem_ctx : forall G i, CTX.eq (freeid_rename_ctx i i G) G.
Proof.
  apply (@CTXProperties.set_induction (fun G : CTX.t => forall i, CTX.eq (freeid_rename_ctx i i G) G)).
  intros s Hempty i.
  unfold freeid_rename_ctx.
  rewrite CTXProperties.fold_1b.
  intros a; split; intros Hin.
  rewrite CTXFacts.empty_iff in Hin; destruct Hin.
  specialize (Hempty a); tauto.
  auto.

  intros s1 s2 IH x Hnotinxs1 Hadd i.
  unfold freeid_rename_ctx.
  rewrite (@CTXProperties.fold_2 s1 s2 x _ CTX.Equal); intuition.
  unfold freeid_rename_ctx in IH.
  destruct x as [u rho]; unfold freeid_rename_ctx_fun; simpl.
  rewrite freeid_rename_idem_value.
  apply CTXProperties.Add_Equal in Hadd.
  rewrite Hadd.
  apply add_cong.
  apply IH.

  unfold Morphisms.Proper; unfold Morphisms.respectful.
  intros a' b' Heqab G1' G2' HeqG1G2; destruct a'; destruct b'.
  injection Heqab; intros; subst.
  unfold freeid_rename_ctx_fun.
  intuition.

  unfold SetoidList.transpose.
  intros a' b' G1'; destruct a'; destruct b'.
  unfold freeid_rename_ctx_fun.
  intuition.
Qed.

(* ============================================================================= *)

Lemma freeid_rename_idem_proc : forall P i, freeid_rename_proc i i P = P.
Proof.
  intros P; induction P; intros i; simpl; 
    (repeat rewrite freeid_rename_idem_value); 
    (repeat rewrite IHP);
    (repeat rewrite IHP1);
    (repeat rewrite IHP2);
    try reflexivity.
Qed.

(* ============================================================================= *)

Lemma ctx_preservation_real_extension : 
  forall x s G1 G2 vo,
    ~ In x (free_ids_context G1)
    ->
    ctx_preservation G1 G2 vo
    -> 
    ctx_preservation
      (CTX.add (ValName (Nm (Free x)), TChannel s) (CTX.add (ValName (CoNm (Free x)), TChannel (SDual s)) G1))
      (CTX.add (ValName (Nm (Free x)), TChannel s) (CTX.add (ValName (CoNm (Free x)), TChannel (SDual s)) G2)) 
      vo.
Proof.
  intros x s G1 G2 vo Hnotin Hpres.
  inversion Hpres; subst.
  apply CPNoInteraction; apply add_cong; apply add_cong; auto.
  apply (CPInteraction _ _ nm1 (dual_name nm1) s0 m t); auto; 
    try solve [do 2 apply CTXFacts.add_2; auto].

  
  eapply CTX_eq_trans; [ | apply replace_cong; rewrite <- add_replace_comm ]; [ | reflexivity | ].
  eapply CTX_eq_trans; [ | rewrite <- add_replace_comm ]; [ | reflexivity | ].
  apply add_cong.
  eapply CTX_eq_trans; [ | apply replace_cong; rewrite <- add_replace_comm ]; [ | reflexivity | ].
  eapply CTX_eq_trans; [ | rewrite <- add_replace_comm ]; [ | reflexivity | ].
  apply add_cong.
  auto.

  contradict Hnotin; injection Hnotin; intros; subst; rewrite free_ids_context_iff; exists (CoNm (Free x)); eexists; split; simpl in H1; simpl; eauto.
  contradict Hnotin; injection Hnotin; intros; subst; rewrite free_ids_context_iff; exists (CoNm (Free x)); eexists; split; simpl in H1; simpl; eauto.
  rewrite Hnotin; eauto.
  contradict Hnotin; injection Hnotin; intros; subst; rewrite free_ids_context_iff; exists (Nm (Free x)); eexists; split; simpl in H1; simpl; eauto.
  contradict Hnotin; injection Hnotin; intros; subst; rewrite free_ids_context_iff; exists (Nm (Free x)); eexists; split; simpl in H1; simpl; eauto.
  rewrite Hnotin; eauto.
Qed.
  
(* ============================================================================= *)

Lemma freeid_rename_value_non_free_id : 
  forall x y v, 
    ~ In x (free_ids_value v)
    ->
    freeid_rename_value x y v = v.
Proof.
  intros x y v Hnotin.
  repeat (match goal with
           | [ v : value |- _ ] => destruct v
           | [ n : name |- _ ] => destruct n
           | [ i : id |- _ ] => destruct i
           | [ v : variable |- _ ] => destruct v
           | [ |- ?X = ?X ] => reflexivity
           | [ |- context[if ?X then _ else _ ] ] => destruct X; subst
          end; simpl in *); tauto.
Qed.

(* ============================================================================= *)

Lemma partitition_right_subset : 
  forall G GL GR1 GR2,
    G |-part GL (+) GR1
    ->
    CTX.Subset GR2 GR1
    ->
    CTX.union GL GR2 |-part GL (+) GR2.
Proof.
  intros G GL GR1 GR2 Hpart Hsubset.
  inversion Hpart; subst.
  constructor.
  reflexivity.
  apply subset_preserves_well_formed_ctx with (G1:=G); auto.
  rewrite Hsubset.
  rewrite <- H.
  reflexivity.
  intros u rho.
  specialize (H1 u rho); destruct H1 as [H1|H1]; [|destruct H1 as [H1|H1]]; try tauto.
  right; left.
  contradict H1.  
  apply Hsubset; auto.
Qed.

(* ============================================================================= *)

Lemma SO3_value_notin : 
  forall x y w u1 v1,
    SO3_value x y w u1 v1
    ->
    x <> y
    -> 
    ~ In y (free_ids_value u1)
    ->
    ~ In y (free_ids_value w)
    ->
    free_name_or_token w 
    -> 
    v1 <> ValVariable (Var (Free x)).
Proof.
  intros x y w u1 v1 Hso3v Hneqxy Hnotinyu1 Hnotinyw Hfnotw.

  pose (SO3_value_cases _ _ _ _ _ Hso3v) as Hu.
  destruct Hu as [Hu|Hu]; [
    subst; 
      destruct (value_dec v1 (ValVariable (Var (Free x)))) as [e|n]; [
        subst; apply SO3_value_var_determines_subst_improved in Hso3v; auto; subst; inversion Hfnotw
        | assumption
      ]
    | destruct Hu as [Hu|Hu]; [
      destruct Hu as [Hu1 Hu2]
      | destruct Hu as [Hu1 Hu2]; subst; inversion Hfnotw; subst; simpl; discriminate
    ]
  ].
  destruct (value_dec v1 (ValVariable (Var (Free x)))) as [e|n]; [
    subst
    | assumption
  ].
  destruct u1 as [nm| |var]; subst; simpl in *; try solve [discriminate e];
    destruct var as [i]; destruct i as [f|b]; subst; simpl in *; try solve [discriminate e].
  destruct (string_dec f x); [
    subst; simpl in *; injection e; intros; subst; contradict Hnotinyu1; left; reflexivity
    | contradict n; injection n; intros; subst; reflexivity
  ].
Qed.

Lemma SO3_notin : 
  forall x y w P1 P2,
    SO3 x y w P1 P2
    ->
    x <> y
    -> 
    ~ In y (free_ids_proc P1)
    ->
    ~ In y (free_ids_value w)
    ->
    free_name_or_token w 
    -> 
    ~ In (ValVariable (Var (Free x))) (free_values_proc P2).
Proof.
  intros x y w P1 P2 Hso3 Hneqxy HnotinyP1 Hnotinyw Hfnotw Hin.
  apply SO3_free_values_in_context1_aux with (2:=Hso3) in Hin.
  destruct Hin as [v Hin]; destruct Hin as [Hin1 Hin2].
  apply SO3_value_notin in Hin2; auto.
  contradict HnotinyP1.
  rewrite free_ids_proc_alt.
  rewrite in_flat_map.
  exists v; split; auto.
Qed.

(* ============================================================================= *)

Lemma SO3_free_values_in_context2 : 
  forall x y w P1 P2 G rho,
    CTX.add (ValVariable (Var (Free x)), rho) G |-p P1
    ->
    SO3 x y w P1 P2
    ->
    x <> y
    -> 
    ~ In y (free_ids_proc P1)
    ->
    ~ In y (free_ids_value w)
    ->
    free_name_or_token w 
    ->
    free_values_in_context (ctx_add_value w rho G) P2.
Proof.
  intros x y w P1 P2 G rho HtypP1 Hso3 Hneqxy HnotinyP1 Hnotinyw Hfnotw.
  pose (free_values_in_context_1 _ _ HtypP1) as Hfvic.
  
  assert (free_values_in_context (ctx_add_value w rho (CTX.add (ValVariable (Var (Free x)), rho) G)) P2) as Hfvic2; [
    apply SO3_free_values_in_context1 with (2:=Hso3); auto; apply CTXFacts.add_1; reflexivity
    |
  ].

  intros v Hin.
  specialize (Hfvic2 v Hin).
  destruct Hfvic2 as [sigma Hfvic2].
  inversion Hfnotw; subst; simpl in *; repeat rewrite CTXFacts.add_iff in *;
    repeat match goal with
             | [ H : _ \/ _ |- _ ] => destruct H as [H|H]
             | [ H : (_,_)=(_,_) |- _ ] => injection H; intros; subst; clear H
           end;
    (try solve [exists sigma; apply CTXFacts.add_1; reflexivity]);
    (try solve [contradict Hin; apply SO3_notin with (1:=Hso3); auto]); [
      |
      | 
    ];
    exists sigma; try apply CTXFacts.add_2; assumption.
Qed.

(* ============================================================================= *)

Lemma preservation_interaction_stateful :
  forall (m:name) i v P1 Q1 P2 Q2 G1 GL GR sR rho t vo,
    balanced G1
    ->
    ~ In i (free_ids_proc ((ValName m) ? ; P1 +++ P2 ||| (ValName (dual_name m) ! v; Q1 +++ Q2)))
    ->
    G1 |-part GL (+) GR
    ->
    GL |-p (ValName m) ? ; P1
    ->
    sR -- MOut rho --> t
    ->
    ValName (dual_name m) <> v
    ->
    GR |-v dual_name m : TChannel sR
    ->
    GR |-v v : rho
    ->
    ctx_replace (dual_name m) (TChannel sR) (TChannel t) (CTX.remove (v, rho) GR) |-p Q1
    ->
    mk_obs m v vo
    ->
    exists G2 : ctx, (G2 |-p subst_open_proc P1 i 0 v ||| Q1) /\ ctx_preservation G1 G2 vo.
Proof.
  intros m i v P1 Q1 P2 Q2 G1  GL GR sR rho t vo Hprespre H0 Hpart HtypL1 Htrans Hneq Hlookupdual Hlookupvalue HtypR Hvo.

  inversion HtypL1 as [? ? ? sL L Hlookup _ HtypL| | | | | | | |]; subst.

  assert (exists t2, dual_types_transition2 (TChannel sL) (TChannel sR) (rho) (TChannel t2) (TChannel t)) as Hdtt; [intros; subst|].  
  unfold balanced in Hprespre.
  apply proj1 in Hprespre.
  unfold ctx_matched_names in Hprespre.
  specialize (Hprespre m (dual_name m) (TChannel sL) (TChannel sR) eq_refl).
  assert (CTX.In (ValName m, TChannel sL) G1) as Hu1; [|specialize (Hprespre Hu1)].
  apply lookup_channel_in; auto; apply partition_lookup_left with (GL:=GL) (GR:=GR); auto.
  assert (CTX.In (ValName (dual_name m), TChannel sR) G1) as Hu2; [|specialize (Hprespre Hu2)].
  apply lookup_channel_in; auto; apply partition_lookup_left with (GL:=GR) (GR:=GL); auto; apply partition_comm; auto.
  inversion Hprespre; subst.
  destruct (sdual_transition _ _ _ Htrans) as [t2 Htrans2]; destruct Htrans2 as [Htrans2 Heq]; subst.
  eexists.
  apply DTT2Left; eauto.

  eexists.
  replace (MOut rho) with (m_dual (MInp rho)) in Htrans.
  apply DTT2Right; eauto.
  reflexivity.

  destruct Hdtt as [tu2 Hdtt].

  assert (exists x : free_id, ~ In x ((i :: nil) ++ (free_ids_value v) ++ (free_ids_proc P1) ++ (free_ids_context G1) ++ L)) as Hu; [apply fresh_free_id_exists|].
  destruct Hu as [x Hin].

  assert (~ In x L) as Hina.
  contradict Hin; (repeat rewrite in_app_iff); right; right; auto.

  destruct (dual_types_transition2_spec _ _ _ _ _ Hdtt Htrans) as [Htrans2 Hdual]; simpl in Htrans2.

  specialize (HtypL _ rho tu2 x Hina Htrans2 eq_refl).

  SSCase "dual_name m <> v"%string.
  set (GL2:=(ctx_add_value v rho (ctx_replace m (TChannel sL) (TChannel tu2) GL))).
  set (GR2:=(ctx_replace (dual_name m) (TChannel sR) (TChannel t) (CTX.remove (v, rho) GR))).
  exists (CTX.union GL2 GR2).
  split.
  apply TypPar with (GL:=GL2) (GR:=GR2); auto.
  eapply partition_interaction; eauto.

  destruct Hlookupvalue; [constructor 1 | constructor 2].
  destruct H; eapply H; eauto.

  intros HinmGR.
  assert (|-st TChannel sL).
  inversion Hlookup; subst.
  inversion Hpart; subst.
  destruct (H4 m (TChannel sL)) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]]; try solve [contradict Hu; auto]; auto.
  inversion H; subst.
  specialize (H2 _ _ Htrans2); rewrite H2; auto.

  intros HindmGL.
  assert (|-st TChannel sR).
  inversion Hlookupdual; subst.
  inversion Hpart; subst.
  destruct (H4 (dual_name m) (TChannel sR)) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]]; try solve [contradict Hu; auto]; auto.
  inversion H; subst.
  specialize (H2 _ _ Htrans); rewrite H2; auto.

  assert (SO3 x i v (open_proc x 0 P1) (subst_open_proc P1 i 0 v)) as Hso3.
  apply SO3Base. 
  contradict Hin; simpl; (repeat rewrite in_app_iff); tauto.
  contradict H0; simpl; (repeat rewrite in_app_iff); tauto.
  inversion Hprespre; inversion Hlookupvalue; subst; [|constructor].
  assert (CTX.In (v, rho) G1).
  inversion Hpart; subst.
  rewrite H4; rewrite CTXFacts.union_iff; tauto.
  destruct H1 as [H1 _]; specialize (H1 _ _ H4); inversion H1; constructor.

  apply typed_strengthen with (G2:=ctx_add_value v rho (ctx_replace m (TChannel sL) (TChannel tu2) (CTX.add (ValVariable (Var (Free x)), rho) GL))).
  apply subst_r with (x:=x) (y:=i) (P:=open_proc x 0 P1) (2:=Hso3).
  
  eapply ctx_equal_preserves_typed.
  apply HtypL.

  unfold ctx_replace; intros a; destruct a; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff); split; intros Hin2;
    repeat (match goal with
              | [ H : _ \/ _ |- _ ] => destruct H
              | [ H : _ /\ _ |- _ ] => destruct H
              | [ H : _ = _ |- _ ] => solve [discriminate H]
              | [ H : _ = _ |- _ ] => injection H; intros; subst; clear H
            end);
    (try solve [tauto]);
    (try solve [right; split; [left; reflexivity | intros Hu; discriminate Hu]]).
  
  contradict Hin; subst; rewrite in_app_iff; left; intuition.

  contradict Hin; subst; (repeat rewrite in_app_iff); right; left; intuition.

  contradict H0; simpl; (repeat rewrite in_app_iff); left; left; right.
  apply free_ids_open_proc in H0; destruct H0; [contradict Hin; subst; rewrite in_app_iff; left; intuition | auto].

  contradict H0; simpl; (repeat rewrite in_app_iff); right; left; right; left; auto.

  unfold ctx_replace; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff).
  right; split; [left; auto | intros Hu; discriminate Hu].

  intros k Heq; subst; inversion Hlookupvalue; subst; auto.
  inversion H; subst.
  specialize (H2 _ _ H1); inversion H2.

  eapply ctx_equal_part_1.
  apply ctx_replace_preserves_partition_left.
  apply CTXFacts.add_2.
  inversion Hlookup; subst; auto.
  intros Hin2.
  assert (ValName m = v /\ TChannel sL = rho) as Heq2; [|destruct Heq2; subst].
  destruct v; simpl in Hin2;
    [ | rewrite CTXFacts.empty_iff in Hin2; destruct Hin2 | ]; 
    (rewrite CTXFacts.add_iff in Hin2; rewrite CTXFacts.empty_iff in Hin2; destruct Hin2 as [Hin2|Hin2]; [|destruct Hin2]);
    [injection Hin2; intros; subst; clear Hin2; split; reflexivity | discriminate Hin2].
  assert (|-st TChannel sL).
  inversion Hpart; subst.
  specialize (H2 (ValName m) (TChannel sL)); destruct H2; [|destruct H2 as [H2|H2]]; [| |auto].
  contradict H2; inversion Hlookup; subst; auto.
  contradict H2; inversion Hlookupvalue; subst; auto.
  inversion H; subst.
  rewrite (H2 _ _ Htrans2); reflexivity.
  
  apply ctx_add_preserves_partition_left; [ constructor | | apply partitition_right_subset with (G:=G1) (GR1:=GR); [apply Hpart | ] ].
  apply FContext.
  constructor.
  intros v1 sigma1.
  destruct (CTXProperties.In_dec (v1, sigma1) (CTX.union GL (ctx_add_value v rho CTX.empty))); [right | left; assumption].
  rewrite CTXFacts.union_iff in i0; destruct i0 as [i0|i0].
  assert (CTX.In (v1, sigma1) G1).
  inversion Hpart; subst.
  rewrite H; rewrite CTXFacts.union_iff; left; auto.
  assert (~ In x (free_ids_context G1)).
  contradict Hin; simpl; (repeat rewrite in_app_iff); right; right; right; left; assumption.
  contradict H1; rewrite free_ids_context_iff.
  exists v1; exists sigma1; split; auto.
  rewrite <- H1; simpl; left; reflexivity.
  assert (v1 = v); [|subst].
  pose (SO3_free_name_or_token _ _ _ _ _ Hso3) as Hfnot; inversion Hfnot; subst; simpl in i0;
    [ rewrite CTXFacts.add_iff in i0 | rewrite CTXFacts.add_iff in i0 | ]; rewrite CTXFacts.empty_iff in i0; 
      (try destruct i0 as [i0|i0]); 
      try solve [destruct i0];
        injection i0; intros; subst; reflexivity.
  contradict Hin; simpl; rewrite <- Hin; simpl; (repeat rewrite in_app_iff); right; left; reflexivity.

  intros a; destruct a; intros Hin2.

  assert (v0 = v /\ t0 = rho /\ free_name v0) as Hu2; [|destruct Hu2; subst].
  pose (SO3_free_name_or_token _ _ _ _ _ Hso3) as Hfnot; inversion Hfnot; subst; simpl in Hin2;
    [ rewrite CTXFacts.add_iff in Hin2 | rewrite CTXFacts.add_iff in Hin2 | ]; rewrite CTXFacts.empty_iff in Hin2;
      [ | | solve [destruct Hin2] ]; (destruct Hin2 as [Hin2|Hin2]; [|destruct Hin2]); 
      (injection Hin2; intros; subst; split; [reflexivity | split; [reflexivity | constructor]]).
  destruct H1 as [Heq2 H1]; subst.
  inversion H1; inversion Hlookupvalue; subst; auto; discriminate H4.

  assert ((v = ValName m /\ rho = TChannel sL /\ sL = tu2) \/ v <> ValName m) as Hcases.
  destruct (value_dec v (ValName m)); [|right; assumption].
  subst; left; split; [reflexivity|].
  inversion Hpart; subst.
  inversion Hlookup; subst.
  inversion Hlookupvalue; subst.
  pose (partition_wf _ _ _ Hpart) as Hu2; inversion Hu2; subst.
  assert (rho = TChannel sL); [|subst].
  apply (H8 (ValName m)).
  rewrite H; rewrite CTXFacts.union_iff; right; auto.
  rewrite H; rewrite CTXFacts.union_iff; left; auto.
  split; [reflexivity|].
  specialize (H2 m (TChannel sL)); destruct H2 as [H2|H2]; [|destruct H2 as [H2|H2]].
  contradict H2; auto.
  contradict H2; auto.
  inversion H2; subst.
  apply (H11 _ _ Htrans2).

  destruct Hcases; destruct v; simpl; unfold ctx_replace; intros a; destruct a; split; 
    (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.union_iff || rewrite CTXFacts.remove_iff || rewrite CTXFacts.empty_iff); intros Hin2; 
    repeat (match goal with
              | [ H : _ \/ _ |- _ ] => destruct H
              | [ H : _ /\ _ |- _ ] => destruct H
              | [ H : _ = _ |- _ ] => solve [discriminate H]
              | [ H : _ = _ |- _ ] => injection H; intros; subst; clear H
              | [ H : False |- _ ] => destruct H
            end); auto.
  right; split; [right; right; left; reflexivity | contradict H; injection H; intros; subst; reflexivity].
  right; split; [right; right; left; reflexivity | contradict H; discriminate H].

  unfold GL2; unfold ctx_replace; intros a; destruct a; destruct v; simpl; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff); tauto.


  apply SO3_free_values_in_context2 with (2:=Hso3); auto.
  contradict Hin; simpl; rewrite <- Hin; simpl; (repeat rewrite in_app_iff); left; reflexivity.
  intros Hin2; apply free_ids_open_proc in Hin2; destruct Hin2 as [Hin2|Hin2]; [
    subst; contradict Hin; (repeat rewrite in_app_iff); left; intuition
    | contradict H0; simpl; (repeat rewrite in_app_iff); left; left; right; assumption
  ].
  contradict H0; simpl; (repeat rewrite in_app_iff); right; left; right; left; assumption.

  apply (SO3_free_name_or_token _ _ _ _ _ Hso3).
  

  assert (CTX.In (ValName m, TChannel sL) GL) as Huin1.
  apply lookup_channel_in; auto.

  assert (CTX.In (ValName (dual_name m), TChannel sR) GR) as Huin2.
  apply lookup_channel_in; auto.

  eapply ctx_preservation_eq; [ 
    | eapply (ctx_preservation_stateful G1 GL GR m (dual_name m) sL tu2 sR t (rho) v rho vo eq_refl Hneq Hpart Huin1 Huin2 Hlookupvalue Hdtt)
    | 
  ]; auto.
  inversion Hpart; intros; subst.
  assumption.

  unfold GL2; unfold GR2.
  reflexivity.
Qed.

(* ============================================================================= *)

Lemma ctx_union_add_swap : 
  forall v rho G1 G2,
    CTX.eq (CTX.union (CTX.add (v, rho) G1) G2) (CTX.union G1 (CTX.add (v, rho) G2)).
Proof.
  intros v rho G1 G2.
  eapply CTX_eq_trans; [
    rewrite CTXProperties.union_add; apply add_cong; rewrite CTXProperties.union_sym; reflexivity
    | 
  ].
  rewrite <- CTXProperties.union_add; rewrite CTXProperties.union_sym.
  reflexivity.
Qed.

(* ============================================================================= *)

Lemma preservation_interaction_stateless : 
  forall m i v P1 Q1 P2 Q2 G1 GL GR sR rho t G vo,
    balanced G1
    ->
    ~ In i (free_ids_proc ((ValName m) ? ; P1 +++ P2 ||| (ValName (dual_name m) ! v; Q1 +++ Q2)))
    ->
    G1 |-part GL (+) GR
    ->
    GL |-p m ? ; P1
    ->
    sR -- MOut rho --> t
    ->
    |-st rho
    ->
    GR |-v dual_name m : TChannel sR
    ->
    GR |-v v : rho
    ->
    G = CTX.remove (v, rho) GR \/ G = GR
    ->
    ctx_replace (dual_name m) (TChannel sR) (TChannel t) G |-p Q1
    ->
    mk_obs m v vo
    ->
    exists G2 : ctx, (G2 |-p subst_open_proc P1 i 0 v ||| Q1) /\ ctx_preservation G1 G2 vo.
Proof.
  intros m i v P1 Q1 P2 Q2 G1 GL GR sR rho t G vo Hprespre H0 Hpart HtypL1 Htrans Hstateless Hlookupdual Hlookupvalue Hchoice HtypR Hvo.

  assert (ctx_replace (dual_name m) (TChannel sR) (TChannel t) GR |-p Q1) as HtypR2; [
    destruct Hchoice; subst; [
      | assumption
    ]
    |
  ].
  destruct (value_dec (dual_name m) v) as [e|n]; [
    subst;
      assert (forall sigma, CTX.In (ValName (dual_name m), sigma) GR -> sigma = TChannel sR) as Heqtyp; [
        intros sigma Hin1;
          inversion Hlookupdual as [? ? ? Hwf Hin2|]; subst;
            inversion Hwf as [? _ Heqtypes _]; subst;
              apply (Heqtypes _ _ _ Hin1 Hin2)
        |
      ];
      assert (TChannel sR = rho); [
        inversion Hlookupdual as [? ? ? Hwf Hin1|]; subst;
          inversion Hlookupvalue as [? ? ? _ Hin2|]; subst;
            inversion Hwf as [? _ Heqtypes _]; subst;
              apply (Heqtypes _ _ _ Hin1 Hin2)
        | subst
      ];
      assert (sR = t); [
        inversion Hstateless as [? Heqsess|]; subst;
          apply (Heqsess _ _ Htrans)
        | subst
      ];
      eapply ctx_equal_preserves_typed; [apply HtypR|]; 
        apply CTXProperties.subset_antisym; [
          (apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|]);
          apply CTXProperties.subset_remove_3;
            apply CTXProperties.subset_remove_3;
              (intros a Hin; destruct a as [v0 rho0]; destruct (value_dec v0 (dual_name m)) as [e|n]; [
                subst; rewrite (Heqtyp _ Hin) in *; apply CTXFacts.add_1; reflexivity
                | apply CTXFacts.add_2;
                  apply CTXFacts.remove_2; [contradict n; injection n; intros; subst; reflexivity|];
                    assumption
              ])
          | (apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|]);
            apply CTXProperties.subset_remove_3;
              (intros a Hin; destruct a as [v0 rho0]; destruct (value_dec v0 (dual_name m)) as [e|n]; [
                subst; rewrite (Heqtyp _ Hin) in *; apply CTXFacts.add_1; reflexivity
                | apply CTXFacts.add_2;
                  apply CTXFacts.remove_2; [contradict n; injection n; intros; subst; reflexivity|];
                    apply CTXFacts.remove_2; [contradict n; injection n; intros; subst; reflexivity|];
                      assumption
              ])
        ]
    | 
  ].
  assert ((exists k, v = ValToken k) \/ ~ (exists k, v = ValToken k)) as Htokenornot; [
    destruct v as [nm|tok|var]; try solve [right; intros Heq; destruct Heq as [k Heq]; subst; discriminate Heq]; 
      left; eexists; reflexivity
    |
  ].
  destruct Htokenornot as [Htoken|Hnottoken]; [
    destruct Htoken as [k Htoken]; subst;
      eapply ctx_equal_preserves_typed; [
        apply HtypR
        | assert (forall sigma, ~ CTX.In (ValToken k, sigma) GR); [
          intros sigma Hin;
            inversion Hlookupdual as [? ? ? Hwf|]; subst;
              inversion Hwf as [? Hfv _ _ ]; subst;
                pose (Hfv _ _ Hin) as Hu; inversion Hu
          |
        ];
        apply CTXProperties.subset_antisym; [
          (apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|]);
          intros a Hin; destruct a as [v0 rho0]; destruct (value_dec v0 (dual_name m)) as [e2|n2]; [
            subst; 
              rewrite CTXFacts.remove_iff in Hin; destruct Hin as [Hin1 Hin2];
                apply CTXFacts.remove_3 in Hin1;
                  contradict Hin2;
                  assert (TChannel sR = rho0); [
                    inversion Hlookupdual as [? ? ? Hwf Hin3|]; subst; 
                      inversion Hwf as [a Hfv Heqtypes _ ]; subst; 
                        apply (Heqtypes _ _ _ Hin3 Hin1)
                    | subst; reflexivity
                  ]
            | do 2 apply CTXFacts.remove_3 in Hin;
              apply CTXFacts.add_2;
                apply CTXFacts.remove_2; [contradict n2; injection n2; intros; subst; reflexivity|];
                  assumption
          ]
          | apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|];
            intros a Hin; destruct a; rewrite CTXFacts.remove_iff in Hin; destruct Hin as [Hin1 Hin2];
              apply CTXFacts.add_2;
                apply CTXFacts.remove_2; [assumption|];
                  apply CTXFacts.remove_2; [intros Heq; injection Heq; intros; subst; specialize (H t0); contradict H; assumption|];
                    assumption
        ]
      ]
    | eapply partition_typed_weaken_left with (GR:=CTX.add (v, rho) CTX.empty); [
      apply HtypR
      | apply partition_comm;
        eapply ctx_equal_part_3; [
          apply partition_add_remove_swap; [
            apply partition_comm;
              apply ctx_replace_preserves_partition_left; [
                inversion Hlookupdual; subst; apply H1
                | rewrite CTXFacts.empty_iff; intros Hin; destruct Hin
                | apply partition_empty; inversion Hlookupdual; subst; assumption
              ]
            | apply CTXFacts.add_2;
              apply CTXFacts.remove_2; [contradict n; injection n; intros; subst; reflexivity|];
                inversion Hlookupvalue; subst; [ 
                  auto
                  | contradict Hnottoken; eexists; reflexivity
                ]
          ]
          | Case "c"%string
        ]
    ]
  ].

  apply CTXProperties.subset_antisym; [
    intros a Hin; destruct a; unfold ctx_replace in Hin; (repeat rewrite CTXFacts.add_iff in Hin || rewrite CTXFacts.remove_iff in Hin); 
      destruct Hin as [Hin1 Hin2]; destruct Hin1 as [Hin1|Hin1]; [
        injection Hin1; intros; subst; clear Hin1; apply CTXFacts.add_1; reflexivity
        | destruct Hin1 as [Hin1 Hin3];
          apply CTXFacts.add_2;
            apply CTXFacts.remove_2; [assumption|];
              apply CTXFacts.remove_2; [assumption|];
                assumption
      ]
    | apply CTXProperties.subset_add_3; [
      apply CTXFacts.remove_2; [contradict n; injection n; intros; subst; reflexivity|];
        apply CTXFacts.add_1; reflexivity
      | intros a Hin; destruct a; unfold ctx_replace in Hin; (repeat rewrite CTXFacts.add_iff in Hin || rewrite CTXFacts.remove_iff in Hin); 
        destruct Hin as [Hin1 Hin2]; destruct Hin1 as [Hin1 Hin3];
          apply CTXFacts.remove_2; [assumption|];
            apply CTXFacts.add_2;
              apply CTXFacts.remove_2; [assumption|];
                assumption
    ]
  ].

  clear HtypR; clear Hchoice; rename HtypR2 into HtypR.








  inversion HtypL1 as [? ? ? sL L Hlookup _ HtypL| | | | | | | |]; subst.

  assert (exists t2, dual_types_transition2 (TChannel sL) (TChannel sR) (rho) (TChannel t2) (TChannel t)) as Hdtt; [intros; subst|]; [
    unfold balanced in Hprespre;
      apply proj1 in Hprespre;
        unfold ctx_matched_names in Hprespre;
          specialize (Hprespre m (dual_name m) (TChannel sL) (TChannel sR) eq_refl);
            assert (CTX.In (ValName m, TChannel sL) G1) as Hu1; [|specialize (Hprespre Hu1)]; [
              apply lookup_channel_in; auto; apply partition_lookup_left with (GL:=GL) (GR:=GR); auto
              |
            ];
            assert (CTX.In (ValName (dual_name m), TChannel sR) G1) as Hu2; [|specialize (Hprespre Hu2)]; [
              apply lookup_channel_in; auto; apply partition_lookup_left with (GL:=GR) (GR:=GL); auto; apply partition_comm; auto
              |
            ];
            inversion Hprespre; subst; [
              destruct (sdual_transition _ _ _ Htrans) as [t2 Htrans2]; destruct Htrans2 as [Htrans2 Heq]; subst; eexists; apply DTT2Left; eauto
              | eexists; replace (MOut rho) with (m_dual (MInp rho)) in Htrans; [
                apply DTT2Right; eauto
                | reflexivity
              ]
            ]
    | destruct Hdtt as [tu2 Hdtt]
  ].

  

  assert (exists x : free_id, ~ In x ((i :: nil) ++ (free_ids_value v) ++ (free_ids_proc P1) ++ (free_ids_context G1) ++ L)) as Hu; [
    apply fresh_free_id_exists
    |
  ].
  destruct Hu as [x Hin].

  assert (~ In x L) as Hina.
  contradict Hin; (repeat rewrite in_app_iff); right; right; auto.

  destruct (dual_types_transition2_spec _ _ _ _ _ Hdtt Htrans) as [Htrans2 Hdual]; simpl in Htrans2.

  specialize (HtypL _ rho tu2 x Hina Htrans2 eq_refl).

  set (GL2:=(ctx_add_value v rho (ctx_replace m (TChannel sL) (TChannel tu2) GL))).
  set (GR2:=(ctx_replace (dual_name m) (TChannel sR) (TChannel t) GR)).
  exists (CTX.union GL2 GR2).
  split.
  apply TypPar with (GL:=GL2) (GR:=GR2); auto.


  unfold GL2 in *; clear GL2; unfold GR2 in *; clear GR2.
  assert (v = m -> rho = TChannel sL /\ sL = tu2) as Heqvmtypes; [
    intros Heqvm; subst;
      inversion Hpart as [? ? ? Heq HwfG _]; subst;
        inversion HwfG as [? HfvG HeqtypesG _]; subst;
          inversion Hlookup as [? ? ? _ HinmGL|]; subst;
            assert (CTX.In (ValName m, TChannel sL) G1) as HinmG1; [
              rewrite Heq; apply CTXFacts.union_2; auto
              |
            ];
            assert (free_value m) as Hfvm; [apply (HfvG _ _ HinmG1)|];
              inversion Hlookupvalue as [? ? ? _ HinmrhoGR|]; subst;
                assert (CTX.In (ValName m, rho) G1) as HinmrhoG1; [
                  rewrite Heq; apply CTXFacts.union_3; auto
                  |
                ];
                rewrite (HeqtypesG _ _ _ HinmrhoG1 HinmG1) in *; 
                  inversion Hstateless as [a Hstat|]; subst; rewrite (Hstat _ _ Htrans2) in *; split; reflexivity
    |
  ].
  assert (v = dual_name m -> rho = TChannel sR /\ sR = t) as Heqvdmtypes; [
    intros Heqvm; subst;
      inversion Hlookupdual as [? ? ? HwfGR HindmGR|]; subst;
        inversion HwfGR as [? _ HeqtypesGR _]; subst;
          inversion Hlookupvalue as [? ? ? _ HindmrhoGR|]; subst;
            rewrite (HeqtypesGR _ _ _ HindmrhoGR HindmGR) in *; 
              inversion Hstateless as [a Hstat|]; subst; rewrite (Hstat _ _ Htrans) in *; split; reflexivity
    |
  ].

  assert (m <> dual_name m) as Hneqmdm; [destruct m; discriminate | ].

  assert (
    CTX.eq
    (CTX.union (ctx_add_value v rho (ctx_replace m (TChannel sL) (TChannel tu2) GL)) (ctx_replace (dual_name m) (TChannel sR) (TChannel t) GR))
    (CTX.union (ctx_replace m (TChannel sL) (TChannel tu2) GL) (ctx_replace (dual_name m) (TChannel sR) (TChannel t) GR))
  ) as Heqctx1; [
    inversion Hlookupvalue as [? ? ? HwfGR Hin1 |]; subst; [|simpl; reflexivity];
      inversion HwfGR as [? HfvGR HeqtypesGR _]; subst;
        assert (free_value v) as Hfvv; [apply (HfvGR _ _ Hin1) | ];
          inversion Hfvv; subst; simpl;
            (rewrite CTXProperties.union_add;
              rewrite ctx_add_idem; [reflexivity|];
                apply CTXFacts.union_3;
                  match goal with
                    | [ |- CTX.In (?X, _) _ ] => 
                      destruct (value_dec X (dual_name m)) as [e|n]
                  end; [
                    rewrite e in *; clear e; destruct (Heqvdmtypes eq_refl); subst; apply CTXFacts.add_1; reflexivity
                    | apply CTXFacts.add_2; apply CTXFacts.remove_2; [
                      discriminate || (contradict n; injection n; intros Heq1 Heq2; rewrite Heq2; reflexivity)
                      | assumption
                    ]
                  ]
            )
    | eapply ctx_equal_part_1; [|symmetry; apply Heqctx1]; clear Heqctx1
  ].

  assert (forall sigma, CTX.In (ValName m, sigma) GR -> ( |-st TChannel sL ) /\ sigma = TChannel sL /\ sL = tu2) as HinmGReq; [
    intros sigma HinmGR;
      inversion Hpart as [? ? ? Heqctx HwfG1 Hdisjoint]; subst;
        inversion HwfG1 as [? HfvG1 HeqtypesG1 _]; subst;
          assert (sigma = TChannel sL); [
            apply (HeqtypesG1 (ValName m)); [
              rewrite Heqctx; apply CTXFacts.union_3; assumption
              | rewrite Heqctx; apply CTXFacts.union_2; inversion Hlookup; subst; assumption
            ]
            | subst
          ];
          specialize (Hdisjoint m (TChannel sL)) ; destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
            inversion Hlookup; subst; contradict Hdisjoint; assumption
            | destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
              contradict Hdisjoint; assumption
              | split; [
                assumption
                | split; [
                  reflexivity
                  | inversion Hdisjoint as [? Hstat|]; subst; apply (Hstat _ _ Htrans2)
                ]
              ]
            ]
          ]
    |
  ].

  assert (forall sigma, CTX.In (ValName (dual_name m), sigma) GL -> ( |-st TChannel sR ) /\ sigma = TChannel sR /\ sR = t) as HindmGLeq; [
    intros sigma HindmGL;
      inversion Hpart as [? ? ? Heqctx HwfG1 Hdisjoint]; subst;
        inversion HwfG1 as [? HfvG1 HeqtypesG1 _]; subst;
          assert (sigma = TChannel sR); [
            apply (HeqtypesG1 (ValName (dual_name m))); [
              rewrite Heqctx; apply CTXFacts.union_2; assumption
              | rewrite Heqctx; apply CTXFacts.union_3; inversion Hlookupdual; subst; assumption
            ]
            | subst
          ];
          specialize (Hdisjoint (dual_name m) (TChannel sR)) ; destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
            contradict Hdisjoint; assumption
            | destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
              inversion Hlookupdual; subst; contradict Hdisjoint; assumption
              | split; [
                assumption
                | split; [
                  reflexivity
                  | inversion Hdisjoint as [? Hstat|]; subst; apply (Hstat _ _ Htrans)
                ]
              ]
            ]
          ]
    |
  ].

  inversion Hpart as [? ? ? _ HwfG1a _]; subst.
  
  assert (
    CTX.eq
    (CTX.union (ctx_replace m (TChannel sL) (TChannel tu2) GL) (ctx_replace (dual_name m) (TChannel sR) (TChannel t) GR))
    (ctx_replace (dual_name m) (TChannel sR) (TChannel t) (ctx_replace m (TChannel sL) (TChannel tu2) (CTX.union GL GR)))
  ) as Heqctx2; [
    |
  ].
  unfold ctx_replace.
  rewrite CTXProperties.union_sym.
  rewrite CTXProperties.union_add.
  rewrite add_cong; [
    | rewrite CTXProperties.union_sym;
      rewrite CTXProperties.union_add;
      reflexivity
  ].
  eapply CTX_eq_trans; [
    | rewrite <- add_remove_comm; [|contradict Hneqmdm; injection Hneqmdm; intros Heq1; rewrite Heq1 in *; reflexivity];
      reflexivity
  ].
  apply CTXProperties.subset_antisym; [
    apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity | ];
      apply CTXProperties.subset_add_3; [apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity | ];
        apply CTXProperties.union_subset_3; intros a Hin2; destruct a; rewrite CTXFacts.remove_iff in Hin2; destruct Hin2 as [Hin2 Hin3]; [
          destruct (value_dec v0 (dual_name m)) as [e|n]; [
            subst; specialize (HindmGLeq _ Hin2); destruct HindmGLeq as [Hu1 Hu2]; destruct Hu2 as [Hu2 Hu3]; subst; apply CTXFacts.add_1; reflexivity
            | do 2 apply CTXFacts.add_2;
              apply CTXFacts.remove_2; [contradict n; injection n; intros; subst; auto|];
                apply CTXFacts.remove_2; [assumption|];
                  apply CTXFacts.union_2; assumption
          ]
          | destruct (value_dec v0 m) as [e|n]; [
            subst; specialize (HinmGReq _ Hin2); destruct HinmGReq as [Hu1 Hu2]; destruct Hu2 as [Hu2 Hu3]; subst; 
              apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity
            | do 2 apply CTXFacts.add_2;
              apply CTXFacts.remove_2; [assumption|];
                apply CTXFacts.remove_2; [contradict n; injection n; intros; subst; auto|];
                  apply CTXFacts.union_3; assumption
          ]
        ]
    |
    apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity | ];
      apply CTXProperties.subset_add_3; [apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity | ]; 
        Case "c"%string
  ].
  intros a Hin2; destruct a; (repeat rewrite CTXFacts.remove_iff in Hin2); destruct Hin2 as [Hin2 Hin3]; destruct Hin2 as [Hin2 Hin4];
    do 2 apply CTXFacts.add_2.
  rewrite CTXFacts.union_iff in Hin2; destruct Hin2 as [Hin2|Hin2]; [
    apply CTXFacts.union_2
    | apply CTXFacts.union_3
  ]; apply CTXFacts.remove_2; auto.

  eapply ctx_equal_part_1; [|symmetry; apply Heqctx2]; clear Heqctx2.
  apply partition_comm.
  apply ctx_replace_preserves_partition_left; [
    inversion Hlookupdual; subst; assumption
    | intros Hin2;
      inversion Hlookupvalue as [? ? ? HwfGR Hin1 |]; subst; [|simpl in *]; [
        inversion HwfGR as [? HfvGR HeqtypesGR _]; subst;
          (assert (free_value v) as Hfvv; [apply (HfvGR _ _ Hin1) | ]);
          (inversion Hfvv; subst; simpl in *;
            (rewrite CTXFacts.add_iff in Hin2; destruct Hin2 as [Hin2|Hin2]; [
              solve [discriminate Hin2] || (injection Hin2; intros Heq1 Heq2; rewrite Heq2 in *; destruct (Heqvdmtypes eq_refl); subst; reflexivity)
              |
            ]))
        |
      ];
      (unfold ctx_replace in Hin2; rewrite CTXFacts.add_iff in Hin2; rewrite CTXFacts.remove_iff in Hin2;
        destruct Hin2 as [Hin2|Hin2]; [
          injection Hin2; intros Heq1 Heq2; destruct m; discriminate Heq2
          | destruct Hin2 as [Hin2 Hin3]; apply HindmGLeq in Hin2; destruct Hin2 as [Hin2 Hin4]; destruct Hin4 as [Hin4 Hin5]; subst; reflexivity
        ])
    |
  ].

  assert (CTX.eq
    (ctx_add_value v rho (ctx_replace m (TChannel sL) (TChannel tu2) GL))
    (ctx_replace m (TChannel sL) (TChannel tu2) (ctx_add_value v rho GL))
  ) as Heqctx3; [
    |
  ].
  inversion Hlookup as [? ? ? ? Hinm|]; subst;
    inversion Hlookupvalue as [? ? ? HwfGR Hin1 |]; subst; [|simpl in *]; [
      inversion HwfGR as [? HfvGR HeqtypesGR _]; subst;
        (assert (free_value v) as Hfvv; [apply (HfvGR _ _ Hin1) | ]);
        (inversion Hfvv; subst; simpl in * );
        (match goal with 
           | [ |- CTX.eq (CTX.add (?X, _) _) _ ]  => 
             destruct (value_dec X m) as [e|n]
           end; [
             rewrite <- e in *; clear e;
               specialize (Heqvmtypes eq_refl); destruct Heqvmtypes; subst;
                 rewrite ctx_add_idem; [
                   | apply CTXFacts.add_1; reflexivity
                 ];
                 rewrite ResultBasics.ctx_replace_idem; [|assumption];
                   rewrite ResultBasics.ctx_replace_idem; [|apply CTXFacts.add_1; reflexivity];
                     rewrite ctx_add_idem; [reflexivity|assumption]
             | apply add_replace_comm; assumption
           ])
      | reflexivity
    ].

  apply partition_comm.
  eapply ctx_equal_part_2; [|symmetry; apply Heqctx3]; clear Heqctx3.
  apply ctx_replace_preserves_partition_left; [
    inversion Hlookup as [? ? ? ? Hinm|]; subst;
      inversion Hlookupvalue as [? ? ? HwfGR Hin1 |]; subst; [|simpl in *]; [
        inversion HwfGR as [? HfvGR HeqtypesGR _]; subst;
          (assert (free_value v) as Hfvv; [apply (HfvGR _ _ Hin1) | ]);
          (inversion Hfvv; subst; simpl in *; apply CTXFacts.add_2)
        |
      ]; assumption
    | intros Hin2; apply HinmGReq in Hin2; destruct Hin2 as [Hin2 Hin4]; destruct Hin4 as [Hin4 Hin5]; subst; reflexivity
    |
  ].

  inversion Hpart as [? ? ? HeqG1 HwfG1]; subst.
  eapply ctx_equal_part_1; [| apply HeqG1].
  inversion Hlookupvalue as [? ? ? HwfGR Hin1 |]; subst; [|simpl in *; assumption].
  inversion HwfGR as [? HfvGR HeqtypesGR _]; subst.
  (assert (free_value v) as Hfvv; [apply (HfvGR _ _ Hin1) | ]).
  inversion Hfvv; subst;
    apply partition_add_idem_stateless; auto;
      inversion Hlookupvalue; subst;
        apply partition_comm in Hpart; 
          apply partition_lookup_left with (1:=Hpart); assumption.


  assert (SO3 x i v (open_proc x 0 P1) (subst_open_proc P1 i 0 v)) as Hso3.
  apply SO3Base. 
  contradict Hin; simpl; (repeat rewrite in_app_iff); tauto.
  contradict H0; simpl; (repeat rewrite in_app_iff); tauto.
  inversion Hprespre; inversion Hlookupvalue; subst; [|constructor].
  assert (CTX.In (v, rho) G1); [
    inversion Hpart; subst;
      rewrite H4; rewrite CTXFacts.union_iff; tauto
    |
  ];
  destruct H1 as [H1 _]; specialize (H1 _ _ H4); inversion H1; constructor.

  apply typed_strengthen with (G2:=ctx_add_value v rho (ctx_replace m (TChannel sL) (TChannel tu2) (CTX.add (ValVariable (Var (Free x)), rho) GL))).
  apply subst_r with (x:=x) (y:=i) (P:=open_proc x 0 P1) (2:=Hso3).
  
  eapply ctx_equal_preserves_typed.
  apply HtypL.

  unfold ctx_replace; intros a; destruct a; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff); split; intros Hin2;
    repeat (match goal with
              | [ H : _ \/ _ |- _ ] => destruct H
              | [ H : _ /\ _ |- _ ] => destruct H
              | [ H : _ = _ |- _ ] => solve [discriminate H]
              | [ H : _ = _ |- _ ] => injection H; intros; subst; clear H
            end);
    (try solve [tauto]);
    (try solve [right; split; [left; reflexivity | intros Hu; discriminate Hu]]).
  
  contradict Hin; subst; rewrite in_app_iff; left; intuition.

  contradict Hin; subst; (repeat rewrite in_app_iff); right; left; intuition.

  contradict H0; simpl; (repeat rewrite in_app_iff); left; left; right.
  apply free_ids_open_proc in H0; destruct H0; [contradict Hin; subst; rewrite in_app_iff; left; intuition | auto].

  contradict H0; simpl; (repeat rewrite in_app_iff); right; left; right; left; auto.

  unfold ctx_replace; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff).
  right; split; [left; auto | intros Hu; discriminate Hu].

  intros k Heq; subst; inversion Hlookupvalue; subst; auto.
  inversion H; subst.
  specialize (H2 _ _ H1); inversion H2.

  eapply ctx_equal_part_1.
  apply ctx_replace_preserves_partition_left.
  apply CTXFacts.add_2.
  inversion Hlookup; subst; auto.
  intros Hin2.
  assert (ValName m = v /\ TChannel sL = rho) as Heq2; [|destruct Heq2; subst].
  destruct v; simpl in Hin2;
    [ | rewrite CTXFacts.empty_iff in Hin2; destruct Hin2 | ]; 
    (rewrite CTXFacts.add_iff in Hin2; rewrite CTXFacts.empty_iff in Hin2; destruct Hin2 as [Hin2|Hin2]; [|destruct Hin2]);
    [injection Hin2; intros; subst; clear Hin2; split; reflexivity | discriminate Hin2].
  assert (|-st TChannel sL).
  inversion Hpart; subst.
  specialize (H2 (ValName m) (TChannel sL)); destruct H2; [|destruct H2 as [H2|H2]]; [| |auto].
  contradict H2; inversion Hlookup; subst; auto.
  contradict H2; inversion Hlookupvalue; subst; auto.
  inversion H; subst.
  rewrite (H2 _ _ Htrans2); reflexivity.
  
  apply ctx_add_preserves_partition_left; [ constructor | | apply partitition_right_subset with (G:=G1) (GR1:=GR); [apply Hpart | ] ].
  apply FContext.
  constructor.
  intros v1 sigma1.
  destruct (CTXProperties.In_dec (v1, sigma1) (CTX.union GL (ctx_add_value v rho CTX.empty))); [right | left; assumption].
  rewrite CTXFacts.union_iff in i0; destruct i0 as [i0|i0].
  assert (CTX.In (v1, sigma1) G1).
  inversion Hpart; subst.
  rewrite H; rewrite CTXFacts.union_iff; left; auto.
  assert (~ In x (free_ids_context G1)).
  contradict Hin; simpl; (repeat rewrite in_app_iff); right; right; right; left; assumption.
  contradict H1; rewrite free_ids_context_iff.
  exists v1; exists sigma1; split; auto.
  rewrite <- H1; simpl; left; reflexivity.
  assert (v1 = v); [|subst].
  pose (SO3_free_name_or_token _ _ _ _ _ Hso3) as Hfnot; inversion Hfnot; subst; simpl in i0;
    [ rewrite CTXFacts.add_iff in i0 | rewrite CTXFacts.add_iff in i0 | ]; rewrite CTXFacts.empty_iff in i0; 
      (try destruct i0 as [i0|i0]); 
      try solve [destruct i0];
        injection i0; intros; subst; reflexivity.
  contradict Hin; simpl; rewrite <- Hin; simpl; (repeat rewrite in_app_iff); right; left; reflexivity.

  intros a; destruct a; intros Hin2.

  assert (v0 = v /\ t0 = rho /\ free_name v0) as Hu2; [|destruct Hu2; subst].
  pose (SO3_free_name_or_token _ _ _ _ _ Hso3) as Hfnot; inversion Hfnot; subst; simpl in Hin2;
    [ rewrite CTXFacts.add_iff in Hin2 | rewrite CTXFacts.add_iff in Hin2 | ]; rewrite CTXFacts.empty_iff in Hin2;
      [ | | solve [destruct Hin2] ]; (destruct Hin2 as [Hin2|Hin2]; [|destruct Hin2]); 
      (injection Hin2; intros; subst; split; [reflexivity | split; [reflexivity | constructor]]).
  destruct H1 as [Heq2 H1]; subst.
  inversion H1; inversion Hlookupvalue; subst; auto; discriminate H4.

  assert ((v = ValName m /\ rho = TChannel sL /\ sL = tu2) \/ v <> ValName m) as Hcases.
  destruct (value_dec v (ValName m)); [|right; assumption].
  subst; left; split; [reflexivity|].
  inversion Hpart; subst.
  inversion Hlookup; subst.
  inversion Hlookupvalue; subst.
  pose (partition_wf _ _ _ Hpart) as Hu2; inversion Hu2; subst.
  assert (rho = TChannel sL); [|subst].
  apply (H8 (ValName m)).
  rewrite H; rewrite CTXFacts.union_iff; right; auto.
  rewrite H; rewrite CTXFacts.union_iff; left; auto.
  split; [reflexivity|].
  specialize (H2 m (TChannel sL)); destruct H2 as [H2|H2]; [|destruct H2 as [H2|H2]].
  contradict H2; auto.
  contradict H2; auto.
  inversion H2; subst.
  apply (H11 _ _ Htrans2).

  destruct Hcases; destruct v; simpl; unfold ctx_replace; intros a; destruct a; split; 
    (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.union_iff || rewrite CTXFacts.remove_iff || rewrite CTXFacts.empty_iff); intros Hin2; 
    repeat (match goal with
              | [ H : _ \/ _ |- _ ] => destruct H
              | [ H : _ /\ _ |- _ ] => destruct H
              | [ H : _ = _ |- _ ] => solve [discriminate H]
              | [ H : _ = _ |- _ ] => injection H; intros; subst; clear H
              | [ H : False |- _ ] => destruct H
            end); auto.
  right; split; [right; right; left; reflexivity | contradict H; injection H; intros; subst; reflexivity].
  right; split; [right; right; left; reflexivity | contradict H; discriminate H].

  unfold GL2; unfold ctx_replace; intros a; destruct a; destruct v; simpl; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff); tauto.

  

  apply SO3_free_values_in_context2 with (2:=Hso3); auto.
  contradict Hin; simpl; rewrite <- Hin; simpl; (repeat rewrite in_app_iff); left; reflexivity.
  intros Hin2; apply free_ids_open_proc in Hin2; destruct Hin2 as [Hin2|Hin2]; [
    subst; contradict Hin; (repeat rewrite in_app_iff); left; intuition
    | contradict H0; simpl; (repeat rewrite in_app_iff); left; left; right; assumption
  ].
  contradict H0; simpl; (repeat rewrite in_app_iff); right; left; right; left; assumption.

  apply (SO3_free_name_or_token _ _ _ _ _ Hso3).
  

  assert (CTX.In (ValName m, TChannel sL) GL) as Huin1.
  apply lookup_channel_in; auto.

  assert (CTX.In (ValName (dual_name m), TChannel sR) GR) as Huin2.
  apply lookup_channel_in; auto.


  destruct (value_dec (ValName (dual_name m)) v) as [e|Hneqdmv]; [
    unfold GL2 in *; clear GL2; unfold GR2 in *; clear GR2;
    rewrite <- e in *; clear e v
    | eapply ctx_preservation_eq; [ 
      | eapply (ctx_preservation_stateless G1 GL GR m (dual_name m) sL tu2 sR t (rho)  v rho vo eq_refl Hneqdmv Hpart Huin1 Huin2 Hlookupvalue Hdtt)
      | 
    ]; auto; [
      inversion Hpart; intros; subst; assumption
      | unfold GL2; unfold GR2; reflexivity
    ]
  ].

  inversion Hlookupdual as [? ? ? HwfGR _|]; subst.
  inversion HwfGR as [? HfvGR HeqtypesGR _]; subst.
  assert (free_value (dual_name m)) as Hfvv; [
    apply (HfvGR _ _ Huin2)
    |
  ].
  assert (rho = TChannel sR); [
    inversion Hlookupvalue as [? ? ? ? Hin2|]; subst; inversion Hfvv; subst; apply (HeqtypesGR _ _ _ Hin2 Huin2)
    | subst
  ].

  assert (sR = t); [
    inversion Hstateless as [? Hstat|]; subst; apply (Hstat _ _ Htrans)
    | subst
  ].
  assert (sL = tu2); [
    inversion Hdtt; subst; reflexivity
    | subst
  ].
  assert (ValName m <> ValName (dual_name m)) as Hneqmv; [
    destruct m; discriminate
    |
  ].
  assert (
    CTX.eq
    (ctx_add_value (dual_name m) (TChannel t) (ctx_replace m (TChannel tu2) (TChannel tu2) GL))
    (ctx_add_value (dual_name m) (TChannel t) GL)
  ) as Heq1; [
    inversion Hfvv; subst; simpl; apply add_cong; (rewrite ResultBasics.ctx_replace_idem; [reflexivity|assumption])
    |
  ].
  assert (CTX.eq (ctx_replace (dual_name m) (TChannel t) (TChannel t) GR) GR) as Heq2; [
    inversion Hfvv; subst; simpl; (rewrite ResultBasics.ctx_replace_idem; [reflexivity|]); rewrite H1 in *; assumption
    |
  ].

  inversion Hdual; subst.

  apply CPInteraction with (nm1:=m) (nm2:=dual_name m) (4:=Htrans2); [
    reflexivity
    | apply partition_is_subset_left with (1:=Hpart); auto
    | apply partition_is_subset_right with (1:=Hpart); auto
    | eapply CTX_eq_trans; [apply CTXProperties.union_equal_1 with (1:=Heq1) | ];
      eapply CTX_eq_trans; [apply CTXProperties.union_equal_2 with (1:=Heq2) | ];
        apply channel_lookup_yields_free_value in Hlookup;
          inversion Hlookup as [? Heq | ? Heq | ? Heq]; rewrite <- Heq in *; clear Heq; simpl in *;
            (rewrite ctx_union_add_swap; rewrite ctx_add_idem; [
              | inversion Hlookupvalue; subst; assumption
            ];
            inversion Hpart as [? ? ? Heq]; subst; 
              rewrite <- Heq;
                rewrite ctx_replace_idem; [
                  rewrite ctx_replace_idem; [
                    reflexivity
                    | apply partition_is_subset_right with (1:=Hpart); auto
                  ]
                  | apply CTXFacts.add_2; 
                    apply CTXFacts.remove_2; [discriminate|];
                      apply partition_is_subset_left with (1:=Hpart); auto
                ]
            )
    | inversion Hvo; subst; simpl in *; 
      inversion H; subst; simpl in *; constructor
  ].

  apply CPInteraction with (nm1:=dual_name m) (nm2:=m) (4:=Htrans); [
    destruct m; reflexivity
    | apply partition_is_subset_right with (1:=Hpart); auto
    | apply partition_is_subset_left with (1:=Hpart); auto
    | eapply CTX_eq_trans; [apply CTXProperties.union_equal_1 with (1:=Heq1) | ];
      eapply CTX_eq_trans; [apply CTXProperties.union_equal_2 with (1:=Heq2) | ];
        apply channel_lookup_yields_free_value in Hlookup;
          inversion Hlookup as [? Heq | ? Heq | ? Heq]; rewrite <- Heq in *; clear Heq; simpl in *;
            (rewrite ctx_union_add_swap; rewrite ctx_add_idem; [
              | inversion Hlookupvalue; subst; assumption
            ];
            inversion Hpart as [? ? ? Heq]; subst; 
              rewrite <- Heq; 
                rewrite ctx_replace_idem; [
                  rewrite ctx_replace_idem; [
                    reflexivity
                    | apply partition_is_subset_left with (1:=Hpart); auto
                  ]
                  | apply CTXFacts.add_2; 
                    apply CTXFacts.remove_2; [discriminate|];
                      apply partition_is_subset_right with (1:=Hpart); auto
                ])
    | inversion Hvo; subst; simpl in *; 
      inversion H; subst; simpl in *; constructor
  ].

Qed.

(* ============================================================================= *)

Theorem subject_reduction_alt : 
  forall P Q vo,
    reduction P Q vo
    ->
    forall G1,
      balanced G1
      ->
      G1 |-p P
      ->
      exists G2,
        ((G2 |-p Q) /\ ctx_preservation G1 G2 vo).
Proof.
  intros P Q vo Hredn; induction Hredn; intros G1 Hprespre Htyp.
  
  Case "interaction"%string.
  subst.
  inversion Htyp as [ | |G GL GR ? ? Hpart HtypL HtypR | | | | | | ]; subst; clear Htyp.
  inversion HtypL as [ | | |? ? ? HtypL1 _| | | | |]; subst; clear HtypL.
  inversion HtypR as [ | | |? ? ? HtypR1 _| | | | |]; subst; clear HtypR.

  inversion HtypR1 as [|? G ? ? ? ? sR rho t Htrans Hneq Hlookupdual Hlookupvalue Hchoice ? HtypR| | | | | | | ]; subst; clear HtypR1.
  destruct Hchoice; [
    SCase "communicated stateful value"%string;
    destruct Hneq as [Hneq | Hneq]; [
      subst; apply preservation_interaction_stateful with (2:=H0) (3:=Hpart) (5:=Htrans); auto
      | assert (G = CTX.remove (v, rho) GR \/ G = GR) as Heq; [auto|]
    ]
    | SCase "communicated stateless value"%string;
      destruct H; assert (G = CTX.remove (v, rho) GR \/ G = GR) as Heq; [auto|]
  ];
  apply preservation_interaction_stateless with (G:=G) (2:=H0) (3:=Hpart) (5:=Htrans); auto.


  Case "structural equivalence"%string.
  rewrite (struct_equiv_preserves_typed P1 P2 H) in Htyp.
  apply IHHredn in Htyp.
  destruct Htyp as [G2 Htyp].
  rewrite (struct_equiv_preserves_typed Q2 Q1 H0) in Htyp.
  destruct Htyp as [Htyp Hpres].
  exists G2; split; auto.
  auto.


  Case "IsEq"%string.
  inversion Htyp; subst.
  exists G1.
  split.
  apply H6.
  apply token_lookup in H2; injection H2; intros; subst.
  apply token_lookup in H4; injection H4; intros; subst.
  reflexivity.
  apply CPNoInteraction; reflexivity.


  Case "IsNotEq"%string.
  inversion Htyp; subst.
  exists G1.
  split.
  apply H7.
  apply token_lookup in H3; injection H3; intros; subst.
  apply token_lookup in H5; injection H5; intros; subst.
  assumption.
  apply CPNoInteraction; reflexivity.
  
  
  Case "Par"%string.
  inversion Htyp; subst; clear Htyp.
  apply IHHredn in H3; [|eapply balanced_partition; eauto].
  destruct H3 as [G2 H3]; destruct H3 as [Htyp Hpres].
  exists (CTX.union G2 GR).
  destruct (ctx_preservation_partition _ _ _ _ _ H1 Hpres) as [Hpart2 Hpres2].
  split; auto.
  apply TypPar with (GL:=G2) (GR:=GR); auto.


  Case "New"%string.
  inversion Htyp; subst; clear Htyp.

  assert
    (forall i : free_id, 
      ~ In i (free_ids_context G1 ++ free_ids_proc P ++ L ++ L0)
      -> exists G2', 
        ((G2' |-p open_proc i 0 Q)
          /\ 
          (ctx_preservation 
            (CTX.add (ValName (Nm (Free i)), TChannel s) (CTX.add (ValName (CoNm (Free i)), TChannel (SDual s)) G1))
            G2'
            (expand_new_obs_choice noc i)
          )
        )
    ).
  intros i Hnotin.
  repeat rewrite in_app_iff in Hnotin. 
  assert (~ In i (free_ids_context G1)) as HnotinG1; [intuition|].
  assert (~ In i (free_ids_proc P)) as HnotinP; [intuition|].
  assert (~ In i L) as HnotinL; [intuition|].
  assert (~ In i (L ++ free_ids_proc P)) as HnotinLP; [contradict Hnotin; rewrite in_app_iff in Hnotin; destruct Hnotin; tauto|].
  assert (~ In i L0) as HnotinL0; [contradict Hnotin; tauto|].
  specialize (H0 i HnotinLP).
  specialize (H4 i _ HnotinL0 eq_refl).
  specialize (H1 i HnotinLP (CTX.add (ValName (Nm (Free i)), TChannel s) (CTX.add (ValName (CoNm (Free i)), TChannel (SDual s)) G1))).
  apply H1 in H4.
  apply H4.
  apply ctx_preservation_extension; auto.

  destruct (fresh_free_id_exists (L ++ L0 ++ (free_ids_proc P) ++ (free_ids_proc Q) ++ (free_ids_context G1))) as [x].
  assert (~ In x L0) as HnotinxL; [contradict H3; (repeat rewrite in_app_iff); tauto|].
  assert (~ In x (free_ids_proc P)) as HnotinxP; [contradict H3; (repeat rewrite in_app_iff); tauto|].
  assert (~ In x (free_ids_proc Q)) as HnotinxQ; [contradict H3; (repeat rewrite in_app_iff); tauto|].
  assert (~ In x (free_ids_context G1)) as HnotinxG1; [contradict H3; (repeat rewrite in_app_iff); tauto|].
  assert (~ In x (L ++ free_ids_proc P)) as HnotinxLP; [contradict H3; (repeat rewrite in_app_iff) ; (repeat rewrite in_app_iff in H3); tauto|].

  pose (H4 x _ HnotinxL eq_refl) as HtypOpenP.
  pose (ctx_preservation_extension G1 _ s HnotinxG1 Hprespre) as Hprespreext.
  destruct (H1 _ HnotinxLP _ Hprespreext HtypOpenP) as [G2 Hu]; destruct Hu as [HtypOpenQ Hpres].
  clear HtypOpenP; clear Hprespreext.

  apply ctx_preservation_extension_inverse with (x:=x) in Hpres; auto; simpl; auto.
  destruct Hpres as [G2' Hpres]; destruct Hpres as [t Hpres]; destruct Hpres as [HeqG2 Hcases].
  exists G2'.
  split; [
    | destruct Hcases as [Hcases|Hcases]; [
      destruct Hcases as [Hu1 Hu2]; subst; auto;
        inversion H; subst; simpl in *; [
          auto
          | (repeat rewrite in_app_iff in H3);
            inversion Hu2; subst; 
              inversion H10; subst; 
                contradict H3; do 4 right; rewrite free_ids_context_iff; eexists; eexists; split; eauto; simpl; auto
        ]
      | destruct Hcases as [m Hu]; destruct Hu as [Hu1 Hu2]; destruct Hu2 as [Hu2 Hu3];
        inversion H; subst; simpl in *; auto; [
          inversion H; subst; 
            (repeat rewrite in_app_iff in H3); 
            inversion Hu3; subst; simpl in H6; contradiction H3; right; right; left; apply H6; auto
          | apply CPNoInteraction; symmetry; assumption
        ]
    ]
  ].

  apply TypNew with (L:=x :: free_ids_proc P ++ free_ids_proc Q ++ free_ids_context G1 ++ L) (s:=t).
  intros y G' Hnotinyall Heq; subst.


  assert (~ In y (free_ids_context G2)) as HnotinyfrG2.
  destruct Hcases as [Hcases|Hcases]; [destruct Hcases as [Heq Hpres2]; subst|].

  eapply ctx_preservation_free_ids_context; eauto.
  eapply ctx_preservation_eq; [reflexivity | | symmetry; eauto].

  apply ctx_preservation_real_extension; [|apply Hpres2]; auto.
  contradict Hnotinyall.
  rewrite free_ids_context_iff in Hnotinyall.
  destruct Hnotinyall as [u Hnotinyall]; destruct Hnotinyall as [rho Hnotinyall]; destruct Hnotinyall as [Hu1 Hu2].
  (repeat rewrite CTXFacts.add_iff in Hu1).
  simpl.
  (repeat rewrite in_app_iff).
  destruct Hu1 as [Hu1|Hu1]; [|destruct Hu1 as [Hu1|Hu1]]; 
    try solve [injection Hu1; intros; subst; simpl in Hu2; left; tauto].
  right; right; right; left.
  rewrite free_ids_context_iff.  
  eexists; eexists; split; eauto.

  destruct Hcases as [m Hu1]; destruct Hu1 as [Hu1 Hu2]; destruct Hu2 as [Hu2 Hu2a].
  contradict Hnotinyall.
  rewrite free_ids_context_iff in Hnotinyall.
  destruct Hnotinyall as [u Hnotinyall]; destruct Hnotinyall as [rho Hnotinyall]; destruct Hnotinyall as [Hu3 Hu4].
  rewrite HeqG2 in Hu3.
  rewrite <- Hu2 in Hu3.
  (repeat rewrite CTXFacts.add_iff in Hu3).
  simpl.
  (repeat rewrite in_app_iff).
  destruct Hu3 as [Hu3|Hu3]; [|destruct Hu3 as [Hu3|Hu3]]; 
    try solve [injection Hu3; intros; subst; simpl in Hu4; left; tauto].
  right; right; right; left.
  rewrite free_ids_context_iff.  
  eexists; eexists; split; eauto.


  assert (~ In x (free_ids_context G2')).
  destruct Hcases as [Hcases|Hcases]; [
    destruct Hcases as [Heq Hcases]; subst
    | destruct Hcases as [m Htrans]; destruct Htrans as [Htrans Heq]; destruct Heq as [Heq Hother]
  ].
  apply ctx_preservation_free_ids_context with (1:=Hcases); auto.
  contradict HnotinxG1.
  rewrite free_ids_context_iff in HnotinxG1.
  destruct HnotinxG1 as [u HnotinxG1]; destruct HnotinxG1 as [rho HnotinxG1]; destruct HnotinxG1 as [Hu1 Hu2].
  rewrite <- Heq in Hu1.
  rewrite free_ids_context_iff.
  exists u; exists rho; auto.


  eapply ctx_equal_preserves_typed.
  rewrite <- (freeid_rename_proc_open Q x y 0); auto.
  apply typed_rename.
  apply HtypOpenQ.
  auto.

  intros a; destruct a as [u rho]; rewrite freeid_rename_ctx_characterization; auto.
  split; intros Hin.
  destruct Hin as [v Hin]; destruct Hin as [Heq Hin]; subst.
  rewrite HeqG2 in Hin.
  (repeat rewrite CTXFacts.add_iff in Hin).
  destruct Hin as [Hin|Hin]; [|destruct Hin as [Hin|Hin]].
  injection Hin; intros; subst; simpl.
  destruct (string_dec x x); [apply CTXFacts.add_1; reflexivity|contradict n; auto].
  injection Hin; intros; subst; simpl.
  destruct (string_dec x x); [apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity|contradict n; auto].
  do 2 apply CTXFacts.add_2.

  rewrite freeid_rename_value_non_free_id; auto.
  contradict H5.
  rewrite free_ids_context_iff.
  exists v; exists rho; split; auto.

  (repeat rewrite CTXFacts.add_iff in Hin).
  destruct Hin as [Heq | Hin]; [|destruct Hin as [Heq | Hin]]; try (injection Heq; intros; subst).
  exists (Nm (Free x)); split; simpl.
  destruct (string_dec x x); [|contradict n; auto]; reflexivity.
  rewrite HeqG2.
  apply CTXFacts.add_1; auto.
  exists (CoNm (Free x)); split; simpl.
  destruct (string_dec x x); [|contradict n; auto]; reflexivity.
  rewrite HeqG2.
  apply CTXFacts.add_2; apply CTXFacts.add_1; auto.
  exists u; split.
  rewrite freeid_rename_value_non_free_id; auto.
  contradict H5.
  rewrite free_ids_context_iff.
  exists u; exists rho; split; auto.

  rewrite HeqG2; auto.
  apply CTXFacts.add_2; apply CTXFacts.add_2; auto.
Qed.  
  
(* ============================================================================= *)

Theorem subject_reduction : 
  forall (G1 : ctx) (P Q : proc) (alpha : obs),
    reduction P Q alpha ->
    G1 |-p P ->
    balanced G1 ->
    exists G2, ((G2 |-p Q) /\ ctx_preservation G1 G2 alpha).
Proof.
  intros.
  eapply subject_reduction_alt; eauto.
Qed.

