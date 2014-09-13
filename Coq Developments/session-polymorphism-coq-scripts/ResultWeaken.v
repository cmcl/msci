Require Export Arith.EqNat.
Require Export Arith.Lt.
Require Export Arith.Compare_dec.
Require Export List.
Require Export ListLocal.
Require Import String.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import TacticsLocal.
Require Import TypeAssignmentPoly.
Require Import ResultOpenClose.
Require Import ResultBasics.

(* ============================================================================= *)

Lemma partition_typed_weaken_left : 
  forall GL P, 
    GL |-p P
    ->
    forall G GR,
      G |-part GL (+) GR
      -> 
      G |-p P.
Proof.
  intros GL P Htyp_GLP.

  induction Htyp_GLP; intros Gu GuR Hpart_G.

  Case "Input"%string.
  eapply TypPrefixInput with (L := (free_ids_context Gu) ++ L); intros.
  SCase "u:TChannel ?"%string.
  eapply partition_lookup_left; eauto.
  SCase "free_values_in_context Gu P"%string.
  eapply partition_free_values_in_context_left; eauto.
  SCase "open_proc x 0 P"%string.
  eapply H2; eauto; subst; intuition; clear H0 H1 H2.
  apply ctx_add_preserves_partition_left; [ constructor | constructor; [constructor|] | ].
  SSCase ""%string.
  intros v sigma.
  match goal with | |- context[CTX.In ?a ?G] => destruct (CTXProperties.In_dec a G) as [i|n]; [right|left;auto] end.
  unfold ctx_replace in i; rewrite CTXFacts.add_iff in i; rewrite CTXFacts.remove_iff in i; destruct i.
  injection H0; intros; subst.
  intros Heq.
  apply H3.
  apply In_app1.
  eapply free_ids_context_vs_context; eauto.
  eapply partition_is_subset_left; eauto.
  inversion H; eauto.
  intros Heq.
  apply H3.
  apply In_app1.
  eapply free_ids_context_vs_context; eauto.
  destruct H0; eauto.
  SSCase "replace |-part"%string.
  apply ctx_replace_preserves_partition_left; eauto.
  inversion H; intuition.
  intros Hin.
  inversion Hpart_G as [? ? ? _ _ U1]; subst.
  specialize (U1 u (TChannel s)).
  intuition.
  contradict H0.
  inversion H; intuition.
  inversion H1 as [? U1|]; subst.
  erewrite U1; eauto.

  Case "Output"%string.
  destruct H3; subst.
  SCase "Not Stateless"%string.
  eapply TypPrefixOutput; eauto; try (solve [eapply partition_lookup_left; eauto]).
  eapply IHHtyp_GLP with (GR := (CTX.remove (v, rho) GuR)).

  destruct (value_dec u v) as [He|Hn]; [subst|].
  SSCase "u=v /\ |-st rho"%string.
  destruct H0 as [H0|H0]; [contradict H0; reflexivity|].
  assert (rho=TChannel s); [|subst].
  assert (G|-wf).
  eapply partition_wf_left; eauto.
  inversion H3; subst.
  apply (H5 v rho (TChannel s)).
  inversion H2; auto; subst.
  inversion H1; subst.
  inversion H8; subst.
  assert (free_value k) as Hu; [eapply H10; eauto|inversion Hu].
  inversion H1; subst; auto.
  unfold ctx_replace.
  eapply ctx_equal_part_1; [| (apply add_cong; symmetry; apply ctx_remove_not_in; rewrite CTXFacts.remove_iff; tauto)].
  eapply ctx_equal_part_2; [| (apply add_cong; symmetry; apply ctx_remove_not_in; rewrite CTXFacts.remove_iff; tauto)].
  apply ctx_replace_preserves_partition_left.
  inversion H2; auto.
  rewrite CTXFacts.remove_iff; intros Hin; contradict Hin; tauto.
  apply partition_comm.
  apply ctx_remove_preserves_partition_left_2.
  inversion H2; auto.
  apply partition_comm; auto.

(*
  SearchAbout partition.
ctx_replace_preserves_partition_left.
.

  eapply ctx_equal_part_1.
  apply ctx_add_preserves_partition_left.
  eapply channel_lookup_yields_free_value; eauto.
  constructor.
  eapply channel_lookup_yields_free_value; eauto.
  intros w sigma.
  destruct (CTX.E.eq_dec (w, sigma) (v, TChannel s)).
  injection e; intros; subst; clear e.
  left; rewrite CTXFacts.remove_iff; tauto.
  
  rewrite CTXFacts.remove_1.

  SearchAbout free_value.
  Focus 3.
  apply ctx_remove_preserves_partition_both; [rewrite CTXFacts.remove_iff; tauto|].
  assert (CTX.In (v, TChannel s) Gu).
  assert (Gu |-v v : TChannel s).
  eapply partition_lookup_left; eauto.
  inversion H3; subst; auto.
  eapply ctx_equal_part_1; [apply Hpart_G | intros a; destruct a; split; rewrite CTXFacts.add_iff; rewrite CTXFacts.remove_iff; intros Hin].
  destruct (CTX.E.eq_dec (v, TChannel s) (v0, t0)).
  injection e; intros; subst; clear e.
  left; auto.
  right; split; auto.
  destruct Hin as [Hin|Hin]; [|destruct Hin as [Hin1 Hin2]].
  injection Hin; intros; subst; clear Hin; auto.
  auto.
  Unfocus.
  SearchAbout partition.
*)

  SSCase "u<>v"%string.
(*  destruct H0 as [H0|H0]. *)
  apply ctx_replace_preserves_partition_left.
  rewrite CTXFacts.remove_iff; inversion H1; subst; crush.
  intros HinGuR.
  inversion Hpart_G as [? ? ? _ _ U1]; subst.
  specialize (U1 u (TChannel s)).
  destruct U1 as [U2|U2].
  contradict U2.
  inversion H1; subst; apply H4.
  destruct U2 as [U3|U3].
  contradict U3; rewrite CTXFacts.remove_iff in HinGuR; destruct HinGuR; auto.
  inversion U3; subst.
  specialize (H4 (MOut rho) t).
  rewrite <- H4; auto.
  apply ctx_remove_preserves_partition_left; eauto.
  rewrite CTXFacts.remove_iff; intuition.
  apply partition_comm.
  destruct (is_token_dec v) as [i|n].
  apply ctx_remove_preserves_partition_left_2; (try apply partition_comm); auto.
  inversion H2; subst; auto.
  specialize (i k); contradict i; auto.
  unfold is_not_token in n.
  apply is_not_token_value in n.
  elim n; intros; subst.
  apply partition_remove_token.
  apply partition_comm; auto.

  SCase "Stateless"%string.
  destruct H3; subst.
  eapply TypPrefixOutput; [eauto|auto| eapply partition_lookup_left; eauto | eapply partition_lookup_left; eauto | right; eauto | eauto |].
  eapply IHHtyp_GLP with (GR := GuR).
  apply ctx_replace_preserves_partition_left.
  apply lookup_channel_in; auto.
  inversion Hpart_G as [? ? ? _ _ U1]; subst.
  specialize (U1 u (TChannel s)); destruct U1 as [U2|U2]; [intros|destruct U2 as [U3|U3]].
  contradict U2; apply lookup_channel_in; auto.
  intros U4; contradict U3; assumption.
  intros; inversion U3 as [U4 U5|]; subst.
  erewrite U5; eauto.
  auto.

  Case "Par"%string.
  apply TypPar with (GL := CTX.union GL (CTX.diff GuR G)) (GR := GR).
  apply partition_weaken_into_left_1; auto.
  apply IHHtyp_GLP1 with (GR:=(CTX.diff GuR G)); eauto.
  eapply partition_weaken_into_left_2; eauto.
  apply IHHtyp_GLP2 with (GR0:=CTX.empty); eauto.
  eapply partition_empty_old; eauto.

  Case "Sum"%string.
  apply TypSum.
  eapply IHHtyp_GLP1; eauto.
  eapply IHHtyp_GLP2; eauto.
  
  Case "IsEq"%string.
  eapply TypIsEq; eauto.
  eapply partition_lookup_left; eauto.
  eapply partition_lookup_left; eauto.
  eapply partition_free_values_in_context_left; eauto.

  Case "IsNotEq"%string.
  eapply TypIsNotEq; eauto.
  eapply partition_lookup_left; eauto.
  eapply partition_lookup_left; eauto.
  eapply partition_free_values_in_context_left; eauto.

  Case "New"%string.
  apply TypNew with (s:=s) (L := (free_ids_context Gu) ++ L); subst.
  intros x G' Hin Heq; subst.
  eapply H0 with (GR:=GuR).
  contradict Hin; apply in_or_app; right; auto.
  reflexivity.
  apply ctx_add_preserves_partition_left_dual_names.
  apply FContext. 
  apply FNm.
  intros v sigma.
  destruct (list_eq_dec string_dec (free_ids_value (Nm (Free x))) (free_ids_value v)) as [e|n]; subst; [left|right]; auto.
  intros H2; contradict Hin.
  apply in_or_app; left.
  eapply free_ids_context_vs_context; eauto.
  auto.
  
  Case "Rep"%string.
  eapply TypRep with (G':=G'); eauto.
  inversion Hpart_G; auto.
  intros a Hin.
  apply (partition_is_subset_left a) in Hpart_G; auto.

  Case "Zero"%string.
  apply TypZero.
  eapply partition_wf; eauto.

Qed.

(* ============================================================================= *)

Lemma typed_preserved_by_add : 
  forall x s G P,
    ~ In x (free_ids_context G)
    ->
    G |-p P
    ->
    CTX.add (ValName (Nm (Free x)), TChannel s)
      (CTX.add (ValName (CoNm (Free x)), TChannel (SDual s)) G) |-p P.
Proof.
  intros x s G P Hin Htyp.
  eapply partition_typed_weaken_left; 
    [ | 
      eapply part_preserved_by_add_right; 
        [ | 
          eapply typed_ctx_wf 
        ]
    ]; eauto.
Qed.

(* ============================================================================= *)

Lemma weakening : 
  forall (G G1 G2 : ctx) (P : proc),
    (G1 |-p P) -> 
    (G |-part G1 (+) G2) -> 
    G |-p P.
Proof.
  intros G G1 G2 P Htyp Hpart.
  eapply partition_typed_weaken_left; eauto.
Qed.

(* ============================================================================= *)
