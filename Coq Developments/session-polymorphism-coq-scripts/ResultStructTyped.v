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

(* ============================================================================= *)

Lemma struct_equiv_preserves_typed_par_sym :
  forall P Q G, (G |-p P|||Q -> G |-p Q|||P).
Proof.
  intros P Q G Htyp.
  inversion Htyp; subst.
  apply partition_comm in H1.
  apply TypPar with (GL:=GR) (GR:=GL); auto.
Qed.

Lemma struct_equiv_preserves_typed_sum_sym :
  forall P Q G, (G |-p P+++Q -> G |-p Q+++P).
Proof.
  intros P Q G Htyp.
  inversion Htyp; subst.
  apply TypSum; auto.
Qed.

(* ============================================================================= *)

Lemma struct_equiv_preserves_typed_par_assoc :
  forall P Q R G, (G |-p (P|||Q)|||R -> G |-p P|||(Q|||R)).
Proof.
  intros P Q R G Htyp.
  inversion Htyp; clear Htyp; subst.
  inversion H3; clear H3; subst.
  apply TypPar with (GL:=GL0) (GR:=CTX.union GR0 GR); auto; [|apply TypPar with (GL:=GR0) (GR:=GR); auto].

  inversion H1; inversion H2; subst.
  constructor; auto.
  rewrite <- CTXProperties.union_assoc.
  rewrite <- H10.
  auto.

  intros u rho.
  rewrite CTXFacts.union_iff.
  destruct (H12 u rho) as [Hu|Hu]; 
    [ left; auto
      | destruct Hu as [Hu|Hu];
        [ 
          | right; right; auto
        ]
    ].
  destruct (H3 u rho) as [Hu1|Hu1]; 
    [ left; auto
      | destruct Hu1 as [Hu1|Hu1];
        [ 
          | right; right; auto
        ]
    ].
  rewrite H10 in Hu1; rewrite CTXFacts.union_iff in Hu1.
  contradict Hu1; auto.
  right; left.
  contradict Hu1; destruct Hu1; auto; contradict Hu; auto.
  
  constructor; auto.
  reflexivity.
  
  apply subset_preserves_well_formed_ctx with (G1:=G).
  eapply partition_wf; eauto.
  apply CTXProperties.union_subset_3; [|eapply part_is_subset_right; eauto].
  eapply CTXProperties.subset_trans.
  eapply part_is_subset_right; eauto.
  eapply part_is_subset_left; eauto.

  inversion H1; inversion H2; subst.
  intros u rho.
  destruct (H3 u rho) as [Hu|Hu]; [
    | destruct Hu as [Hu|Hu]; [
      right; left; auto
      | right; right; auto
    ]
  ].
  destruct (H12 u rho) as [Hu1|Hu1]; [
    | destruct Hu1 as [Hu1|Hu1]; [
      | right; right; auto
    ]
  ].
  rewrite H10 in Hu; rewrite CTXFacts.union_iff in Hu.
  left; contradict Hu; right; auto.
  left; auto.
Qed.

(* ============================================================================= *)

Lemma struct_equiv_preserves_typed_par_assoc_alt :
  forall P Q R G, (G |-p P|||(Q|||R) -> G |-p (P|||Q)|||R).
Proof.
  intros P Q R G Htyp.
  apply struct_equiv_preserves_typed_par_sym.
  apply struct_equiv_preserves_typed_par_assoc.
  apply struct_equiv_preserves_typed_par_sym.
  apply struct_equiv_preserves_typed_par_assoc.
  apply struct_equiv_preserves_typed_par_sym.
  auto.
Qed.

(* ============================================================================= *)

Lemma typed_par_partition : 
  forall P Q G GL GR, 
    G |-p P ||| Q 
    ->
    (forall v rho, (  In v (free_values_proc P) /\ (CTX.In (v, rho) G)) <-> CTX.In (v, rho) GL)
    ->
    (forall v rho, ((~ In v (free_values_proc P) \/ In v (free_values_proc Q)) /\ (CTX.In (v, rho) G)) <-> CTX.In (v, rho) GR)
    ->
    (G |-part GL (+) GR).
Proof.
  intros P Q G GL GR Htyp HGL HGR.
  inversion Htyp; subst.
  constructor; [|eapply partition_wf; eauto|].
  intros a; destruct a; split; intros Hin.
  rewrite CTXFacts.union_iff.
  destruct (In_dec value_dec v (free_values_proc P)); 
    [ left; rewrite <- HGL; split; auto
      | right; rewrite <- HGR; split; auto
    ].  
  rewrite CTXFacts.union_iff in Hin; destruct Hin; 
    [ rewrite <- HGL in H
      | rewrite <- HGR in H
    ]; destruct H; auto.

  intros u rho.
  destruct (CTXProperties.In_dec (u, rho) GL) as [i|n]; [|left; auto].
  rewrite <- HGL in i; destruct i as [Hu1 Hu2].
  destruct (CTXProperties.In_dec (u, rho) GR) as [i|n]; [|right; left; auto].
  rewrite <- HGR in i; destruct i as [Hu3 _]; destruct Hu3 as [Hu3|Hu3].
  contradict Hu3; auto.

  assert (CTX.In (u, rho) GL0).
  eapply part_typed_find_type; eauto.
  assert (CTX.In (u, rho) GR0).
  apply partition_comm in H1.
  eapply part_typed_find_type; eauto.

  inversion H1; subst.
  specialize (H6 u rho).
  destruct H6; [
    contradict H6; auto 
    | destruct H6; [
      contradict H6; auto
      | right; right; auto
    ]
  ].
Qed.

Lemma typed_par_left : 
  forall P Q G GL, 
    G |-p P ||| Q 
    ->
    (forall v rho, (  In v (free_values_proc P) /\ (CTX.In (v, rho) G)) <-> CTX.In (v, rho) GL)
    ->
    (GL |-p P).
Proof.
  intros P Q G GL Htyp HGL.
  inversion Htyp; subst.

  assert (CTX.Subset GL GL0).
  intros a; destruct a; rewrite <- HGL.
  intros Hin; destruct Hin as [Hin1 Hin2].
  apply (free_values_in_context_1 _ _ H3) in Hin1.
  destruct Hin1 as [sigma Hin1]; eauto.
  replace t with sigma; auto.
  apply partition_is_subset_left with (G:=G) (GR:=GR) in Hin1; auto.
  inversion H1; subst.
  inversion H0; subst.
  rewrite H6 with (u:=v) (rho:=t) (sigma:=sigma); auto.
  
  eapply typed_strengthen; eauto.
  intros v Hin.
  apply free_values_in_context_1 in H3.
  specialize (H3 v Hin); destruct H3 as [sigma H3].
  exists sigma.
  rewrite <- HGL.
  split; auto.
  eapply partition_is_subset_left; eauto.
Qed.

Definition typed_par_left_exists (P : proc) (G : CTX.t) : CTX.t := 
  CTX.filter
  (fun a => 
    match a with 
      | (v, rho) => 
        if (In_dec value_dec v (free_values_proc P)) 
          then
            true
          else 
            false
    end)
  G.

Lemma typed_par_left_exists_spec : 
  forall P G,
    (forall v rho, (  In v (free_values_proc P) /\ (CTX.In (v, rho) G)) <-> CTX.In (v, rho) (typed_par_left_exists P G)).
Proof.
  intros P G v rho; split; unfold typed_par_left_exists; (repeat rewrite CTX.filter_spec);
    try solve [intros a b; destruct a; destruct b; intros Heq; injection Heq; intros; subst; clear Heq; reflexivity].

  intros Hin; destruct Hin; split; auto.
  destruct (in_dec value_dec v (free_values_proc P)); auto.

  intros Hin; destruct Hin; split; auto.
  destruct (in_dec value_dec v (free_values_proc P)) in H0; auto.
  contradict H0; auto.
Qed.

Lemma typed_par_right_partition : 
  forall P Q G GR,
    GR |-wf
    ->
    (forall (v : value) (rho : type), (~ In v (free_values_proc P) \/ In v (free_values_proc Q)) /\ CTX.In (v, rho) G <-> CTX.In (v, rho) GR)
    ->
    exists GR', (GR |-part typed_par_left_exists Q G (+) GR').
Proof.
  intros P Q G GR Hwf HGR.
  exists
    (CTX.filter
      (fun a => 
        match a with
          | (v, rho) => 
            if (In_dec value_dec v (free_values_proc P)) 
              then
                false
              else 
                (if (In_dec value_dec v (free_values_proc Q)) 
                  then
                    false
                  else 
                    true)
        end)
      G).
  constructor; auto.

  intros a; destruct a; split; intros Hin; rewrite CTXFacts.union_iff in *.
  rewrite CTX.filter_spec; try solve [intros a b; destruct a; destruct b; intros Heq; injection Heq; intros; subst; clear Heq; reflexivity].
  rewrite <- HGR in Hin; 
    destruct Hin as [Hin1 Hin2]; destruct Hin1 as [Hin1|Hin1]; 
      destruct (In_dec value_dec v (free_values_proc P)); destruct (In_dec value_dec v (free_values_proc Q));
        try solve [left; contradict Hin1; auto];
          try solve [left; rewrite <- typed_par_left_exists_spec; auto].
  right; split; auto.
  
  rewrite <- HGR.
  destruct Hin as [Hin|Hin].
  rewrite <- typed_par_left_exists_spec in Hin; destruct Hin as [Hin1 Hin2]; split; auto.
  rewrite CTX.filter_spec in Hin;
    try solve [intros a b; destruct a; destruct b; intros Heq; injection Heq; intros; subst; clear Heq; reflexivity].
  destruct Hin as [Hin1 Heq]; split; auto.
  destruct (In_dec value_dec v (free_values_proc P)); destruct (In_dec value_dec v (free_values_proc Q)); auto.
  discriminate Heq.

  intros v rho.
  rewrite CTX.filter_spec;
    try solve [intros a b; destruct a; destruct b; intros Heq; injection Heq; intros; subst; clear Heq; reflexivity].
  destruct (In_dec value_dec v (free_values_proc P)).
  destruct (In_dec value_dec v (free_values_proc Q)).
  right; left; intuition.
  right; left; intuition.
  destruct (In_dec value_dec v (free_values_proc Q)).
  right; left; intuition.
  left; rewrite <- typed_par_left_exists_spec; intuition.
Qed.  

Lemma typed_par_right : 
  forall P Q G GR, 
    G |-p P ||| Q 
    ->
    (forall v rho, ((~ In v (free_values_proc P) \/ In v (free_values_proc Q)) /\ (CTX.In (v, rho) G)) <-> CTX.In (v, rho) GR)
    ->
    (GR |-p Q).
Proof.
  intros P Q G GR Htyp HGR.
  inversion Htyp; subst.
  
  assert ((typed_par_left_exists Q G) |-p Q) as Hu1.
  apply typed_par_left with (G:=G) (P:=Q) (Q:=P); auto.
  apply struct_equiv_preserves_typed_par_sym; auto.
  intros v rho; rewrite typed_par_left_exists_spec; reflexivity.

  assert (GR |-wf) as Hwf.
  apply subset_preserves_well_formed_ctx with (G1:=G).
  eapply typed_ctx_wf; eauto.
  intros a; destruct a; rewrite <- HGR; intuition.

  destruct (typed_par_right_partition P Q G GR Hwf HGR).
  eapply partition_typed_weaken_left with (G:=GR) (GL:=typed_par_left_exists Q G); eauto.
Qed.

(* ============================================================================= *)

Lemma struct_equiv_preserves_typed_par_sym_left :
  forall P Q G, 
    G |-p New (insert_proc 0 P ||| Q)
    -> 
    (typed_par_left_exists P G) |-p P.
Proof.
  intros P Q G Htyp.
  inversion Htyp; subst; simpl in *.
  
  assert (exists x : free_id, ~ In x ((free_ids_proc P) ++ (free_ids_context G) ++ L)).
  apply fresh_free_id_exists.
  elim H; clear H.
  intros x Hin.
  
  apply typed_par_left with (G:=CTX.add (ValName (Nm (Free x)), TChannel s) (CTX.add (ValName (CoNm (Free x)), TChannel (SDual s)) G)) (Q:=open_proc x 0 Q).
  replace P with (open_proc x 0 (insert_proc 0 P)); try solve [rewrite <- open_insert_proc; auto].
  eapply H1; auto.
  
  contradict Hin; repeat (apply in_or_app; right); assumption.

  assert (forall sigma, ~ (CTX.In (ValName (Nm (Free x)), sigma) G) /\ ~ (CTX.In (ValName (CoNm (Free x)), sigma) G)) as Hnotin3.
  assert (~ In x (free_ids_context G)) as Hnotin2.
  contradict Hin; repeat (apply in_or_app; (try solve [left; auto] || right)).
  rewrite free_ids_context_iff in Hnotin2.
  intros sigma.
  split; contradict Hnotin2; eexists; exists sigma; split; eauto; simpl; left; reflexivity.

  assert (forall v, In v (free_values_proc P) -> In v (free_values_proc (New (insert_proc 0 P ||| Q)))) as Hu.
  intros v Hin1; simpl.
  apply in_or_app; left.
  apply free_values_insert_proc1; auto.

  intros v rho.
  rewrite <- typed_par_left_exists_spec.
  split; intros Hin1; destruct Hin1 as [Hin1 Hin2]; split; auto; repeat (rewrite CTXFacts.add_iff in *).
  repeat (destruct Hin2 as [Hin2|Hin2]); auto; injection Hin2; intros; subst; clear Hin2;
    apply Hu in Hin1; eapply free_values_in_context_1 in Hin1; eauto; 
      destruct Hin1 as [sigma ?]; specialize (Hnotin3 sigma); 
        destruct Hnotin3 as [Hnotin3a Hnotin3b]; try solve [contradict Hnotin3a; auto]; try solve [contradict Hnotin3b; auto].

  right; right; auto.
Qed.  

(* ============================================================================= *)

Definition typed_par_right_exists (P : proc) (Q : proc) (G : CTX.t) : CTX.t := 
  CTX.filter
  (fun a => 
    match a with 
      | (v, rho) => 
        if (In_dec value_dec v (free_values_proc P)) 
          then
            (if (In_dec value_dec v (free_values_proc Q)) 
              then
                true
              else 
                false)
          else 
            true 
    end)
  G.

(* Could have used typed_par_right in earlier statements? *)
Lemma typed_par_right_exists_spec : 
  forall P Q G,
    forall v rho, (((~ In v (free_values_proc P) \/ In v (free_values_proc Q)) /\ (CTX.In (v, rho) G)) <-> CTX.In (v, rho) (typed_par_right_exists P Q G)).
Proof.
  intros P Q G v rho; split; unfold typed_par_right_exists; (repeat rewrite CTX.filter_spec);
    try solve [intros a b; destruct a; destruct b; intros Heq; injection Heq; intros; subst; clear Heq; reflexivity].

  intros Hin; destruct Hin; split; auto.
  destruct (in_dec value_dec v (free_values_proc P)); destruct (in_dec value_dec v (free_values_proc Q)); auto.
  destruct H; intuition.

  intros Hin; destruct Hin; split; auto.
  destruct (in_dec value_dec v (free_values_proc P)) in H0; destruct (in_dec value_dec v (free_values_proc Q)) in H0; auto.
  discriminate H0.
Qed.

(* ============================================================================= *)

Definition CTX_add_names (x : free_id) (s : session) (G : CTX.t) : CTX.t := 
  CTX.add (ValName (Nm (Free x)), TChannel s) (CTX.add (ValName (CoNm (Free x)), TChannel (SDual s)) G).

Lemma struct_equiv_preserves_typed_par_sym_right :
  forall P Q G, 
    G |-p New (insert_proc 0 P ||| Q)
    ->
    exists L, 
      exists s, 
        (forall x,
          ~ In x ((free_ids_proc P) ++ (free_ids_context G) ++ L)
          ->
          CTX_add_names x s (typed_par_right_exists P Q G) |-p open_proc x 0 Q).
Proof.
  intros P Q G Htyp.
  inversion Htyp; subst; simpl in *.

  exists L.
  exists s.
  intros x Hnotin.

  assert (~ In x L) as Hnotin1.
  contradict Hnotin; repeat (apply in_or_app; right); assumption.
  specialize (H1 x _ Hnotin1 eq_refl); clear Hnotin1.

  eapply typed_par_right; eauto.

  intros v rho.
  
  clear H1.

  assert (~ In x (free_ids_proc P)) as Hnotin3; [contradict Hnotin; apply in_or_app; left; auto | ].

  split; intros Hin; unfold CTX_add_names in *; 
  repeat
    (match goal with 
       | [ H : False |- _ ] => destruct H
       | [ H : _ \/ _ |- _ ] => destruct H
       | [ H : _ /\ _ |- _ ] => destruct H
       | [ |- _ /\ _ ] => split
       | [ H : CTX.In _ (CTX.add _ _) |- _ ] => repeat (rewrite CTXFacts.add_iff in H)
       | [ |- CTX.In _ (CTX.add _ _) ] => repeat (rewrite CTXFacts.add_iff)
       | [ H : (_, _) = (_, _) |- _ ] => injection H; intros; subst; clear H
     end); 
    (try solve [left; auto]);
    (try solve [right; auto]); 
    (try rewrite <- typed_par_right_exists_spec).

  right; right; split; auto.
  rewrite <- open_insert_proc in H; auto.

  right; right; split; auto.
  right.
  apply free_values_open_proc1 in H; destruct H; auto.

  assert (~ In x (free_ids_context G)) as Hnotin2.
  contradict Hnotin; repeat (apply in_or_app; (try solve [left; auto]); right); assumption.
  contradict H; eapply free_ids_value_context_contra; eauto.

  rewrite <- open_insert_proc.
  left; contradict Hnotin3; rewrite free_ids_proc_alt.
  rewrite in_flat_map.
  eexists; split; eauto.
  left; auto.

  rewrite <- open_insert_proc.
  left; contradict Hnotin3; rewrite free_ids_proc_alt.
  rewrite in_flat_map.
  eexists; split; eauto.
  left; auto.

  rewrite <- open_insert_proc.
  rewrite <- typed_par_right_exists_spec in H; destruct H as [Hu1 Hu2]; destruct Hu1 as [Hu1|Hu1].
  left; auto.
  right.
  apply free_values_open_proc2; auto.

  rewrite <- typed_par_right_exists_spec in H; destruct H as [Hu1 Hu2]; destruct Hu1 as [Hu1|Hu1];
    right; right; auto.
Qed.  

(* ============================================================================= *)

Lemma struct_equiv_preserves_typed_par_part :
  forall P Q G, 
    G |-p New (insert_proc 0 P ||| Q)
    ->
    G |-part (typed_par_left_exists P G) (+) (typed_par_right_exists P Q G).
Proof.
  intros P Q G Htyp.
  inversion Htyp; subst.
  constructor.

  intros a; destruct a.
  rewrite CTXFacts.union_iff; rewrite <- typed_par_left_exists_spec; rewrite <- typed_par_right_exists_spec.
  split; intros Hin.
  destruct (In_dec value_dec v (free_values_proc P)); [left | right]; split; auto.

  destruct Hin as [Hin|Hin]; 
    [destruct Hin as [Hin1 Hin2] | destruct Hin as [Hin1 Hin2]]; auto.

  eapply typed_ctx_wf; eauto.

  intros v rho.
  rewrite <- typed_par_left_exists_spec; rewrite <- typed_par_right_exists_spec.

  destruct (CTXProperties.In_dec (v, rho) G) as [i1|n1]; [|left; contradict n1; destruct n1; auto].
  destruct (In_dec value_dec v (free_values_proc P)) as [i2|n2]; [right|left; contradict n2; destruct n2; auto].
  destruct (In_dec value_dec v (free_values_proc Q)) as [i3|n3]; [right|left; contradict n3; destruct n3; intuition].

  assert (exists x : free_id, ~ In x L) as Hu1; [apply fresh_free_id_exists|destruct Hu1 as [x Hu1]].
  specialize (H1 x _ Hu1 eq_refl).
  simpl in H1; rewrite <- open_insert_proc in H1.
  inversion H1; subst.
  pose (free_values_in_context_1 _ _ H4) as Hfvc1.
  pose (free_values_in_context_1 _ _ H5) as Hfvc2.
  unfold free_values_in_context in *.
  specialize (Hfvc1 _ i2); destruct Hfvc1 as [sigma1 Hfvc1].
  eapply free_values_open_proc2 in i3.
  specialize (Hfvc2 _ i3); destruct Hfvc2 as [sigma2 Hfvc2].
  inversion H2; subst.
  assert (sigma1 = sigma2); [|subst].
  pose (partition_wf _ _ _ H2) as w; inversion w; apply (H7 v sigma1 sigma2); [eapply partition_is_subset_left|eapply partition_is_subset_right]; eauto.
  assert (rho = sigma2); [|subst].
  pose (partition_wf _ _ _ H2) as w; inversion w; apply (H7 v rho sigma2); [eapply partition_is_subset_left|eapply partition_is_subset_right]; eauto.
  eapply part_typed_find_type; eauto; subst.
  intuition.
  specialize (H3 v sigma2); destruct H3 as [H3|H3]; [|destruct H3 as [H3|H3]]; intuition.
Qed.

(* ============================================================================= *)

Lemma struct_equiv_preserves_typed_par_new : 
  forall P Q G, G |-p New (insert_proc 0 P ||| Q) -> G |-p P ||| New Q.
Proof.
  intros P Q G Htyp.
  apply TypPar with (GL:=(typed_par_left_exists P G)) (GR:=(typed_par_right_exists P Q G)).
  apply struct_equiv_preserves_typed_par_part; auto.
  eapply struct_equiv_preserves_typed_par_sym_left; eauto.

  pose (struct_equiv_preserves_typed_par_sym_right P Q G Htyp) as Htyp2.
  destruct Htyp2 as [L Htyp2]; destruct Htyp2 as [s Htyp2].

  eapply TypNew with (L:=(free_ids_proc P ++ free_ids_context G ++ L)).
  intros x G' Hnotin Heq; subst.
  specialize (Htyp2 x Hnotin).
  apply Htyp2.
Qed.

(* ============================================================================= *)

Lemma struct_equiv_preserves_typed_sum_new_left : 
  forall P Q G,
    G |-p New (insert_proc 0 P +++ Q)
    ->
    G |-p P.
Proof.
  intros P Q G Htyp.
  inversion Htyp; subst.

  assert (exists x : free_id, ~ In x ((free_ids_proc P) ++ (free_ids_context G) ++ L)).
  apply fresh_free_id_exists.
  destruct H as [x Hin].

  assert (~ In x L) as Hin2.
  contradict Hin; repeat (apply in_or_app; right; auto).

  pose (H1 x _ Hin2 eq_refl) as Hu.
  simpl in Hu.
  rewrite <- open_insert_proc in Hu.
  inversion Hu; subst.

  eapply typed_strengthen; eauto.
  intuition.

  intros u Hin3.
  apply free_values_in_context_1 in H3.
  specialize (H3 u Hin3).
  destruct H3 as [sigma Hin4].
  repeat rewrite CTXFacts.add_iff in Hin4.

  assert (~ In x (free_ids_proc P)) as Hnotin.
  contradict Hin; apply in_or_app; left; auto.

  rewrite free_ids_proc_alt in Hnotin.
  rewrite in_flat_map in Hnotin.

  destruct Hin4 as [Heq|Hin4]; [|destruct Hin4 as [Heq|Hin4]];
    try solve [injection Heq; intros; subst; clear Heq; contradict Hnotin; eexists; split; eauto; simpl; left; auto].

  eexists; eauto.
Qed.

(* ============================================================================= *)

Lemma struct_equiv_preserves_typed_sum_new_right : 
  forall P Q G,
    G |-p New (insert_proc 0 P +++ Q)
    ->
    exists L, 
      exists s, 
        (forall x,
          ~ In x ((free_ids_proc P) ++ (free_ids_context G) ++ L)
          ->
          CTX_add_names x s G |-p open_proc x 0 Q).
Proof.
  intros P Q G Htyp.
  inversion Htyp; subst.
  
  exists L; exists s; intros x Hnotin.

  assert (~ In x L) as Hnotin1.
  contradict Hnotin; repeat (apply in_or_app; right); assumption.
  specialize (H1 x _ Hnotin1 eq_refl); clear Hnotin1.

  inversion H1; subst.
  apply H4.
Qed.

(* ============================================================================= *)

Lemma struct_equiv_preserves_typed_sum_new : 
  forall P Q G,
    G |-p New (insert_proc 0 P +++ Q)
    ->
    G |-p P +++ New Q.
Proof.
  intros P Q G Htyp.
  apply TypSum.
  eapply struct_equiv_preserves_typed_sum_new_left; eauto.
  pose (struct_equiv_preserves_typed_sum_new_right P Q G Htyp) as Htyp2.
  destruct Htyp2 as [L Htyp2]; destruct Htyp2 as [s Htyp2].
  eapply TypNew with (L:=(free_ids_proc P ++ free_ids_context G ++ L)).
  intros x G' Hnotin Heq; subst.
  specialize (Htyp2 x Hnotin).
  apply Htyp2.
Qed.

(* ============================================================================= *)

Theorem struct_equiv_preserves_typed : 
  forall P Q, P == Q -> forall G, (G |-p P <-> G |-p Q).
Proof.
  intros P Q Hequiv_pq.
  induction Hequiv_pq; intros G; split; intuition.

  apply (IHHequiv_pq G); auto.
  apply (IHHequiv_pq G); auto.

  apply (IHHequiv_pq2 G); auto.
  apply (IHHequiv_pq1 G); auto.

  apply (IHHequiv_pq1 G); auto.
  apply (IHHequiv_pq2 G); auto.

  SCase "P -> P|||Zero"%string.
  apply TypPar with (GL := G) (GR := CTX.empty); auto.
  apply partition_empty_typing in H; auto.
  apply TypZero.
  apply empty_ctx_wf.

  SCase "P|||Zero -> P"%string.
  inversion H; clear H; subst.
  apply partition_typed_weaken_left with (GL:=GL) (GR:=GR); auto.

  SCase "P -> P+++Zero"%string.
  apply TypSum; auto.
  apply TypZero.
  apply typed_ctx_wf in H; auto.

  SCase "P+++Zero -> P"%string.
  inversion H; clear H; auto.

  SCase "P|||Q -> Q|||P"%string.
  apply struct_equiv_preserves_typed_par_sym; auto.

  SCase "Q|||P -> P|||Q"%string.
  apply struct_equiv_preserves_typed_par_sym; auto.

  SCase "P+++Q -> Q+++P"%string.
  apply struct_equiv_preserves_typed_sum_sym; auto.

  SCase "Q+++P -> P+++Q"%string.
  apply struct_equiv_preserves_typed_sum_sym; auto.

  SCase "(P|||Q)|||R -> P|||(Q|||R)"%string.
  apply struct_equiv_preserves_typed_par_assoc; auto.

  SCase "P|||(Q|||R) -> (P|||Q)|||R"%string.
  apply struct_equiv_preserves_typed_par_assoc_alt; auto.

  SCase "(P+++Q)+++R -> P+++(Q+++R)"%string.
  inversion H; clear H; subst; auto.
  inversion H3; clear H3; subst; auto.
  apply TypSum; auto.
  apply TypSum; auto.

  SCase "P+++(Q+++R) -> (P+++Q)+++R"%string.
  inversion H; clear H; subst; auto.
  inversion H4; clear H4; subst; auto.
  apply TypSum; auto.
  apply TypSum; auto.

  SCase "!P -> P|||(!P)"%string.
  inversion H; subst.
  apply TypPar with (GL:=G') (GR:=G); 
    [ | auto | apply TypRep with (G':=G'); intuition ].
  apply Partition; intuition.
  intros a; intuition.
  apply CTXFacts.union_1 in H0; destruct H0; intuition.
  destruct (CTXProperties.In_dec (u, rho) G'); subst.
  right; right; apply H3 with (u:=u); auto.
  left; auto.

  SCase "P|||(!P) -> !P"%string.
  inversion H; subst; intuition.
  apply partition_comm in H2.
  apply partition_typed_weaken_left with (GL:=GR) (GR:=GL); auto.

  SCase "P ||| New Q -> New (insert_proc 0 P ||| Q)"%string.
  inversion H; subst.
  inversion H5; subst.
  apply TypNew with (s:=s) (L := (free_ids_context G) ++ L).
  intros x G' Hnotin Heq; subst.
  simpl.
  rewrite <- open_insert_proc.
  apply TypPar with 
    (GL:=GL) 
    (GR:=
      CTX.add (ValName (Nm (Free x)), TChannel s)
      (CTX.add (ValName (CoNm (Free x)), TChannel (SDual s)) 
        GR)); auto; [ | apply H3; intuition ].
  apply partition_comm in H2.
  apply partition_comm.
  apply ctx_add_preserves_partition_left_dual_names.
  constructor.
  constructor.
  intros v sigma.
  destruct (CTXProperties.In_dec (v, sigma) G).
  right.
  intros Heq; contradict Hnotin.
  apply in_or_app.
  left.
  eapply free_ids_context_vs_context; eassumption.
  left; assumption.
  assumption.

  SCase "New (insert_proc 0 P ||| Q) -> P ||| New Q"%string.
  apply struct_equiv_preserves_typed_par_new; auto.

  SCase "P+++(New Q) -> New (insert_proc 0 P +++ Q)"%string.
  inversion H; subst.
  inversion H4; subst.
  apply TypNew with (s:=s) (L := (free_ids_context G) ++ L).
  intros x G' Hnotin Heq; subst.
  simpl.
  apply TypSum.
  rewrite <- open_insert_proc.
  apply typed_preserved_by_add.
  contradict Hnotin.
  apply in_or_app; left; auto.
  auto.
  apply H2; auto.
  contradict Hnotin.
  apply in_or_app; right; auto.

  SCase "New (insert_proc 0 P +++ Q) -> P+++(New Q)"%string.
  apply struct_equiv_preserves_typed_sum_new; auto.
  
  SCase "Q1 == Q2 -> P|||Q1 -> P|||Q2"%string.
  inversion H; subst.
  apply IHHequiv_pq in H5.
  apply TypPar with (GL:=GL) (GR:=GR); auto.

  SCase "Q1 == Q2 -> P|||Q2 -> P|||Q1"%string.
  inversion H; subst.
  apply IHHequiv_pq in H5.
  apply TypPar with (GL:=GL) (GR:=GR); auto.

  SCase "Q1 == Q2 -> P+++Q1 -> P+++Q2"%string.
  inversion H; subst.
  apply IHHequiv_pq in H4.
  apply TypSum; auto.

  SCase "Q1 == Q2 -> P+++Q2 -> P+++Q1"%string.
  inversion H; subst.
  apply IHHequiv_pq in H4.
  apply TypSum; auto.

  SCase "New P -> New Q"%string.
  inversion H1; clear H1; subst.
  apply TypNew with (L:=(free_ids_proc P)++(free_ids_proc Q)++L) (s:=s).
  intros y G' Hnotin_y Heq; subst.
  assert (~ In y (free_ids_proc P) /\ ~ In y (free_ids_proc Q)).
  split; contradict Hnotin_y; apply in_or_app; [left|right;apply in_or_app;left]; auto.
  destruct H1.
  apply (H0 y H1 H2 _).
  apply H4.
  contradict Hnotin_y.
  apply in_or_app; right; apply in_or_app; right; auto.
  reflexivity.

  SCase "New Q -> New P"%string.
  inversion H1; clear H1; subst.
  apply TypNew with (L:=(free_ids_proc P)++(free_ids_proc Q)++L) (s:=s).
  intros y G' Hnotin_y Heq; subst.
  assert (~ In y (free_ids_proc P) /\ ~ In y (free_ids_proc Q)).
  split; contradict Hnotin_y; apply in_or_app; [left|right;apply in_or_app;left]; auto.
  destruct H1.
  apply (H0 y H1 H2 _).
  apply H4.
  contradict Hnotin_y.
  apply in_or_app; right; apply in_or_app; right; auto.
  reflexivity.

Qed.

(* ============================================================================= *)
