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

(* ============================================================================= *)

Lemma subst_value_r_nm : 
  forall G x n v i rho sigma,
    ctx_add_value (ValName (Nm (Free i))) rho G |-part G (+) (ctx_add_value (ValName (Nm (Free i))) rho CTX.empty)
    ->
    G |-v open_value x n v : sigma
    ->
    CTX.In (ValVariable (Var (Free x)), rho) G
    ->
    ctx_add_value (ValName (Nm (Free i))) rho (CTX.remove (ValVariable (Var (Free x)), rho) G) 
    |-v subst_value (open_value x n v) (Var (Free x)) (ValName (Nm (Free i))) : sigma.
Proof.
  intros G x n v i rho sigma Hpart Hlookupov HinxG.

  assert ( CTX.add (ValName (Nm (Free i)), rho) G |-wf ) as Hwfadd.
  eapply partition_wf; eauto.

  assert ( CTX.add (ValName (Nm (Free i)), rho) (CTX.remove (ValVariable (Var (Free x)), rho) G) |-wf ) as Hwfaddremove.
  eapply subset_preserves_well_formed_ctx; [apply Hwfadd|intuition].
  clear Hwfadd.

  repeat (match goal with 
            | [ v : value |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ v : variable |- _ ] => destruct v
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
            | [ H : ?X = ?Y |- _ ] => solve [discriminate H]
            | [ H : ?X = ?Y |- _ ] => injection H; intros; subst; clear H
            | [ H : _ |-v ValName (Nm (Bound _)) : _ |- _ ] => solve [contradict H; apply lookup_nm_bound]
            | [ H : _ |-v ValName (CoNm (Bound _)) : _ |- _ ] => solve [contradict H; apply lookup_conm_bound]
            | [ H : _ |-v ValVariable (Var (Bound _)) : _ |- _ ] => solve [contradict H; apply lookup_var_bound]
            | [ |- _ |-v _ : _ ] => solve [apply LContext; auto; apply CTXFacts.remove_2; auto; discriminate]
          end; simpl in *);
  (try solve [inversion Hlookupov; subst; apply LContext; auto; apply CTXFacts.add_2; apply CTXFacts.remove_2; auto; contradict n0; injection n0; intros; subst; auto]);
  (try solve [apply LContext; auto; apply CTXFacts.add_2; apply CTXFacts.remove_2; auto; [discriminate|inversion Hlookupov; subst; auto]]);
  (try solve [
    assert (rho=sigma); [
      inversion Hlookupov; subst; inversion H; subst; apply (H2 _ _ _ HinxG H0)
      | subst; apply LContext; auto; intuition
    ]
  ]).

  inversion Hlookupov; subst; [inversion H; subst; pose (H1 _ _ H0) as Hu; inversion Hu|apply LToken; auto].
Qed.

(* ============================================================================= *)

Lemma subst_value_r_conm : 
  forall G x n v i rho sigma,
    ctx_add_value (ValName (CoNm (Free i))) rho G |-part G (+) (ctx_add_value (ValName (CoNm (Free i))) rho CTX.empty)
    ->
    G |-v open_value x n v : sigma
    ->
    CTX.In (ValVariable (Var (Free x)), rho) G
    ->
    ctx_add_value (ValName (CoNm (Free i))) rho (CTX.remove (ValVariable (Var (Free x)), rho) G) 
    |-v subst_value (open_value x n v) (Var (Free x)) (ValName (CoNm (Free i))) : sigma.
Proof.
  intros G x n v i rho sigma Hpart Hlookupov HinxG.

  assert ( CTX.add (ValName (CoNm (Free i)), rho) G |-wf ) as Hwfadd.
  eapply partition_wf; eauto.

  assert ( CTX.add (ValName (CoNm (Free i)), rho) (CTX.remove (ValVariable (Var (Free x)), rho) G) |-wf ) as Hwfaddremove.
  eapply subset_preserves_well_formed_ctx; [apply Hwfadd|intuition].
  clear Hwfadd.

  repeat (match goal with 
            | [ v : value |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ v : variable |- _ ] => destruct v
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
            | [ H : ?X = ?Y |- _ ] => solve [discriminate H]
            | [ H : ?X = ?Y |- _ ] => injection H; intros; subst; clear H
            | [ H : _ |-v ValName (Nm (Bound _)) : _ |- _ ] => solve [contradict H; apply lookup_nm_bound]
            | [ H : _ |-v ValName (CoNm (Bound _)) : _ |- _ ] => solve [contradict H; apply lookup_conm_bound]
            | [ H : _ |-v ValVariable (Var (Bound _)) : _ |- _ ] => solve [contradict H; apply lookup_var_bound]
            | [ |- _ |-v _ : _ ] => solve [apply LContext; auto; apply CTXFacts.remove_2; auto; discriminate]
          end; simpl in *);
  (try solve [inversion Hlookupov; subst; apply LContext; auto; apply CTXFacts.add_2; apply CTXFacts.remove_2; auto; contradict n0; injection n0; intros; subst; auto]);
  (try solve [apply LContext; auto; apply CTXFacts.add_2; apply CTXFacts.remove_2; auto; [discriminate|inversion Hlookupov; subst; auto]]);
  (try solve [
    assert (rho=sigma); [
      inversion Hlookupov; subst; inversion H; subst; apply (H2 _ _ _ HinxG H0)
      | subst; apply LContext; auto; intuition
    ]
  ]).

  inversion Hlookupov; subst; [inversion H; subst; pose (H1 _ _ H0) as Hu; inversion Hu|apply LToken; auto].
Qed.

(* ============================================================================= *)

Lemma subst_value_r_token : 
  forall G x n v k sigma,
    ctx_add_value (ValToken k) (TSingleton k) G |-part G (+) (ctx_add_value k (TSingleton k) CTX.empty)
    ->
    G |-v open_value x n v : sigma
    ->
    CTX.In (ValVariable (Var (Free x)), TSingleton k) G
    ->
    ctx_add_value k (TSingleton k) (CTX.remove (ValVariable (Var (Free x)), (TSingleton k)) G) |-v subst_value (open_value x n v) (Var (Free x)) k : sigma.
Proof.
  intros G x n v k sigma Hpart Hlookupov HinxG.

  destruct k.
  eapply ctx_equal_preserves_lookup; [|rewrite ctx_add_value_token; reflexivity].
  assert ((CTX.remove (ValVariable (Var (Free x)), TSingleton (Token s)) G) |-wf ) as Hwfremove.
  eapply subset_preserves_well_formed_ctx.
  inversion Hlookupov; eauto.
  intuition.
  inversion Hlookupov; subst.
  repeat (match goal with 
            | [ v : value |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ v : variable |- _ ] => destruct v
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
            | [ H : ?X = ?Y |- _ ] => solve [discriminate H]
            | [ H : ?X = ?Y |- _ ] => injection H; intros; subst; clear H
            | [ H : _ |-v ValName (Nm (Bound _)) : _ |- _ ] => solve [contradict H; apply lookup_nm_bound]
            | [ H : _ |-v ValName (CoNm (Bound _)) : _ |- _ ] => solve [contradict H; apply lookup_conm_bound]
            | [ H : _ |-v ValVariable (Var (Bound _)) : _ |- _ ] => solve [contradict H; apply lookup_var_bound]
            | [ |- _ |-v _ : _ ] => solve [apply LContext; auto; apply CTXFacts.remove_2; auto; discriminate]
          end; simpl in *);
  (try solve [assert (sigma = TSingleton (Token s)); [|subst]; inversion H; subst; [apply (H2 _ _ _ H0 HinxG) | apply LToken; auto]]);
  (try solve [apply LContext; auto; apply CTXFacts.remove_2; auto; contradict n0; injection n0; intros; subst; auto]).

  destruct k.
  injection H; intros; subst.
  simpl.
  apply LToken; auto.
Qed.
  
(* ============================================================================= *)

Lemma subst_value_r : 
  forall G x n v w rho sigma,
    ctx_add_value w rho G |-part G (+) (ctx_add_value w rho CTX.empty)
    ->
    G |-v open_value x n v : sigma
    ->
    CTX.In (ValVariable (Var (Free x)), rho) G
    ->
    free_name_or_token w
    -> 
    (forall k, w = Token k -> rho = TSingleton (Token k))
    ->
    ctx_add_value w rho (CTX.remove (ValVariable (Var (Free x)), rho) G) |-v subst_value (open_value x n v) (Var (Free x)) w : sigma.
Proof.
  intros G x n v w rho sigma Hpart Hlookupov HinxG Hfnotw Htokentype.

  destruct Hfnotw.
  apply subst_value_r_nm; auto.
  apply subst_value_r_conm; auto.

  destruct k.
  specialize (Htokentype s eq_refl).
  subst.
  apply subst_value_r_token; auto.
Qed.

(* ============================================================================= *)

Inductive SO : proc -> proc -> Prop :=
| SOBase : forall i n u v P, SO (subst_proc (open_proc i n P) u v) (open_proc i n (subst_proc P u v))
| SOStep : forall i n P Q, SO P Q -> SO (open_proc i n P) (open_proc i n Q).

(* ============================================================================= *)

Lemma SO_input_aux : 
  forall P' Q',
    SO P' Q' 
    -> 
    forall u P v Q, 
      P' = u ? ; P
      ->
      Q' = v ? ; Q
      -> 
      SO P Q.
Proof.
  intros P' Q' Hso; induction Hso; intros u2 P2 v2 Q2 Heq1 Heq2; subst.
  destruct P; simpl in *; subst;
    match goal with
      | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  apply SOBase.

  destruct P; simpl in *; subst; try solve [discriminate Heq1].
  destruct Q; simpl in *; subst; try solve [discriminate Heq2].
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  apply SOStep.
  eapply IHHso; eauto.
Qed.

Lemma SO_input : forall u P v Q, SO (u ? ; P) (v ? ; Q) -> SO P Q.
Proof.
  intros u P v Q Hso.
  eapply SO_input_aux; eauto.
Qed.


(* ============================================================================= *)

Inductive SO3 : free_id -> free_id -> value -> proc -> proc -> Prop :=
| SO3Base : forall x y n v P, 
      ~ In x (free_ids_proc P)
      ->
      ~ In y (free_ids_proc P)
      ->
      free_name_or_token v
      -> 
      SO3 x y v (open_proc x n P) (subst_open_proc P y n v)
| SO3Step : forall x y v i n P Q, 
      ~ In i (free_ids_proc P)
      ->
      ~ In i (free_ids_proc Q)
      ->
      i <> x
      -> 
      SO3 x y v P Q
      ->
      SO3 x y v (open_proc i n P) (open_proc i n Q).

(* ============================================================================= *)

Lemma SO3_input_aux : 
  forall x y w P' Q',
    SO3 x y w P' Q' 
    -> 
    forall u P v Q, 
      P' = u ? ; P
      ->
      Q' = v ? ; Q
      -> 
      SO3 x y w P Q.
Proof.
  intros x y w P' Q' Hso; induction Hso; intros u2 P2 v2 Q2 Heq1 Heq2; subst.
  destruct P; simpl in *; subst;
    match goal with
      | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  apply SO3Base; intuition.

  destruct P; simpl in *; subst; try solve [discriminate Heq1].
  destruct Q; simpl in *; subst; try solve [discriminate Heq2].
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  apply SO3Step; try solve [contradict H; intuition].
  eapply IHHso; eauto.
Qed.

(* ============================================================================= *)

Lemma SO3_input : forall x y w u P v Q, SO3 x y w (u ? ; P) (v ? ; Q) -> SO3 x y w P Q.
Proof.
  intros x y w u P v Q Hso.
  eapply SO3_input_aux; eauto.
Qed.

(* ============================================================================= *)

Lemma SO3_output_aux : 
  forall x y w P' Q',
    SO3 x y w P' Q' 
    -> 
    forall u1 u2 v1 v2 P Q, 
      P' = u1 ! u2 ; P
      ->
      Q' = v1 ! v2 ; Q
      -> 
      SO3 x y w P Q.
Proof.
  intros x y w P' Q' Hso; induction Hso; intros u1 u2 v1 v2 P2 Q2 Heq1 Heq2; subst.
  unfold subst_open_proc in *.
  destruct P; simpl in *; subst;
    match goal with
      | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  apply SO3Base; auto; (repeat rewrite in_app_iff in *).
  contradict H; auto.
  contradict H0; auto.

  destruct P; simpl in *; subst; try solve [discriminate Heq1].
  destruct Q; simpl in *; subst; try solve [discriminate Heq2].
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  apply SO3Step; auto.
  contradict H; intuition.
  contradict H0; intuition.
  eapply IHHso; eauto.
Qed.

(* ============================================================================= *)

Lemma SO3_output : forall x y w u1 u2 v1 v2 P Q, SO3 x y w (u1 ! u2 ; P) (v1 ! v2 ; Q) -> SO3 x y w P Q.
Proof.
  intros x y w u1 u2 v1 v2 P Q Hso.
  eapply SO3_output_aux; eauto.
Qed.

(* ============================================================================= *)

Lemma SO3_iseq_aux : 
  forall x y w P' Q',
    SO3 x y w P' Q' 
    -> 
    forall u1 u2 v1 v2 P Q, 
      P' = IsEq u1 u2 P
      ->
      Q' = IsEq v1 v2 Q
      -> 
      SO3 x y w P Q.
Proof.
  intros x y w P' Q' Hso; induction Hso; intros u1 u2 v1 v2 P2 Q2 Heq1 Heq2; subst.
  unfold subst_open_proc in *.
  destruct P; simpl in *; subst;
    match goal with
      | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  apply SO3Base; auto; (repeat rewrite in_app_iff in *).
  contradict H; auto.
  contradict H0; auto.

  destruct P; simpl in *; subst; try solve [discriminate Heq1].
  destruct Q; simpl in *; subst; try solve [discriminate Heq2].
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  apply SO3Step; auto.
  contradict H; intuition.
  contradict H0; intuition.
  eapply IHHso; eauto.
Qed.

(* ============================================================================= *)

Lemma SO3_iseq : forall x y w u1 u2 v1 v2 P Q, SO3 x y w (IsEq u1 u2 P) (IsEq v1 v2 Q) -> SO3 x y w P Q.
Proof.
  intros x y w u1 u2 v1 v2 P Q Hso.
  eapply SO3_iseq_aux; eauto.
Qed.

(* ============================================================================= *)

Lemma SO3_isneq_aux : 
  forall x y w P' Q',
    SO3 x y w P' Q' 
    -> 
    forall u1 u2 v1 v2 P Q, 
      P' = IsNotEq u1 u2 P
      ->
      Q' = IsNotEq v1 v2 Q
      -> 
      SO3 x y w P Q.
Proof.
  intros x y w P' Q' Hso; induction Hso; intros u1 u2 v1 v2 P2 Q2 Heq1 Heq2; subst.
  unfold subst_open_proc in *.
  destruct P; simpl in *; subst;
    match goal with
      | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  apply SO3Base; auto; (repeat rewrite in_app_iff in *).
  contradict H; auto.
  contradict H0; auto.

  destruct P; simpl in *; subst; try solve [discriminate Heq1].
  destruct Q; simpl in *; subst; try solve [discriminate Heq2].
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  apply SO3Step; auto.
  contradict H; intuition.
  contradict H0; intuition.
  eapply IHHso; eauto.
Qed.

(* ============================================================================= *)

Lemma SO3_isneq : forall x y w u1 u2 v1 v2 P Q, SO3 x y w (IsNotEq u1 u2 P) (IsNotEq v1 v2 Q) -> SO3 x y w P Q.
Proof.
  intros x y w u1 u2 v1 v2 P Q Hso.
  eapply SO3_isneq_aux; eauto.
Qed.

(* ============================================================================= *)

Lemma SO3_par_aux : 
  forall x y w P' Q',
    SO3 x y w P' Q' 
    -> 
    forall P1 P2 Q1 Q2, 
      P' = P1 ||| P2
      ->
      Q' = Q1 ||| Q2
      -> 
      (SO3 x y w P1 Q1) /\ (SO3 x y w P2 Q2).
Proof.
  intros x y w P' Q' Hso; induction Hso; intros P3 P4 Q3 Q4 Heq1 Heq2; subst.
  unfold subst_open_proc in *.
  destruct P; simpl in *; subst;
    match goal with
      | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  split; apply SO3Base; auto; (repeat rewrite in_app_iff in *);
    (try solve [contradict H; auto]);
    (try solve [contradict H0; auto]).

  destruct P; simpl in *; subst; try solve [discriminate Heq1].
  destruct Q; simpl in *; subst; try solve [discriminate Heq2].
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  specialize (IHHso _ _ _ _ eq_refl eq_refl); destruct IHHso; split; apply SO3Step; auto; 
    contradict H; intuition.
Qed.

(* ============================================================================= *)

Lemma SO3_par : forall x y w P1 P2 Q1 Q2, SO3 x y w (P1 ||| P2) (Q1 ||| Q2) -> (SO3 x y w P1 Q1) /\ (SO3 x y w P2 Q2).
Proof.
  intros x y w P1 P2 Q1 Q2 Hso.
  eapply SO3_par_aux; eauto.
Qed.

(* ============================================================================= *)

Lemma SO3_sum_aux : 
  forall x y w P' Q',
    SO3 x y w P' Q' 
    -> 
    forall P1 P2 Q1 Q2, 
      P' = P1 +++ P2
      ->
      Q' = Q1 +++ Q2
      -> 
      (SO3 x y w P1 Q1) /\ (SO3 x y w P2 Q2).
Proof.
  intros x y w P' Q' Hso; induction Hso; intros P3 P4 Q3 Q4 Heq1 Heq2; subst.
  unfold subst_open_proc in *.
  destruct P; simpl in *; subst;
    match goal with
      | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  split; apply SO3Base; auto; (repeat rewrite in_app_iff in *);
    (try solve [contradict H; auto]);
    (try solve [contradict H0; auto]).

  destruct P; simpl in *; subst; try solve [discriminate Heq1].
  destruct Q; simpl in *; subst; try solve [discriminate Heq2].
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  specialize (IHHso _ _ _ _ eq_refl eq_refl); destruct IHHso; split; apply SO3Step; auto;
    contradict H; intuition.
Qed.

(* ============================================================================= *)

Lemma SO3_sum : forall x y w P1 P2 Q1 Q2, SO3 x y w (P1 +++ P2) (Q1 +++ Q2) -> (SO3 x y w P1 Q1) /\ (SO3 x y w P2 Q2).
Proof.
  intros x y w P1 P2 Q1 Q2 Hso.
  eapply SO3_sum_aux; eauto.
Qed.

(* ============================================================================= *)

Lemma SO3_new_aux : 
  forall x y w P' Q',
    SO3 x y w P' Q' 
    -> 
    forall P Q, 
      P' = New P
      ->
      Q' = New Q
      -> 
      SO3 x y w P Q.
Proof.
  intros x y w P' Q' Hso; induction Hso; intros P1 Q1 Heq1 Heq2; subst.
  unfold subst_open_proc in *.
  destruct P; simpl in *; subst;
    match goal with
      | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  apply SO3Base; auto; (repeat rewrite in_app_iff in *);
    (try solve [contradict H; auto]);
    (try solve [contradict H0; auto]).

  destruct P; simpl in *; subst; try solve [discriminate Heq1].
  destruct Q; simpl in *; subst; try solve [discriminate Heq2].
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  specialize (IHHso _ _ eq_refl eq_refl); apply SO3Step; auto.
Qed.

(* ============================================================================= *)

Lemma SO3_new : forall x y w P Q, SO3 x y w (New P) (New Q) -> (SO3 x y w P Q).
Proof.
  intros x y w P Q Hso.
  eapply SO3_new_aux; eauto.
Qed.

(* ============================================================================= *)

Lemma SO3_rep_aux : 
  forall x y w P' Q',
    SO3 x y w P' Q' 
    -> 
    forall P Q, 
      P' = Rep P
      ->
      Q' = Rep Q
      -> 
      SO3 x y w P Q.
Proof.
  intros x y w P' Q' Hso; induction Hso; intros P1 Q1 Heq1 Heq2; subst.
  unfold subst_open_proc in *.
  destruct P; simpl in *; subst;
    match goal with
      | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  apply SO3Base; auto; (repeat rewrite in_app_iff in *);
    (try solve [contradict H; auto]);
    (try solve [contradict H0; auto]).

  destruct P; simpl in *; subst; try solve [discriminate Heq1].
  destruct Q; simpl in *; subst; try solve [discriminate Heq2].
  injection Heq1; intros; subst; clear Heq1.
  injection Heq2; intros; subst; clear Heq2.
  specialize (IHHso _ _ eq_refl eq_refl); apply SO3Step; auto.
Qed.

(* ============================================================================= *)

Lemma SO3_rep : forall x y w P Q, SO3 x y w (Rep P) (Rep Q) -> (SO3 x y w P Q).
Proof.
  intros x y w P Q Hso.
  eapply SO3_rep_aux; eauto.
Qed.

(* ============================================================================= *)

Lemma SO3_inp_decompose : 
  forall x y w P' Q, 
    SO3 x y w P' Q
    -> 
    forall u P, 
      P' = (u?; P) 
      -> 
      exists v1, exists Q1, Q = v1?;Q1.
Proof.
  intros x y w P' Q Hso2; induction Hso2; intros u1 P1 Heq; subst; unfold subst_open_proc; subst.
  destruct P; simpl in *; subst;
    try match goal with
        | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  inversion Heq; intros; subst; clear Heq.
  eexists; eexists; auto.

  destruct P; simpl in *; subst;
    try match goal with
        | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  inversion Heq; intros; subst; clear Heq.
  specialize (IHHso2 _ _ eq_refl).
  destruct IHHso2 as [v1 IHHso2]; destruct IHHso2 as [Q1 Heq].
  subst.
  eexists; eexists; simpl; eauto.
Qed.
  
(* ============================================================================= *)

Lemma SO3_out_decompose : 
  forall x y w P' Q, 
    SO3 x y w P' Q 
    -> 
    forall u v P, 
      P' = (u!v; P) 
      ->
      exists u1, exists v1, exists Q1, (Q = u1 ! v1 ; Q1).
Proof.
  intros x y w P' Q Hso2; induction Hso2; intros u1 v1 P1 Heq; subst; unfold subst_open_proc; 
  destruct P; simpl in *; subst;
    try match goal with
        | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  inversion Heq; intros; subst; clear Heq.
  eexists; eexists; eexists; eauto.

  inversion Heq; intros; subst; clear Heq.
  specialize (IHHso2 _ _ _ eq_refl).
  destruct IHHso2 as [u1 IHHso2]; destruct IHHso2 as [v1 IHHso2]; destruct IHHso2 as [Q1 Heq].
  subst.
  eexists; eexists; simpl; eauto.
Qed.
  
(* ============================================================================= *)

Lemma SO3_iseq_decompose : 
  forall x y w P' Q, 
    SO3 x y w P' Q 
    -> 
    forall u v P, 
      P' = (IsEq u v P) 
      ->
      exists u1, exists v1, exists Q1, (Q = IsEq u1 v1 Q1).
Proof.
  intros x y w P' Q Hso2; induction Hso2; intros u1 v1 P1 Heq; subst; unfold subst_open_proc; 
  destruct P; simpl in *; subst;
    try match goal with
        | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  inversion Heq; intros; subst; clear Heq.
  eexists; eexists; eexists; eauto.

  inversion Heq; intros; subst; clear Heq.
  specialize (IHHso2 _ _ _ eq_refl).
  destruct IHHso2 as [u1 IHHso2]; destruct IHHso2 as [v1 IHHso2]; destruct IHHso2 as [Q1 Heq].
  subst.
  eexists; eexists; simpl; eauto.
Qed.
  
(* ============================================================================= *)

Lemma SO3_isneq_decompose : 
  forall x y w P' Q, 
    SO3 x y w P' Q 
    -> 
    forall u v P, 
      P' = (IsNotEq u v P) 
      ->
      exists u1, exists v1, exists Q1, (Q = IsNotEq u1 v1 Q1).
Proof.
  intros x y w P' Q Hso2; induction Hso2; intros u1 v1 P1 Heq; subst; unfold subst_open_proc; 
  destruct P; simpl in *; subst;
    try match goal with
        | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  inversion Heq; intros; subst; clear Heq.
  eexists; eexists; eexists; eauto.

  inversion Heq; intros; subst; clear Heq.
  specialize (IHHso2 _ _ _ eq_refl).
  destruct IHHso2 as [u1 IHHso2]; destruct IHHso2 as [v1 IHHso2]; destruct IHHso2 as [Q1 Heq].
  subst.
  eexists; eexists; simpl; eauto.
Qed.
  
(* ============================================================================= *)

Lemma SO3_par_decompose : 
  forall x y w P' Q, 
    SO3 x y w P' Q 
    -> 
    forall P1 P2, 
      P' = P1 ||| P2
      ->
      exists Q1, exists Q2, (Q = Q1 ||| Q2).
Proof.
  intros x y w P' Q Hso2; induction Hso2; intros P1 P2 Heq; subst; unfold subst_open_proc;
  destruct P; simpl in *; subst;
    try match goal with
        | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  inversion Heq; intros; subst; clear Heq.
  eexists; eexists; eexists; eauto.

  inversion Heq; intros; subst; clear Heq.
  specialize (IHHso2 _ _ eq_refl).
  destruct IHHso2 as [Q1 IHHso2]; destruct IHHso2 as [Q2 Heq].
  subst.
  eexists; eexists; simpl; eauto.
Qed.
  
(* ============================================================================= *)

Lemma SO3_sum_decompose : 
  forall x y w P' Q, 
    SO3 x y w P' Q 
    -> 
    forall P1 P2, 
      P' = P1 +++ P2
      ->
      exists Q1, exists Q2, (Q = Q1 +++ Q2).
Proof.
  intros x y w P' Q Hso2; induction Hso2; intros P1 P2 Heq; subst; unfold subst_open_proc;
  destruct P; simpl in *; subst;
    try match goal with
        | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  inversion Heq; intros; subst; clear Heq.
  eexists; eexists; eexists; eauto.

  inversion Heq; intros; subst; clear Heq.
  specialize (IHHso2 _ _ eq_refl).
  destruct IHHso2 as [Q1 IHHso2]; destruct IHHso2 as [Q2 Heq].
  subst.
  eexists; eexists; simpl; eauto.
Qed.
  
(* ============================================================================= *)

Lemma SO3_new_decompose : 
  forall x y w P' Q', 
    SO3 x y w P' Q'
    -> 
    forall P, 
      P' = New P
      -> 
      exists Q, Q' = New Q.
Proof.
  intros x y w P' Q' Hso2; induction Hso2; intros P1 Heq; subst; unfold subst_open_proc; subst.
  destruct P; simpl in *; subst;
    try match goal with
        | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  inversion Heq; intros; subst; clear Heq.
  eexists; auto.

  destruct P; simpl in *; subst;
    try match goal with
        | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  inversion Heq; intros; subst; clear Heq.
  specialize (IHHso2 _ eq_refl).
  destruct IHHso2 as [Q1 Heq].
  subst.
  eexists; simpl; eauto.
Qed.
  
(* ============================================================================= *)

Lemma SO3_rep_decompose : 
  forall x y w P' Q, 
    SO3 x y w P' Q 
    -> 
    forall P, 
      P' = (Rep P) 
      ->
      exists Q1, (Q = Rep Q1).
Proof.
  intros x y w P' Q Hso2; induction Hso2; intros P1 Heq; subst; unfold subst_open_proc; 
  destruct P; simpl in *; subst;
    try match goal with
        | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  inversion Heq; intros; subst; clear Heq.
  eexists; eauto.

  inversion Heq; intros; subst; clear Heq.
  specialize (IHHso2 _ eq_refl).
  destruct IHHso2 as [Q1 Heq].
  subst.
  eexists; simpl; eauto.
Qed.
  
(* ============================================================================= *)

Lemma SO3_zero_decompose : 
  forall x y w P' Q, 
    SO3 x y w P' Q 
    -> 
    P' = Zero
    ->
    Q = Zero.
Proof.
  intros x y w P' Q Hso2; induction Hso2; intros Heq; subst; unfold subst_open_proc; 
  destruct P; simpl in *; subst;
    try match goal with
        | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  inversion Heq; intros; subst; clear Heq.
  reflexivity.

  inversion Heq; intros; subst; clear Heq.
  specialize (IHHso2 eq_refl).
  subst.
  simpl; reflexivity.
Qed.
  
(* ============================================================================= *)

Lemma open_value_inj : 
  forall i n u v,
    ~ In i (free_ids_value u)
    ->
    ~ In i (free_ids_value v)
    ->
    (open_value i n u <> open_value i n v   <->   u <> v).
Proof.
  intros i n u v Hnotinu Hnotinv.
  split.
  intros Hneq; contradict Hneq; subst; auto.
  intros Hneq; contradict Hneq.

  rewrite <- (close_open_value i n u); auto.
  rewrite <- (close_open_value i n v); auto.
  rewrite Hneq.
  reflexivity.
Qed.

(* ============================================================================= *)

Lemma subst_value_result :
  forall u v w, subst_value u v w = u \/ (u = v /\ subst_value u v w = w).
Proof.
  intros u v w.
  destruct u; [destruct n; simpl|simpl; left; reflexivity| destruct v0; simpl];
    try solve [left; reflexivity].
  destruct i; 
    try solve [left; reflexivity].
  destruct (value_dec (Var (Free f)) v); 
    try solve [left; reflexivity].
  right; split; auto.
Qed.

(* ============================================================================= *)

Lemma free_ids_value_open : 
  forall x v i n,  In x (free_ids_value v) -> In x (free_ids_value (open_value i n v)).
Proof.
  intros x v i n Hin.
  repeat (match goal with 
           | [ v : value |- _ ] => destruct v
           | [ n : name |- _ ] => destruct n
           | [ v : variable |- _ ] => destruct v
           | [ H : False |- _ ] => destruct H
           | [ i : id |- _ ] => destruct i
           | [ H : _ \/ _ |- _ ] => destruct H
         end; simpl in *; try solve [left; auto]).
Qed.

(* ============================================================================= *)

Lemma open_value_is_free_var :
  forall x n u,
    ~ In x (free_ids_value u)
    ->
    open_value x n u = ValVariable (Var (Free x))
    -> 
    u = ValVariable (Var (Bound n)).
Proof.
  intros x n u Hnotinx Heq.
  destruct u; simpl in Heq; try solve [discriminate Heq].
  destruct v; simpl in Heq; try solve [discriminate Heq].
  destruct i; simpl in Heq; try solve [discriminate Heq].
  injection Heq; intros; subst.
  contradict Hnotinx.
  simpl; left; reflexivity.
  destruct (eq_nat_decide b n).
  apply eq_nat_eq in e; subst.
  reflexivity.
  destruct (le_lt_dec b n); simpl in Heq; discriminate Heq.
Qed.

(* ============================================================================= *)

Lemma open_value_cases : 
  forall x n u v,
    open_value x n u = v
    ->
    ((u = v)
      \/ (u = ValName (Nm (Bound n)) /\ v = ValName (Nm (Free x)))
      \/ (u = ValName (CoNm (Bound n)) /\ v = ValName (CoNm (Free x)))
      \/ (u = ValVariable (Var (Bound n)) /\ v = ValVariable (Var (Free x)))
      \/ (exists m, m < n /\ u = ValName (Nm (Bound m)) /\ v = ValName (Nm (Bound m)))
      \/ (exists m, m < n /\ u = ValName (CoNm (Bound m)) /\ v = ValName (CoNm (Bound m)))
      \/ (exists m, m < n /\ u = ValVariable (Var (Bound m)) /\ v = ValVariable (Var (Bound m)))
      \/ (exists m, m > n /\ u = ValName (Nm (Bound m)) /\ v = ValName (Nm (Bound (pred m))))
      \/ (exists m, m > n /\ u = ValName (CoNm (Bound m)) /\ v = ValName (CoNm (Bound (pred m))))
      \/ (exists m, m > n /\ u = ValVariable (Var (Bound m)) /\ v = ValVariable (Var (Bound (pred m))))).
Proof.
  intros x n u v Heq; subst.
  destruct u as [nm|t|var]; [destruct nm as [i|i]|left; reflexivity|destruct var as [i]]; destruct i; simpl;
    try solve [left; reflexivity]; 
      (destruct (eq_nat_decide b n) as [e0|n0]; [apply eq_nat_eq in e0; subst|]); right;
        try solve [left; split; reflexivity];
          try solve [right; left; split; reflexivity];
            try solve [right; right; left; split; reflexivity];
              right; right; right;
                (destruct (le_lt_dec b n) as [e1|n1]);
                (repeat (try solve [(try left); exists b; (repeat split; auto); rewrite eq_nat_is_eq in *; omega] || right)).
Qed.

(* ============================================================================= *)

Lemma open_value_dual_name : 
  forall i j n u v nm,
    open_value i n u = ValName nm
    ->
    open_value i n v = ValName (dual_name nm)
    -> 
    In j (free_ids_value u)
    ->
    In j (free_ids_value v)
    ->
    exists nm', u = ValName nm' /\ v = ValName (dual_name nm').
Proof.
  intros i j n u v nm Heq1 Heq2.
  repeat (match goal with
            | [ u : value |- _ ] => destruct u
            | [ nm : name |- _ ] => destruct nm
            | [ i : id |- _ ] => destruct i
            | [ H : _ = _ |- _ ] => solve [discriminate H]
          end; simpl in *);
  injection Heq1; intros; subst; clear Heq1;
    injection Heq2; intros; subst; clear Heq2;
      repeat match goal with 
               | [ H : _ \/ _ |- _ ] => destruct H
               | [ H : False |- _ ] => destruct H
             end;
      (eexists; split; [reflexivity|eauto]).
Qed.

(* ============================================================================= *)

Inductive free_name : value -> Prop :=
| FNNm : forall i, free_name (ValName (Nm (Free i)))
| FNCoNm : forall i, free_name (ValName (CoNm (Free i))).

Lemma SO3_output_neq_pres_aux : 
  forall x y w P1' P2',
    SO3 x y w P1' P2'
    ->
    forall u1 v1 P1 u2 v2 P2,
      P1' = (u1 ! v1; P1)
      ->
      P2' = (u2 ! v2; P2)
      ->
      free_name w
      ->
      (~ exists i, (In i (free_ids_value w) /\ (In i (free_ids_value u1) \/ In i (free_ids_value v1))))
      ->
      (forall i, In i (free_ids_value u1) /\ In i (free_ids_value v1) -> exists nm, u1 = ValName nm /\ v1 = ValName (dual_name nm))
      ->
      u1 <> v1
      -> 
      u2 <> v2.
Proof.
  intros x y w P1' P2' Hso3; induction Hso3; intros u1 v1 P1 u2 v2 P2 Heq1 Heq2 Hfv Hdisjointfreeids Hnoidoverlap Hneq; subst.
  
  Case "Base case"%string.
  destruct P; simpl in *; subst;
    try match goal with
        | [ H : _ = _ |- _ ] => try solve [discriminate H]
    end.
  inversion Heq1; intros; subst; clear Heq1.
  inversion Heq2; intros; subst; clear Heq2.

  (destruct (subst_value_result (open_value y n v0) (Var (Free y)) v) as [Heq1|Heq1]; [|destruct Heq1 as [Heq1a Heq1b]]);
  (destruct (subst_value_result (open_value y n v3) (Var (Free y)) v) as [Heq2|Heq2]; [|destruct Heq2 as [Heq2a Heq2b]]).

  SCase "v0 subst idem /\ v3 subst idem"%string.
  rewrite Heq1; rewrite Heq2.
  rewrite open_value_inj in Hneq; try solve [contradict H; intuition].
  rewrite <- (open_value_inj y n v0 v3) in Hneq; try solve [contradict H0; intuition].

  SCase "v0 subst idem /\ v3 subst not-idem"%string.
  rewrite Heq2b.
  assert (v3 = ValVariable (Var (Bound n))) as Heq3.
  eapply open_value_is_free_var; eauto.
  contradict H0; intuition.
  rewrite Heq3 in *.
  simpl in Hneq; simpl in Hdisjointfreeids.
  destruct (eq_nat_decide n n); [|contradict n0; apply eq_eq_nat; reflexivity].

  assert (v0 <> ValVariable (Var (Free y))).
  contradict H0; rewrite H0 in *; rewrite in_app_iff; left; simpl; auto.
  assert (v0 <> ValVariable (Var (Bound n))).
  contradict Hneq; rewrite Hneq in *; simpl; destruct (eq_nat_decide n n) as [e0|n0]; [reflexivity|contradict n0; auto].
  assert (v0 <> ValVariable (Var (Free x))).
  contradict Hneq; rewrite Hneq in *; simpl; destruct (eq_nat_decide n n) as [e0|n0]; [reflexivity|contradict n0; auto].

  pose (open_value_cases y n v0 _ eq_refl) as p.
  repeat (match goal with 
            | [ H : _ \/ _ |- _ ] => destruct H 
            | [ H : _ /\ _ |- _ ] => destruct H 
            | [ H : _ = _ |- _ ] => solve [discriminate H]
            | [ H1 : ?X = ?Y , H2 : ?X <> ?Y |- _ ] => solve [contradict H2; assumption]
            | [ H : exists _ : nat, _ |- _ ] => destruct H
          end);
  (try solve [rewrite Heq1; intros Heq4; rewrite Heq4 in *; apply Hdisjointfreeids; inversion Hfv; subst; exists i; simpl; tauto]); 
  (try solve [rewrite H7; simpl; inversion Hfv; discriminate]).

  rewrite H5 in *.
  specialize (Hnoidoverlap x).
  match goal with [ H : ?X -> (exists _, _) |- _ ] => assert X as Hu; [| specialize (H Hu)] end.
  simpl; destruct (eq_nat_decide n n); [simpl; tauto| contradict n0; auto].
  destruct Hnoidoverlap as [nm Heq4]; destruct Heq4 as [Heq4 Heq5].
  simpl in Heq5; destruct (eq_nat_decide n n); [simpl; discriminate Heq5| contradict n0; auto].
  
  rewrite H5 in *.
  specialize (Hnoidoverlap x).
  match goal with [ H : ?X -> (exists _, _) |- _ ] => assert X as Hu; [| specialize (H Hu)] end.
  simpl; destruct (eq_nat_decide n n); [simpl; tauto| contradict n0; auto].
  destruct Hnoidoverlap as [nm Heq4]; destruct Heq4 as [Heq4 Heq5].
  simpl in Heq5; destruct (eq_nat_decide n n); [simpl; discriminate Heq5| contradict n0; auto].


  SCase "v0 subst not-idem /\ v3 subst idem"%string.
  rewrite Heq1b.
  assert (v0 = ValVariable (Var (Bound n))) as Heq3.
  eapply open_value_is_free_var; eauto.
  contradict H0; intuition.
  rewrite Heq3 in *.
  simpl in Hneq; simpl in Hdisjointfreeids.
  destruct (eq_nat_decide n n); [|contradict n0; apply eq_eq_nat; reflexivity].

  assert (v3 <> ValVariable (Var (Free y))).
  contradict H0; rewrite H0 in *; (repeat rewrite in_app_iff); right; left; simpl; auto.
  assert (v3 <> ValVariable (Var (Bound n))).
  contradict Hneq; rewrite Hneq in *; simpl; destruct (eq_nat_decide n n) as [e0|n0]; [reflexivity|contradict n0; auto].
  assert (v3 <> ValVariable (Var (Free x))).
  contradict Hneq; rewrite Hneq in *; simpl; destruct (eq_nat_decide n n) as [e0|n0]; [reflexivity|contradict n0; auto].

  pose (open_value_cases y n v3 _ eq_refl) as p.
  repeat (match goal with 
            | [ H : _ \/ _ |- _ ] => destruct H 
            | [ H : _ /\ _ |- _ ] => destruct H 
            | [ H : _ = _ |- _ ] => solve [discriminate H]
            | [ H1 : ?X = ?Y , H2 : ?X <> ?Y |- _ ] => solve [contradict H2; assumption]
            | [ H : exists _ : nat, _ |- _ ] => destruct H
          end);
  (try solve [rewrite Heq2; intros Heq4; rewrite <- Heq4 in *; apply Hdisjointfreeids; inversion Hfv; subst; exists i; simpl; tauto]);
  (try solve [rewrite H7; simpl; inversion Hfv; discriminate]).

  rewrite H5 in *.
  specialize (Hnoidoverlap x).
  match goal with [ H : ?X -> (exists _, _) |- _ ] => assert X as Hu; [| specialize (H Hu)] end.
  simpl; destruct (eq_nat_decide n n); [simpl; tauto| contradict n0; auto].
  destruct Hnoidoverlap as [nm Heq4]; destruct Heq4 as [Heq4 Heq5].
  simpl in Heq4; destruct (eq_nat_decide n n); [simpl; discriminate Heq4| contradict n0; auto].

  rewrite H5 in *.
  specialize (Hnoidoverlap x).
  match goal with [ H : ?X -> (exists _, _) |- _ ] => assert X as Hu; [| specialize (H Hu)] end.
  simpl; destruct (eq_nat_decide n n); [simpl; tauto| contradict n0; auto].
  destruct Hnoidoverlap as [nm Heq4]; destruct Heq4 as [Heq4 Heq5].
  simpl in Heq4; destruct (eq_nat_decide n n); [simpl; discriminate Heq4| contradict n0; auto].


  SCase "v0 subst not-idem /\ v3 subst not-idem"%string.
  rewrite Heq1b.
  assert (v0 = ValVariable (Var (Bound n))) as Heq3a.
  eapply open_value_is_free_var; eauto.
  contradict H0; intuition.
  rewrite Heq3a in *.
  rewrite Heq2b.
  assert (v3 = ValVariable (Var (Bound n))) as Heq3b.
  eapply open_value_is_free_var; eauto.
  contradict H0; intuition.
  rewrite Heq3b in *.
  contradict Hneq; reflexivity.

  
  Case "Inductive step case"%string.
  destruct P; simpl in *; subst;
    try match goal with
        | [ H : _ = _ |- _ ] => solve [discriminate H]
    end.
  inversion Heq1; intros; subst; clear Heq1.
  destruct Q; simpl in *; subst;
    try match goal with
        | [ H : _ = _ |- _ ] => solve [discriminate H]
    end.
  inversion Heq2; intros; subst; clear Heq2.

  rewrite open_value_inj in Hneq.
  rewrite open_value_inj.
  eapply IHHso3; eauto.

  contradict Hdisjointfreeids; auto.
  destruct Hdisjointfreeids as [i1 Hin]; destruct Hin as [Hin1 Hin2]; destruct Hin2 as [Hin2|Hin2].
  exists i1; split; auto; left; apply free_ids_value_open; auto.
  exists i1; split; auto; right; apply free_ids_value_open; auto.

  intros i0 Hin; destruct Hin as [Hin1 Hin2]; specialize (Hnoidoverlap i0).
  match goal with [ H : ?X -> (exists _, _) |- _ ] => assert X as Hu; [| specialize (H Hu)] end.
  split; apply free_ids_open_value2; auto.
  destruct Hnoidoverlap as [nm Hnoidoverlap]; destruct Hnoidoverlap as [Heq1 Heq2].
  eapply open_value_dual_name; eauto.

  contradict H0; intuition.
  contradict H0; intuition.
  contradict H; intuition.
  contradict H; intuition.
Qed.

(* ============================================================================= *)

Lemma free_ids_values_var_in : forall f i, In f (free_ids_value (Var i)) -> i = Free f.
Proof.
  intros f i Hin.
  destruct i; simpl in *;
  repeat match goal with 
           | [ H : _ \/ _ |- _ ] => destruct H
           | [ H : False |- _ ] => destruct H
         end.
  subst; reflexivity.
Qed.

Lemma free_ids_values_nm_in : forall f i, In f (free_ids_value (Nm i)) -> i = Free f.
Proof.
  intros f i Hin.
  destruct i; simpl in *;
  repeat match goal with 
           | [ H : _ \/ _ |- _ ] => destruct H
           | [ H : False |- _ ] => destruct H
         end.
  subst; reflexivity.
Qed.

Lemma free_ids_values_conm_in : forall f i, In f (free_ids_value (CoNm i)) -> i = Free f.
Proof.
  intros f i Hin.
  destruct i; simpl in *;
  repeat match goal with 
           | [ H : _ \/ _ |- _ ] => destruct H
           | [ H : False |- _ ] => destruct H
         end.
  subst; reflexivity.
Qed.

(* ============================================================================= *)

Lemma SO3_output_neq_pres : 
  forall G x y w u1 v1 P1 u2 v2 P2,
    G |-p (u1 ! v1; P1)
    ->
    SO3 x y w (u1 ! v1; P1) (u2 ! v2; P2)
    ->
    free_name w
    ->
    (~ exists i, (In i (free_ids_value w) /\ (In i (free_ids_value u1) \/ In i (free_ids_value v1))))
    ->
    u1 <> v1
    -> 
    u2 <> v2.
Proof.
  intros G x y w u1 v1 P1 u2 v2 P2 Htyp Hso3 Hfw Hdisjointfreeids Hneq.
  apply (SO3_output_neq_pres_aux _ _ _ _ _ Hso3 _ _ _ _ _ _ eq_refl eq_refl Hfw Hdisjointfreeids); auto.
  inversion Htyp; subst.
  inversion H5; subst; intros i Hu; destruct Hu as [Hin1 Hin2]; [|simpl in Hin2; destruct Hin2].
  inversion H4; subst.
  inversion H; subst.

  (destruct u1 as [nm1|t1|var1]; [|simpl in Hin1; destruct Hin1|]);
  (destruct v1 as [nm2|t2|var2]; [|simpl in Hin2; destruct Hin2|]);
  (try destruct nm1); 
  (try destruct nm2);
  (try destruct var1);
  (try destruct var2);
  (repeat match goal with
            | [ H : In _ (free_ids_value (ValName (Nm _))) |- _ ] => apply free_ids_values_nm_in in H; subst
            | [ H : In _ (free_ids_value (ValName (CoNm _))) |- _ ] => apply free_ids_values_conm_in in H; subst
            | [ H : In _ (free_ids_value (ValVariable (Var _))) |- _ ] => apply free_ids_values_var_in in H; subst
            | [ H : ?X <> ?X |- _  ]=> contradict H; reflexivity
          end);
  (try solve [eexists; split; auto]);
  (try (specialize (H11 i); destruct H11 as [Hu|Hu]; [|destruct Hu as [Hu1 Hu2]]; 
    match goal with
      | [ H1 : forall rho : type, ~ CTX.In (?X, rho) _, H2 : CTX.In (?X, ?Y) _ |- _ ] => specialize (H1 Y); contradict H1; auto
    end)).
Qed.

(* ============================================================================= *)

Lemma SO3_free_name_or_token : forall x y w P Q, SO3 x y w P Q -> free_name_or_token w.
Proof.
  intros x y w P Q Hso3; induction Hso3; auto.
Qed.

Lemma free_name_or_token_open_idem : forall x n u, free_name_or_token u -> open_value x n u = u.
Proof.
  intros x n u Hfnot; inversion Hfnot; subst; auto.
Qed.

(* ============================================================================= *)

Lemma SO3_input_channel1 : 
  forall x y w P' Q',
    SO3 x y w P' Q'
    ->
    forall u1 P u2 Q,
      P' = u1?; P
      ->
      Q' = u2?; Q
      ->
      (u1 = u2) \/ (free_value u1 /\ freeid_rename_value x y u1 = u2) \/ (u1 = ValVariable (Var (Free x)) /\ u2 = w).
Proof.
  intros x y w P' Q' Hso3; induction Hso3; intros u1 P1 u2 Q2 Heq1 Heq2; subst;
    unfold subst_open_proc;
      destruct P; simpl in *; subst;
        try match goal with
              | [ H : _ = _ |- _ ] => solve [discriminate H]
            end;
  (injection Heq1; intros; subst; clear Heq1);
  (injection Heq2; intros; subst; clear Heq2).
  destruct v0;
  repeat (match goal with
            | [ v : variable |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
            | [ H : _ = _ |- _ ] => solve [discriminate H]
            | [ H : _ = _ |- _ ] => injection H; intros; subst; clear H
            | [ |- _ ] => tauto
          end; simpl in H; simpl in H0; simpl; 
  (try solve [right; left; split; [constructor|reflexivity]]);
  (try solve [contradict H; left; reflexivity])).

  destruct Q; simpl in *; subst;
    try match goal with
          | [ H : _ = _ |- _ ] => solve [discriminate H]
        end;
  (injection H2; intros; subst; clear H2).
  destruct (IHHso3 _ _ _ _ eq_refl eq_refl) as [Heq|Hu]; [|destruct Hu as [Hu|Hu]; destruct Hu as [Hu1 Hu2]; subst];
    [(subst; left; reflexivity) | |].

  destruct v0;
  repeat (match goal with
            | [ v : variable |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
          end; simpl in H; simpl in H0; simpl; 
  (try solve [simpl; left; reflexivity]);
  (try solve [right; left; split; [constructor|reflexivity]])).
  simpl; left; reflexivity.
  right; right; split; simpl; auto.
  pose (SO3_free_name_or_token _ _ _ _ _ Hso3) as Hfnot.
  apply free_name_or_token_open_idem; auto.
Qed.

(* ============================================================================= *)

Lemma SO3_output_channel1 : 
  forall x y w P' Q',
    SO3 x y w P' Q'
    ->
    forall u1 v1 P u2 v2 Q,
      P' = u1!v1; P
      ->
      Q' = u2!v2; Q
      ->
      (u1 = u2) \/ (free_value u1 /\ freeid_rename_value x y u1 = u2) \/ (u1 = ValVariable (Var (Free x)) /\ u2 = w).
Proof.
  intros x y w P' Q' Hso3; induction Hso3; intros u1 v1 P1 u2 v2 Q2 Heq1 Heq2; subst;
    unfold subst_open_proc;
      destruct P; simpl in *; subst;
        try match goal with
              | [ H : _ = _ |- _ ] => solve [discriminate H]
            end;
  (injection Heq1; intros; subst; clear Heq1);
  (injection Heq2; intros; subst; clear Heq2).
  destruct v0;
  repeat (match goal with
            | [ v : variable |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
            | [ H : _ = _ |- _ ] => solve [discriminate H]
            | [ H : _ = _ |- _ ] => injection H; intros; subst; clear H
            | [ |- _ ] => tauto
          end; simpl in H; simpl in H0; simpl; 
  (try solve [right; left; split; [constructor|reflexivity]]);
  (try solve [contradict H; left; reflexivity])).

  destruct Q; simpl in *; subst;
    try match goal with
          | [ H : _ = _ |- _ ] => solve [discriminate H]
        end;
  (injection H2; intros; subst; clear H2).
  destruct (IHHso3 _ _ _ _ _ _ eq_refl eq_refl) as [Heq|Hu]; [|destruct Hu as [Hu|Hu]; destruct Hu as [Hu1 Hu2]; subst];
    [(subst; left; reflexivity) | |].

  destruct v0;
  repeat (match goal with
            | [ v : variable |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
          end; simpl in H; simpl in H0; simpl; 
  (try solve [simpl; left; reflexivity]);
  (try solve [right; left; split; [constructor|reflexivity]])).
  simpl; left; reflexivity.
  right; right; split; simpl; auto.
  pose (SO3_free_name_or_token _ _ _ _ _ Hso3) as Hfnot.
  apply free_name_or_token_open_idem; auto.
Qed.

(* ============================================================================= *)

Lemma SO3_output_channel2 : 
  forall x y w P' Q',
    SO3 x y w P' Q'
    ->
    forall u1 v1 P u2 v2 Q,
      P' = u1!v1; P
      ->
      Q' = u2!v2; Q
      ->
      (v1 = v2) \/ (free_value v1 /\ freeid_rename_value x y v1 = v2) \/ (v1 = ValVariable (Var (Free x)) /\ v2 = w).
Proof.
  intros x y w P' Q' Hso3; induction Hso3; intros u1 v1 P1 u2 v2 Q2 Heq1 Heq2; subst;
    unfold subst_open_proc;
      destruct P; simpl in *; subst;
        try match goal with
              | [ H : _ = _ |- _ ] => solve [discriminate H]
            end;
  (injection Heq1; intros; subst; clear Heq1);
  (injection Heq2; intros; subst; clear Heq2).
  destruct v3;
  repeat (match goal with
            | [ v : variable |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
            | [ H : _ = _ |- _ ] => solve [discriminate H]
            | [ H : _ = _ |- _ ] => injection H; intros; subst; clear H
            | [ |- _ ] => tauto
          end; simpl in H; simpl in H0; simpl; 
  (try solve [right; left; split; [constructor|reflexivity]]);
  (try solve [contradict H0; rewrite in_app_iff; right; intuition])).

  destruct Q; simpl in *; subst;
    try match goal with
          | [ H : _ = _ |- _ ] => solve [discriminate H]
        end;
  (injection H2; intros; subst; clear H2).
  destruct (IHHso3 _ _ _ _ _ _ eq_refl eq_refl) as [Heq|Hu]; [|destruct Hu as [Hu|Hu]; destruct Hu as [Hu1 Hu2]; subst];
    [(subst; left; reflexivity) | |].

  destruct v3;
  repeat (match goal with
            | [ v : variable |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
          end; simpl in H; simpl in H0; simpl; 
  (try solve [simpl; left; reflexivity]);
  (try solve [right; left; split; [constructor|reflexivity]])).
  simpl; left; reflexivity.
  right; right; split; simpl; auto.
  pose (SO3_free_name_or_token _ _ _ _ _ Hso3) as Hfnot.
  apply free_name_or_token_open_idem; auto.
Qed.

(* ============================================================================= *)

Lemma freeid_rename_value_cases_contra : 
  forall x y v,
      v <> freeid_rename_value x y v -> In y (free_ids_value (freeid_rename_value x y v)).
Proof.
  intros x y v Hneq.
  repeat (match goal with
            | [ v : value |- _ ] => destruct v
            | [ v : variable |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
            | [ H : context[if ?X then _ else _] |- _ ] => destruct X
            | [ H : _ = _ |- _ ] => solve [discriminate H]
            | [ H : _ = _ |- _ ] => solve [reflexivity]
            | [ |- _ \/ False  ] => left
            | [ H : False |- _ ] => solve [destruct H]
          end; simpl in *); 
  try solve [contradict Hneq; reflexivity].
Qed.

(* ============================================================================= *)

Lemma freeid_rename_value_cases_contra2 : 
  forall x y v,
      v <> freeid_rename_value x y v -> In x (free_ids_value v).
Proof.
  intros x y v Hneq.
  repeat (match goal with
            | [ v : value |- _ ] => destruct v
            | [ v : variable |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
            | [ H : context[if ?X then _ else _] |- _ ] => destruct X
            | [ H : _ = _ |- _ ] => solve [discriminate H]
            | [ H : _ = _ |- _ ] => solve [reflexivity]
            | [ |- _ \/ False  ] => left
            | [ H : False |- _ ] => solve [destruct H]
          end; simpl in *);
  try solve [contradict Hneq; reflexivity];
    auto.
Qed.

(* ============================================================================= *)

Lemma SO3_output_distinct_or_stateless : 
  forall x y w u1 v1 P1 u2 v2 P2 rho,
    SO3 x y w (u1 ! v1; P1) (u2 ! v2; P2)
    ->
    (u1 <> v1 \/ |-st rho)
    ->
    x <> y
    ->
    ~ In y (free_ids_proc (u1 ! v1; P1))
    ->
    ~ In y (free_ids_value w)
    ->
    ((u1 = w \/ v1 = w) -> u2 <> v2 \/ |-st rho)
    ->
    (u2 <> v2 \/ |-st rho).
Proof.
  intros x y w u1 v1 P1 u2 v2 P2 rho Hso3 Hneqorst Hneqxy Hnotiny Hnotinyw Heqwimpst;
  (simpl in Hnotiny; (repeat rewrite in_app_iff in Hnotiny));
  destruct Hneqorst as [Hneqorst|Hneqorst]; [|right;assumption].
  (destruct (SO3_output_channel1 _ _ _ _ _ Hso3 _ _ _ _ _ _ eq_refl eq_refl) as [Hu1|Hu1]; [|destruct Hu1 as [Hu1|Hu1]];
    [Case "u1=u2"%string | Case "free_value u1 /\ u1{x:=y} = u2"%string | Case "u1=Var (Free x) /\ u2=w"%string]);
  (destruct (SO3_output_channel2 _ _ _ _ _ Hso3 _ _ _ _ _ _ eq_refl eq_refl) as [Hu2|Hu2]; [|destruct Hu2 as [Hu2|Hu2]];
    [SCase "v1=v2"%string | SCase "free_value v1 /\ v1{x:=y} = v2"%string | SCase "v1=Var (Free x) /\ v2=w"%string]);
  (repeat match goal with
            | [ H : _ /\ _ |- _ ] => let x := fresh H in let y := fresh H in destruct H as [x y]
          end);
  subst;
  (try solve [contradict Hneqorst; reflexivity]);
  (try solve [left; assumption]);
  (try solve [
    destruct (value_dec v1 (freeid_rename_value x y v1)) as [e|n]; [rewrite <- e; left; assumption|];
      apply freeid_rename_value_cases_contra in n; 
        left; contradict Hnotiny; subst; intuition]);
  (try solve [
    destruct (value_dec u1 (freeid_rename_value x y u1)) as [e|n]; [rewrite <- e; left; assumption|];
      apply freeid_rename_value_cases_contra in n; 
        left; contradict Hnotiny; subst; intuition]);
  (try solve [destruct (value_dec u2 w); [subst; apply Heqwimpst; left; reflexivity|left; assumption]]);
  (try solve [destruct (value_dec w v2); [subst; apply Heqwimpst; right; reflexivity|left; assumption]]);
  (try solve [left; contradict Hneqorst; apply freeid_rename_value_inj in Hneqorst; [auto| |]; contradict Hnotiny; tauto]);
  (try solve [
    destruct (value_dec (freeid_rename_value x y u1) w); [ 
      subst;
        destruct (value_dec u1 (freeid_rename_value x y u1)); [
          apply Heqwimpst; left; auto 
          | apply freeid_rename_value_cases_contra in n; contradict Hnotinyw; assumption
        ]
      | left; assumption 
    ]]);
  (try solve [
    destruct (value_dec w (freeid_rename_value x y v1)); [ 
      subst;
        destruct (value_dec v1 (freeid_rename_value x y v1)); [
          apply Heqwimpst; right; auto 
          | apply freeid_rename_value_cases_contra in n; contradict Hnotinyw; assumption
        ]
      | left; assumption 
    ]
  ]).
Qed.

(* ============================================================================= *)

Inductive SO3_value : free_id -> free_id -> value -> value -> value -> Prop :=
| SO3VBase : forall x y n v u, 
      ~ In x (free_ids_value u)
      ->
      ~ In y (free_ids_value u)
      ->
      free_name_or_token v
      -> 
      SO3_value x y v (open_value x n u) (subst_value (open_value y n u) (ValVariable (Var (Free y))) v)
| SO3VStep : forall x y v i n u1 u2, 
      ~ In i (free_ids_value u1)
      ->
      ~ In i (free_ids_value u2)
      ->
      i <> x
      ->
      SO3_value x y v u1 u2
      ->
      SO3_value x y v (open_value i n u1) (open_value i n u2).

(* ============================================================================= *)

Lemma SO3_value_input : 
  forall x y w P1' P2',
    SO3 x y w P1' P2'
    ->
    forall u1 P1 u2 P2,
      P1' = u1 ? ; P1
      -> 
      P2' = u2 ? ; P2
      -> 
      SO3_value x y w u1 u2.
Proof.
  intros x y w P1' P2' Hso3; induction Hso3; intros u1 P1 u2 P2 Heq1 Heq2; subst;
    unfold subst_open_proc;
      destruct P; simpl in *; subst;
        try match goal with
              | [ H : _ = _ |- _ ] => solve [discriminate H]
            end;
  (injection Heq1; intros; subst; clear Heq1);
  (injection Heq2; intros; subst; clear Heq2).
  rewrite in_app_iff in *; apply SO3VBase; auto; tauto.

  destruct Q; simpl in *; subst;
    try match goal with
          | [ H : _ = _ |- _ ] => solve [discriminate H]
        end;
    (injection H2; intros; subst; clear H2);
    rewrite in_app_iff in *.
  apply SO3VStep; auto; apply IHHso3 with (1:=eq_refl) (2:=eq_refl).
Qed.

(* ============================================================================= *)

Lemma SO3_value_output1 : 
  forall x y w P1' P2',
    SO3 x y w P1' P2'
    ->
    forall u1 v1 P1 u2 v2 P2,
      P1' = u1 ! v1 ; P1
      -> 
      P2' = u2 ! v2 ; P2
      -> 
      SO3_value x y w u1 u2.
Proof.
  intros x y w P1' P2' Hso3; induction Hso3; intros u1 v1 P1 u2 v2 P2 Heq1 Heq2; subst;
    unfold subst_open_proc;
      destruct P; simpl in *; subst;
        try match goal with
              | [ H : _ = _ |- _ ] => solve [discriminate H]
            end;
  (injection Heq1; intros; subst; clear Heq1);
  (injection Heq2; intros; subst; clear Heq2).
  rewrite in_app_iff in *; apply SO3VBase; auto; tauto.

  destruct Q; simpl in *; subst;
    try match goal with
          | [ H : _ = _ |- _ ] => solve [discriminate H]
        end;
    (injection H2; intros; subst; clear H2);
    rewrite in_app_iff in *.
  apply SO3VStep; auto; apply IHHso3 with (1:=eq_refl) (2:=eq_refl).
Qed.

(* ============================================================================= *)

Lemma SO3_value_output2 : 
  forall x y w P1' P2',
    SO3 x y w P1' P2'
    ->
    forall u1 v1 P1 u2 v2 P2,
      P1' = u1 ! v1 ; P1
      -> 
      P2' = u2 ! v2 ; P2
      -> 
      SO3_value x y w v1 v2.
Proof.
  intros x y w P1' P2' Hso3; induction Hso3; intros u1 v1 P1 u2 v2 P2 Heq1 Heq2; subst;
    unfold subst_open_proc;
      destruct P; simpl in *; subst;
        try match goal with
              | [ H : _ = _ |- _ ] => solve [discriminate H]
            end;
  (injection Heq1; intros; subst; clear Heq1);
  (injection Heq2; intros; subst; clear Heq2).
  (repeat rewrite in_app_iff in *); apply SO3VBase; auto; tauto.

  destruct Q; simpl in *; subst;
    try match goal with
          | [ H : _ = _ |- _ ] => solve [discriminate H]
        end;
    (injection H2; intros; subst; clear H2);
    (repeat rewrite in_app_iff in * ).
  apply SO3VStep; auto; apply IHHso3 with (1:=eq_refl) (2:=eq_refl).
Qed.

(* ============================================================================= *)

Lemma SO3_value_iseq1 : 
  forall x y w P1' P2',
    SO3 x y w P1' P2'
    ->
    forall u1 v1 P1 u2 v2 P2,
      P1' = IsEq u1 v1 P1
      -> 
      P2' = IsEq u2 v2 P2
      -> 
      SO3_value x y w u1 u2.
Proof.
  intros x y w P1' P2' Hso3; induction Hso3; intros u1 v1 P1 u2 v2 P2 Heq1 Heq2; subst;
    unfold subst_open_proc;
      destruct P; simpl in *; subst;
        try match goal with
              | [ H : _ = _ |- _ ] => solve [discriminate H]
            end;
  (injection Heq1; intros; subst; clear Heq1);
  (injection Heq2; intros; subst; clear Heq2).
  (repeat rewrite in_app_iff in *); apply SO3VBase; auto; tauto.

  destruct Q; simpl in *; subst;
    try match goal with
          | [ H : _ = _ |- _ ] => solve [discriminate H]
        end;
    (injection H2; intros; subst; clear H2);
    (repeat rewrite in_app_iff in * ).
  apply SO3VStep; auto; apply IHHso3 with (1:=eq_refl) (2:=eq_refl).
Qed.

(* ============================================================================= *)

Lemma SO3_value_iseq2 : 
  forall x y w P1' P2',
    SO3 x y w P1' P2'
    ->
    forall u1 v1 P1 u2 v2 P2,
      P1' = IsEq u1 v1 P1
      -> 
      P2' = IsEq u2 v2 P2
      -> 
      SO3_value x y w v1 v2.
Proof.
  intros x y w P1' P2' Hso3; induction Hso3; intros u1 v1 P1 u2 v2 P2 Heq1 Heq2; subst;
    unfold subst_open_proc;
      destruct P; simpl in *; subst;
        try match goal with
              | [ H : _ = _ |- _ ] => solve [discriminate H]
            end;
  (injection Heq1; intros; subst; clear Heq1);
  (injection Heq2; intros; subst; clear Heq2).
  (repeat rewrite in_app_iff in *); apply SO3VBase; auto; tauto.

  destruct Q; simpl in *; subst;
    try match goal with
          | [ H : _ = _ |- _ ] => solve [discriminate H]
        end;
    (injection H2; intros; subst; clear H2);
    (repeat rewrite in_app_iff in * ).
  apply SO3VStep; auto; apply IHHso3 with (1:=eq_refl) (2:=eq_refl).
Qed.

(* ============================================================================= *)

Lemma SO3_value_isneq1 : 
  forall x y w P1' P2',
    SO3 x y w P1' P2'
    ->
    forall u1 v1 P1 u2 v2 P2,
      P1' = IsNotEq u1 v1 P1
      -> 
      P2' = IsNotEq u2 v2 P2
      -> 
      SO3_value x y w u1 u2.
Proof.
  intros x y w P1' P2' Hso3; induction Hso3; intros u1 v1 P1 u2 v2 P2 Heq1 Heq2; subst;
    unfold subst_open_proc;
      destruct P; simpl in *; subst;
        try match goal with
              | [ H : _ = _ |- _ ] => solve [discriminate H]
            end;
  (injection Heq1; intros; subst; clear Heq1);
  (injection Heq2; intros; subst; clear Heq2).
  (repeat rewrite in_app_iff in *); apply SO3VBase; auto; tauto.

  destruct Q; simpl in *; subst;
    try match goal with
          | [ H : _ = _ |- _ ] => solve [discriminate H]
        end;
    (injection H2; intros; subst; clear H2);
    (repeat rewrite in_app_iff in * ).
  apply SO3VStep; auto; apply IHHso3 with (1:=eq_refl) (2:=eq_refl).
Qed.

(* ============================================================================= *)

Lemma SO3_value_isneq2 : 
  forall x y w P1' P2',
    SO3 x y w P1' P2'
    ->
    forall u1 v1 P1 u2 v2 P2,
      P1' = IsNotEq u1 v1 P1
      -> 
      P2' = IsNotEq u2 v2 P2
      -> 
      SO3_value x y w v1 v2.
Proof.
  intros x y w P1' P2' Hso3; induction Hso3; intros u1 v1 P1 u2 v2 P2 Heq1 Heq2; subst;
    unfold subst_open_proc;
      destruct P; simpl in *; subst;
        try match goal with
              | [ H : _ = _ |- _ ] => solve [discriminate H]
            end;
  (injection Heq1; intros; subst; clear Heq1);
  (injection Heq2; intros; subst; clear Heq2).
  (repeat rewrite in_app_iff in *); apply SO3VBase; auto; tauto.

  destruct Q; simpl in *; subst;
    try match goal with
          | [ H : _ = _ |- _ ] => solve [discriminate H]
        end;
    (injection H2; intros; subst; clear H2);
    (repeat rewrite in_app_iff in * ).
  apply SO3VStep; auto; apply IHHso3 with (1:=eq_refl) (2:=eq_refl).
Qed.

(* ============================================================================= *)

Lemma SO3_value_free_name_or_token : forall x y w u1 u2, SO3_value x y w u1 u2 -> free_name_or_token w.
Proof.
  intros x y w P Q Hso3v; induction Hso3v; auto.
Qed.

(* ============================================================================= *)

Lemma SO3_value_cases : 
  forall x y w v1 v2,
    SO3_value x y w v1 v2
    ->
    (v1 = v2) \/ (free_value v1 /\ freeid_rename_value x y v1 = v2) \/ (v1 = ValVariable (Var (Free x)) /\ v2 = w).
Proof.
  intros x y w v1 v2 Hso3v; induction Hso3v; subst.
  destruct u;
  repeat (match goal with
            | [ v : variable |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
            | [ H : _ = _ |- _ ] => solve [discriminate H]
            | [ H : _ = _ |- _ ] => injection H; intros; subst; clear H
            | [ |- _ ] => tauto
          end; simpl in H; simpl in H0; simpl; 
  (try solve [right; left; split; [constructor|reflexivity]]);
  (try solve [contradict H0; rewrite in_app_iff; right; intuition])).

  destruct IHHso3v as [Heq|Hu]; [|destruct Hu as [Hu|Hu]; destruct Hu as [Hu1 Hu2]; subst];
    [(subst; left; reflexivity) | |].

  destruct u1;
  repeat (match goal with
            | [ v : variable |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
          end; simpl in H; simpl in H0; simpl; 
  (try solve [simpl; left; reflexivity]);
  (try solve [right; left; split; [constructor|reflexivity]])).
  simpl; left; reflexivity.
  right; right; split; simpl; auto.
  pose (SO3_value_free_name_or_token _ _ _ _ _ Hso3v) as Hfnot.
  apply free_name_or_token_open_idem; auto.
Qed.

(* ============================================================================= *)

Lemma list_nil : forall {A:Type} (xs : list A), xs <> nil <-> exists x, In x xs.
Proof.
  intros A xs; split; intros H.
  destruct xs as [|x ys]; [contradict H; reflexivity | exists x; intuition].
  destruct H as [x H].
  induction xs.
  contradict H; apply in_nil.
  discriminate.
Qed.

Lemma free_value_open_idem :
  forall x n i u,
    In i (free_ids_value u) -> open_value x n u = u.
Proof.
  intros x n i u Hin.
  repeat (match goal with
            | [ v : value |- _ ] => destruct v
            | [ v : variable |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
            | [ H : _ \/ _ |- _ ] => destruct H
            | [ H : _ = _ |- _ ] => solve [discriminate H]
            | [ H : _ = _ |- _ ] => injection H; intros; subst; clear H
            | [ H : False |- _ ] => destruct H
          end; simpl in *); reflexivity.
Qed.

Lemma free_value_open_idem2 :
  forall x n u,
    free_ids_value u <> nil -> open_value x n u = u.
Proof.
  intros x n u Hneq.
  rewrite list_nil in Hneq.
  destruct Hneq; eapply free_value_open_idem; eauto.
Qed.

(* ============================================================================= *)

(* ============================================================================= *)

(* ============================================================================= *)

(* ============================================================================= *)

Lemma SO3_value_free_value_exists_cases : 
  forall x y w u1 u2,
    SO3_value x y w u1 u2
    -> 
    ((u1 = u2 /\ free_ids_value u1 = nil)
      \/ (free_ids_value u1 <> nil /\ free_ids_value u2 <> nil)
      \/ (u1 = ValVariable (Var (Free x)) /\ u2 = w /\ exists k, w = ValToken k)).
Proof.
  intros x y w u1 u2 Hso3v; induction Hso3v.
  destruct u;
  repeat (match goal with
            | [ v : variable |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
            | [ H : _ = _ |- _ ] => solve [discriminate H]
          end; simpl in *);
  (try solve [right; left; split; intros Hin; discriminate Hin]);
  (try solve [left; split; reflexivity]);
  inversion H1; subst; simpl; try solve [right; left; split; intros Hin; discriminate Hin].
  right; left; injection e; intros; subst; contradict H0; left; reflexivity.
  right; right; repeat split; exists k; auto.

  destruct IHHso3v as [Hu|Hu]; [|destruct Hu as [Hu|Hu]]; destruct Hu as [Hu1 Hu2]; [| | destruct Hu2 as [Hu2 Hu3]]; subst;
    (try solve [
      (destruct u2 as [nm|t|var]; simpl; [|left; split; reflexivity|]; [
        destruct nm as [i2|i2]
        | destruct var as [i2]
      ]; (destruct i2 as [f2|b2]; simpl; [right; left; split; intros Hin; discriminate Hin | ]);
      destruct (eq_nat_decide b2 n); simpl;
        (try solve [right; left; split; intros Hin; discriminate Hin]);
        (left; split; [reflexivity| destruct (le_lt_dec b2 n); simpl; reflexivity]))]).

  right; left.
  rewrite list_nil in Hu1; destruct Hu1 as [x1 Hu1]; apply free_ids_open_value2 with (i:=i) (n:=n) in Hu1.
  rewrite list_nil in Hu2; destruct Hu2 as [x2 Hu2]; apply free_ids_open_value2 with (i:=i) (n:=n) in Hu2.
  repeat rewrite list_nil.
  split; eexists; eauto.

  right; right; destruct Hu3 as [k Heq]; subst; simpl; repeat split.
  exists k; reflexivity.
Qed.

(* ============================================================================= *)

Lemma SO3_value_is_not_rename_aux : 
  forall x y w u1 u2,
    SO3_value x y w u1 u2
    -> 
    u1 = ValVariable (Var (Free x))
    ->
    u2 = ValVariable (Var (Free y))
    ->
    x <> y
    ->
    free_name_or_token w
    ->
    False.
Proof.
  intros x y w u1 u2 Hso3v; induction Hso3v; intros Heq1 Heq2 Hneqxy Hfnot; subst.
  destruct u;
  repeat (match goal with
            | [ v : variable |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ i : id |- _ ] => destruct i
            | [ |- context[if ?X then _ else _] ] => destruct X
            | [ H : _ = _ |- _ ] => solve [discriminate H]
          end; simpl in *).
  injection Heq1; intros; subst; clear Heq1.
  contradict H; left; reflexivity.
  destruct (eq_nat_decide b n).
  destruct (value_dec (ValVariable (Var (Free y))) (ValVariable (Var (Free y)))).
  inversion Hfnot; subst; discriminate H2.
  contradict n0; reflexivity.
  destruct (le_lt_dec b n); discriminate Heq1.

  destruct SO3_value_free_value_exists_cases with (1:=Hso3v) as [Hu|Hu]; 
    [|destruct Hu as [Hu|Hu]]; destruct Hu as [Hu1 Hu2]; [| | destruct Hu2 as [Hu2 Hu3]]; subst.
  rewrite Heq1 in Heq2; contradict Hneqxy; injection Heq2; intros; subst; reflexivity.

  apply free_value_open_idem2 with (x:=i) (n:=n) in Hu1.
  apply free_value_open_idem2 with (x:=i) (n:=n) in Hu2.
  rewrite Hu1 in Heq1; clear Hu1.
  rewrite Hu2 in Heq2; clear Hu2.
  apply IHHso3v; auto.

  destruct Hu3 as [k Hu3]; subst; simpl in Heq2; discriminate Heq2.
Qed.  
  

Lemma SO3_value_is_not_rename : 
  forall x y w,
    x <> y
    ->
    free_name_or_token w
    ->
    ~ SO3_value x y w (ValVariable (Var (Free x))) (ValVariable (Var (Free y))).
Proof.
  intros x y w Hneq Hfnot Hso3v.
  apply SO3_value_is_not_rename_aux in Hso3v; auto.
Qed.  

(* ============================================================================= *)

Lemma ctx_add_value_in1 :
  forall u sigma v rho G,
    CTX.In (u, sigma) G
    -> 
    CTX.In (u, sigma) (ctx_add_value v rho G).
Proof.
  intros u sigma v rho G Hin.
  destruct v; simpl; intuition.
Qed.  

(* ============================================================================= *)

Lemma subst_r_value_alt : 
  forall G sigma x y u1 u2 w rho,
  G |-v u1 : sigma
  ->
  SO3_value x y w u1 u2
  -> 
  x <> y
  ->
  ~ In y (free_ids_value u1)
  ->
  ~ In y (free_ids_value w)
  ->
  CTX.In (ValVariable (Var (Free x)), rho) G
  ->
  (forall k, w = Token k -> rho = TSingleton (Token k))
  ->
  ctx_add_value w rho G |-part G (+) ctx_add_value w rho CTX.empty
  ->
  ctx_add_value w rho G |-v u2 : sigma.
Proof.
  intros G sigma x y u1 u2 w rho Hlookup Hso3v Hneqxy Hnotinyu1 Hnotinyw HinxG Htoken Hpart.
  apply partition_wf in Hpart.
  destruct (SO3_value_cases _ _ _ _ _ Hso3v) as [Hu|Hu]; [|destruct Hu as [Hu|Hu]; destruct Hu as [Hu1 Hu2]].
  subst.
  inversion Hlookup; subst; [|apply LToken; auto].
  apply LContext; auto.
  apply ctx_add_value_in1; auto.

  destruct (value_dec u1 (freeid_rename_value x y u1)) as [e|n].
  rewrite <- Hu2; rewrite <- e; clear Hu2 e.
  inversion Hlookup; subst; [ apply LContext | apply LToken]; auto.
  apply ctx_add_value_in1; auto.
  apply freeid_rename_value_cases_contra2 in n.

  pose (SO3_value_free_name_or_token _ _ _ _ _ Hso3v) as Hfnot.
  destruct Hu1; simpl in n; (destruct n as [Heq|Hfalse]; [subst|destruct Hfalse]);
    inversion Hlookup; inversion H; subst; (destruct (H6 x) as [Hu3|Hu3]; [|destruct Hu3 as [Hu3 Hu4]]).
  destruct (Hu3 _ HinxG).
  destruct (Hu3 _ H0).
  destruct (Hu3 _ HinxG).
  destruct (Hu4 _ H0).
  destruct (Hu3 _ H0).
  assert (rho = sigma); [|subst].
  apply (H5 _ _ _ HinxG H0).
  simpl.

  destruct (string_dec x x); [|tauto].
  pose (SO3_value_is_not_rename x y _ Hneqxy Hfnot) as n.
  contradict n.
  replace (ValVariable (Var (Free y))) with (freeid_rename_value x y (Var (Free x))).
  apply Hso3v.
  simpl.
  destruct (string_dec x x); tauto.

  rewrite Hu1 in *; rewrite Hu2.
  inversion Hlookup; subst.
  assert (sigma = rho); [|subst].
  inversion H; subst; apply (H2 _ _ _ H0 HinxG).
  pose (SO3_value_free_name_or_token _ _ _ _ _ Hso3v) as Hu; inversion Hu; subst; simpl; [ 
    |
    | destruct k as [k]; rewrite (Htoken k eq_refl) in HinxG; 
      assert (rho = TSingleton (Token k)); [|subst; apply LToken; auto]; 
        apply Htoken; auto
  ]; 
  apply LContext; auto; intuition.
Qed.
  
(* ============================================================================= *)

Lemma SO3_value_var_bound_determines_subst : 
  forall x y w u1 u2,
    SO3_value x y w u1 u2
    -> 
    forall n,
      x <> y
      ->
      ~ In y (free_ids_value u1)
      ->
      ~ In y (free_ids_value w)
      ->
      u1 = ValVariable (Var (Bound n))
      -> 
      u2 = u1.
Proof.
  intros x y w u1 u2 Hso3v; induction Hso3v; intros n0 Hneq Hnotinu1 Hnotinw Heq; subst.
  assert (open_value y n u = Var (Bound n0)) as Hu.
  destruct u; simpl in *; try discriminate Heq.
  destruct v0; simpl in *; try discriminate Heq.
  destruct i; simpl in *; try discriminate Heq.
  destruct (eq_nat_decide b n); try discriminate Heq.
  destruct (le_lt_dec b n); simpl; assumption.
  rewrite Hu.
  simpl.
  symmetry; apply Heq.

  assert (u1 = ValVariable (Var (Bound n0)) \/ exists n1, pred n1 = n0 /\ u1 = ValVariable (Var (Bound n1))) as Hu.
  destruct u1; simpl in *; try discriminate Heq.
  destruct v0; simpl in *; try discriminate Heq.
  destruct i0; simpl in *; try discriminate Heq.
  destruct (eq_nat_decide b n); try discriminate Heq.
  destruct (le_lt_dec b n); simpl; [left; assumption| right].
  injection Heq; intros; subst.
  exists b; split; reflexivity.

  destruct Hu as [Hu|Hu].
  rewrite IHHso3v with (n:=n0); auto; contradict Hnotinu1; apply free_ids_open_value2; auto.
  destruct Hu as [n1 Hu]; destruct Hu; subst.
  rewrite IHHso3v with (n:=n1); auto; contradict Hnotinu1; apply free_ids_open_value2; auto.
Qed.

(* ============================================================================= *)

Lemma SO3_value_var_determines_subst : 
  forall x y w u1 u2,
    SO3_value x y w u1 u2
    -> 
    x <> y
    ->
    ~ In y (free_ids_value u1)
    ->
    ~ In y (free_ids_value w)
    ->
    u1 = ValVariable (Var (Free x))
    -> 
    (u2 = w \/ u1 = u2).
Proof.
  intros x y w u1 u2 Hso3v; induction Hso3v; intros Hneq Hnotinu1 Hnotinw Heq; subst.
  destruct u;
  repeat (match goal with
            | [ v : variable |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ i : id |- _ ] => destruct i
            | [ H : _ = _ |- _ ] => solve [discriminate H]
          end; simpl in *);
  (try solve [injection Heq; intros; subst; clear Heq; contradict H; left; reflexivity]).
  destruct (eq_nat_decide b n) as [e0|n0].
  destruct (value_dec (ValVariable (Var (Free y))) (ValVariable (Var (Free y)))) as [e1|n1]; [left|contradict n1]; reflexivity.
  destruct (le_lt_dec b n); discriminate Heq.

  assert ((u1 = ValVariable (Var (Bound n)) /\ i = x) \/ u1 = ValVariable (Var (Free x))).
  destruct u1; simpl in *; try discriminate Heq.
  destruct v0; simpl in *; try discriminate Heq.
  destruct i0; simpl in *; try discriminate Heq.
  right; assumption.
  destruct (eq_nat_decide b n) as [e0|n0].
  apply eq_nat_eq in e0; subst.
  injection Heq; intros; subst.
  left; split; auto.
  destruct (le_lt_dec b n); discriminate Heq.
  destruct H2 as [H2|H2].
  destruct H2; subst.
  assert (u2 = ValVariable (Var (Bound n))); [|subst].
  eapply (SO3_value_var_bound_determines_subst _ _ _ _ _ Hso3v ); auto.
  right; reflexivity.
  assert (~ In y (free_ids_value u1)) as Hu1; [contradict Hnotinu1; apply free_ids_open_value2; auto|].
  destruct (IHHso3v Hneq Hu1 Hnotinw H2); subst.
  left.
  pose (SO3_value_free_name_or_token _ _ _ _ _ Hso3v) as Hu; inversion Hu; subst; simpl; reflexivity.
  subst.
  right; reflexivity.
Qed.

(* ============================================================================= *)

(* Stronger lemma now that i<>x is in SO3Step *)
Lemma SO3_value_var_determines_subst_improved : 
  forall x y w u1 u2,
    SO3_value x y w u1 u2
    -> 
    x <> y
    ->
    ~ In y (free_ids_value u1)
    ->
    ~ In y (free_ids_value w)
    ->
    u1 = ValVariable (Var (Free x))
    ->
    u2 = w.
Proof.
  intros x y w u1 u2 Hso3v; induction Hso3v; intros Hneq Hnotinu1 Hnotinw Heq; subst.
  destruct u;
  repeat (match goal with
            | [ v : variable |- _ ] => destruct v
            | [ n : name |- _ ] => destruct n
            | [ i : id |- _ ] => destruct i
            | [ H : _ = _ |- _ ] => solve [discriminate H]
          end; simpl in *);
  (try solve [injection Heq; intros; subst; clear Heq; contradict H; left; reflexivity]).
  destruct (eq_nat_decide b n) as [e0|n0].
  destruct (value_dec (ValVariable (Var (Free y))) (ValVariable (Var (Free y)))) as [e1|n1]; [|contradict n1]; reflexivity.
  destruct (le_lt_dec b n); discriminate Heq.

  assert (u1 = ValVariable (Var (Free x))).
  destruct u1; simpl in *; try discriminate Heq.
  destruct v0; simpl in *; try discriminate Heq.
  destruct i0; simpl in *; try discriminate Heq.
  assumption.
  destruct (eq_nat_decide b n) as [e0|n0].
  apply eq_nat_eq in e0; subst.
  injection Heq; intros; subst.
  contradict H1; reflexivity.

  destruct (le_lt_dec b n); discriminate Heq.
  subst.

  assert (~ In y (free_ids_value (ValVariable (Var (Free x))))) as Hu1; [contradict Hnotinu1; apply free_ids_open_value2; auto|].
  pose (IHHso3v Hneq Hu1 Hnotinw eq_refl) as Hu2; rewrite Hu2; clear Hu2.
  pose (SO3_value_free_name_or_token _ _ _ _ _ Hso3v) as Hu; inversion Hu; subst; simpl; reflexivity.
Qed.

(* ============================================================================= *)

Lemma ctx_add_value1 : 
  forall v rho u sigma G,
    CTX.In (v, rho) G
    ->
    CTX.In (v, rho) (ctx_add_value u sigma G).
Proof.
  intros v rho u sigma G Hin.
  destruct u; simpl; auto; apply CTXFacts.add_2; auto.
Qed.

Lemma ctx_add_value2 : 
  forall u rho sigma G1 G2,
    (ctx_add_value u sigma G1) |-wf 
    ->
    CTX.In (u, rho) G1
    ->
    CTX.In (u, sigma) (ctx_add_value u sigma G2).
Proof.
  intros u rho sigma G1 G2 Hwf Hin.
  destruct u; simpl; auto; try solve [apply CTXFacts.add_1; auto].
  inversion Hwf; subst.
  specialize (H _ _ Hin).
  inversion H.
Qed.

(* ============================================================================= *)

Lemma SO3_value_var_determines_subst_cases : 
  forall x y w u1 u2,
    SO3_value x y w u1 u2
    -> 
    x <> y
    ->
    ~ In y (free_ids_value u1)
    ->
    ~ In y (free_ids_value w)
    ->
    (((u1 <> ValVariable (Var (Free x))) \/ (u1 = ValVariable (Var (Free x)) /\ u1 = u2 /\ u2 <> w))
      \/ ((u1 = ValVariable (Var (Free x)) /\ u2 = w))).
Proof.
  intros x y w u1 u2 Hso3v Hneqxy Hnotinu1 Hnotinw.
  destruct (value_dec u1 (ValVariable (Var (Free x)))) as [e1|n1]; [|intuition].
  pose (SO3_value_var_determines_subst _ _ _ _ _ Hso3v Hneqxy Hnotinu1 Hnotinw) as Hu; destruct Hu; subst; try solve [intuition].
  left; right; repeat (split; [auto|]).
  subst.
  pose (SO3_value_free_name_or_token _ _ _ _ _ Hso3v) as Hu; inversion Hu; discriminate.
Qed.

(* ============================================================================= *)

Lemma typed_change_type : 
  forall v rho sigma G P,
    G |-p P 
    ->
    CTX.In (v, rho) G
    ->
    ~ In v (free_values_proc P)
    -> 
    ctx_replace v rho sigma G |-p P.
Proof.
  intros v rho sigma G P Htyp Hin Hnotinv; unfold ctx_replace.
  apply partition_typed_weaken_left with (GL:=CTX.remove (v, rho) G) (GR:=CTX.add (v, sigma) CTX.empty).
  apply typed_strengthen with (G2:=G); auto.
  intuition.
  intros u Hin2.
  pose (free_values_in_context_1 _ _ Htyp) as Hfvic.
  specialize (Hfvic u Hin2).
  destruct Hfvic as [sigma2 Hin3].
  exists sigma2.
  apply CTXFacts.remove_2.
  intros Heq; injection Heq; intros; subst; clear Heq.
  contradict Hin3; auto.
  auto.
  constructor.
  intros a; destruct a; 
    repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff || rewrite CTXFacts.union_iff || rewrite CTXFacts.empty_iff); 
      tauto.
  pose (typed_ctx_wf _ _ Htyp) as Hwf; inversion Hwf; subst.
  constructor.
  intros u rho0 Hin2. 
  repeat (rewrite CTXFacts.add_iff in Hin2 || rewrite CTXFacts.remove_iff in Hin2); 
    destruct Hin2 as [Hin2|Hin2]; [|destruct Hin2 as [Hin2 Hin3]];
      [injection Hin2; intros; subst; clear Hin2|].
  apply (H _ _ Hin).
  apply (H _ _ Hin2).
  intros u rho0 sigma0 Hinr2 Hins2.
  (repeat (rewrite CTXFacts.add_iff in Hinr2 || rewrite CTXFacts.remove_iff in Hinr2); 
    destruct Hinr2 as [Hinr2|Hinr2]; [|destruct Hinr2 as [Hinr2 Hinr3]];
      [injection Hinr2; intros; subst; clear Hinr2|]);
  (repeat (rewrite CTXFacts.add_iff in Hins2 || rewrite CTXFacts.remove_iff in Hins2); 
    destruct Hins2 as [Hins2|Hins2]; [|destruct Hins2 as [Hins2 Hins3]];
      [injection Hins2; intros; subst; clear Hins2|]).
  reflexivity.
  rewrite (H0 _ _ _ Hin Hins2) in *; contradict Hins3; reflexivity.
  rewrite (H0 _ _ _ Hin Hinr2) in *; contradict Hinr3; reflexivity.
  apply (H0 _ _ _ Hinr2 Hins2).

  intros x; specialize (H1 x).
  destruct H1 as [H1|H1]; [|destruct H1 as [H1 H2]].
  destruct (value_dec (ValVariable (Var (Free x))) v) as [e|n]; [
    subst; right; split; intros rho0; specialize (H1 _ Hin); destruct H1
    | left; intros rho0; specialize (H1 rho0); contradict H1;
      rewrite CTXFacts.add_iff in H1; rewrite CTXFacts.remove_iff in H1; destruct H1 as [H1|H1];
        [ injection H1; intros; subst; clear H1; contradict n; reflexivity
          | destruct H1; auto
        ]
  ].
  (destruct (value_dec (ValName (Nm (Free x))) v) as [e1|n1]); 
  (destruct (value_dec (ValName (CoNm (Free x))) v) as [e2|n2]); 
  subst;
  try discriminate e2.
  left; intros rho0; specialize (H1 rho); contradict H1; auto.
  left; intros rho0; specialize (H2 rho); contradict H2; auto.
  right; split; intros rho0; (repeat rewrite CTXFacts.add_iff in * || rewrite CTXFacts.remove_iff in * ); [
    specialize (H1 rho0); contradict H1
    | 
  ].
  destruct H1 as [H1|H1]; [
    injection H1; intros; subst; clear H1; contradict n1; reflexivity
    | destruct H1; auto
  ].
  intros Hin2; destruct Hin2 as [Hin2|Hin2].
  injection Hin2; intros; subst; clear Hin2.
  contradict n2; reflexivity.
  destruct Hin2 as [Hin2 Hin3]; specialize (H2 rho0); contradict H2; auto.

  pose (typed_ctx_wf _ _ Htyp) as Hwf; inversion Hwf; subst.
  intros v1 rho1.
  destruct (value_dec v v1) as [e|n].
  subst.
  left.
  rewrite CTXFacts.remove_iff; intros Hin2; destruct Hin2 as [Hin2 Hin3].
  assert (rho <> rho1).
  contradict Hin3; subst; reflexivity.
  contradict H2; apply H0 with (u:=v1); auto.
  right; left.
  rewrite CTXFacts.add_iff; intros Hin2; destruct Hin2 as [Hin2 | Hin3].
  injection Hin2; intros; subst; clear Hin2.
  contradict n; reflexivity.
  rewrite CTXFacts.empty_iff in Hin3.
  assumption.
Qed.

(* ============================================================================= *)

Lemma SO3_value_free_values_in_context1 : 
  forall u2 v2 x y w u1, 
    In v2 (free_values_value u2)
    ->
    SO3_value x y w u1 u2
    ->
    (exists v1, In v1 (free_values_value u1) /\ SO3_value x y w v1 v2).
Proof.
  intros u2 v2 x y w u1 Hin Hso3v.
  destruct (SO3_value_cases _ _ _ _ _ Hso3v).
  eexists; split; subst; eauto.
  apply free_values_value_1 in Hin; subst; assumption.

  destruct H.
  destruct H; subst.

  rewrite <- (free_values_value_yields_equal_values _ _ Hin) in Hso3v.
  rewrite <- (free_values_value_yields_equal_values _ _ Hin) in Hin.
  exists u1; split; auto.
  apply free_values_value_2; auto.
  
  destruct H; subst.
  exists (ValVariable (Var (Free x))); split; auto.
  apply free_values_value_2; constructor.
  rewrite <- (free_values_value_yields_equal_values _ _ Hin) in Hso3v.
  rewrite <- (free_values_value_yields_equal_values _ _ Hin).
  auto.
Qed.

(* ============================================================================= *)

Ltac SO3_free_values_in_context1_aux_tac1 := 
  repeat match goal with
           | [ H : exists _, _ |- _ ] => destruct H
           | [ H : _ = _ |- _ ] => discriminate H
         end.

Lemma SO3_free_values_in_context1_aux : 
  forall P2 v2 x y w P1, 
    In v2 (free_values_proc P2)
    ->
    SO3 x y w P1 P2
    ->
    (exists v1, In v1 (free_values_proc P1) /\ SO3_value x y w v1 v2).
Proof.
  intros P2; induction P2; intros v2 x y w P1 Hin Hso3;
    destruct P1; simpl in *; pose Hso3 as Hso3copy;
      ((eapply SO3_inp_decompose with (2:=eq_refl) in Hso3copy; SO3_free_values_in_context1_aux_tac1)
        || (eapply SO3_out_decompose with (2:=eq_refl) in Hso3copy; SO3_free_values_in_context1_aux_tac1)
          || (eapply SO3_par_decompose with (2:=eq_refl) in Hso3copy; SO3_free_values_in_context1_aux_tac1)
            || (eapply SO3_sum_decompose with (2:=eq_refl) in Hso3copy; SO3_free_values_in_context1_aux_tac1)
              || (eapply SO3_rep_decompose with (2:=eq_refl) in Hso3copy; SO3_free_values_in_context1_aux_tac1)
                || (eapply SO3_zero_decompose with (2:=eq_refl) in Hso3copy; SO3_free_values_in_context1_aux_tac1)
                  || (eapply SO3_iseq_decompose with (2:=eq_refl) in Hso3copy; SO3_free_values_in_context1_aux_tac1)
                    || (eapply SO3_isneq_decompose with (2:=eq_refl) in Hso3copy; SO3_free_values_in_context1_aux_tac1)
                      || (eapply SO3_new_decompose with (2:=eq_refl) in Hso3copy; SO3_free_values_in_context1_aux_tac1));
  repeat match goal with 
           | [ H : _ = _ |- _ ] => injection H; intros; subst; clear H
         end.

  Case "input"%string.
  repeat (rewrite in_app_iff in *);
    repeat match goal with 
             | [ H : _ \/ _ |- _ ] => destruct H
           end.
  pose (SO3_value_input _ _ _ _ _ Hso3 _ _ _ _ eq_refl eq_refl) as Hso3v1.
  apply SO3_value_free_values_in_context1 with (v2:=v2) in Hso3v1; [|auto]; 
    destruct Hso3v1 as [v1 Hso3v1]; destruct Hso3v1 as [Hu1 Hu2].
  exists v1; (repeat rewrite in_app_iff); split; auto.
  pose (SO3_input _ _ _ _ _ _ _ Hso3) as Hso31.
  pose (IHP2 _ _ _ _ _ H Hso31) as Hu.
  destruct Hu as [v1 Hu]; destruct Hu as [Hu1 Hu2].
  exists v1; (repeat rewrite in_app_iff); split; auto.

  Case "output"%string.
  repeat (rewrite in_app_iff in *);
    repeat match goal with 
             | [ H : _ \/ _ |- _ ] => destruct H
           end.
  pose (SO3_value_output1 _ _ _ _ _ Hso3 _ _ _ _ _ _ eq_refl eq_refl) as Hso3v1.
  apply SO3_value_free_values_in_context1 with (v2:=v2) in Hso3v1; [|auto]; 
    destruct Hso3v1 as [v4 Hso3v1]; destruct Hso3v1 as [Hu1 Hu2].
  exists v4; (repeat rewrite in_app_iff); split; auto.
  pose (SO3_value_output2 _ _ _ _ _ Hso3 _ _ _ _ _ _ eq_refl eq_refl) as Hso3v1.
  apply SO3_value_free_values_in_context1 with (v2:=v2) in Hso3v1; [|auto]; 
    destruct Hso3v1 as [v4 Hso3v1]; destruct Hso3v1 as [Hu1 Hu2].
  exists v4; (repeat rewrite in_app_iff); split; auto.
  pose (SO3_output _ _ _ _ _ _ _ _ _ Hso3) as Hso31.
  pose (IHP2 _ _ _ _ _ H Hso31) as Hu.
  destruct Hu as [v4 Hu]; destruct Hu as [Hu1 Hu2].
  exists v4; (repeat rewrite in_app_iff); split; auto.

  Case "iseq"%string.
  repeat (rewrite in_app_iff in *);
    repeat match goal with 
             | [ H : _ \/ _ |- _ ] => destruct H
           end.
  pose (SO3_value_iseq1 _ _ _ _ _ Hso3 _ _ _ _ _ _ eq_refl eq_refl) as Hso3v1.
  apply SO3_value_free_values_in_context1 with (v2:=v2) in Hso3v1; [|auto]; 
    destruct Hso3v1 as [v4 Hso3v1]; destruct Hso3v1 as [Hu1 Hu2].
  exists v4; (repeat rewrite in_app_iff); split; auto.
  pose (SO3_value_iseq2 _ _ _ _ _ Hso3 _ _ _ _ _ _ eq_refl eq_refl) as Hso3v1.
  apply SO3_value_free_values_in_context1 with (v2:=v2) in Hso3v1; [|auto]; 
    destruct Hso3v1 as [v4 Hso3v1]; destruct Hso3v1 as [Hu1 Hu2].
  exists v4; (repeat rewrite in_app_iff); split; auto.
  pose (SO3_iseq _ _ _ _ _ _ _ _ _ Hso3) as Hso31.
  pose (IHP2 _ _ _ _ _ H Hso31) as Hu.
  destruct Hu as [v4 Hu]; destruct Hu as [Hu1 Hu2].
  exists v4; (repeat rewrite in_app_iff); split; auto.

  Case "isneq"%string.
  repeat (rewrite in_app_iff in *);
    repeat match goal with 
             | [ H : _ \/ _ |- _ ] => destruct H
           end.
  pose (SO3_value_isneq1 _ _ _ _ _ Hso3 _ _ _ _ _ _ eq_refl eq_refl) as Hso3v1.
  apply SO3_value_free_values_in_context1 with (v2:=v2) in Hso3v1; [|auto]; 
    destruct Hso3v1 as [v4 Hso3v1]; destruct Hso3v1 as [Hu1 Hu2].
  exists v4; (repeat rewrite in_app_iff); split; auto.
  pose (SO3_value_isneq2 _ _ _ _ _ Hso3 _ _ _ _ _ _ eq_refl eq_refl) as Hso3v1.
  apply SO3_value_free_values_in_context1 with (v2:=v2) in Hso3v1; [|auto]; 
    destruct Hso3v1 as [v4 Hso3v1]; destruct Hso3v1 as [Hu1 Hu2].
  exists v4; (repeat rewrite in_app_iff); split; auto.
  pose (SO3_isneq _ _ _ _ _ _ _ _ _ Hso3) as Hso31.
  pose (IHP2 _ _ _ _ _ H Hso31) as Hu.
  destruct Hu as [v4 Hu]; destruct Hu as [Hu1 Hu2].
  exists v4; (repeat rewrite in_app_iff); split; auto.

  Case "new"%string.
  repeat (rewrite in_app_iff in *);
    repeat match goal with 
             | [ H : _ \/ _ |- _ ] => destruct H
           end.
  pose (SO3_new _ _ _ _ _ Hso3) as Hso31.
  pose (IHP2 _ _ _ _ _ Hin Hso31) as Hu.
  destruct Hu as [v4 Hu]; destruct Hu as [Hu1 Hu2].
  exists v4; (repeat rewrite in_app_iff); split; auto.

  Case "par"%string.
  repeat (rewrite in_app_iff in *);
    repeat match goal with 
             | [ H : _ \/ _ |- _ ] => destruct H
           end.
  pose (SO3_par _ _ _ _ _ _ _ Hso3) as Hso31; destruct Hso31 as [Hso31 Hso32].
  pose (IHP2_1 _ _ _ _ _ H Hso31) as Hu.
  destruct Hu as [v4 Hu]; destruct Hu as [Hu1 Hu2].
  exists v4; (repeat rewrite in_app_iff); split; auto.
  pose (SO3_par _ _ _ _ _ _ _ Hso3) as Hso31; destruct Hso31 as [Hso31 Hso32].
  pose (IHP2_2 _ _ _ _ _ H Hso32) as Hu.
  destruct Hu as [v4 Hu]; destruct Hu as [Hu1 Hu2].
  exists v4; (repeat rewrite in_app_iff); split; auto.

  Case "sum"%string.
  repeat (rewrite in_app_iff in *);
    repeat match goal with 
             | [ H : _ \/ _ |- _ ] => destruct H
           end.
  pose (SO3_sum _ _ _ _ _ _ _ Hso3) as Hso31; destruct Hso31 as [Hso31 Hso32].
  pose (IHP2_1 _ _ _ _ _ H Hso31) as Hu.
  destruct Hu as [v4 Hu]; destruct Hu as [Hu1 Hu2].
  exists v4; (repeat rewrite in_app_iff); split; auto.
  pose (SO3_sum _ _ _ _ _ _ _ Hso3) as Hso31; destruct Hso31 as [Hso31 Hso32].
  pose (IHP2_2 _ _ _ _ _ H Hso32) as Hu.
  destruct Hu as [v4 Hu]; destruct Hu as [Hu1 Hu2].
  exists v4; (repeat rewrite in_app_iff); split; auto.

  Case "rep"%string.
  pose (SO3_rep _ _ _ _ _ Hso3) as Hso31.
  pose (IHP2 _ _ _ _ _ Hin Hso31) as Hu.
  destruct Hu as [v4 Hu]; destruct Hu as [Hu1 Hu2].
  exists v4; (repeat rewrite in_app_iff); split; auto.

  Case "zero"%string.
  destruct Hin.

Qed.

(* ============================================================================= *)

Lemma free_values_proc_yields_free_value : forall P v, In v (free_values_proc P) -> free_value v.
Proof.
  intros P; induction P; intros u Hin; simpl in Hin; repeat rewrite in_app_iff in *;
    repeat match goal with 
         | [ H : _ \/ _ |- _ ] => destruct H
         | [ H : False |- _ ] => destruct H
         | [ u : value |- free_value u ] => solve [eapply free_values_value_yields_free_values; eauto]
       end;
    (try solve [apply IHP; auto]);
    (try solve [apply IHP1; auto]);
    (try solve [apply IHP2; auto]).
Qed.

(* ============================================================================= *)

Lemma SO3_free_values_in_context1 : 
  forall x y w P1 P2 G rho,
    G |-p P1
    ->
    SO3 x y w P1 P2
    ->
    x <> y
    ->
    CTX.In (ValVariable (Var (Free x)), rho) G
    ->
    free_name_or_token w
    ->
    free_values_in_context G P1
    ->
    free_values_in_context (ctx_add_value w rho G) P2.
Proof.
  intros x y w P1 P2 G rho Htyp Hso3 Hneq HinxG Hfnot Hfvic.
  intros v HinvP2.
  pose (SO3_free_values_in_context1_aux _ _ _ _ _ _ HinvP2 Hso3) as Hu.
  destruct Hu as [v1 Hu]; destruct Hu as [Hu1 Hu2].
  specialize (Hfvic v1 Hu1).
  destruct Hfvic as [sigma Hfvic].

  destruct (SO3_value_cases _ _ _ _ _ Hu2) as [Hu3|Hu3]; [|destruct Hu3 as [Hu3|Hu3]].

  subst; exists sigma; apply ctx_add_value_in1; auto.

  destruct Hu3 as [Hu3 Hu4].

  assert (v1 = v \/ v1 = ValVariable (Var (Free x))) as Hcases.
  destruct (value_dec v1 v); [left; assumption | right; subst].
  apply freeid_rename_value_cases_contra2 in n.
  pose (typed_ctx_wf _ _ Htyp) as Hwf; inversion Hwf; subst.
  inversion Hu3; subst; [ 
    simpl in n; destruct n as [n|n]; [|destruct n]; subst; 
      destruct (H1 x) as [Hv|Hv]; [
        specialize (Hv rho); contradict Hv; auto
        |destruct Hv as [Hv1 Hv2]; specialize (Hv1 sigma); contradict Hv1; auto
      ]
    | simpl in n; destruct n as [n|n]; [|destruct n]; subst; 
      destruct (H1 x) as [Hv|Hv]; [
        specialize (Hv rho); contradict Hv; auto
        |destruct Hv as [Hv1 Hv2]; specialize (Hv2 sigma); contradict Hv2; auto
      ]
    | simpl in n; destruct n as [n|n]; [|destruct n]; subst; reflexivity
  ].
  destruct Hcases.
  clear Hu4; subst.
  exists sigma; apply ctx_add_value_in1; auto.

  subst; simpl in Hu2.
  destruct (string_dec x x) as [_|n]; [|contradict n; reflexivity].
  apply SO3_value_is_not_rename_aux in Hu2; auto.
  destruct Hu2.

  destruct Hu3; subst.
  exists rho; inversion Hfnot; subst; [ | | pose (free_values_proc_yields_free_value _ _ HinvP2) as Hcontr; inversion Hcontr ]; 
    simpl; apply CTXFacts.add_1; reflexivity.
Qed.

(* ============================================================================= *)



(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

Lemma SO3_value_cases_input : 
  forall rho s G x y w u1 P1 u2 P2,
    G |-v u1 : TChannel s
    ->
    SO3 x y w (u1 ? ; P1) (u2 ? ; P2)
    ->
    x <> y
    ->
    ~ In y (free_ids_proc (u1 ? ; P1))
    ->
    ~ In y (free_ids_value w)
    ->
    CTX.In (ValVariable (Var (Free x)), rho) G
    ->
    (forall k : string, w = Token k -> rho = TSingleton (Token k))
    ->
    (ctx_add_value w rho G |-part G (+) ctx_add_value w rho CTX.empty)
    ->
    (G |-p u1 ? ; P1)
    ->
    (u1 = u2 /\ u2 = w /\ rho = TChannel s /\ |-st TChannel s)
    \/ (u1 = u2 /\ u2 <> w /\ u1 <> ValVariable (Var (Free x)))
    \/ (u1 = ValVariable (Var (Free x)) /\ u2 = w /\ rho = TChannel s).
Proof.
  intros rho s G x y w u1 P1 u2 P2 H Hso3 Hneqxy HnotinyP Hnotinyv HinxG Htoken Hpart HtypP.

  assert (SO3_value x y w u1 u2) as Hso3v; [eapply SO3_value_input; eauto|].

  assert (~ In y (free_ids_value u1)) as Hnotinyu; [contradict HnotinyP; simpl; intuition|].

  assert (free_name_or_token w) as Hfnot; [apply (SO3_value_free_name_or_token _ _ _ _ _ Hso3v) |].

  destruct (SO3_value_var_determines_subst_cases _ _ _ _ _ Hso3v Hneqxy Hnotinyu Hnotinyv) as [Hsubstleaveschannelalone | Hsubstaffectschannel]; [
    destruct (SO3_value_cases _ _ _ _ _ Hso3v) as [Hu|Hu] ; [ | destruct Hu as [Hu|Hu]; destruct Hu as [Hu1 Hu2]]; subst; [
      destruct (value_dec w u2) as [e|n]; [
        subst; 
          assert (rho = TChannel s); [|subst]; [
            inversion Hfnot; subst; [
              |
              | solve [
                destruct k; specialize (Htoken _ eq_refl); subst;
                  inversion H as [? ? ? Hwf Hin|]; subst; 
                    inversion Hwf as [? Hfv]; subst;
                      pose (Hfv _ _ Hin) as Hu2; inversion Hu2
              ]
            ];
            solve [
              apply partition_wf in Hpart; inversion Hpart as [a1 Hfv Heqtypes Hdisjoint]; subst; inversion H; subst; eapply Heqtypes; 
                [
                  simpl; apply CTXFacts.add_1; reflexivity
                  | simpl; apply CTXFacts.add_2; assumption
                ]
            ]
            |
          ];
          assert (|-st TChannel s); [
            inversion Hpart as [? ? ? _ _ Hdisjoint] ; subst;
              specialize (Hdisjoint u2 (TChannel s));
                destruct Hdisjoint as [Hu|Hu]; [|destruct Hu as [Hu|Hu]]; [| | assumption]; [
                  inversion H; contradict Hu; auto
                  | contradict Hu; simpl; 
                    inversion Hfnot; subst; 
                      (try solve [simpl; apply CTXFacts.add_1; reflexivity]); 
                      destruct k; specialize (Htoken _ eq_refl); subst; discriminate Htoken
                ]
            |
          ]; 
          left; tauto
        | right; left; split; [ 
          reflexivity
          | split; [
            intros Heq; contradict n; subst; reflexivity
            | destruct (value_dec u2 (ValVariable (Var (Free x)))); [ 
              subst; assert (~ In y (free_ids_value (ValVariable (Var (Free x))))) as Hnotinyx; [simpl; tauto | ];
                pose (SO3_value_var_determines_subst_improved _ _ _ _ _ Hso3v Hneqxy Hnotinyx Hnotinyv eq_refl) as Hu;
                  contradict n; auto
              | assumption
            ]
          ] ]
      ]
      | destruct (value_dec u1 (freeid_rename_value x y u1)); [
        rewrite <- e in *; clear e; destruct (value_dec u1 w) as [e0|n0]; [
          rewrite e0 in *; clear e0;
            assert (rho = TChannel s); [|subst]; [
              inversion Hfnot; subst; [
                |
                | solve [
                  destruct k; specialize (Htoken _ eq_refl); subst;
                    inversion H as [? ? ? Hwf Hin|]; subst; 
                      inversion Hwf as [? Hfv]; subst;
                        pose (Hfv _ _ Hin) as Hu2; inversion Hu2
                ]
              ];
              solve [
                apply partition_wf in Hpart; inversion Hpart as [a1 Hfv Heqtypes Hdisjoint]; subst; inversion H; subst; eapply Heqtypes; 
                  [
                    simpl; apply CTXFacts.add_1; reflexivity
                    | simpl; apply CTXFacts.add_2; assumption
                  ]
              ]
              |
            ];
            assert (|-st TChannel s); [
              inversion Hpart as [? ? ? _ _ Hdisjoint] ; subst;
                specialize (Hdisjoint w (TChannel s));
                  destruct Hdisjoint as [Hu|Hu]; [|destruct Hu as [Hu|Hu]]; [| | assumption]; [
                    inversion H; contradict Hu; auto
                    | contradict Hu; simpl; 
                      inversion Hfnot; subst; 
                        (try solve [simpl; apply CTXFacts.add_1; reflexivity]); 
                        destruct k; specialize (Htoken _ eq_refl); subst; discriminate Htoken
                  ]
              |
            ];
            left; tauto
          | right; left; split; [
            reflexivity
            | split; [
              auto
              | destruct (value_dec u1 (ValVariable (Var (Free x)))); [ 
                subst; assert (~ In y (free_ids_value (ValVariable (Var (Free x))))) as Hnotinyx; [simpl; tauto | ];
                  pose (SO3_value_var_determines_subst_improved _ _ _ _ _ Hso3v Hneqxy Hnotinyx Hnotinyv eq_refl) as Hu;
                    contradict n0; auto
                | assumption
              ]
            ]
          ]
        ]
        | pose (freeid_rename_value_cases_contra2 _ _ _ n) as Hinxu;
          inversion H as [? ? ? Hwf Hin|]; subst; inversion Hwf as [? Hfv ? Hdisjoint]; subst;
            assert (u1 = ValVariable (Var (Free x))) as Heq; [
              pose (Hfv _ _ Hin) as Hfvu; inversion Hfvu; subst; simpl in Hinxu; (destruct Hinxu as [Heq|Hinxu]; [|destruct Hinxu]); subst;
                specialize (Hdisjoint x); (destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [|destruct Hdisjoint as [Hdisjointa Hdisjointb]]);
                  (try solve [specialize (Hdisjoint _ HinxG); destruct Hdisjoint]);
                  (try solve [specialize (Hdisjointa _ Hin); destruct Hdisjointa]);
                  (try solve [specialize (Hdisjointb _ Hin); destruct Hdisjointb]);
                  reflexivity
              | subst; simpl in Hso3v; destruct (string_dec x x) as [e0|n0]; [|contradict n0; auto]; contradict Hso3v; apply SO3_value_is_not_rename; auto
            ]
      ]
      | solve [ tauto ]
    ] 
    | 
      destruct Hsubstaffectschannel; subst;
        assert (rho = TChannel s); [ 
          inversion H as [a b c Hwf HinxGs|]; subst; inversion Hwf as [? ? Heqtypes]; subst; apply (Heqtypes _ _ _ HinxG HinxGs) 
          | subst
        ]; 
        solve [tauto]
  ].

Qed.


(* ============================================================================= *)

Lemma SO3_value_unknown_varx_contra : 
  forall x y w v1 v2,
    SO3_value x y w v1 v2
    ->
    x <> y
    ->
    ~ In x (free_ids_value w)
    ->
    v2 <> ValVariable (Var (Free x)).
Proof.
  intros x y w v1 v2 Hso3v; induction Hso3v; intros Hneqxy Hnotinxw.
  destruct u as [| |var]; simpl; try discriminate.
  destruct var as [i]; simpl; try discriminate.
  destruct i as [f|b]; simpl; try discriminate.
  destruct (value_dec (ValVariable (Var (Free f))) (ValVariable (Var (Free y)))); [simpl; try discriminate | ].
  contradict Hnotinxw; subst; simpl; auto.
  contradict H; injection H; intros; subst; simpl; auto.
  destruct (eq_nat_decide b n).
  destruct (value_dec (ValVariable (Var (Free y))) (ValVariable (Var (Free y)))).
  contradict Hnotinxw; subst; simpl; auto.
  contradict Hneqxy; injection Hneqxy; intros; subst; reflexivity.
  destruct (le_lt_dec b n); discriminate.
  assert (u2 <> ValVariable (Var (Free x))); auto.
  contradict H2.
  assert (In (ValVariable (Var (Free x)))  (free_values_value (open_value i n u2))) as Hu; [
    rewrite H2; simpl; left; reflexivity
    | apply free_values_open_value1 in Hu; simpl in Hu; 
      destruct Hu as [Hu|Hu]; [ destruct Hu as [Hu|Hu]; [subst; contradict H1; reflexivity | destruct Hu ] | ];
        apply free_values_value_1  in Hu; assumption
  ].
Qed.

(* ============================================================================= *)

Lemma ctx_add_change_type : 
  forall w s m t G,
    (s -- m --> t)
    ->
    CTX.add (w, (TChannel s)) G |-part G (+) CTX.add (w, (TChannel s)) CTX.empty
    ->
    CTX.add (w, (TChannel t)) G |-part G (+) CTX.add (w, (TChannel t)) CTX.empty.
Proof.
  intros w s m t G Htrans Hpart.
  inversion Hpart; subst.
  destruct (CTXProperties.In_dec (w, TChannel s) G) as [i|n].
  assert ( |-st TChannel s ) as Hstateless; [
    specialize (H1 w (TChannel s)); destruct H1 as [H1|H1]; [|destruct H1 as [H1|H1]]; auto; [
      contradict H1; assumption
      | contradict H1; apply CTXFacts.add_1; reflexivity
    ]
    |
  ].
  assert (s = t); [
    inversion Hstateless; subst; eapply H3; eauto
    | subst; assumption
  ].
  constructor.
  apply CTXProperties.subset_antisym; [
    apply CTXProperties.subset_add_3; [apply CTXFacts.union_3; apply CTXFacts.add_1; reflexivity|]; 
      apply CTXProperties.union_subset_1
    |
  ].
  apply CTXProperties.union_subset_3; [
    apply CTXProperties.subset_add_2; reflexivity
    | apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity
      | apply CTXProperties.subset_empty
    ]
  ].
  
  inversion H0; subst.
  constructor.
  intros u rho Hin.
  rewrite CTXFacts.add_iff in Hin; destruct Hin as [Hin|Hin]; [
    injection Hin; intros; subst; apply (H2 _ (TChannel s)); apply CTXFacts.add_1; reflexivity
    | apply (H2 _ rho); apply CTXFacts.add_2; assumption
  ].
  intros u rho sigma Hin1 Hin2.
  rewrite CTXFacts.add_iff in *.
  (destruct Hin1 as [Hin1|Hin1]; [injection Hin1; intros; subst; clear Hin1 | ]);
  (destruct Hin2 as [Hin2|Hin2]; [injection Hin2; intros; subst; clear Hin2 | ]);
  auto.
  contradict n; assert (sigma = TChannel s); [
    apply (H3 u sigma (TChannel s)); [
      apply CTXFacts.add_2; assumption
      | apply CTXFacts.add_1; reflexivity
    ]
    | subst; assumption
  ].
  contradict n; assert (TChannel s = rho); [
    apply (H3 u (TChannel s) rho); [
      apply CTXFacts.add_1; reflexivity
      | apply CTXFacts.add_2; assumption
    ]
    | subst; assumption
  ].
  apply (H3 u); apply CTXFacts.add_2; assumption.
  intros x; specialize (H4 x); destruct H4 as [H4|H4]; [left | right; split; [destruct H4 as [H4 _] | destruct H4 as [_ H4]]];
    (intros rho; 
      match goal with 
        | [ |- ~ (CTX.In ?X _ ) ] => destruct (CTX.E.eq_dec X (w, TChannel t)) as [e1|n1]
      end;
      [
        injection e1; intros; subst; clear e1; specialize (H4 (TChannel s)); contradict H4; apply CTXFacts.add_1; reflexivity
        | specialize (H4 rho); contradict H4; rewrite CTXFacts.add_iff in H4; destruct H4 as [H4|H4]; [
          contradict n1; symmetry; assumption
          | apply CTXFacts.add_2; assumption
        ]
      ]).


  assert (~ CTX.In (w, TChannel t) G).
  inversion H0; subst.
  intros Hin.
  assert (TChannel s = TChannel t) as Heq; [
    apply (H3 w); [apply CTXFacts.add_1; reflexivity | apply CTXFacts.add_2; assumption]
    | injection Heq; intros; subst; clear Heq
  ].
  contradict Hin; assumption.

  intros u rho.
  destruct (CTX.E.eq_dec (u, rho) (w, TChannel t)) as [i1|n1].
  injection i1; intros; subst; clear i1; left; assumption.
  specialize (H1 u rho).
  destruct H1 as [H1|H1]; [left; assumption| destruct H1 as [H1|H1]; [ | right; right; assumption ]].
  right; left.
  rewrite CTXFacts.add_iff; rewrite CTXFacts.empty_iff.
  contradict n1; destruct n1 as [n1|n1]; [symmetry; assumption|destruct n1].
Qed.
  
Lemma ctx_add_value_change_type : 
  forall w s m t G,
    free_name_or_token w
    ->
    (s -- m --> t)
    ->
    ctx_add_value w (TChannel s) G |-part G (+) ctx_add_value w (TChannel s) CTX.empty
    ->
    ctx_add_value w (TChannel t) G |-part G (+) ctx_add_value w (TChannel t) CTX.empty.
Proof.
  intros w s m t G Hfnot Htrans Hpart.
  inversion Hfnot; subst; simpl in *; (try apply Hpart); apply ctx_add_change_type with (1:=Htrans) in Hpart; apply Hpart.
Qed.

(* ============================================================================= *)

Lemma subst_r_input_new : 
  forall G u P s L x rho1 y Q1 w,
    G |-v u : TChannel s
    ->
    SO3 x y w (u ? ; P) Q1
    ->
    x <> y
    ->
    ~ In x (free_ids_value w)
    ->
    ~ In y (free_ids_proc (u ? ; P))
    ->
    ~ In y (free_ids_value w)
    ->
    CTX.In (ValVariable (Var (Free x)), rho1) G
    ->
    (forall k : string, w = Token k -> rho1 = TSingleton (Token k))
    ->
    (ctx_add_value w rho1 G |-part G (+) ctx_add_value w rho1 CTX.empty)
    ->
    (G |-p u ? ; P)
    ->
    (forall (G' : CTX.t) (rho : type) (t : session) (x : free_id),
       ~ In x L ->
       (s -- MInp rho --> t) ->
       G' = CTX.add (ValVariable (Var (Free x)), rho) (ctx_replace u (TChannel s) (TChannel t) G) ->
       forall (x0 : free_id) (rho0 : type) (y : free_id) (Q : proc) (v : value),
         SO3 x0 y v (open_proc x 0 P) Q ->
         x0 <> y ->
         ~ In x0 (free_ids_value v) ->
         ~ In y (free_ids_proc (open_proc x 0 P)) ->
         ~ In y (free_ids_value v) ->
         CTX.In (ValVariable (Var (Free x0)), rho0) G' ->
         (forall k : string, v = Token k -> rho0 = TSingleton (Token k)) ->
         (ctx_add_value v rho0 G' |-part G' (+) ctx_add_value v rho0 CTX.empty) ->
         ctx_add_value v rho0 G' |-p Q)
    ->
    ctx_add_value w rho1 G |-p Q1.
Proof.
  intros G u P s L x rho1 y Q1 w H Hso3 Hneqxy Hnotinxw HnotinyP Hnotinyv HinxG Htoken Hpart HtypP H2.

  assert (ctx_add_value w rho1 G |-wf) as HwfaddvG; [eapply partition_wf; eauto|].

  assert (free_values_in_context G P) as HfvicP; [inversion HtypP; subst; auto|].

  pose (SO3_inp_decompose _ _ _ _ _ Hso3 _ _ eq_refl) as e; destruct e as [u2 e]; destruct e as [Q2 e]; subst.

  assert (SO3_value x y w u u2) as Hso3v; [eapply SO3_value_input; eauto|].

  assert (free_name_or_token w) as Hfnot; [apply (SO3_value_free_name_or_token _ _ _ _ _ Hso3v) |].

  assert (SO3 x y w P Q2) as Hso3a; [apply SO3_input in Hso3; auto|].

  assert (~ In y (free_ids_value u)) as Hnotinyu; [contradict HnotinyP; simpl; intuition|].

  assert (free_values_in_context (ctx_add_value w rho1 G) (u2 ? ; Q2)) as Hfvic; [
    apply SO3_free_values_in_context1 with (1:=HtypP) (2:=Hso3); auto; [
      intros w1 Hinw; simpl in Hinw; rewrite in_app_iff in Hinw; destruct Hinw as [Hinw|Hinw]; [
        apply free_values_value_1 in Hinw; subst; inversion H; subst; eexists; eauto
        | apply HfvicP in Hinw; auto
      ]
    ]
    | 
  ].

  apply TypPrefixInput with (s:=s) (L:=free_ids_value w ++ free_ids_proc P ++ free_ids_proc Q2 ++ L ++ free_ids_context G ++ (x::y::nil)); [
    apply subst_r_value_alt with (x:=x) (y:=y) (u1:=u); auto; contradict HnotinyP; simpl; intuition
    | intros w1 Hinw; specialize (Hfvic w1);
      assert (In w1 (free_values_proc (u2 ? ; Q2))) as Hinw1'; [|specialize (Hfvic Hinw1')]; [
        simpl; rewrite in_app_iff; right; auto
        | destruct Hfvic as [sigma Hin]; exists sigma; auto
      ]        
    |
  ].

  destruct (SO3_value_cases_input _ _ _ _ _ _ _ _ _ _ H Hso3 Hneqxy HnotinyP Hnotinyv HinxG Htoken Hpart HtypP) as [Hu|Hu];
    [ destruct Hu as [Heq1 Heq2]; destruct Heq2 as [Heq2 Heq3]; destruct Heq3 as [Heq3 Hstateless]; subst
      | destruct Hu as [Hu|Hu]; [
        destruct Hu as [Heq1 Hnequ2w]; destruct Hnequ2w as [Hnequ2w Hnequ2x]; subst
        | destruct Hu as [Heq1 Heq2]; destruct Heq2 as [Heq2 Heq3]; subst
      ]
    ];
    (intros G' rho t x0 Hnotin Htrans Heq; subst);
    (assert (~ In x0 L) as Hnotinx0L; [contradict Hnotin; (repeat rewrite in_app_iff); intuition|]);
    (assert (x0 <> x) as Hneqx0x; [contradict Hnotin; (repeat rewrite in_app_iff); subst; (do 5 right); intuition | ]);
    (assert (x0 <> y) as Hneqx0y; [contradict Hnotin; (repeat rewrite in_app_iff); subst; (do 5 right); intuition | ]);
    (assert (w <> ValVariable (Var (Free x0))) as Hneqwx0; [contradict Hnotin; (repeat rewrite in_app_iff); left; subst; simpl; tauto|]);
    [ Case "(u1 = u2 /\ u2 = w /\ rho = TChannel s /\ |-st TChannel s)"%string 
      | Case "(u1 = u2 /\ u2 <> w /\ u2 <> ValVariable (Var (Free x)))"%string
      | Case "(u1 = ValVariable (Var (Free x)) /\ u2 = w /\ rho = TChannel s)"%string
    ];
    (
      (eapply ctx_equal_preserves_typed; [
        eapply H2 with (x0:=x) (y:=y); [apply Hnotinx0L|apply Htrans|reflexivity| | | | | | | |]; auto; clear H2; [
          apply SO3Step; try solve [contradict Hnotin; (repeat rewrite in_app_iff); right; tauto]; apply SO3_input in Hso3; apply Hso3
          |
            assumption
          |
            intros Hin; apply free_ids_open_proc in Hin; destruct Hin as [Heq|Hin]; [subst|]; [
              contradict Hnotin; (repeat rewrite in_app_iff); right; right; right; right; right; intuition
              | contradict HnotinyP; simpl; (repeat rewrite in_app_iff); right; assumption
            ]
          |
            assumption
          |
          |
            apply Htoken
          |
        ]
        |
      ])
      ||
        (eapply ctx_equal_preserves_typed; [
          apply typed_change_type with (v:=ValVariable (Var (Free x))) (rho:=TChannel t) (sigma:=TChannel s); [
            eapply H2 with (x0:=x0) (x1:=x) (y:=y) (rho0:=TChannel t); [apply Hnotinx0L|apply Htrans| | | | | | | | | ]; auto; [
              apply SO3Step; try solve [contradict Hnotin; (repeat rewrite in_app_iff); right; tauto]; apply SO3_input in Hso3; apply Hso3
          |
            assumption
              | 
                intros Hin; apply free_ids_open_proc in Hin; destruct Hin as [Heq|Hin]; [subst|]; [
                  contradict Hnotin; (repeat rewrite in_app_iff); right; right; right; right; right; intuition
                  | contradict HnotinyP; simpl; (repeat rewrite in_app_iff); right; assumption
                ]
              | 
                assumption
              |
              |
                intros k Hin; specialize (Htoken k Hin); discriminate Htoken
              |
            ]
            |
            |
          ]   
          |
        ])
    ).


  (* (u1 = u2 /\ u2 = w /\ rho = TChannel s /\ |-st TChannel s) *)
  SCase "CTX.In (x,TChannel s) (add / replace / G)"%string.
  inversion Hfnot; subst; unfold ctx_replace; simpl;
    (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)); 
    (right; right; split; [assumption|discriminate]).

  SCase "partitioning"%string.
  inversion H as [? ? ? HwfG HinvG|]; subst.
  assert (s = t); [ inversion Hstateless as [? Heqst|]; subst; eapply Heqst; eauto | subst ].
  apply ctx_equal_part_1 with (G1:=(CTX.add (ValVariable (Var (Free x0)), rho) (ctx_replace w (TChannel t) (TChannel t) G))); auto.
  assert (free_value (ValVariable (Var (Free x0)))) as Hfv; [ constructor | ].
  assert (fresh_for_ctx (ValVariable (Var (Free x0))) (ctx_replace w (TChannel t) (TChannel t) G)) as Hffc; [
    constructor; [
      auto
      | intros v sigma; destruct (CTXProperties.In_dec (v, sigma) (ctx_replace w (TChannel t) (TChannel t) G)) as [i|n]; [ right | left; assumption ];
        unfold ctx_replace in i; (repeat rewrite CTXFacts.add_iff in i || rewrite CTXFacts.remove_iff in i);
          destruct i as [i|i]; [
            injection i; intros; subst; clear i; 
                inversion Hfnot as [i|i|i]; subst; simpl; [| |discriminate];
                  contradict Hneqx0x; injection Hneqx0x; intros; subst; contradict Hnotin; rewrite in_app_iff; left; simpl; left; reflexivity
            | destruct i as [i1 i2]; 
              simpl; 
                assert (~ In x0 (free_ids_context G)) as Hnotinx0G; [
                  contradict Hnotin; (repeat rewrite in_app_iff); right; right; right; right; left; assumption
                  |
                ]; 
                contradict Hnotinx0G; 
                eapply free_ids_context_vs_context; eauto
          ]
    ]
    |
  ].
  apply ctx_add_preserves_partition_left; auto.
  apply ctx_replace_preserves_partition_left; auto.
  apply ctx_equal_part_1 with (G1:=ctx_add_value w (TChannel t) G); auto.
  inversion Hfnot; simpl; try reflexivity; subst; 
    (intros a; destruct a; split; simpl; repeat rewrite CTXFacts.add_iff in *; intros Hin; [
      destruct Hin as [Hin|Hin]; [injection Hin; intros; subst|]; auto
      | right; auto
    ]
    ).
  symmetry; inversion Hfnot; subst; simpl; try reflexivity; 
    (eapply CTX_eq_trans; [
    apply CTXProperties.add_equal; unfold ctx_replace; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff); tauto
    | reflexivity
  ]).

  SCase "CTX.eq"%string.
  assert (s = t); [ inversion Hstateless as [? Heqst|]; subst; eapply Heqst; eauto | subst ];
    inversion Hfnot; subst; simpl; unfold ctx_replace;
      intros a; destruct a; (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff));
        tauto.

  (* (u1 = u2 /\ u2 <> w /\ u2 <> Var (Free x)) *)
  SCase "CTX.In (x,TChannel s) (add / replace / G)"%string.
  inversion Hfnot; subst; unfold ctx_replace; simpl;
    (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff));
    (right; right; split; [assumption | contradict Hnequ2x; injection Hnequ2x; intros; subst; reflexivity]).

  SCase "partitioning"%string.
  assert (
    CTX.eq
    (ctx_add_value w rho1 (CTX.add (ValVariable (Var (Free x0)), rho) (ctx_replace u2 (TChannel s) (TChannel t) G)))
    (CTX.add (ValVariable (Var (Free x0)), rho) (ctx_replace u2 (TChannel s) (TChannel t) (ctx_add_value w rho1 (G))))
  ) as Heqctx; [
    SSCase "here"%string
    |
  ].
  apply CTXProperties.subset_antisym.
  inversion Hfnot; subst; simpl; try reflexivity; 
    (apply CTXProperties.subset_add_3; [
      apply CTXFacts.add_2; apply CTXFacts.add_2; 
        apply CTXFacts.remove_2; [contradict Hnequ2w; injection Hnequ2w; intros; subst; reflexivity|];
          apply CTXFacts.add_1; reflexivity
      | apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity | ];
        apply CTXProperties.subset_add_2;
          apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity | ];
            apply CTXProperties.subset_add_2; 
              intros a; destruct a; intros Hin; rewrite CTXFacts.remove_iff in Hin; destruct Hin as [Hin1 Hin2];
                apply CTXFacts.remove_2; [assumption|];
                  apply CTXFacts.add_2; assumption
    ]).
  inversion Hfnot; subst; simpl; try reflexivity;
    (apply CTXProperties.subset_add_3; [apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity | ]; 
      apply CTXProperties.subset_add_3; [apply CTXFacts.add_2; apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity | ];
        intros a; destruct a; intros Hin; rewrite CTXFacts.remove_iff in Hin; rewrite CTXFacts.add_iff in Hin; 
          destruct Hin as [Hin1 Hin2]; destruct Hin1 as [Hin1|Hin1]; [
            injection Hin1; intros; subst; clear Hin1; apply CTXFacts.add_1; reflexivity
            | apply CTXFacts.add_2; apply CTXFacts.add_2; apply CTXFacts.add_2; apply CTXFacts.remove_2; assumption; apply CTXFacts.add_1; reflexivity
          ]).
  eapply ctx_equal_part_1; [|rewrite Heqctx; reflexivity].
  apply ctx_add_preserves_partition_left; [
    constructor
    |
    | apply ctx_replace_preserves_partition_left; [
      inversion H; auto
      | inversion Hfnot; subst; simpl; (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.empty_iff)); intros Hin; 
        (try solve [destruct Hin]);
        (destruct Hin as [Hin|Hin]; [
          injection Hin; intros; subst; clear Hin; contradict Hnequ2w; reflexivity
          | destruct Hin
        ])
      | apply Hpart
    ]
  ].
  apply fresh_for_ctx_replace; [
    assumption
    | constructor
    |
    | inversion H as [a b c _ Hinu2G|]; subst; inversion Hfnot; subst; simpl; (assumption || (apply CTXFacts.add_2; assumption))
  ].
  constructor; [
    constructor
    |
  ].
  intros v sigma.
  destruct (CTXProperties.In_dec (v, sigma) (ctx_add_value w rho1 G)) as [i|n]; [
    right; 
      inversion Hfnot; subst; simpl in *; (repeat rewrite CTXFacts.add_iff in * );
        try (destruct i as [i|i]; [
          solve [injection i; intros; subst; simpl; contradict Hnotin; injection Hnotin; intros; subst; left; reflexivity]
          | (contradict Hnotin; (repeat rewrite in_app_iff); right; right; right; right; left; apply free_ids_context_vs_context with (1:=Hnotin) (2:=i))
        ]);
        (contradict Hnotin; (repeat rewrite in_app_iff); right; right; right; left; apply free_ids_context_vs_context with (1:=Hnotin) (2:=i))
    | left; apply n
  ].

  SCase "CTX.eq"%string.
  inversion Hfnot; subst; simpl; unfold ctx_replace;
    intros a; destruct a; (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)); try reflexivity;
      split; intros Hin;
        repeat (match goal with 
                  | [ H : _ \/ _ |- _ ] => destruct H
                  | [ H : _ /\ _ |- _ ] => destruct H
                  | [ H : _ = _ |- _ ] => solve [discriminate H]
                  | [ H : _ = _ |- _ ] => injection H; intros; subst; clear H
                end); 
          (try solve [left; reflexivity]);
          (try solve [right; left; reflexivity]);
          (try solve [right; right; left; reflexivity]);
          (try solve [right; right; split; [left; reflexivity | contradict Hnequ2w; injection Hnequ2w; intros; subst; reflexivity]]);
          (try solve [right; right; split; [right | ]; assumption]);
          (try solve [right; right; right; split; assumption]).

  (* (u1 = ValVariable (Var (Free x)) /\ u2 = w /\ rho = TChannel s) *)
  SCase "CTX.In (x,TChannel t) (add / replace / G)"%string.
  unfold ctx_replace; (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff));
    right; left; reflexivity.

  SCase "partitioning"%string.
  assert (
    CTX.eq
    (ctx_add_value w (TChannel t) (CTX.add (ValVariable (Var (Free x0)), rho) (ctx_replace (ValVariable (Var (Free x))) (TChannel s) (TChannel t) G)))
    (CTX.add (ValVariable (Var (Free x0)), rho) (ctx_replace (ValVariable (Var (Free x))) (TChannel s) (TChannel t) (ctx_add_value w (TChannel t) (G))))
  ) as Heqctx; [
    SSCase "here"%string
    |
  ].
  apply CTXProperties.subset_antisym.
  inversion Hfnot; subst; simpl; try reflexivity; 
    (apply CTXProperties.subset_add_3; [
      apply CTXFacts.add_2; apply CTXFacts.add_2;
        apply CTXFacts.remove_2; [discriminate|];
          apply CTXFacts.add_1; reflexivity
      | apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity | ];
        apply CTXProperties.subset_add_2;
          apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity | ];
            apply CTXProperties.subset_add_2; 
              intros a; destruct a; intros Hin; rewrite CTXFacts.remove_iff in Hin; destruct Hin as [Hin1 Hin2];
                apply CTXFacts.remove_2; [assumption|];
                  apply CTXFacts.add_2; assumption
    ]).
  inversion Hfnot; subst; simpl; try reflexivity;
    (apply CTXProperties.subset_add_3; [apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity | ]; 
      apply CTXProperties.subset_add_3; [apply CTXFacts.add_2; apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity | ];
        intros a; destruct a; intros Hin; rewrite CTXFacts.remove_iff in Hin; rewrite CTXFacts.add_iff in Hin; 
          destruct Hin as [Hin1 Hin2]; destruct Hin1 as [Hin1|Hin1]; [
            injection Hin1; intros; subst; clear Hin1; apply CTXFacts.add_1; reflexivity
            | apply CTXFacts.add_2; apply CTXFacts.add_2; apply CTXFacts.add_2; apply CTXFacts.remove_2; assumption; apply CTXFacts.add_1; reflexivity
          ]).
  eapply ctx_equal_part_1; [|rewrite Heqctx; reflexivity].
  apply ctx_add_value_change_type with (2:=Htrans) in Hpart; auto.
  apply ctx_add_preserves_partition_left; [
    constructor
    |
    | apply ctx_replace_preserves_partition_left; [
      inversion H; auto
      | inversion Hfnot; subst; simpl; (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.empty_iff)); intros Hin; 
        (try solve [destruct Hin]);
        (destruct Hin as [Hin|Hin]; [
          discriminate
          | destruct Hin
        ])
      | assumption
    ]
  ].
  apply fresh_for_ctx_replace; [
    apply partition_wf in Hpart; assumption
    | constructor
    |
    | inversion H as [a b c _ Hinu2G|]; subst; inversion Hfnot; subst; simpl; (assumption || (apply CTXFacts.add_2; assumption))
  ].
  constructor; [
    constructor
    |
  ].
  intros v sigma.
  destruct (CTXProperties.In_dec (v, sigma) (ctx_add_value w (TChannel t) G)) as [i|n]; [
    right; 
      inversion Hfnot; subst; simpl in *; (repeat rewrite CTXFacts.add_iff in * );
        try (destruct i as [i|i]; [
          solve [injection i; intros; subst; simpl; contradict Hnotin; injection Hnotin; intros; subst; left; reflexivity]
          | (contradict Hnotin; (repeat rewrite in_app_iff); right; right; right; right; left; apply free_ids_context_vs_context with (1:=Hnotin) (2:=i))
        ]);
        (contradict Hnotin; (repeat rewrite in_app_iff); right; right; right; left; apply free_ids_context_vs_context with (1:=Hnotin) (2:=i))
    | left; apply n
  ].

  SCase "CTX.In (x,TChannel t) (add / replace / G)"%string.
  inversion Hfnot; subst; unfold ctx_replace; simpl;
    (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff));
    (try solve [right; right; left; reflexivity]);
    right; left; reflexivity.

  SCase "free_values_proc / open_proc"%string.
  intros Hin; apply free_values_open_proc1 in Hin; destruct Hin as [Hin|Hin]; [
    simpl in Hin; destruct Hin as [Hin|Hin]; [ contradict Hneqx0x; symmetry; assumption | destruct Hin ]
      | pose (SO3_free_values_in_context1_aux _ _ _ _ _ _ Hin Hso3a) as Hu; 
        destruct Hu as [v1 Hu]; destruct Hu as [Hin1 Hso3v1]; 
          apply SO3_value_unknown_varx_contra in Hso3v1; auto
  ].

  SCase "CTX.eq"%string.
  assert (forall rho, CTX.In (w, rho) G -> rho = TChannel t) as Heqrhot; [
    intros rho0 Hin;
      assert (rho0 = TChannel s); [
        apply partition_wf in Hpart; inversion Hpart as [? ? Heqtypes]; subst;
          apply (Heqtypes w); [
            apply ctx_add_value1; auto
            | eapply ctx_add_value2; eauto
          ]
        | subst
      ];
      assert (|-st TChannel s) as Hstateless; [
        inversion Hpart as [? ? ? ? ? Hdisjoint]; subst;
          specialize (Hdisjoint w (TChannel s)); destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [|destruct Hdisjoint as [Hdisjoint|Hdisjoint]]; try auto; [
            contradict Hdisjoint; auto
            | contradict Hdisjoint; eapply ctx_add_value2; eauto
          ]
        |
      ];
      inversion Hstateless as [? Heqtypes |]; subst; erewrite Heqtypes; eauto
      |
  ].

  assert (forall rho, CTX.In (ValVariable (Var (Free x)), rho) G -> rho = TChannel s) as Heqrhos; [
    intros sigma Hin; pose (typed_ctx_wf _ _ HtypP) as Hu; inversion Hu as [? Hfv Heqtypes Hdisjoint]; subst; apply (Heqtypes _ _ _ Hin HinxG)
    |
  ].

  inversion Hfnot; subst; simpl; unfold ctx_replace;
    intros a; destruct a; (repeat (rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff)) ; 
      (split; [SSCase "fwd"%string | SSCase "bwd"%string ]); intros Hin;
        repeat (match goal with 
                  | [ H : _ \/ _ |- _ ] => destruct H
                  | [ H : _ /\ _ |- _ ] => destruct H
                  | [ H : _ = _ |- _ ] => solve [discriminate H]
                  | [ H : _ = _ |- _ ] => injection H; intros; subst; clear H
                end);
        (try solve [right; right; split; [right; assumption | discriminate]]);
        (try solve [right; left; reflexivity]);
        (try solve [left; reflexivity]);
        (try solve [contradict H1; reflexivity]); 
        (try solve [
          destruct (value_dec (ValName (Nm (Free i))) v) as [e|n]; [
            subst; rewrite <- (Heqrhot t0); auto
            | right; right; split; [ right; assumption | contradict n; injection n; intros; subst; reflexivity ]
          ]]);
        (try solve [
          destruct (value_dec (ValName (CoNm (Free i))) v) as [e|n]; [
            subst; rewrite <- (Heqrhot t0); auto
            | right; right; split; [ right; assumption | contradict n; injection n; intros; subst; reflexivity ]
          ]]);        (try solve [right; split; [right; left; reflexivity | contradict Hneqx0x; injection Hneqx0x; intros; subst; reflexivity]]);
        (try solve [right; split; [left; reflexivity | discriminate]]);
        (try solve [
          destruct (value_dec (ValVariable (Var (Free x))) v) as [e|n]; [
            subst; rewrite (Heqrhos _ H0); left; reflexivity
            | right; split; [right; right; right; split; [assumption | ] | ]; contradict n; injection n; intros; subst; reflexivity
          ]
        ]);
        (try solve [right; right; split; [assumption | discriminate]]);
        (try solve [
          right; right; split; [
            assumption
            | destruct (value_dec k v) as [e|n]; [
              subst; pose (typed_ctx_wf _ _ HtypP) as Hu; inversion Hu as [? Hfv Heqtypes Hdisjoint]; pose (Hfv _ _ H0) as Hu2; inversion Hu2
              | intros Heq; injection Heq; intros; subst; contradict n; reflexivity
            ]
          ]
        ]);
        (try solve [right; split; [left; reflexivity | intros Heq; injection Heq; intros; subst; contradict Hneqx0x; reflexivity ]]);
        (try solve [destruct k; pose (Htoken _ eq_refl) as Hu; inversion Hu]).
Qed.


(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

Lemma SO3_value_cases_output1 : 
  forall rho sigma s t G x y w u1 v1 P1 u2 v2 P2,
    G |-v u1 : TChannel s
    ->
    G |-v v1 : sigma
    ->
    transition s (MOut sigma) t
    ->
    SO3 x y w (u1 ! v1 ; P1) (u2 ! v2 ; P2)
    ->
    x <> y
    ->
    ~ In y (free_ids_proc (u1 ! v1 ; P1))
    ->
    ~ In y (free_ids_value w)
    ->
    CTX.In (ValVariable (Var (Free x)), rho) G
    ->
    (forall k : string, w = Token k -> rho = TSingleton (Token k))
    ->
    (ctx_add_value w rho G |-part G (+) ctx_add_value w rho CTX.empty)
    ->
    (G |-p u1 ! v1 ; P1)
    ->
    (u1 = u2 /\ u2 = w /\ rho = TChannel s /\ |-st TChannel s)
    \/ (u1 = u2 /\ u2 <> w /\ u1 <> ValVariable (Var (Free x)))
    \/ (u1 = ValVariable (Var (Free x)) /\ u2 = w /\ rho = TChannel s).
Proof.
  intros rho sigma s t G x y w u1 v1 P1 u2 v2 P2 H Hlookupv1 Htrans Hso3 Hneqxy HnotinyP Hnotinyv HinxG Htoken Hpart HtypP.

  assert (SO3_value x y w u1 u2) as Hso3v; [eapply SO3_value_output1; eauto|].

  assert (~ In y (free_ids_value u1)) as Hnotinyu; [contradict HnotinyP; simpl; intuition|].

  assert (free_name_or_token w) as Hfnot; [apply (SO3_value_free_name_or_token _ _ _ _ _ Hso3v) |].

  destruct (SO3_value_var_determines_subst_cases _ _ _ _ _ Hso3v Hneqxy Hnotinyu Hnotinyv) as [Hsubstleaveschannelalone | Hsubstaffectschannel]; [
    destruct (SO3_value_cases _ _ _ _ _ Hso3v) as [Hu|Hu] ; [ | destruct Hu as [Hu|Hu]; destruct Hu as [Hu1 Hu2]]; subst; [
      destruct (value_dec w u2) as [e|n]; [
        subst; 
          assert (rho = TChannel s); [|subst]; [
            inversion Hfnot; subst; [
              |
              | solve [
                destruct k; specialize (Htoken _ eq_refl); subst;
                  inversion H as [? ? ? Hwf Hin|]; subst; 
                    inversion Hwf as [? Hfv]; subst;
                      pose (Hfv _ _ Hin) as Hu2; inversion Hu2
              ]
            ];
            solve [
              apply partition_wf in Hpart; inversion Hpart as [a1 Hfv Heqtypes Hdisjoint]; subst; inversion H; subst; eapply Heqtypes; 
                [
                  simpl; apply CTXFacts.add_1; reflexivity
                  | simpl; apply CTXFacts.add_2; assumption
                ]
            ]
            |
          ];
          assert (|-st TChannel s); [
            inversion Hpart as [? ? ? _ _ Hdisjoint] ; subst;
              specialize (Hdisjoint u2 (TChannel s));
                destruct Hdisjoint as [Hu|Hu]; [|destruct Hu as [Hu|Hu]]; [| | assumption]; [
                  inversion H; contradict Hu; auto
                  | contradict Hu; simpl; 
                    inversion Hfnot; subst; 
                      (try solve [simpl; apply CTXFacts.add_1; reflexivity]); 
                      destruct k; specialize (Htoken _ eq_refl); subst; discriminate Htoken
                ]
            |
          ]; 
          left; tauto
        | right; left; split; [ 
          reflexivity
          | split; [
            intros Heq; contradict n; subst; reflexivity
            | destruct (value_dec u2 (ValVariable (Var (Free x)))); [ 
              subst; assert (~ In y (free_ids_value (ValVariable (Var (Free x))))) as Hnotinyx; [simpl; tauto | ];
                pose (SO3_value_var_determines_subst_improved _ _ _ _ _ Hso3v Hneqxy Hnotinyx Hnotinyv eq_refl) as Hu;
                  contradict n; auto
              | assumption
            ]
          ] ]
      ]
      | destruct (value_dec u1 (freeid_rename_value x y u1)); [
        rewrite <- e in *; clear e; destruct (value_dec u1 w) as [e0|n0]; [
          rewrite e0 in *; clear e0;
            assert (rho = TChannel s); [|subst]; [
              inversion Hfnot; subst; [
                |
                | solve [
                  destruct k; specialize (Htoken _ eq_refl); subst;
                    inversion H as [? ? ? Hwf Hin|]; subst; 
                      inversion Hwf as [? Hfv]; subst;
                        pose (Hfv _ _ Hin) as Hu2; inversion Hu2
                ]
              ];
              solve [
                apply partition_wf in Hpart; inversion Hpart as [a1 Hfv Heqtypes Hdisjoint]; subst; inversion H; subst; eapply Heqtypes; 
                  [
                    simpl; apply CTXFacts.add_1; reflexivity
                    | simpl; apply CTXFacts.add_2; assumption
                  ]
              ]
              |
            ];
            assert (|-st TChannel s); [
              inversion Hpart as [? ? ? _ _ Hdisjoint] ; subst;
                specialize (Hdisjoint w (TChannel s));
                  destruct Hdisjoint as [Hu|Hu]; [|destruct Hu as [Hu|Hu]]; [| | assumption]; [
                    inversion H; contradict Hu; auto
                    | contradict Hu; simpl; 
                      inversion Hfnot; subst; 
                        (try solve [simpl; apply CTXFacts.add_1; reflexivity]); 
                        destruct k; specialize (Htoken _ eq_refl); subst; discriminate Htoken
                  ]
              |
            ];
            left; tauto
          | right; left; split; [
            reflexivity
            | split; [
              auto
              | destruct (value_dec u1 (ValVariable (Var (Free x)))); [ 
                subst; assert (~ In y (free_ids_value (ValVariable (Var (Free x))))) as Hnotinyx; [simpl; tauto | ];
                  pose (SO3_value_var_determines_subst_improved _ _ _ _ _ Hso3v Hneqxy Hnotinyx Hnotinyv eq_refl) as Hu;
                    contradict n0; auto
                | assumption
              ]
            ]
          ]
        ]
        | pose (freeid_rename_value_cases_contra2 _ _ _ n) as Hinxu;
          inversion H as [? ? ? Hwf Hin|]; subst; inversion Hwf as [? Hfv ? Hdisjoint]; subst;
            assert (u1 = ValVariable (Var (Free x))) as Heq; [
              pose (Hfv _ _ Hin) as Hfvu; inversion Hfvu; subst; simpl in Hinxu; (destruct Hinxu as [Heq|Hinxu]; [|destruct Hinxu]); subst;
                specialize (Hdisjoint x); (destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [|destruct Hdisjoint as [Hdisjointa Hdisjointb]]);
                  (try solve [specialize (Hdisjoint _ HinxG); destruct Hdisjoint]);
                  (try solve [specialize (Hdisjointa _ Hin); destruct Hdisjointa]);
                  (try solve [specialize (Hdisjointb _ Hin); destruct Hdisjointb]);
                  reflexivity
              | subst; simpl in Hso3v; destruct (string_dec x x) as [e0|n0]; [|contradict n0; auto]; contradict Hso3v; apply SO3_value_is_not_rename; auto
            ]
      ]
      | solve [ tauto ]
    ] 
    | 
      destruct Hsubstaffectschannel; subst;
        assert (rho = TChannel s); [ 
          inversion H as [a b c Hwf HinxGs|]; subst; inversion Hwf as [? ? Heqtypes]; subst; apply (Heqtypes _ _ _ HinxG HinxGs) 
          | subst
        ]; 
        solve [tauto]
  ].
Qed.


(* ============================================================================= *)
(* ============================================================================= *)

Lemma SO3_value_cases_output2 : 
  forall rho sigma s t G x y w u1 v1 P1 u2 v2 P2,
    G |-v u1 : TChannel s
    ->
    G |-v v1 : sigma
    ->
    transition s (MOut sigma) t
    ->
    SO3 x y w (u1 ! v1 ; P1) (u2 ! v2 ; P2)
    ->
    x <> y
    ->
    ~ In y (free_ids_proc (u1 ! v1 ; P1))
    ->
    ~ In y (free_ids_value w)
    ->
    CTX.In (ValVariable (Var (Free x)), rho) G
    ->
    (forall k : string, w = Token k -> rho = TSingleton (Token k))
    ->
    (ctx_add_value w rho G |-part G (+) ctx_add_value w rho CTX.empty)
    ->
    (G |-p u1 ! v1 ; P1)
    ->
    (v1 = v2 /\ v2 = w /\ rho = sigma /\ |-st sigma)
    \/ (v1 = v2 /\ v2 <> w /\ v1 <> ValVariable (Var (Free x)))
    \/ (v1 = ValVariable (Var (Free x)) /\ v2 = w /\ rho = sigma).
Proof.
  intros rho sigma s t G x y w u1 v1 P1 u2 v2 P2 H Hlookupv1 Htrans Hso3 Hneqxy HnotinyP Hnotinyv HinxG Htoken Hpart HtypP.

  assert (SO3_value x y w v1 v2) as Hso3v; [eapply SO3_value_output2; eauto|].

  assert (~ In y (free_ids_value v1)) as Hnotinyu; [contradict HnotinyP; simpl; intuition|].

  assert (free_name_or_token w) as Hfnot; [apply (SO3_value_free_name_or_token _ _ _ _ _ Hso3v) |].

  destruct (SO3_value_var_determines_subst_cases _ _ _ _ _ Hso3v Hneqxy Hnotinyu Hnotinyv) as [Hsubstleaveschannelalone | Hsubstaffectschannel]; [
    | destruct Hsubstaffectschannel; subst;
      assert (rho = sigma); [ 
        inversion Hlookupv1 as [a b c Hwf HinxGs|]; subst; inversion Hwf as [? ? Heqtypes]; subst; apply (Heqtypes _ _ _ HinxG HinxGs) 
        | subst
      ]; 
      solve [tauto]
  ].

  destruct (SO3_value_cases _ _ _ _ _ Hso3v) as [Hu|Hu] ; [ | destruct Hu as [Hu|Hu]; destruct Hu as [Hu1 Hu2]]; subst. 
  
  destruct (value_dec w v2) as [e|n].
  subst;
  assert (rho = sigma); [
    inversion Hfnot; subst; [
      |
      | destruct k; specialize (Htoken _ eq_refl); subst; 
        inversion Hlookupv1 as [? ? ? Hwf Hin|]; subst; [ 
          inversion Hwf as [? Hfv]; pose (Hfv _ _ Hin) as Hu; inversion Hu
          | reflexivity
        ]
    ];
    (apply partition_wf in Hpart; inversion Hpart as [a1 Hfv Heqtypes Hdisjoint]; subst; inversion Hlookupv1; subst; eapply Heqtypes; [
      simpl; apply CTXFacts.add_1; reflexivity
      | simpl; apply CTXFacts.add_2; assumption
    ])
    | subst
  ].
  assert (|-st sigma); [
    inversion Hpart as [? ? ? _ _ Hdisjoint] ; subst;
      specialize (Hdisjoint v2 sigma); 
        destruct Hdisjoint as [Hu|Hu]; [|destruct Hu as [Hu|Hu]]; [| | assumption]; [
          inversion Hlookupv1; subst; [
            contradict Hu; assumption
            | constructor
          ]
          | inversion Hfnot; subst; [
            |
            | destruct k; specialize (Htoken _ eq_refl); subst; constructor 
          ]; 
          (contradict Hu; simpl; 
            inversion Hfnot; subst; 
              (try solve [simpl; apply CTXFacts.add_1; reflexivity]); 
              destruct k; specialize (Htoken _ eq_refl); subst)
        ]
    | left; tauto
  ].

  right; left; split; [
    reflexivity
    | split ; [
      auto
      | destruct (value_dec v2 (ValVariable (Var (Free x)))); [ 
        subst; assert (~ In y (free_ids_value (ValVariable (Var (Free x))))) as Hnotinyx; [simpl; tauto | ];
          pose (SO3_value_var_determines_subst_improved _ _ _ _ _ Hso3v Hneqxy Hnotinyx Hnotinyv eq_refl) as Hu;
            contradict n; auto
        | assumption
      ]
    ]
  ].


  destruct (value_dec v1 (freeid_rename_value x y v1)).
  rewrite <- e in *; clear e.

  destruct (value_dec v1 w) as [e0|n0].
  rewrite e0 in *; clear e0.
  assert (rho = sigma); [
    inversion Hfnot; subst; [
      |
      | destruct k; specialize (Htoken _ eq_refl); subst;
        inversion Hlookupv1 as [? ? ? Hwf Hin|]; subst; [
          inversion Hwf as [? Hfv]; subst;
            pose (Hfv _ _ Hin) as Hu2; inversion Hu2
          | reflexivity
        ]
    ];
    (apply partition_wf in Hpart; inversion Hpart as [a1 Hfv Heqtypes Hdisjoint]; subst; inversion H; subst; eapply Heqtypes; 
      [
        simpl; apply CTXFacts.add_1; reflexivity
        | simpl; apply CTXFacts.add_2; inversion Hlookupv1; subst; assumption
      ])
    | subst 
  ].
  assert (|-st sigma); [
    inversion Hpart as [? ? ? _ _ Hdisjoint] ; subst;
      specialize (Hdisjoint w (sigma));
        destruct Hdisjoint as [Hu|Hu]; [|destruct Hu as [Hu|Hu]]; [| | assumption]; [
          inversion Hlookupv1; subst; [
            contradict Hu; assumption
            | constructor
          ]
          | contradict Hu; simpl; 
            inversion Hfnot; subst; 
              (try solve [simpl; apply CTXFacts.add_1; reflexivity]); 
              inversion Hu1
        ]
    | subst; Case "b"%string
  ];
  left; tauto.

  right; left; split; [
    reflexivity
    | split; [
      auto
      | destruct (value_dec v1 (ValVariable (Var (Free x)))); [ 
        subst; assert (~ In y (free_ids_value (ValVariable (Var (Free x))))) as Hnotinyx; [simpl; tauto | ];
          pose (SO3_value_var_determines_subst_improved _ _ _ _ _ Hso3v Hneqxy Hnotinyx Hnotinyv eq_refl) as Hu;
            contradict n0; auto
        | assumption
      ]
    ]
  ].


  pose (freeid_rename_value_cases_contra2 _ _ _ n) as Hinxu;
    inversion Hlookupv1 as [? ? ? Hwf Hin|]; subst; [|simpl in n; intuition]; inversion Hwf as [? Hfv ? Hdisjoint]; subst;
      assert (v1 = ValVariable (Var (Free x))) as Heq; [
        pose (Hfv _ _ Hin) as Hfvu; inversion Hfvu; subst; simpl in Hinxu; (destruct Hinxu as [Heq|Hinxu]; [|destruct Hinxu]); subst;
          specialize (Hdisjoint x); (destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [|destruct Hdisjoint as [Hdisjointa Hdisjointb]]);
            (try solve [specialize (Hdisjoint _ HinxG); destruct Hdisjoint]);
            (try solve [specialize (Hdisjointa _ Hin); destruct Hdisjointa]);
            (try solve [specialize (Hdisjointb _ Hin); destruct Hdisjointb]);
            reflexivity
        | subst; simpl in Hso3v; destruct (string_dec x x) as [e0|n0]; [|contradict n0; auto]; contradict Hso3v; apply SO3_value_is_not_rename; auto
      ].

  right; right; split; [auto | split; [auto | ] ].

  inversion Hlookupv1 as [? ? ? Hwf Hin|]; subst.
  inversion Hwf as [? ? Heqtypes]; subst.
  apply (Heqtypes _ _ _ HinxG Hin).
Qed.

(* ============================================================================= *)

Lemma free_name_or_token_split : 
  forall v, free_name_or_token v -> (free_name v \/ exists k, v = ValToken k).
Proof.
  intros v Hfnot; inversion Hfnot; subst; [ | | right; eexists; reflexivity ]; left; constructor.
Qed.

(* ============================================================================= *)

Lemma ctx_replace_idem :
  forall v rho G,
    CTX.In (v, rho) G -> CTX.eq (ctx_replace v rho rho G) G.
Proof.
  intros v rho G Hin.
  intros a; destruct a; unfold ctx_replace; split; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff); intros Hin2.
  destruct Hin2.
  injection H; intros; subst; tauto.
  tauto.
  destruct (CTX.E.eq_dec (v, rho) (v0, t)) as [e|n].
  injection e; intros; subst.
  tauto.
  tauto.
Qed.

(* ============================================================================= *)

Lemma add_remove_idem : 
  forall v rho G,
    CTX.eq (CTX.add (v, rho) (CTX.remove (v, rho) G)) (CTX.add (v, rho) G).
Proof.
  intros v rho G.
  intros a; destruct a; unfold ctx_replace; split; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff); intros Hin2.
  tauto.
  destruct Hin2 as [Hin2 | Hin2]; [injection Hin2; intros; subst; clear Hin2 | ].
  left; reflexivity.
  destruct (CTX.E.eq_dec (v, rho) (v0, t)) as [e|n].
  injection e; intros; subst.
  tauto.
  tauto.
Qed.

(* ============================================================================= *)

Lemma add_value_comm : 
  forall u rho v sigma G,
    free_name_or_token u
    ->
    u <> v
    ->
    CTX.eq (ctx_add_value u rho (CTX.remove (v, sigma) G)) (CTX.remove (v, sigma) (ctx_add_value u rho G)).
Proof.
  intros u rho v sigma G Hfnot Hneq.
  inversion Hfnot; subst; simpl; intros a; destruct a; unfold ctx_replace; split; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff); intros Hin2; try solve [tauto];
    (destruct Hin2 as [Hin2|Hin2]; [
      injection Hin2; intros; subst; clear Hin2; split; [left; reflexivity | contradict Hneq; injection Hneq; intros; subst; reflexivity]
      |
    ]; tauto).
Qed.

(* ============================================================================= *)

Lemma free_ids_open_value_stronger :
  forall v i j n,
    In j (free_ids_value (open_value i n v))
    ->
    (j = i /\ (v = ValName (Nm (Bound n)) \/ v = ValName (CoNm (Bound n)) \/ v = ValVariable (Var (Bound n)))) \/ In j (free_ids_value v).
Proof.
  intros v i j n Hin.
  destruct v as [nm| |var]; simpl in *; [|destruct Hin|]; [
    destruct nm as [i1|i1]
    | destruct var as [i1]
  ]; simpl in *;
  (destruct i1 as [f|b]; simpl in *; [ 
    destruct Hin as [Hin|Hin]; [right; left; assumption | destruct Hin]
    | 
  ]);
  (destruct (eq_nat_decide b n); [
    simpl in *; destruct Hin as [Hin|Hin]; [
      apply eq_nat_eq in e; subst; tauto
      | destruct Hin
    ]
    |
  ]);
  destruct (le_lt_dec b n); simpl in Hin; destruct Hin.
Qed.

Lemma free_ids_proc_rename_aux : 
  forall P x y n,
    In x (free_ids_proc (open_proc x n P))
    ->
    ~ In x (free_ids_proc P)
    ->
    ~ In y (free_ids_proc P)
    ->
    In y (free_ids_proc (open_proc y n P)).
Proof.
  intros P; induction P; intros x y n HnotinopenxP HnotinxP HnotinyP; simpl in *; (repeat rewrite in_app_iff in * );
    (try destruct HnotinopenxP);
    (repeat (match goal with 
               | [ H : _ \/ _ |- _ ] => destruct H
               | [ H : In _ (free_ids_value (open_value _ _ _)) |- _ ] => apply free_ids_open_value_stronger in H
               | [ H : _ /\ _ |- _ ] => destruct H
               | [ H : False |- _ ] => destruct H
               | [ |- context[eq_nat_decide ?X ?Y] ] => destruct (eq_nat_decide X Y)
               | [ |- context[le_lt_dec ?X ?Y] ] => destruct (le_lt_dec X Y)
               | [ H : ~ eq_nat ?X ?X |- _ ] => solve [contradict n0; apply eq_eq_nat; reflexivity]
               | [ H : In _ (free_ids_value _) |- _ ] => solve [contradict HnotinxP; tauto]
               | [ |- _ ] => subst; simpl in *
             end));
    (try solve [left; left; reflexivity]); 
    (try solve [right; left; left; reflexivity]); 
    (try solve [apply IHP with (x:=x); auto]);
    (try solve [right; apply IHP with (x:=x); auto]);
    (try solve [right; right; apply IHP with (x:=x); auto]);
    (try solve [left; apply IHP1 with (x:=x); auto]);
    (try solve [right; apply IHP2 with (x:=x); auto]).
Qed. 

Lemma free_ids_proc_rename : 
  forall P x y n,
    ~ In x (free_ids_proc (open_proc x n P))
    ->
    ~ In x (free_ids_proc P)
    ->
    ~ In y (free_ids_proc P)
    ->
    ~ In y (free_ids_proc (open_proc y n P)).
Proof.
  intros P x y n HnotinopenxP HnotinxP HnotinyP.
  contradict HnotinopenxP.
  apply free_ids_proc_rename_aux with (x:=y); auto.
Qed.

Lemma subst_value_idem : 
  forall w x v,
    ~ In x (free_ids_value w)
    ->
    subst_value w (ValVariable (Var (Free x))) v = w.
Proof.
  intros w x v Hnotinxw.
  destruct w as [| |var]; simpl; try reflexivity.
  destruct var as [i]; simpl.
  destruct i as [f|b]; simpl; try reflexivity.
  destruct (value_dec (ValVariable (Var (Free f))) (ValVariable (Var (Free x)))) as [e|n]; [
    injection e; intros; subst; contradict Hnotinxw; simpl; tauto
    | reflexivity
  ].
Qed.

Lemma subst_proc_idem : 
  forall P x v,
    ~ In x (free_ids_proc P)
    ->
    subst_proc P (ValVariable (Var (Free x))) v = P.
Proof.
  intros P; induction P; intros x w HnotinxP; simpl in *; (repeat rewrite in_app_iff in * );
    (repeat rewrite subst_value_idem; try solve [tauto]);
    try solve [
      (rewrite IHP; tauto)
    || (rewrite IHP1; try solve [tauto]; rewrite IHP2; try solve [tauto])].
Qed.

Lemma open_value_inj2 : 
  forall v x y n,
    ~ In x (free_ids_value (open_value x n v))
    ->
    ~ In y (free_ids_value (open_value y n v))
    ->
    open_value x n v = open_value y n v.
Proof.
  intros v x y n Hnotinopenx Hnotinopeny.
  destruct v as [nm | | var]; subst; simpl in *; try reflexivity; [
    destruct nm as [i|i]
    | destruct var as [i]
  ]; 
  destruct i as [f|b]; subst; simpl in *; try reflexivity; 
    destruct (eq_nat_decide b n); simpl in *; try reflexivity;
      contradict Hnotinopenx; left; reflexivity.
Qed.

Lemma open_proc_inj : 
  forall P x y n,
    ~ In x (free_ids_proc (open_proc x n P))
    ->
    ~ In y (free_ids_proc (open_proc y n P))
    ->
    open_proc x n P = open_proc y n P.
Proof.
  intros P; induction P; intros x y n Hnotinopenx Hnotinopeny; simpl in *; (repeat rewrite in_app_iff in * );
    ((repeat rewrite open_value_inj2 with (x:=x) (y:=y)); try solve [tauto]);
    solve [
      (rewrite IHP with (x:=x) (y:=y); try solve [tauto])
      || (rewrite IHP1 with (x:=x) (y:=y); try solve [tauto]; rewrite IHP2 with (x:=x) (y:=y); try solve [tauto])
    ].
Qed.
  
Lemma SO3_proc_no_free_var_aux :
   forall x y w P Q,
     SO3 x y w P Q
     ->
     ~ In x (free_ids_proc P)
     -> 
     P = Q.
Proof.
  intros x y w P Q Hso3; induction Hso3; intros Hnotin.
  unfold subst_open_proc.
  pose (free_ids_proc_rename _ _ _ _ Hnotin H H0) as Hu.
  rewrite (subst_proc_idem _ _ _ Hu).
  apply open_proc_inj; auto.

  rewrite IHHso3; auto.
  contradict Hnotin.
  apply free_ids_open_proc2; auto.
Qed.

Lemma SO3_proc_no_free_var :
   forall G x y w P Q,
     G |-p P
     ->
     SO3 x y w P Q
     ->
     ~ In x (free_ids_context G)
     ->
     P = Q.
Proof.
  intros G x y w P Q Htyp Hso3 HnotinxG.
  apply SO3_proc_no_free_var_aux with (1:=Hso3).
  apply free_values_in_context_1 in Htyp.
  contradict HnotinxG.
  apply free_ids_values_proc in HnotinxG.
  destruct HnotinxG as [u Hin]; destruct Hin as [Hin1 Hin2].
  specialize (Htyp u Hin1).
  destruct Htyp as [sigma Hin3].
  rewrite free_ids_context_iff.
  exists u; exists sigma; tauto.
Qed.

(* ============================================================================= *)

Lemma subst_r_output_stateful : 
  forall G x y w u v P Q1 s t rho rho1,
    G |-v u : TChannel s
    ->
    G |-v v : rho
    ->
    u <> v
    ->
    v <> w
    ->
    ~ (v = ValVariable (Var (Free x)) /\ In w (free_values_proc (u ! v; P)))
    ->
    (s -- MOut rho --> t)
    ->
    SO3 x y w (u ! v; P) Q1
    ->
    x <> y
    ->
    ~ In x (free_ids_value w)
    ->
    ~ In y (free_ids_proc (u ! v; P))
    ->
    ~ In y (free_ids_value w)
    ->
    CTX.In (ValVariable (Var (Free x)), rho1) G
    ->
    (forall k : string, w = Token k -> rho1 = TSingleton (Token k))
    ->
    ctx_add_value w rho1 G |-part G (+) ctx_add_value w rho1 CTX.empty
    ->
    G |-p u ! v; P
    ->
    ctx_replace u (TChannel s) (TChannel t) (CTX.remove (v, rho) G) |-p P
    ->
    (forall (x : free_id) (rho0 : type) (y : free_id) 
      (Q : proc) (v0 : value),
      SO3 x y v0 P Q ->
      x <> y ->
      ~ In x (free_ids_value v0) ->
      ~ In y (free_ids_proc P) ->
      ~ In y (free_ids_value v0) ->
      CTX.In (ValVariable (Var (Free x)), rho0)
      (ctx_replace u (TChannel s) (TChannel t) (CTX.remove (v, rho) G)) ->
      (forall k : string, v0 = Token k -> rho0 = TSingleton (Token k)) ->
      (ctx_add_value v0 rho0 (ctx_replace u (TChannel s) (TChannel t) (CTX.remove (v, rho) G))
        |-part ctx_replace u (TChannel s) (TChannel t) (CTX.remove (v, rho) G)
          (+) ctx_add_value v0 rho0 CTX.empty) ->
      ctx_add_value v0 rho0 (ctx_replace u (TChannel s) (TChannel t) (CTX.remove (v, rho) G))
      |-p Q)
    ->
    ctx_add_value w rho1 G |-p Q1.
Proof.
  intros G x y w u v P Q1 s t rho rho1 H HlookupvG Hnequv Hneqvw Hnofreew Htrans Hso3 Hneqxy Hnotinxw HnotinyP Hnotinyv HinxG Htoken Hpart HtypP HtypbareP H2.

  assert (ctx_add_value w rho1 G |-wf) as HwfaddvG; [eapply partition_wf; eauto|].

  pose (SO3_out_decompose _ _ _ _ _ Hso3 _ _ _ eq_refl) as e; destruct e as [u2 e]; destruct e as [v2 e]; destruct e as [Q2 e]; subst.

  assert (SO3_value x y w u u2) as Hso3v; [eapply SO3_value_output1; eauto|].
  assert (SO3_value x y w v v2) as Hso3vb; [eapply SO3_value_output2; eauto|].

  assert (free_name_or_token w) as Hfnot; [apply (SO3_value_free_name_or_token _ _ _ _ _ Hso3v) |].

  assert (SO3 x y w P Q2) as Hso3a; [apply SO3_output in Hso3; auto|].

  assert (~ In y (free_ids_value u)) as Hnotinyu; [contradict HnotinyP; simpl; intuition|].

  assert (u = w \/ v = w -> u2 <> v2 \/ (|-st rho)) as Hneqorstateless.
  intros Hinor; destruct Hinor as [Hin|Hin]; subst.

  inversion Hpart as [? ? ? _ HwfwG Hdisjoint]; subst.

  assert (CTX.In (w, TChannel s) (ctx_add_value w rho1 G)) as Hinw1; [
    inversion H as [? ? ? ? Hinu |]; subst;
      inversion Hfnot; simpl; subst; try solve [assumption]; apply CTXFacts.add_2; assumption
    |
  ].
  assert (free_value w) as Hfvw; [inversion HwfwG as [? Hfv _ _ ]; subst; eapply Hfv; eauto | ].
  assert (CTX.In (w, rho1) (ctx_add_value w rho1 G)) as Hinw2; [
    inversion Hfnot; simpl; subst; [ 
      |
      | inversion Hfvw
    ]; apply CTXFacts.add_1; reflexivity
    |
  ].
  assert (TChannel s = rho1); [
    inversion HwfwG as [? ? Heqtypes]; subst; eapply Heqtypes; eauto
    | subst
  ].
  assert (|-st TChannel s).
  specialize (Hdisjoint w (TChannel s)).
  destruct Hdisjoint as [Hdisjoint | Hdisjoint]; [|destruct Hdisjoint as [Hdisjoint | Hdisjoint]; [|auto]].
  contradict Hdisjoint; inversion H; subst; auto.
  contradict Hdisjoint; inversion Hfnot; subst; simpl; [| | inversion Hfvw]; apply CTXFacts.add_1; reflexivity.

  destruct (SO3_value_cases_output2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H HlookupvG Htrans Hso3 Hneqxy HnotinyP Hnotinyv HinxG Htoken Hpart HtypP) as [Hu|Hu];
    [ destruct Hu as [Heq1 Heq2]; destruct Heq2 as [Heq2 Heq3]; destruct Heq3 as [Heq3 Hstateless]; rewrite Heq1 in *; clear Heq1; subst;
      contradict Hnequv; reflexivity
      | destruct Hu as [Hu|Hu]; [
        destruct Hu as [Heq1 Hnequ2w]; destruct Hnequ2w as [Hnequ2w Hnequ2x]; subst
        | destruct Hu as [Heq1 Heq2]; destruct Heq2 as [Heq2 Heq3]; subst
      ]
    ].
  assert (u2 = w); [
    destruct (SO3_value_cases _ _ _ _ _ Hso3v) as [Hu|Hu]; [
      symmetry; assumption
      | destruct Hu as [Hu|Hu]; [
        destruct Hu as [Hu1 Hu2]; 
          rewrite <- Hu2; destruct (value_dec (freeid_rename_value x y w) w) as [e|n]; [
            apply e
            | contradict Hnotinxw; eapply freeid_rename_value_cases_contra2; contradict n; symmetry; apply n
          ]
        | destruct Hu as [Hu1 Hu2]; assumption
      ]
    ]
    | subst
  ].
  left; assumption.
  right; assumption.

  destruct (free_name_or_token_split _ Hfnot) as [Hfn|Htok]; [
    | destruct Htok as [k Heq]; subst; apply token_lookup in HlookupvG; subst; right; constructor
  ].
  assert (CTX.In (w, rho) G) as Hin1a; [
    inversion Hfn; subst; inversion HlookupvG; subst; assumption
    |
  ].
  assert (CTX.In (w, rho) (ctx_add_value w rho1 G)) as Hin1; [
    inversion Hfn; subst; simpl; apply CTXFacts.add_2; apply Hin1a
    |
  ].
  assert (CTX.In (w, rho1) (ctx_add_value w rho1 G)) as Hin2; [
    inversion Hfn; subst; simpl; apply CTXFacts.add_1; reflexivity
    |
  ].
  assert (rho = rho1); [ 
    | subst
  ].
  inversion HwfaddvG as [? ? Heqtypes]; subst; apply (Heqtypes _ _ _ Hin1 Hin2).
  right.
  inversion Hpart as [? ? ? ? ? Hdisjoint]; subst.
  specialize (Hdisjoint w rho1); destruct Hdisjoint as [Hnotin | Hdisjoint]; [
    contradict Hnotin; assumption
    | destruct Hdisjoint as [Hnotin | Hdisjoint]; [
      contradict Hnotin; inversion Hfn; subst; apply CTXFacts.add_1; reflexivity
      | assumption
    ]
  ].

  eapply TypPrefixOutput with (1:=Htrans); [
    apply SO3_output_distinct_or_stateless with (1:=Hso3) (6:=Hneqorstateless); auto
    |
    |
    | left; reflexivity
    | reflexivity
    |
  ].

  (* ctx_add_value w rho1 G |-v u2 : TChannel s *)
  apply subst_r_value_alt with (x:=x) (y:=y) (u1:=u); auto; contradict HnotinyP; simpl; intuition.

  (*   ctx_add_value w rho1 G |-v v2 : rho *)
  apply subst_r_value_alt with (x:=x) (y:=y) (u1:=v); auto; contradict HnotinyP; simpl; intuition.

  (* is v=x ? *)
  destruct (value_dec v (ValVariable (Var (Free x)))) as [e|n]; [
    subst
    |
  ].
  assert (v2 = w); [
    apply SO3_value_var_determines_subst_improved with (1:=Hso3vb); auto; simpl; contradict Hneqxy; destruct Hneqxy; tauto
    | subst
  ].
  assert (u = u2); [
    destruct (SO3_value_cases _ _ _ _ _ Hso3v) as [Hu|Hu]; [
      assumption
      | destruct Hu as [Hu|Hu]; [
        destruct Hu as [Hu1 Hu2]; subst; 
          destruct (value_dec u (freeid_rename_value x y u)) as [e|n]; [ 
            assumption
            | apply freeid_rename_value_cases_contra2 in n;
              destruct u as [nm| |var]; simpl in n; try solve [destruct n]; [ 
                destruct nm as [i|i] 
                | destruct var as [i] 
              ]; simpl in n; 
              destruct i as [f|b]; simpl in n; destruct n; match goal with | [ H : False |- _ ] => destruct H | _ => idtac end; subst;
                try solve [contradict Hnequv; reflexivity];
                  (inversion H as [? ? ? HwfG HinuG|]; subst;
                    inversion HwfG as [? ? ? Hdisjoint]; subst; destruct (Hdisjoint x) as [Hu|Hu]; [
                      specialize (Hu rho1); contradict Hu; assumption
                      | destruct Hu as [Hu3 Hu4]; 
                        ((specialize (Hu3 (TChannel s)); contradict Hu3; assumption) 
                          || (specialize (Hu4 (TChannel s)); contradict Hu4; assumption))
                    ])
          ]
        | destruct Hu as [Hu1 Hu2]; subst; contradict Hnequv; reflexivity
      ]
    ]
    | subst
  ].
  assert (rho = rho1); [
    assert (CTX.In (ValVariable (Var (Free x)), rho) G) as HinxG2; [
      inversion HlookupvG; assumption
      |
    ];
    inversion HlookupvG as [? ? ? Hwf _|]; subst;
      inversion Hwf as [? ? Heqtypes]; subst;
        apply (Heqtypes _ _ _ HinxG2 HinxG)
    | subst
  ].
  assert (
    CTX.eq
    (ctx_replace u2 (TChannel s) (TChannel t) (CTX.remove (w, rho1) G))
    (ctx_replace u2 (TChannel s) (TChannel t) (CTX.remove (w, rho1) (ctx_add_value w rho1 G)))
  ) as Heqctx; [

    | subst
  ].
  apply CTXProperties.subset_antisym.
  apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|].
  intros a Hin; destruct a;  (repeat rewrite CTXFacts.remove_iff in Hin); destruct Hin as [Hin1 Hneq2]; destruct Hin1 as [Hin1 Hneq1].
  apply CTXFacts.add_2.
  apply CTXFacts.remove_2; [assumption|].
  apply CTXFacts.remove_2; [assumption|].
  inversion Hfnot; subst; try apply CTXFacts.add_2; assumption.
  apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|].
  intros a Hin; destruct a;  (repeat rewrite CTXFacts.remove_iff in Hin); destruct Hin as [Hin1 Hneq2]; destruct Hin1 as [Hin1 Hneq1].
  apply CTXFacts.add_2.
  apply CTXFacts.remove_2; [assumption|].
  apply CTXFacts.remove_2; [assumption|].
  inversion Hfnot; subst; simpl in Hin1; repeat rewrite CTXFacts.add_iff in Hin1; try solve [assumption]; 
    (destruct Hin1 as [Hin1|Hin1]; [
      contradict Hneq1; assumption
      | assumption
    ]).
  apply ctx_equal_preserves_typed with (2:=Heqctx).

  assert (P = Q2); [
    apply SO3_proc_no_free_var with (1:=HtypbareP) (2:=Hso3a)
    | subst
  ].
  intros Hin.
  rewrite free_ids_context_iff in Hin.
  destruct Hin as [u Hin]; destruct Hin as [rho Hin]; destruct Hin as [Hin1 Hin2].
  unfold ctx_replace in Hin1; (repeat rewrite CTXFacts.add_iff in Hin1 || rewrite CTXFacts.remove_iff in Hin1 ).
  destruct Hin1 as [Hin1|Hin1]; [
    injection Hin1; intros; subst;
      inversion H as [? ? ? Hwf HinuG|]; subst;
        inversion Hwf as [? ? ? Hdisjoint]; subst;
          (destruct u as [nm | | var]; subst; simpl in *; try solve [destruct Hin2]; [
            destruct nm as [i|i]
            | destruct var as [i]
          ]; subst; simpl);
          (destruct i as [f|b]; subst; simpl in *; try solve [destruct Hin2];
            (destruct Hin2 as [Hin2|Hin2]; subst; simpl; [ | solve [destruct Hin2]]));
          specialize (Hdisjoint x);
            (destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
              specialize (Hdisjoint rho1); contradict Hdisjoint; assumption
              | destruct Hdisjoint as [Hdisjoint1 Hdisjoint2]; specialize (Hdisjoint1 (TChannel s)); specialize (Hdisjoint2 (TChannel s));
                try solve [(contradict Hdisjoint1; assumption) || (contradict Hdisjoint2; assumption)]
            ]);
            contradict Hnequv; reflexivity
    | destruct Hin1 as [Hin1 Hin3]; destruct Hin1 as [Hin1 Hin4];
            inversion H as [? ? ? Hwf HinuG|]; subst;
        inversion Hwf as [? ? Heqtypes Hdisjoint]; subst;
            (destruct u as [nm | | var]; subst; simpl in *; try solve [destruct Hin2]; [
            destruct nm as [i|i]
            | destruct var as [i]
          ]; subst; simpl);
          (destruct i as [f|b]; subst; simpl in *; try solve [destruct Hin2];
            (destruct Hin2 as [Hin2|Hin2]; subst; simpl; [ | solve [destruct Hin2]]));
          specialize (Hdisjoint x);
            (destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
              try solve [specialize (Hdisjoint rho1); contradict Hdisjoint; assumption]
              | destruct Hdisjoint as [Hdisjoint1 Hdisjoint2];
                specialize (Hdisjoint1 rho); specialize (Hdisjoint2 rho);
                  try solve [(contradict Hdisjoint1; assumption) || (contradict Hdisjoint2; assumption)]
            ])
  ].
  pose (Heqtypes _ _ _ HinxG Hin1); rewrite e in *.
  contradict Hin4; reflexivity.

  assert (ctx_replace u2 (TChannel s) (TChannel t) G |-p Q2) as HtypQ2.
  eapply partition_typed_weaken_left with (GR:=CTX.add (ValVariable (Var (Free x)), rho1) CTX.empty); [apply HtypbareP | ].
  apply ctx_replace_preserves_partition_left.
  apply CTXFacts.remove_2; [contradict Hnequv; injection Hnequv; intros; subst; reflexivity | inversion H; assumption ].
  rewrite CTXFacts.add_iff; intros Hin; destruct Hin as [Heq|Hin]; [
      injection Heq; intros; subst; contradict Hnequv; reflexivity
      | rewrite CTXFacts.empty_iff in Hin; destruct Hin

    ].
  apply partition_comm.
  apply partition_add_remove_swap.
  apply partition_comm.
  apply partition_empty.
  inversion HlookupvG; assumption.
  assumption.

  eapply typed_strengthen; [apply HtypQ2 | | ].
  apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity | ].
  intros a Hin; destruct a; (repeat rewrite CTXFacts.remove_iff in Hin); 
    destruct Hin as [Hin Hin3]; destruct Hin as [Hin1 Hin2].
  apply CTXFacts.add_2.
  apply CTXFacts.remove_2; auto.

  intros w2 Hinw2.
  destruct (value_dec w2 u2) as [e|n].
  subst; eexists; apply CTXFacts.add_1; reflexivity.
  apply free_values_in_context_1 in HtypP.
  specialize (HtypP w2).
  assert (exists sigma, CTX.In (w2, sigma) G) as Hu; [
    apply HtypP; simpl; rewrite in_app_iff; right; apply in_cons; assumption
    |
  ].
  destruct Hu as [sigma Hu].
  exists sigma.
  apply CTXFacts.add_2.
  apply CTXFacts.remove_2; [ contradict n; injection n; intros; subst; reflexivity |].
  apply CTXFacts.remove_2; [
    contradict Hnofreew; split; auto;
      injection Hnofreew; intros; subst;
        simpl; rewrite in_app_iff; right; apply in_cons; assumption
    | assumption
  ].


  assert (v = v2); [
    (destruct (SO3_value_cases _ _ _ _ _ Hso3vb) as [Heq|Hu]; [
      assumption
      | destruct Hu as [Hu | Hu]; [
        destruct Hu as [Hu1 Hu2]
        | destruct Hu as [Hu1 Hu2]; contradict n; assumption
      ]
    ]);
    (destruct (value_dec v v2) as [e1|n1]; [
      assumption
      | 
    ]);
    subst; apply freeid_rename_value_cases_contra2 in n1;
      (destruct v as [nm| |var]; simpl in n1; try solve [destruct n1]; 
        [destruct nm as [i|i] | destruct var as [i]]; simpl in n1;
          destruct i as [f|b]; simpl in n1; try solve [destruct n1];
            (destruct n1 as [n1|n1]; [ subst | destruct n1]);
            [ | | contradict n; reflexivity ];
            inversion HlookupvG as [? ? ? HwfG HinxG2|]; subst;
              inversion HwfG as [? ? Heqtypes Hdisjoint]; subst;
                (specialize (Hdisjoint x); destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
                  specialize (Hdisjoint rho1); contradict Hdisjoint; assumption
                  | destruct Hdisjoint as [Hdisjoint1 Hdisjoint2]; specialize (Hdisjoint1 rho); specialize (Hdisjoint2 rho); contradict HinxG2; assumption
                ]))
    | subst
  ].

  assert (
    CTX.eq 
    (ctx_replace u2 (TChannel s) (TChannel t) (ctx_add_value w rho1 (CTX.remove (v2, rho) G)))
    (ctx_replace u2 (TChannel s) (TChannel t) (CTX.remove (v2, rho) (ctx_add_value w rho1 G)))
  ) as Hctxeq1; [
    apply add_cong; apply remove_cong; apply add_value_comm; auto
    | apply ctx_equal_preserves_typed with (2:=Hctxeq1)
  ].

  clear Hneqorstateless.
  destruct (SO3_value_cases_output1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H HlookupvG Htrans Hso3 Hneqxy HnotinyP Hnotinyv HinxG Htoken Hpart HtypP) as [Hu|Hu];
    [ destruct Hu as [Heq1 Heq2]; destruct Heq2 as [Heq2 Heq3]; destruct Heq3 as [Heq3 Hstateless]; subst
      | destruct Hu as [Hu|Hu]; [
        destruct Hu as [Heq1 Hnequ2w]; destruct Hnequ2w as [Hnequ2w Hnequ2x]; subst
        | destruct Hu as [Heq1 Heq2]; destruct Heq2 as [Heq2 Heq3]; subst
      ]
    ];
    [ Case "(u1 = u2 /\ u2 = w /\ rho = TChannel s /\ |-st TChannel s)"%string 
      | Case "(u1 = u2 /\ u2 <> w /\ u2 <> ValVariable (Var (Free x)))"%string
      | Case "(u1 = ValVariable (Var (Free x)) /\ u2 = w /\ rho = TChannel s)"%string
    ];
    idtac.

  (* "(u1 = u2 /\ u2 = w /\ rho = TChannel s /\ |-st TChannel s)" *)
  assert (s = t) as Heq; [ inversion Hstateless as [? Heq2|]; subst; apply (Heq2 _ _ Htrans) | subst].

  eapply ctx_equal_preserves_typed.
  eapply H2 with (1:=Hso3a); auto; [
    contradict HnotinyP; simpl; (repeat rewrite in_app_iff); right; right; assumption
    | apply CTXFacts.add_2; 
      apply CTXFacts.remove_2; [intros Heq; injection Heq; intros; subst; inversion Hfnot | ]; 
        apply CTXFacts.remove_2; [intros Heq; injection Heq; intros; subst; contradict n; reflexivity |];
          assumption
    |
  ].

  apply ctx_equal_part_1 with (G1:=(ctx_replace w (TChannel t) (TChannel t) (CTX.remove (v2, rho) G))); [
    | inversion Hfnot; subst; simpl; try solve [reflexivity]; (apply CTXProperties.subset_antisym; [
      apply CTXProperties.subset_add_2; reflexivity
      | apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|]; reflexivity
    ])
  ].
  apply typed_ctx_wf in HtypbareP; inversion Hfnot; subst; simpl; 
    try (apply partition_comm; apply partition_add_idem_stateless; auto; [ apply partition_comm | | constructor ]);
      try solve [apply partition_empty; assumption];
        constructor; auto;
          apply CTXFacts.add_1; reflexivity.

  inversion Hfnot; subst; simpl; try solve [reflexivity];
    (apply CTXProperties.subset_antisym; [
      apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|];
        apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|];
          (intros a Hin; destruct a; (repeat rewrite CTXFacts.remove_iff in Hin); destruct Hin as [Hin Hin3]; destruct Hin as [Hin1 Hin2]);
          apply CTXFacts.add_2;
            (apply CTXFacts.remove_2; [assumption|]);
            apply CTXFacts.add_2;
              (apply CTXFacts.remove_2; [assumption|]); 
              assumption
      | apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|];
        (intros a Hin; destruct a; (repeat rewrite CTXFacts.remove_iff in Hin || rewrite CTXFacts.add_iff in Hin); 
          destruct Hin as [Hin1 Hin2]; 
            destruct Hin1 as [Hin1|Hin1]; [contradict Hin2; assumption|destruct Hin1 as [Hin1 Hin3]]);
        apply CTXFacts.add_2;
          apply CTXFacts.add_2;
            (apply CTXFacts.remove_2; [assumption|]);
            (apply CTXFacts.remove_2; [assumption|]);
            assumption
    ]).

  (* "(u1 = u2 /\ u2 <> w /\ u2 <> ValVariable (Var (Free x)))" *)
  assert (
    CTX.eq 
    (ctx_add_value w rho1 (ctx_replace u2 (TChannel s) (TChannel t) (CTX.remove (v2, rho) G)))
    (ctx_replace u2 (TChannel s) (TChannel t) (ctx_add_value w rho1 (CTX.remove (v2, rho) G)))
  ) as Heqctx; [
    |
  ].
  apply CTXProperties.subset_antisym; [
    inversion Hfnot; subst; simpl; try reflexivity; 
      (apply CTXProperties.subset_add_3; [
        apply CTXFacts.add_2; 
          (apply CTXFacts.remove_2; [contradict Hnequ2w; injection Hnequ2w; intros; subst; reflexivity|]);
          apply CTXFacts.add_1; reflexivity
        |
      ];
      apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity |];
        (intros a Hin; destruct a; (repeat rewrite CTXFacts.remove_iff in Hin); 
          destruct Hin as [Hin Hin3]; destruct Hin as [Hin1 Hin2]; 
            apply CTXFacts.add_2;
              (apply CTXFacts.remove_2; [assumption|]);
              apply CTXFacts.add_2;
                (apply CTXFacts.remove_2; [assumption|]);
                assumption))
    | inversion Hfnot; subst; simpl; try reflexivity; 
      (apply CTXProperties.subset_add_3; [apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity|]);
      (rewrite <- add_remove_comm; [|assumption]);
      (apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|]);
      (apply CTXProperties.subset_add_2;
        (intros a Hin; destruct a; (repeat rewrite CTXFacts.remove_iff in Hin); 
          destruct Hin as [Hin Hin3]; destruct Hin as [Hin1 Hin2]; 
            apply CTXFacts.add_2;
              (apply CTXFacts.remove_2; [assumption|]);
              (apply CTXFacts.remove_2; [assumption|]);
              assumption))
  ].
  apply ctx_equal_preserves_typed with (2:=Heqctx).
  apply H2 with (1:=Hso3a); auto.
  contradict HnotinyP; simpl; (repeat rewrite in_app_iff); right; right; assumption.
  apply CTXFacts.add_2.
  apply CTXFacts.remove_2; [contradict Hnequ2x; injection Hnequ2x; intros; subst; reflexivity|].
  apply CTXFacts.remove_2; [contradict n; injection n; intros; subst; reflexivity|].
  assumption.

  eapply ctx_equal_part_1; [ | rewrite Heqctx; reflexivity].
  apply ctx_replace_preserves_partition_left.
  apply CTXFacts.remove_2; [contradict Hnequv; injection Hnequv; intros; subst; reflexivity|].
  inversion H; subst; assumption.
  inversion Hfnot; subst; simpl; intros Hin; try (rewrite CTXFacts.add_iff in Hin); rewrite CTXFacts.empty_iff in Hin;
    try solve [destruct Hin]; (destruct Hin as [Hin|Hin]; [injection Hin; intros; subst; contradict Hnequ2w; reflexivity|destruct Hin]).
  assert (
    CTX.eq
    (ctx_add_value w rho1 (CTX.remove (v2, rho) G))
    (CTX.remove (v2, rho) (ctx_add_value w rho1 G))
  ) as Heqctx2; [ 
    inversion Hfnot; subst; simpl; try reflexivity; (rewrite <- add_remove_comm; [reflexivity|auto])
    |
  ].
  eapply ctx_equal_part_1; [
    | rewrite Heqctx2; reflexivity
  ].
  apply ctx_remove_preserves_partition_left; [|assumption].
  inversion Hfnot; subst; simpl; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.empty_iff); 
    (try solve [contradict Hneqvw; destruct Hneqvw]);
    (try solve [(contradict Hneqvw; destruct Hneqvw as [Hneqvw|Hfalse]; [|destruct Hfalse]; injection Hneqvw; intros; subst; reflexivity)]).


  (* "(u1 = ValVariable (Var (Free x)) /\ u2 = w /\ rho = TChannel s)" *)
  clear Hctxeq1.
  assert (free_name w) as Hfn; [
    destruct (free_name_or_token_split _ Hfnot) as [Hfn|Htok]; [
      assumption
      | destruct Htok as [k Heq]; destruct k; subst; specialize (Htoken _ eq_refl); discriminate Htoken
    ]
    |
  ].
  
  assert (ctx_add_value w (TChannel t) (ctx_replace (ValVariable (Var (Free x))) (TChannel s) (TChannel t) (CTX.remove (v2, rho) G)) |-p Q2) as IHtyp; [
    apply H2 with (1:=Hso3a); auto; [
      contradict HnotinyP; simpl; (repeat rewrite in_app_iff); right; right; assumption
      | apply CTXFacts.add_1; reflexivity
      | intros k Heq; specialize (Htoken k Heq); discriminate Htoken
      | clear H2
    ] 
    | 
  ].
  
  assert (
    CTX.eq
    (ctx_add_value w (TChannel t) (ctx_replace (ValVariable (Var (Free x))) (TChannel s) (TChannel t) (CTX.remove (v2, rho) G)))
    (ctx_replace (ValVariable (Var (Free x))) (TChannel s) (TChannel t) (CTX.remove (v2, rho) (ctx_add_value w (TChannel t) G)))
  ) as Hctxeq1; [
    |
  ].
  apply CTXProperties.subset_antisym; [
    inversion Hfn; subst; 
      (apply CTXProperties.subset_add_3; [
        apply CTXFacts.add_2; 
          (apply CTXFacts.remove_2; [discriminate|]);
          (apply CTXFacts.remove_2; [contradict Hneqvw; injection Hneqvw; intros; subst; reflexivity|]);
          (apply CTXFacts.add_1; reflexivity)
        |
      ]);
      (apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity | apply CTXProperties.subset_add_2]);
      (intros a Hin; destruct a; (repeat rewrite CTXFacts.remove_iff in Hin); destruct Hin as [Hin Hin3]; destruct Hin as [Hin1 Hin2]; 
        apply CTXFacts.remove_2; [assumption|]; 
          apply CTXFacts.remove_2; [assumption|]; 
            apply CTXFacts.add_2; assumption)
    | inversion Hfn; subst; simpl;
      (apply CTXProperties.subset_add_3; [apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity| ]);
      (intros a Hin; destruct a; (repeat rewrite CTXFacts.remove_iff in Hin || rewrite CTXFacts.add_iff in Hin); 
        destruct Hin as [Hin Hin3]; destruct Hin as [Hin1 Hin2]; destruct Hin1 as [Hin1|Hin1]; [
          apply CTXFacts.add_1; assumption
          | apply CTXFacts.add_2; apply CTXFacts.add_2; apply CTXFacts.remove_2; [assumption|]; apply CTXFacts.remove_2; [assumption|]; assumption
        ])
  ].

  eapply ctx_equal_part_1; [
    | rewrite Hctxeq1; reflexivity
  ].
  apply ctx_replace_preserves_partition_left; [
    apply CTXFacts.remove_2; [contradict Hnequv; injection Hnequv; intros; subst; reflexivity | assumption]
    | inversion Hfn; subst; simpl; rewrite CTXFacts.add_iff; rewrite CTXFacts.empty_iff; intros Hin; 
      (destruct Hin as [Hin|Hin]; [discriminate | destruct Hin])
    |
  ].
  apply ctx_remove_preserves_partition_left; [
    inversion Hfn; subst; simpl; rewrite CTXFacts.add_iff; rewrite CTXFacts.empty_iff; intros Hin; 
      (destruct Hin as [Hin|Hin]; [injection Hin; intros; subst; contradict Hneqvw; reflexivity | destruct Hin])
    | 
  ].
  apply ctx_add_value_change_type with (2:=Htrans); auto.

  assert (
    forall rho, CTX.In (w, rho) G -> rho = TChannel t
  ) as Heqtypesw.
  apply typed_ctx_wf in IHtyp.
  inversion IHtyp as [? Hfv Heqtypes Hdisjoint]; subst; clear Hfv Hdisjoint.
  intros sigma Hin.
  assert
    (CTX.In (w, sigma) 
      (ctx_add_value w (TChannel t) (ctx_replace (ValVariable (Var (Free x))) (TChannel s) (TChannel t) (CTX.remove (v2, rho) G))))
    as Hin1.
  inversion Hfn; subst; simpl; 
    (apply CTXFacts.add_2; apply CTXFacts.add_2; 
      apply CTXFacts.remove_2; [discriminate|]; 
        apply CTXFacts.remove_2; [contradict Hneqvw; injection Hneqvw; intros; subst; reflexivity|];
          assumption).
  assert
    (CTX.In (w, TChannel t) 
      (ctx_add_value w (TChannel t) (ctx_replace (ValVariable (Var (Free x))) (TChannel s) (TChannel t) (CTX.remove (v2, rho) G))))
    as Hin2.
  inversion Hfn; subst; simpl; apply CTXFacts.add_1; reflexivity.
  apply (Heqtypes _ _ _ Hin1 Hin2).

  assert (
    CTX.eq 
    (ctx_replace w (TChannel s) (TChannel t) (ctx_add_value w (TChannel s) (CTX.remove (v2, rho) G)))
    (ctx_add_value w (TChannel t) (CTX.remove (v2, rho) G))
  ) as Hctxeq1.
  apply CTXProperties.subset_antisym; [
    inversion Hfn; subst; simpl;
      (apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|]);
      (intros a Hin; destruct a; (repeat rewrite CTXFacts.remove_iff in Hin || rewrite CTXFacts.add_iff in Hin); 
        destruct Hin as [Hin Hin3]; destruct Hin as [Hin1|Hin1]; [contradict Hin3; assumption|]; destruct Hin1 as [Hin1 Hin2];
          apply CTXFacts.add_2;
            (apply CTXFacts.remove_2; [assumption|]);
            assumption)
    | inversion Hfn; subst; simpl;
      (apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|]);
      (intros a Hin; destruct a; (repeat rewrite CTXFacts.remove_iff in Hin || rewrite CTXFacts.add_iff in Hin); 
        destruct Hin as [Hin1 Hin2];
          match goal with 
            | [ |- CTX.In _ (ctx_replace ?X _ _ _) ] => 
              destruct (value_dec v X) as [e1|n1]; [
                subst; apply Heqtypesw in Hin1; subst; apply CTXFacts.add_1; reflexivity
                |
              ]
          end;
          apply CTXFacts.add_2; 
            (apply CTXFacts.remove_2; [contradict n1; injection n1; intros; subst; reflexivity |]);
            apply CTXFacts.add_2; 
              apply CTXFacts.remove_2; [assumption|]; assumption)
  ].

  eapply ctx_equal_preserves_typed; [
    clear Hctxeq1
    | rewrite Hctxeq1; reflexivity
  ].
  
  apply typed_change_type with (v:=ValVariable (Var (Free x))) (rho:=TChannel t) (sigma:=TChannel s) in IHtyp.
  eapply ctx_equal_preserves_typed; [
    apply IHtyp
    |
  ].

  assert (
    CTX.eq
    (ctx_replace (Var (Free x)) (TChannel t) (TChannel s) (ctx_add_value w (TChannel t) (ctx_replace (Var (Free x)) (TChannel s) (TChannel t) (CTX.remove (v2, rho) G))))
    (ctx_add_value w (TChannel t) ((ctx_replace (Var (Free x)) (TChannel t) (TChannel s) (ctx_replace (Var (Free x)) (TChannel s) (TChannel t) (CTX.remove (v2, rho) G)))))
  ) as Heqctx2.
  clear H2.
  inversion Hfn; subst; simpl; try solve [reflexivity];
    (apply CTXProperties.subset_antisym; [
      (apply CTXProperties.subset_add_3; [apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity | ]);
      (rewrite <- add_remove_comm; [|discriminate]);
      (apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity | ]);
      apply CTXProperties.subset_add_2;
        apply CTXProperties.subset_add_2;
          reflexivity
      | 
        (apply CTXProperties.subset_add_3;
          [apply CTXFacts.add_2;
            (apply CTXFacts.remove_2; [discriminate|]);
            (apply CTXFacts.add_1; reflexivity)
            |
          ]);
        (apply CTXProperties.subset_add_3;
          [ (apply CTXFacts.add_1; reflexivity)
            |
          ]);
        apply CTXProperties.subset_add_2;
          (rewrite <- add_remove_comm; [|discriminate]);
          apply CTXProperties.subset_add_2;
            reflexivity
    ]).
  rewrite Heqctx2; clear Heqctx2 H2.

  assert (
    CTX.eq
    ((ctx_replace (Var (Free x)) (TChannel t) (TChannel s) (ctx_replace (Var (Free x)) (TChannel s) (TChannel t) (CTX.remove (v2, rho) G))))
    ((CTX.remove (v2, rho) G))
  ) as Heqctx3.
  apply CTXProperties.subset_antisym.
  apply CTXProperties.subset_add_3; [(apply CTXFacts.remove_2; [contradict Hnequv; injection Hnequv; intros; subst; reflexivity|]); assumption | ].
  intros a Hin; destruct a; 
    rewrite CTXFacts.remove_iff in Hin; destruct Hin as [Hin1 Hin2];
      unfold ctx_replace in Hin1; rewrite CTXFacts.add_iff in Hin1; destruct Hin1 as [Hin1|Hin1]; [
        contradict Hin2; assumption
        | rewrite CTXFacts.remove_iff in Hin1; destruct Hin1 as [Hin1 Hin3]; 
          rewrite CTXFacts.remove_iff in Hin1; destruct Hin1 as [Hin1 Hin4];
            apply CTXFacts.remove_2; assumption
      ].
  intros a Hin; destruct a; 
    rewrite CTXFacts.remove_iff in Hin; destruct Hin as [Hin1 Hin2].
  destruct (value_dec (ValVariable (Var (Free x))) v) as [e1|n1]; [
    subst; 
      assert (t0 = TChannel s); [
        inversion H as [? ? ? Hwf|]; subst;
          inversion Hwf as [? ? Heqtypes]; subst;
            apply (Heqtypes _ _ _ Hin1 HinxG)
        | subst; apply CTXFacts.add_1; reflexivity
      ]
    | apply CTXFacts.add_2;
      apply CTXFacts.remove_2; [contradict n1; injection n1; intros; subst; reflexivity|]; 
        apply CTXFacts.add_2; 
          apply CTXFacts.remove_2; [contradict n1; injection n1; intros; subst; reflexivity|]; 
            apply CTXFacts.remove_2; [assumption|]; assumption
  ].

  inversion Hfn; subst; simpl; try solve [apply Heqctx3 || apply add_cong; apply Heqctx3].

  inversion Hfn; subst; apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity.

  intros Hin.
  apply SO3_free_values_in_context1_aux with (2:=Hso3a) in Hin.
  destruct Hin as [v1 Hin]; destruct Hin as [Hin Hso3v2].
  apply SO3_value_unknown_varx_contra in Hso3v2; auto.
Qed.

(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

Lemma subst_r_output_stateless_simplified : 
  forall G x y w u v P Q1 s t rho rho1,
    G |-v u : TChannel s
    ->
    G |-v v : rho
    ->
    |-st rho
    ->
    (s -- MOut rho --> t)
    ->
    SO3 x y w (u ! v; P) Q1
    ->
    x <> y
    ->
    ~ In x (free_ids_value w)
    ->
    ~ In y (free_ids_proc (u ! v; P))
    ->
    ~ In y (free_ids_value w)
    ->
    CTX.In (ValVariable (Var (Free x)), rho1) G
    ->
    (forall k : string, w = Token k -> rho1 = TSingleton (Token k))
    ->
    ctx_add_value w rho1 G |-part G (+) ctx_add_value w rho1 CTX.empty
    ->
    G |-p u ! v; P
    ->
    ctx_replace u (TChannel s) (TChannel t) G |-p P
    ->
    (forall (rho0 : type) 
      (Q : proc) (v0 : value),
      SO3 x y v0 P Q
      ->
      x <> y
      ->
      ~ In x (free_ids_value v0)
      ->
      ~ In y (free_ids_proc P)
      ->
      ~ In y (free_ids_value v0)
      ->
      CTX.In (ValVariable (Var (Free x)), rho0) (ctx_replace u (TChannel s) (TChannel t) G)
      ->
      (forall k : string, v0 = Token k -> rho0 = TSingleton (Token k))
      ->
      (ctx_add_value v0 rho0 (ctx_replace u (TChannel s) (TChannel t) G) |-part ctx_replace u (TChannel s) (TChannel t) G (+) ctx_add_value v0 rho0 CTX.empty)
      ->
      ctx_add_value v0 rho0 (ctx_replace u (TChannel s) (TChannel t) G) |-p Q)
    ->
    ctx_add_value w rho1 G |-p Q1.
Proof.
  intros G x y w u v P Q1 s t rho rho1 H HlookupvG Hstatelessrho Htrans Hso3 Hneqxy Hnotinxw HnotinyP Hnotinyv HinxG Htoken Hpart HtypP HtypbareP H2.

  assert (ctx_add_value w rho1 G |-wf) as HwfaddvG; [eapply partition_wf; eauto|].

  pose (SO3_out_decompose _ _ _ _ _ Hso3 _ _ _ eq_refl) as e; destruct e as [u2 e]; destruct e as [v2 e]; destruct e as [Q2 e]; subst.

  assert (SO3_value x y w u u2) as Hso3v; [eapply SO3_value_output1; eauto|].
  assert (SO3_value x y w v v2) as Hso3vb; [eapply SO3_value_output2; eauto|].

  assert (free_name_or_token w) as Hfnot; [apply (SO3_value_free_name_or_token _ _ _ _ _ Hso3v) |].

  assert (SO3 x y w P Q2) as Hso3a; [apply SO3_output in Hso3; auto|].

  assert (~ In y (free_ids_value u)) as Hnotinyu; [contradict HnotinyP; simpl; intuition|].

  eapply TypPrefixOutput with (1:=Htrans); [
    right; assumption
    | apply subst_r_value_alt with (x:=x) (y:=y) (u1:=u); auto; contradict HnotinyP; simpl; intuition
    | apply subst_r_value_alt with (x:=x) (y:=y) (u1:=v); auto; contradict HnotinyP; simpl; intuition
    | right; split; [reflexivity | assumption]
    | reflexivity
    |
  ].

  destruct (value_dec (ValVariable (Var (Free x))) u) as [e|n].

  (* Var (Free x) = u *)
  assert (forall sigma, CTX.In (w, sigma) G -> sigma = rho1 /\ |-st TChannel s) as Hstat.
  intros sigma Hin.
  assert (CTX.In (w, sigma) (ctx_add_value w rho1 G)) as Hin1.
  inversion Hfnot; subst; simpl; try apply CTXFacts.add_2; assumption.
  assert (CTX.In (w, rho1) (ctx_add_value w rho1 G)) as Hin2.
  inversion Hfnot; subst; simpl; [
    apply CTXFacts.add_1; reflexivity
    | apply CTXFacts.add_1; reflexivity
    |
  ].
  inversion H as [? ? ? Hwf|]; subst.
  inversion Hwf as [? Hfv Heqtypes]; subst.
  specialize (Hfv _ _ Hin); inversion Hfv.
  inversion HwfaddvG as [? ? HeqtypesaddvG]; subst.
  rewrite (HeqtypesaddvG _ _ _ Hin1 Hin2) in *.
  assert (rho1 = TChannel s).
  inversion H as [? ? ? Hwf|]; subst.
  inversion Hwf as [? Hfv Heqtypes]; subst.
  assert (CTX.In (ValVariable (Var (Free x)), TChannel s) G) as Hin3.
  inversion H; subst; assumption.
  apply (Heqtypes _ _ _ HinxG Hin3).
  subst.
  inversion Hpart as [? ? ? ? ? Hst]; subst.
  specialize (Hst w (TChannel s)).
  split; auto.
  destruct Hst as [Hst|Hst]; [
    contradict Hst; assumption
    | destruct Hst as [Hst | Hst]; [
      contradict Hst
      | assumption
    ]
  ].
  inversion Hfnot; subst; simpl; try solve [apply CTXFacts.add_1; reflexivity].
  inversion H as [? ? ? Hwf|]; subst.
  inversion Hwf as [? Hfv Heqtypes]; subst.
  specialize (Hfv _ _ Hin); inversion Hfv.

  subst.
  assert (TChannel s = rho1); [
    inversion H as [? ? ? Hwf HinxG2|]; subst;
      inversion Hwf as [? ? Heqtypes]; subst;
        rewrite <- (Heqtypes _ _ _ HinxG2 HinxG) in *;
          reflexivity
    | subst].

  assert (free_name w) as Hfn.
  inversion Hfnot; subst; [
    constructor
    | constructor
    | destruct k as [k]; specialize (Htoken _ eq_refl); discriminate Htoken
  ].

  assert (u2 = w); [apply SO3_value_var_determines_subst_improved in Hso3v; auto|subst].

  assert (
    CTX.eq
    (CTX.add (w, TChannel t) G)
    (ctx_replace w (TChannel s) (TChannel t) (ctx_add_value w (TChannel s) G))
  ) as Hctxeq.
  inversion Hfn; subst; simpl;
    (apply CTXProperties.subset_antisym; [
      (apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|]);
      intros a Hin; destruct a;
        match goal with 
          | [ |- CTX.In _ (ctx_replace ?X _ _ _) ] => 
            destruct (value_dec v0 X) as [e4|n4]; [
              subst;  specialize (Hstat _ Hin); destruct Hstat as [Hstat1 Hstat2]; subst;
                apply CTXFacts.add_1;
                  inversion Hstat2 as [? Heqtypes2|]; subst;
                    rewrite (Heqtypes2 _ _ Htrans); reflexivity
              | apply CTXFacts.add_2;
                apply CTXFacts.remove_2; [contradict n4; injection n4; intros; subst; reflexivity|];
                  apply CTXFacts.add_2;
                    assumption
            ]
        end
      | (apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|]);
        apply CTXProperties.subset_add_2;
          (intros a Hin; destruct a; rewrite CTXFacts.remove_iff in Hin; rewrite CTXFacts.add_iff in Hin;
            destruct Hin as [Hin1 Hin2]; destruct Hin1 as [Hin1|Hin1]; [
              contradict Hin2; assumption
              | assumption
            ])
    ]).

  apply ctx_equal_preserves_typed with (2:=Hctxeq); clear Hctxeq.

  assert (ctx_add_value w (TChannel t) (ctx_replace (ValVariable (Var (Free x))) (TChannel s) (TChannel t) G) |-p Q2) as Htyp2.
  apply H2 with (1:=Hso3a); [
    assumption
    | assumption
    | contradict HnotinyP; simpl; repeat rewrite in_app_iff; right; right; assumption
    | assumption
    | apply CTXFacts.add_1; reflexivity
    | intros k Heq; subst; inversion Hfnot; subst; specialize (Htoken _ eq_refl); discriminate Htoken
    |
  ].
  assert (
    CTX.eq
    (ctx_replace (Var (Free x)) (TChannel s) (TChannel t) (ctx_add_value w (TChannel t) G))
    (ctx_add_value w (TChannel t) (ctx_replace (Var (Free x)) (TChannel s) (TChannel t) G))
  ) as Heqctx.
  inversion Hfn; subst; simpl; try reflexivity; (rewrite add_replace_comm; [reflexivity|discriminate]).

  apply ctx_equal_part_1 with (2:=Heqctx).
  apply ctx_replace_preserves_partition_left; auto.
  inversion Hfn; subst; simpl; rewrite CTXFacts.add_iff; rewrite CTXFacts.empty_iff; 
    (intros Hin; destruct Hin as [Hin|Hin]; [
      discriminate Hin
      | destruct Hin
    ]).

  apply ctx_add_value_change_type with (3:=Hpart) (2:=Htrans).
  inversion Hfn; subst; constructor.

  apply typed_change_type with (v:=(ValVariable (Var (Free x)))) (rho:=TChannel t) (sigma:=TChannel s) in Htyp2.
  apply ctx_equal_preserves_typed with (1:=Htyp2).

  inversion H as [? ? ? Hwf Hu1|]; subst.
  inversion Hwf as [? ? Heqtypes]; subst.
  inversion Hfn; subst; simpl;
    (apply CTXProperties.subset_antisym; [
      (apply CTXProperties.subset_add_3; [apply CTXFacts.add_2; assumption|]);
      (intros a Hin; destruct a; unfold ctx_replace in Hin; (repeat rewrite CTXFacts.add_iff in Hin || rewrite CTXFacts.remove_iff in Hin);
        destruct Hin as [Hin1 Hin2]; destruct Hin1 as [Hin1|Hin1]; [
          injection Hin1; intros; subst; apply CTXFacts.add_1; reflexivity
          | destruct Hin1 as [Hin1|Hin1]; [
            injection Hin1; intros; subst; contradict Hin2; assumption
            | destruct Hin1 as [Hin1 Hin3]; apply CTXFacts.add_2; assumption
          ]
        ])
      |    apply CTXProperties.subset_add_3; [
        apply CTXFacts.add_2;
          apply CTXFacts.remove_2; [discriminate|];
            apply CTXFacts.add_1; reflexivity
        |
      ];
      intros a Hin; destruct a;
        (destruct (value_dec v0 (ValVariable (Var (Free x)))) as [e|n]; [
          subst; rewrite (Heqtypes _ _ _ Hin Hu1) in *; apply CTXFacts.add_1; reflexivity
          | apply CTXFacts.add_2; apply CTXFacts.remove_2; [contradict n; injection n; intros; subst; reflexivity|]
        ]);
          match goal with
    | [ |- CTX.In _ (CTX.add (?X, ?Y) _) ] => 
      (destruct (value_dec v0 X) as [e2|n2]; [
        subst;          
          assert (t0 = TChannel s); [
          apply partition_wf in Hpart; inversion Hpart as [? ? Heqtypes2 _]; subst; apply (Heqtypes2 X); [
            apply CTXFacts.add_2; assumption
            | apply CTXFacts.add_1; reflexivity
          ]
          | subst
        ];
        apply CTXFacts.add_2; 
          apply CTXFacts.add_2;
            apply CTXFacts.remove_2; [discriminate|];
              assumption
        | apply CTXFacts.add_2;
                    apply CTXFacts.add_2;
                      apply CTXFacts.remove_2; [contradict n; injection n; intros; subst; reflexivity|];
                        assumption
      ])
  end
    ]).

  inversion Hfn; subst; simpl; apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity.
  
  intros Hin.

  apply SO3_free_values_in_context1_aux with (2:=Hso3a) in Hin.
  destruct Hin as [v3 Hin]; destruct Hin as [Hin1 Hin2].
  apply SO3_value_unknown_varx_contra in Hin2; [
    contradict Hin2; reflexivity
    | auto
    | auto
  ].


  (* Var (Free x) <> u *)
  assert (u = u2); [
    destruct (SO3_value_cases_output1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H HlookupvG Htrans Hso3 Hneqxy HnotinyP Hnotinyv HinxG Htoken Hpart HtypP) as [Hu|Hu];
      [ destruct Hu as [Heq1 Heq2]; destruct Heq2 as [Heq2 Heq3]; destruct Heq3 as [Heq3 Hstateless]; subst
        | destruct Hu as [Hu|Hu]; [
          destruct Hu as [Heq1 Hnequ2w]; destruct Hnequ2w as [Hnequ2w Hnequ2x]; subst
          | destruct Hu as [Heq1 Heq2]; destruct Heq2 as [Heq2 Heq3]; subst
      ]
      ]; try reflexivity;
      contradict n; reflexivity
    | subst
  ].

  destruct (value_dec u2 w) as [e2|n2]; [subst|].
  (* u2 = w *)
  inversion Hpart as [? ? ? ? HwfextG Hdisjoint]; subst.
  inversion HwfextG as [? Hfv Heqtypes _]; subst.
  assert (rho1 = TChannel s); [|subst].
  apply (Heqtypes w).
  inversion Hfnot; subst; simpl;
    try solve [
      destruct k; specialize (Htoken _ eq_refl); subst;
        inversion H as [? ? ? ? Hin|]; subst; auto; specialize (Hfv _ _ Hin); inversion Hfv];
    apply CTXFacts.add_1; reflexivity.
  inversion Hfnot; subst; simpl; try apply CTXFacts.add_2; inversion H; subst; try assumption.
  assert (|-st TChannel s) as Hstat.
  specialize (Hdisjoint w (TChannel s)); destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
    contradict Hdisjoint; inversion H; subst; assumption
    | destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
      contradict Hdisjoint
      | assumption
    ]
  ].
  inversion Hfnot; subst; simpl; try solve [apply CTXFacts.add_1; reflexivity]; 
    inversion H as [? ? ? ? Hin|]; subst; auto; specialize (Hfv _ _ Hin); inversion Hfv.
  assert (s = t); [|subst].
  inversion Hstat as [? Heqtypes2|]; subst.
  apply (Heqtypes2 _ _ Htrans).

  assert (
    CTX.eq
    (ctx_replace w (TChannel t) (TChannel t) (ctx_add_value w (TChannel t) G))
    (ctx_add_value w (TChannel t) G)
  ) as Heqctx1.
  apply ResultBasics.ctx_replace_idem.
  inversion H as [? ? ? Hwf Hin|]; subst.
  inversion Hfnot; subst; simpl; try solve [apply CTXFacts.add_1; reflexivity]; assumption.
  eapply ctx_equal_preserves_typed; [|symmetry; apply Heqctx1].

  assert (
    CTX.eq
    (ctx_add_value w (TChannel t) G)
    G
  ) as Heqctx2.
  inversion H as [? ? ? Hwf Hin|]; subst.
  inversion Hfnot; subst; simpl; try reflexivity;
  (intros a; rewrite CTXFacts.add_iff; split; intros Hin2; destruct a; [
    destruct Hin2 as [Hin2|Hin2]; [
      injection Hin2; intros; subst; assumption
      | assumption
    ]
    | right; assumption
  ]).
  eapply ctx_equal_preserves_typed; [|symmetry; apply Heqctx2].

  assert (
    CTX.eq
     (ctx_replace w (TChannel t) (TChannel t) G)
     G
  ) as Heqctx3.
  apply ResultBasics.ctx_replace_idem.
  inversion H; subst; assumption.
  
  assert (
    CTX.eq
    (ctx_add_value w (TChannel t) (ctx_replace w (TChannel t) (TChannel t) G))
    (ctx_add_value w (TChannel t) G)
  ) as Heqctx4.
  inversion Hfnot; subst; simpl; try apply add_cong; rewrite Heqctx3; reflexivity.

  eapply ctx_equal_preserves_typed.
  apply H2 with (1:=Hso3a); auto.

  contradict HnotinyP; simpl; repeat rewrite in_app_iff; right; right; assumption.

  apply CTXFacts.add_2.
  apply CTXFacts.remove_2; [contradict n; injection n; intros; subst; reflexivity|].
  assumption.

  eapply ctx_equal_part_1; [|symmetry; apply Heqctx4].
  eapply ctx_equal_part_1; [|apply Heqctx1].
  apply ctx_replace_preserves_partition_left; auto.
  inversion H; subst; auto.

  rewrite Heqctx4.
  apply Heqctx2.
  

  (* u2 <> w *)
  assert (
    CTX.eq
    (ctx_add_value w rho1 (ctx_replace u2 (TChannel s) (TChannel t) G))
    (ctx_replace u2 (TChannel s) (TChannel t) (ctx_add_value w rho1 G))
  ) as Hctxeq.
  inversion Hfnot; subst; simpl; try reflexivity; apply add_replace_comm; auto.

  eapply ctx_equal_preserves_typed; [|apply Hctxeq].
  apply H2 with (1:=Hso3a); auto.

  contradict HnotinyP; simpl; repeat rewrite in_app_iff; right; right; assumption.

  apply CTXFacts.add_2.
  apply CTXFacts.remove_2; [contradict n; injection n; intros; subst; reflexivity|].
  assumption.

  eapply ctx_equal_part_1; [|symmetry; apply Hctxeq].
  apply ctx_replace_preserves_partition_left; auto.
  inversion H; subst; assumption.
  inversion Hfnot; subst; simpl; try rewrite CTXFacts.add_iff; rewrite CTXFacts.empty_iff; intros Hin;
    try solve [destruct Hin];
      (destruct Hin as [Hin|Hin]; [
        injection Hin; intros; subst
        | destruct Hin
        ]);
  (inversion Hpart as [? ? ? ? HwfextG Hdisjoint]; subst;
  assert (|-st TChannel s) as Hstat; [
    match goal with 
      | [ H : _ |-v ?X : ?Y |- _ ] => 
        specialize (Hdisjoint X Y); destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
          inversion H; subst; contradict Hdisjoint; assumption
          | destruct Hdisjoint as [Hdisjoint | Hdisjoint]; [
            | assumption
          ]
        ]
    end;
    simpl in Hdisjoint; rewrite CTXFacts.add_iff in Hdisjoint; rewrite CTXFacts.empty_iff in Hdisjoint;
      contradict Hdisjoint; left; reflexivity
    |
  ]);
  inversion Hstat as [? Heqtypes2|]; subst; rewrite (Heqtypes2 _ _ Htrans); reflexivity.
Qed.


(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

Lemma subst_r_output_stateless : 
  forall G x y w u v P Q1 s t rho rho1 G',
    G |-v u : TChannel s
    ->
    G |-v v : rho
    ->
    |-st rho
    ->
    (s -- MOut rho --> t)
    ->
    SO3 x y w (u ! v; P) Q1
    ->
    (G' = CTX.remove (v, rho) G \/ G' = G /\ (|-st rho))
    ->
    x <> y
    ->
    ~ In x (free_ids_value w)
    ->
    ~ In y (free_ids_proc (u ! v; P))
    ->
    ~ In y (free_ids_value w)
    ->
    CTX.In (ValVariable (Var (Free x)), rho1) G
    ->
    (forall k : string, w = Token k -> rho1 = TSingleton (Token k))
    ->
    ctx_add_value w rho1 G |-part G (+) ctx_add_value w rho1 CTX.empty
    ->
    ctx_replace u (TChannel s) (TChannel t) G' |-p P
    ->
    (forall (rho0 : type) 
      (Q : proc) (v0 : value),
      SO3 x y v0 P Q 
      ->
      x <> y 
      ->
      ~ In x (free_ids_value v0) 
      ->
      ~ In y (free_ids_proc P) 
      ->
      ~ In y (free_ids_value v0) 
      ->
      CTX.In (ValVariable (Var (Free x)), rho0) (ctx_replace u (TChannel s) (TChannel t) G') 
      ->
      (forall k : string, v0 = Token k -> rho0 = TSingleton (Token k)) 
      ->
      (ctx_add_value v0 rho0 (ctx_replace u (TChannel s) (TChannel t) G') |-part ctx_replace u (TChannel s) (TChannel t) G' (+) ctx_add_value v0 rho0 CTX.empty)
      ->
      ctx_add_value v0 rho0 (ctx_replace u (TChannel s) (TChannel t) G') |-p Q)
    ->
    ctx_add_value w rho1 G |-p Q1.
Proof.
  intros G x y w u v P Q1 s t rho rho1 G' HlookupuG HlookupvG Hstateless Htrans Hso3 HGeqor Hneqxy Hnotinxw HnotinyuvP Hnotinyw HinxG Htoken Hpart HtypP IH.

  assert (G |-p u ! v; P) as HtypfullP.
  eapply TypPrefixOutput with (1:=Htrans); eauto. 

  assert
    (CTX.Subset
      (ctx_replace u (TChannel s) (TChannel t) (CTX.remove (v, rho) G))
      (ctx_replace u (TChannel s) (TChannel t) G)) as Hsub1; [
        unfold ctx_replace;
          apply CTXProperties.subset_add_3; [
            apply CTXFacts.add_1; reflexivity
            | apply CTXProperties.subset_add_2; intros a; destruct a; repeat rewrite CTXFacts.remove_iff; intros Hin; destruct Hin; tauto
          ]
        |
      ].

  inversion HlookupuG as [? ? ? Hwf HinuG|]; subst.
  inversion Hwf as [? Hfv Heqtypes Hdisjoint]; subst.

  assert (u = v -> rho = TChannel s /\ s = t /\ CTX.eq (ctx_replace u (TChannel s) (TChannel t) (CTX.remove (v, rho) G)) G) as Hequv; [
    intros Heq; subst;
      assert (rho = TChannel s); [
        inversion HlookupvG as [? ? ? _ HinvG|]; subst; [ apply (Heqtypes v); auto | pose (Hfv _ _ HinuG) as Hu; inversion Hu]
        | subst; split; auto
      ];
      assert (s = t); [
        inversion Hstateless as [? Heqsess|]; subst; eapply Heqsess; eauto
        | subst; split; auto
      ]; 
      inversion HlookupuG; subst;
        unfold ctx_replace; intros a; destruct a; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff); split; intros Hin;
          (destruct (CTX.E.eq_dec (v, TChannel t) (v0, t0)) as [e|n]; [injection e; intros; subst; tauto|]); tauto
    |
  ].

  assert (
    u<>v
    ->
    CTX.eq (ctx_replace u (TChannel s) (TChannel t) (CTX.remove (v, rho) G)) (CTX.remove (v, rho) (ctx_replace u (TChannel s) (TChannel t) G))) 
  as Hnequv; [
    intros Hneq;
      unfold ctx_replace; intros a; destruct a; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff); split; intros Hin; [
        destruct Hin as [Hin|Hin]; [
          injection Hin; intros; subst; clear Hin; 
            split; [left; reflexivity | contradict Hneq; injection Hneq; intros; subst; reflexivity]
          | tauto
        ]
        | tauto
      ]
    |
  ].

  destruct HGeqor as [HGeqor|HGeqor]; [subst | destruct HGeqor; subst; eapply subst_r_output_stateless_simplified; eauto ].

  assert
    ((u <> (ValVariable (Var (Free x))) /\ v = (ValVariable (Var (Free x))))
      \/ u = (ValVariable (Var (Free x)))
      \/ (u <> (ValVariable (Var (Free x))) /\ v <> (ValVariable (Var (Free x))))) as Hchoices.
  (destruct (value_dec u (ValVariable (Var (Free x)))) as [e4|n4]; [subst|]);
  (destruct (value_dec v (ValVariable (Var (Free x)))) as [e5|n5]; [subst|]); tauto.

  destruct Hchoices as [Hchoices|Hchoices].
  (* =========================================== *)
  clear IH.
  pose (SO3_out_decompose _ _ _ _ _ Hso3 _ _ _ eq_refl) as e; destruct e as [u2 e]; destruct e as [v2 e]; destruct e as [Q2 e]; subst.
  assert (SO3_value x y w u u2) as Hso3v; [eapply SO3_value_output1; eauto|].
  assert (SO3_value x y w v v2) as Hso3vb; [eapply SO3_value_output2; eauto|].
  assert (SO3 x y w P Q2) as Hso3a; [apply SO3_output in Hso3; auto|].
  assert (free_name_or_token w) as Hfnot; [apply (SO3_value_free_name_or_token _ _ _ _ _ Hso3v) |].
  destruct Hchoices as [Hchoices1 Hchoices2]; subst.
  assert (~ In x (free_ids_context (ctx_replace u (TChannel s) (TChannel t) (CTX.remove (ValVariable (Var (Free x)), rho) G)))) as HnotinextG.
  (* note :   Hchoices1 : u <> Var (Free x) for next bit *)
  rewrite free_ids_context_iff; intros Hin.
  destruct Hin as [u0 Hin]; destruct Hin as [rho0 Hin]; destruct Hin as [Hin1 Hin2].
  unfold ctx_replace in Hin1; (repeat rewrite CTXFacts.remove_iff in Hin1 || rewrite CTXFacts.add_iff in Hin1);
    destruct Hin1 as [Hin1|Hin1]; [
      injection Hin1; intros; subst;
        specialize (Hdisjoint x); destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
          specialize (Hdisjoint rho1); contradict Hdisjoint; assumption
          | destruct Hdisjoint as [Hdisjoint1 Hdisjoint2]; specialize (Hdisjoint1 (TChannel s)); specialize (Hdisjoint2 (TChannel s))
        ];
        (destruct u0 as [nm| |var]; subst; simpl in Hin2; try solve [destruct Hin2]; [
          destruct nm as [i|i]
          | destruct var as [i]
        ]; subst; simpl in Hin2; 
        destruct i as [f|b]; subst; simpl in Hin2; try solve [destruct Hin2]; destruct Hin2 as [Hin2|Hin2]; try solve [destruct Hin2]; subst; 
          try solve [contradict Hchoices1; reflexivity];
            try solve [contradict Hdisjoint1; assumption];
              try solve [contradict Hdisjoint2; assumption])
      |
    ].
  destruct Hin1 as [Hin1 Hin3]; destruct Hin1 as [Hin1 Hin4].
  specialize (Hdisjoint x); destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
    specialize (Hdisjoint rho1); contradict Hdisjoint; assumption
    | destruct Hdisjoint as [Hdisjoint1 Hdisjoint2]; specialize (Hdisjoint1 rho0); specialize (Hdisjoint2 rho0)
  ];
  (destruct u0 as [nm| |var]; subst; simpl in Hin2; try solve [destruct Hin2]; [
    destruct nm as [i|i]
    | destruct var as [i]
  ]; subst; simpl in Hin2; 
  destruct i as [f|b]; subst; simpl in Hin2; try solve [destruct Hin2]; destruct Hin2 as [Hin2|Hin2]; try solve [destruct Hin2]; subst;
    try solve [contradict Hchoices1; reflexivity];
      try solve [contradict Hdisjoint1; assumption];
        try solve [contradict Hdisjoint2; assumption]).
  inversion HlookupvG as [? ? ? ? HinxG2|]; subst.
  rewrite (Heqtypes _ _ _ Hin1 HinxG2) in *.
  contradict Hin4; reflexivity.
  rewrite <- SO3_proc_no_free_var with (1:=HtypP) (2:=Hso3a) (3:=HnotinextG).
  eapply TypPrefixOutput; [
    apply Htrans
    | right; assumption
    | apply subst_r_value_alt with (x:=x) (y:=y) (u1:=u); auto; contradict HnotinyuvP; simpl; rewrite in_app_iff; tauto
    | apply subst_r_value_alt with (x:=x) (y:=y) (u1:=(ValVariable (Var (Free x)))); auto; simpl; contradict Hneqxy; destruct Hneqxy as [Hneqxy|Hneqxy]; [assumption|destruct Hneqxy]
    | right; split; [reflexivity | auto]
    | reflexivity
    |
  ].
  assert (u = u2); [|subst].
  destruct (SO3_output_channel1 _ _ _ _ _ Hso3 _ _ _ _ _ _ eq_refl eq_refl) as [Hu|Hu]; auto;
    destruct Hu as [Hu|Hu]; destruct Hu as [Hu1 Hu2]; [ | contradict Hchoices1; assumption].
  inversion Hu1; subst; simpl in *; destruct (string_dec i x); try reflexivity; subst;
    (try solve [contradict Hso3v; apply SO3_value_is_not_rename; auto]);
    (destruct (Hdisjoint x) as [Hu|Hu]; [
      specialize (Hu rho); contradict Hu; inversion HlookupvG; assumption
      | destruct Hu as [Hu3 Hu4]; specialize (Hu3 (TChannel s)); specialize (Hu4 (TChannel s));
        try solve [contradict Hu3; assumption]; try solve [contradict Hu4; assumption]
    ]).

  assert (v2 = w); [|subst].
  apply SO3_value_var_determines_subst_improved in Hso3vb; auto; simpl; contradict Hneqxy; destruct Hneqxy as [|Hneqxy]; [assumption|destruct Hneqxy]. 

  assert (rho = rho1); [|subst].
  inversion HlookupvG as [? ? ? ? HinxG2|]; subst.
  apply (Heqtypes _ _ _ HinxG2 HinxG).

  assert (ctx_replace u2 (TChannel s) (TChannel t) G |-p P) as Htyp2.
  apply partition_typed_weaken_left with (1:=HtypP) (GR:=CTX.add (ValVariable (Var (Free x)), rho1) CTX.empty).
  apply ctx_replace_preserves_partition_left.
  apply CTXFacts.remove_2; [contradict Hchoices1; injection Hchoices1; intros; subst; reflexivity|].
  assumption.
  intros Hin; rewrite CTXFacts.add_iff in Hin; rewrite CTXFacts.empty_iff in Hin; 
    destruct Hin as [Hin|Hin]; [
      injection Hin; intros; subst; contradict Hchoices1; reflexivity
      | destruct Hin
    ].
  apply partition_comm.
  apply partition_add_remove_swap.
  apply partition_comm.
  apply partition_empty.
  inversion HlookupuG; assumption.
  assumption.

  eapply partition_typed_weaken_left with (1:=Htyp2).
  apply ctx_replace_preserves_partition_left; [
    assumption
    |
    | apply Hpart
  ].
  intros Hin.
  inversion Hfnot; subst; simpl in Hin; (try rewrite CTXFacts.add_iff in Hin); rewrite CTXFacts.empty_iff in Hin; 
    try solve [destruct Hin];
  (destruct Hin as [Hin|Hin]; [ | destruct Hin];
  injection Hin; intros; subst;
    (assert (s = t); [ 
    inversion Hstateless as [? Heq|]; subst; eapply Heq; eauto
    | subst; reflexivity])).

  (* =========================================== *)

  eapply subst_r_output_stateless_simplified; eauto.

  clear IH; inversion HlookupvG as [? ? ? _ HinvrhoG |]; subst;  [
    apply partition_typed_weaken_left with (1:=HtypP) (GR:=CTX.add (v, rho) CTX.empty) ; 
      destruct (value_dec u v); [
        subst;
          assert (rho = TChannel s); [
            inversion HlookupvG as [? ? ? _ HinvG|]; subst; [ apply (Heqtypes v); auto | pose (Hfv _ _ HinuG) as Hu; inversion Hu]
            | subst
          ];
          assert (s = t); [
            inversion Hstateless as [? Heqsess|]; subst; eapply Heqsess; eauto
            | subst
          ]; 
          unfold ctx_replace;
            Case "a"%string

        | apply ctx_replace_preserves_partition_left; [
          apply CTXFacts.remove_2; [contradict n; injection n; intros; subst; reflexivity | auto]
          | rewrite CTXFacts.add_iff; rewrite CTXFacts.empty_iff; intros Hin;
            destruct Hin as [Hin|Hin]; [injection Hin; intros; subst; contradict n; reflexivity | destruct Hin]
          | apply ctx_remove_preserves_partition_left_2; [apply CTXFacts.add_1; auto | ];
            apply partition_comm; apply partition_add_idem_stateless; auto; [
              apply partition_comm; apply partition_empty; auto
              | eapply Hfv; eauto
            ]
        ]
      ];
      eapply ctx_equal_part with (G1:=G) (GL1:=G); [| | | reflexivity]; [
        apply partition_comm; apply partition_add_idem_stateless; auto; [
          apply partition_comm; apply partition_empty; auto
          | eapply Hfv; eauto
        ]
        |
        |
      ]; 
      intros a; destruct a; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff); split; intros Hin; 
        (destruct (CTX.E.eq_dec (v, TChannel t) (v0, t0)) as [e|n]; [injection e; intros; subst; tauto|]); tauto

    | apply ctx_equal_preserves_typed with (1:=HtypP); 
        unfold ctx_replace;
          assert ((u, TChannel s) <> (ValToken k, TSingleton k)); [discriminate|];
            assert ((u, TChannel t) <> (ValToken k, TSingleton k)); [discriminate|];
              intros a; destruct a; split; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff); intros Hin; [
                tauto
                | destruct Hin; [
                  tauto
                  | assert ((ValToken k, TSingleton k) <> (v, t0)); [
                    intros Hin; injection Hin; intros; subst; assert (free_value k) as Hu; [eapply Hfv; destruct H2; eauto|inversion Hu]
                    |
                  ]; tauto
                ]
              ]
  ].


  intros rho0 Q v0 Hso3x0y0 Hneqx0y0 Hnotinx0v0 Hnotiny0P Hnotiny0v0 Hinx0rho0 Htokenrho0 Hpartv0.
  assert (free_name_or_token v0) as Hfnot; [apply (SO3_free_name_or_token _ _ _ _ _ Hso3x0y0)|].

  assert (ctx_add_value v0 rho0 (ctx_replace u (TChannel s) (TChannel t) (CTX.remove (v, rho) G)) |-p Q) as HtypQ.
  apply IH with (1:=Hso3x0y0); auto; clear IH.

  (* ==================================== *)
  destruct Hchoices as [Hchoices|Hchoices].
  subst.
  unfold ctx_replace in Hinx0rho0; rewrite CTXFacts.add_iff in Hinx0rho0; rewrite CTXFacts.remove_iff in Hinx0rho0;
    destruct Hinx0rho0 as [Hinx0rho0|Hinx0rho0]; [
      injection Hinx0rho0; intros; subst; apply CTXFacts.add_1; reflexivity
      |
    ].
  destruct Hinx0rho0 as [Hu1 Hu2].
  inversion HlookupuG as [? ? ? ? Hin1|]; subst.
  pose (Heqtypes _ _ _ Hu1 Hin1) as Heq; rewrite Heq in *; clear Heq.
  contradict Hu2; reflexivity.

  destruct Hchoices as [n4 n5].
  apply CTXFacts.add_2.
  apply CTXFacts.remove_2; [contradict n4; injection n4; intros; subst; reflexivity|].
  apply CTXFacts.remove_2; [contradict n5; injection n5; intros; subst; reflexivity|].
  assert (rho0 = rho1); [|subst].
  assert (CTX.In (ValVariable (Var (Free x)), rho1) (ctx_replace u (TChannel s) (TChannel t) G)) as Hin2.
  apply CTXFacts.add_2.
  apply CTXFacts.remove_2; [contradict n4; injection n4; intros; subst; reflexivity|].
  assumption.
  apply partition_wf_left in Hpartv0; inversion Hpartv0 as [? ? Heqtypes2]; subst.
  apply (Heqtypes2 _ _ _ Hinx0rho0 Hin2).
  unfold ctx_replace in Hinx0rho0; rewrite CTXFacts.add_iff in Hinx0rho0; rewrite CTXFacts.remove_iff in Hinx0rho0;
    destruct Hinx0rho0 as [Hinx0rho0|Hinx0rho0]; [
      injection Hinx0rho0; intros; subst; contradict n4; reflexivity
      | destruct Hinx0rho0; assumption
    ].

  (* ==================================== *)

  destruct (value_dec u v) as [e|n]; [subst|].
  specialize (Hequv eq_refl); destruct Hequv as [Heq Hequv]; subst; destruct Hequv as [Heq Hequv]; subst.
  apply ctx_equal_part_2 with (GL1:=G); [|symmetry; assumption].
  apply ctx_equal_part_1 with (G1:=ctx_add_value v0 rho0 G).
  inversion Hfnot; subst; simpl; [ | | inversion HlookupvG; subst; apply partition_empty; auto ];
    (apply ctx_equal_part with (1:=Hpartv0); simpl; [
      apply add_cong; rewrite ctx_replace_idem; auto
      | rewrite ctx_replace_idem; auto
      | 
    ]; reflexivity).
  assert (CTX.eq (ctx_replace v (TChannel t) (TChannel t) (CTX.remove (v, TChannel t) G)) G) as Hequvrem; [
    unfold ctx_replace; intros a; destruct a; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff); split; intros Hin;
      (destruct (CTX.E.eq_dec (v, TChannel t) (v1, t0)) as [e|n]; [injection e; intros; subst; tauto | tauto])
        |
      ].
  inversion Hfnot; subst; simpl; try apply add_cong; rewrite Hequvrem; reflexivity.

  clear Hequv; specialize (Hnequv n).
  apply ctx_equal_part_1 with (G1:=ctx_add_value v0 rho0 (CTX.remove (v, rho) (ctx_replace u (TChannel s) (TChannel t) G))); [
    | inversion Hfnot; subst; simpl; (try apply add_cong); rewrite Hnequv; reflexivity
  ].
  apply ctx_equal_part_2 with (GL1:=CTX.remove (v, rho) (ctx_replace u (TChannel s) (TChannel t) G)); [
    | rewrite Hnequv; reflexivity
  ].
  destruct (value_dec v0 v) as [e0|n0]; [subst|].
  assert (rho0 = rho); [|subst]; [
    apply partition_wf in Hpartv0; inversion Hpartv0 as [? _ Heqtypes2 _]; subst;
      inversion Hfnot; subst; simpl in *; 
        try solve [
          eapply (Heqtypes2); [
            apply CTXFacts.add_1; [reflexivity ]
            | apply CTXFacts.add_2;
              apply CTXFacts.add_2;
                (apply CTXFacts.remove_2; [intros Hin; injection Hin; intros; subst; contradict n; reflexivity | inversion HlookupvG; subst; assumption])
          ]
        ];
        destruct k; rewrite (Htokenrho0 _ eq_refl); inversion HlookupvG as [? ? ? ? Hin | ]; subst; [ | reflexivity]; pose (Hfv _ _ Hin) as Hu; inversion Hu
    |
  ].
  apply ctx_equal_part_1 with (G1:=ctx_add_value v rho (ctx_replace u (TChannel s) (TChannel t) G)); [
    | 
  ].
  inversion Hfnot; subst; simpl; try (apply ctx_remove_preserves_partition_left_2; [apply CTXFacts.add_1; reflexivity | assumption]).
  apply ctx_equal_part_2 with (GL1:=ctx_replace u (TChannel s) (TChannel t) G); [
    assumption
    | 
  ].
  apply partition_wf_left in Hpartv0.
  inversion Hpartv0 as [? Hfv2 _ _]; subst.
  assert (~ CTX.In (ValToken k, rho) (ctx_replace u (TChannel s) (TChannel t) G)) as Hnotink.
  intros Hin; specialize (Hfv2 _ _ Hin); inversion Hfv2.
  unfold ctx_replace in * ; intros a; destruct a; (repeat rewrite CTXFacts.add_iff in * || rewrite CTXFacts.remove_iff in * ); 
    split; intros Hin; [
      destruct Hin as [Hin|Hin]; [
        injection Hin; intros; subst; clear Hin;
          split; [ left; reflexivity | pose (Hfv _ _ HinuG) as Hu; inversion Hu; discriminate]
        | destruct Hin as [Hin1 Hin2]; split; [tauto | pose (Hfv _ _ Hin1) as Hu; inversion Hu; discriminate]
      ]
      | tauto
    ].
  inversion Hfnot; subst; simpl; try solve [rewrite add_remove_idem; reflexivity].
  unfold ctx_replace in * ; intros a; destruct a; (repeat rewrite CTXFacts.add_iff in * || rewrite CTXFacts.remove_iff in * ); 
    split; intros Hin; [
      destruct Hin as [Hin|Hin]; [
        injection Hin; intros; subst; clear Hin;
          split; [ left; reflexivity | pose (Hfv _ _ HinuG) as Hu; inversion Hu; discriminate]
        | destruct Hin as [Hin1 Hin2]; split; [tauto | pose (Hfv _ _ Hin1) as Hu; inversion Hu; discriminate]
      ]
      | tauto
    ].
  apply ctx_equal_part_1 with (G1:=CTX.remove (v, rho) (ctx_add_value v0 rho0 (ctx_replace u (TChannel s) (TChannel t) G))).
  apply ctx_remove_preserves_partition_left; [|assumption].
  inversion Hfnot; simpl; subst; 
    try solve [
      rewrite CTXFacts.add_iff; rewrite CTXFacts.empty_iff; intros Hin; destruct Hin as [Hin|Hin]; [
        injection Hin; intros; subst; contradict n0; reflexivity
        | inversion Hin
      ]
    ].
  rewrite CTXFacts.empty_iff; auto.
  rewrite add_value_comm; auto; reflexivity.

  clear IH.

  inversion HlookupvG as [? ? ? _ HinvG | ]; subst; [
    |   eapply partition_typed_weaken_left with (1:=HtypQ);
      eapply ctx_equal_part_2; [
        apply partition_empty; inversion Hpartv0; assumption
        |
      ];
      inversion Hfnot; subst; simpl;
        symmetry; 
          match goal with
            | [ |- CTX.eq (ctx_replace _ _ _ _) _ ] => idtac
            | [ |- _ ] => apply add_cong
          end;
          (apply CTXProperties.subset_antisym; [
            assumption
            |
              unfold ctx_replace;
                apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity | ];
                  apply CTXProperties.subset_add_2;
                    intros a; destruct a; (repeat rewrite CTXFacts.remove_iff); intros Hin; destruct Hin as [Hin Hneq]; 
                      split; [
                        split; [
                          assumption
                          | intros Heq; injection Heq; intros; subst; clear Heq; pose (Hfv _ _ Hin) as Hu; inversion Hu
                        ]
                        | assumption
                      ]
          ])
  ].

  assert (free_value v) as Hfvv; [apply (Hfv _ _ HinvG) | ].

  assert
    (v0 = v -> 
      CTX.eq
      (ctx_add_value v0 rho0 (ctx_replace u (TChannel s) (TChannel t) (CTX.remove (v, rho) G))) 
      (ctx_add_value v0 rho0 (ctx_replace u (TChannel s) (TChannel t) G))) as Heqvovimp; 
    [
      intros Heqv0v; subst;
        assert (rho0 = rho); [
          apply partition_wf in Hpartv0; inversion Hpartv0 as [? _ Heqtypes2 _]; subst; apply (Heqtypes2 v); clear Heqtypes2; [
            inversion Hfvv; subst; inversion Hfnot; subst; simpl; apply CTXFacts.add_1; reflexivity
            | destruct (value_dec u v) as [e|n]; [subst|]; [
              specialize (Hequv eq_refl); destruct Hequv as [Heq Hequv]; subst; destruct Hequv as [Heq Hequv]; subst;
                (unfold ctx_replace; inversion Hfvv; subst; inversion Hfnot; subst; simpl; apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity)
              | unfold ctx_replace; inversion Hfvv; subst; inversion Hfnot; subst; simpl; 
                (apply CTXFacts.add_2; apply CTXFacts.add_2; apply CTXFacts.remove_2; [
                  contradict n; injection n; intros; subst; reflexivity
                  | assumption
                ])
            ]
          ]
          | subst
        ]; 
        (inversion Hfnot; subst; simpl;
          (try solve [inversion Hfvv]);
          try solve [
            ((apply CTXProperties.subset_antisym; [
              (apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity | ]); 
              (apply CTXProperties.subset_add_2; assumption)
              |
            ];
            (apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity | ]);
            unfold ctx_replace; apply CTXProperties.subset_add_3; [apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity | ];
              clear Hpartv0; intros a; destruct a; rewrite CTXFacts.remove_iff; intros Hin; destruct Hin as [Hin Heq];
                match goal with 
                  | [ |- CTX.In _ (CTX.add (?V, _) _) ] => 
                    destruct (value_dec v V) as [e0|n0]; [subst|]; [
                      assert (t0 = rho); [apply (Heqtypes _ _ _ Hin HinvG) | subst];
                        apply CTXFacts.add_1; reflexivity
                      |
                    ]
                end;
                apply CTXFacts.add_2; apply CTXFacts.add_2; apply CTXFacts.remove_2; [assumption|];
                  apply CTXFacts.remove_2; [
                    contradict n0; injection n0; intros; subst; reflexivity
                    | assumption
                  ]))
          ])
      |
    ].

  assert
    (u = v -> 
      CTX.eq
      (ctx_replace u (TChannel s) (TChannel t) (CTX.remove (v, rho) G))
      (ctx_replace u (TChannel s) (TChannel t) G)
    ) as Hequv2; [
      intros Heq; subst; 
        specialize (Hequv eq_refl); destruct Hequv as [Heq Hequv]; subst; destruct Hequv as [Heq Hequv]; subst;
          rewrite Hequv; rewrite ctx_replace_idem; [reflexivity | assumption]
      |
    ].

  assert
    (v0 <> v -> u <> v ->
      CTX.eq
        (ctx_add_value v0 rho0 (ctx_replace u (TChannel s) (TChannel t) (CTX.remove (v, rho) G)))
        (CTX.remove (v, rho) (ctx_add_value v0 rho0 (ctx_replace u (TChannel s) (TChannel t) G)))
    ) as Hneqv0vuv; [
      clear Heqvovimp Hequv2 Hequv Hnequv
      |
    ].
  intros Hneqv0v Hnequv.  
  apply CTXProperties.subset_antisym; [
    inversion Hfnot; simpl; subst;
      match goal with
        | [ |- CTX.Subset (ctx_replace _ _ _ _) _ ] => idtac
        | [ |- _ ] => apply CTXProperties.subset_add_3; [
          apply CTXFacts.remove_2; [contradict Hneqv0v; injection Hneqv0v; intros; subst; reflexivity|];
            apply CTXFacts.add_1; reflexivity  
          | 
        ]
      end;
      (apply CTXProperties.subset_add_3; [
        apply CTXFacts.remove_2; [contradict Hnequv; injection Hnequv; intros; subst; reflexivity|];
          solve [(apply CTXFacts.add_1; reflexivity) || (apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity)]
        |
      ]);
      try solve [unfold ctx_replace; intros a; destruct a; (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff); intros Hin; tauto]
    | inversion Hfnot; subst; simpl; unfold ctx_replace; intros a; destruct a; 
      (repeat rewrite CTXFacts.add_iff || rewrite CTXFacts.remove_iff); intros Hin;
      try solve [
        destruct Hin as [Hin1 Hin2]; destruct Hin1 as [Hin1|Hin1]; [
          injection Hin1; injection Hin1; intros; subst; clear Hin1; left; reflexivity
          | destruct Hin1 as [Hin1|Hin1]; [
            injection Hin1; injection Hin1; intros; subst; clear Hin1; right; left; reflexivity
            | destruct Hin1 as [Hin1 Hin3]; tauto
          ]
        ]
      ];
      destruct Hin as [Hin1 Hin2]; destruct Hin1 as [Hin1|Hin1]; [
        injection Hin1; injection Hin1; intros; subst; clear Hin1; left; reflexivity
        | destruct Hin1 as [Hin1 Hin3]; tauto
      ]
  ].

  destruct (value_dec v0 v) as [e|n]; [
    eapply partition_typed_weaken_left with (1:=HtypQ); 
      subst; eapply ctx_equal_part_2; [ | symmetry; apply Heqvovimp; reflexivity]; apply partition_empty; inversion Hpartv0; assumption; reflexivity
    | destruct (value_dec u v) as [e2|n2]; [subst|]; [
      eapply partition_typed_weaken_left with (1:=HtypQ); 
        specialize (Hequv eq_refl); specialize (Hequv2 eq_refl);
          eapply ctx_equal_part_2; [apply partition_empty; inversion Hpartv0; assumption|];
            inversion Hfnot; subst; simpl; try solve [rewrite Hequv2; reflexivity]; solve [apply add_cong; rewrite Hequv2; reflexivity]
      | SCase "incomplete"%string
    ]
  ].


  specialize (Hneqv0vuv n n2).
  eapply partition_typed_weaken_left with (1:=HtypQ).
  eapply ctx_equal_part_2; [|rewrite Hneqv0vuv; reflexivity].
  apply ctx_remove_preserves_partition_left_2; [|].
  apply CTXFacts.add_1; reflexivity.
  apply partition_comm.
  apply partition_add_idem_stateless; auto.
  apply partition_comm.
  apply partition_empty.
  apply partition_wf in Hpartv0; assumption.
  apply LContext; auto.
  apply partition_wf in Hpartv0; assumption.
  inversion Hfnot; subst; simpl;
    match goal with
      | [ |- CTX.In _ (ctx_replace _ _ _ _) ] => idtac
      | [ |- _ ] => apply CTXFacts.add_2
    end;
    apply CTXFacts.add_2;
      apply CTXFacts.remove_2; auto;
        contradict n2; injection n2; intros; subst; reflexivity.
Qed.

(* ============================================================================= *)
(* ============================================================================= *)
(* ============================================================================= *)

Lemma partition_left_add : 
  forall G GL GR u rho,
    G |-part GL (+) GR
    ->
    CTX.add (u, rho) G |-part G (+) CTX.add (u, rho) CTX.empty
    ->
    CTX.add (u, rho) GL |-part GL (+) CTX.add (u, rho) CTX.empty.
Proof.
  intros G GL GR u rho Hpart Hextpart.

  assert (CTX.In (u, rho) GL -> |-st rho) as Hstateless; [
    intros Hin;
      inversion Hextpart as [? ? ? _ _ Hdisjoint]; subst;
        specialize (Hdisjoint u rho); destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
          contradict Hdisjoint; inversion Hpart as [? ? ? Heq _ _]; subst; rewrite Heq; rewrite CTXFacts.union_iff; left; assumption
          | destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
            contradict Hdisjoint; apply CTXFacts.add_1; reflexivity
            | assumption
          ]
        ]
    |
  ].
  
  apply part_inter with (G':=CTX.add (u, rho) GL) in Hextpart; [
    | inversion Hpart as [? ? ? Heq _ _]; subst; rewrite Heq; intros a Hin;
      rewrite CTXFacts.add_iff in Hin; destruct Hin as [Hin|Hin]; [
        apply CTXFacts.add_1; assumption
        | apply CTXFacts.add_2; rewrite CTXFacts.union_iff; left; assumption
      ]
  ].
  apply partition_wf in Hextpart.
  apply partition_empty in Hextpart.
  destruct (CTXProperties.In_dec (u, rho) GL) as [i|n].
  apply ctx_equal_part_2 with (GL1:=CTX.add (u, rho) GL); [
    apply partition_comm; apply partition_add_idem_stateless; [
      apply partition_comm; assumption
      | apply LContext; [
        eapply partition_wf in Hextpart; assumption
        | apply CTXFacts.add_1; reflexivity
      ]
      | eapply partition_wf in Hextpart; inversion Hextpart as [? Hfv _ _]; subst; 
        apply (Hfv u rho);
          apply CTXFacts.add_2; assumption
      | apply Hstateless; assumption
    ]
    | apply CTXProperties.add_equal; assumption
  ].
  apply partition_comm; eapply ctx_equal_part_3; [
    apply partition_add_remove_swap; [
      apply partition_comm; apply Hextpart
      | apply CTXFacts.add_1; reflexivity
    ]
    |
  ].
  apply CTXProperties.subset_antisym; [
    intros a Hin; rewrite CTXFacts.remove_iff in Hin; rewrite CTXFacts.add_iff in Hin; destruct Hin as [Hin1 Hin2]; destruct Hin1 as [Hin1|Hin1]; [
      contradict Hin2; assumption
      | assumption
    ]
    | intros a Hin; apply CTXFacts.remove_2; [intros Heq; subst; contradict n; assumption|];
      apply CTXFacts.add_2; assumption
  ].
Qed.

(* ============================================================================= *)

Lemma ctx_union_swap_aux : 
  forall n G GL1 GL2 GR,
    n = CTX.cardinal GL2
    ->
    CTX.union GL1 GL2 |-part GL1 (+) GL2
    -> 
    G |-part CTX.union GL1 GL2 (+) GR
    -> 
    G |-part GL1 (+) CTX.union GL2 GR.
Proof.
  intros n; induction n; intros G GL1 GL2 GR Heqn Hpartunion Hpart.
  symmetry in Heqn.
  apply CTXProperties.cardinal_inv_1 in Heqn.
(*  unfold CTX.Empty in Heqn. *)
  eapply ctx_equal_part_2.
  eapply ctx_equal_part_3.
  apply Hpart.
  symmetry.
  apply CTXProperties.empty_union_1; assumption.
  apply CTXProperties.empty_union_2; assumption.

  symmetry in Heqn.
  destruct (CTXProperties.cardinal_inv_2 Heqn) as [a Hin]; destruct a as [v rho].
  set (GL2':=CTX.remove (v, rho) GL2).

  assert (
    CTX.eq 
    (CTX.union GL2 GR)
    (CTX.union GL2' (CTX.add (v, rho) GR))
  ) as Hctxeq.
  apply CTXProperties.subset_antisym; [
    apply CTXProperties.union_subset_3; [
      intros a Hin2; destruct (CTX.E.eq_dec a (v, rho)) as [i3|n3]; [
        subst; apply CTXFacts.union_3; apply CTXFacts.add_1; reflexivity
        | apply CTXFacts.union_2; apply CTXFacts.remove_2; [auto|auto]
      ]
      | intros a Hin2; apply CTXFacts.union_3; apply CTXFacts.add_2; assumption
    ]
    | apply CTXProperties.union_subset_3; [
      intros a Hin2; unfold GL2' in Hin2; rewrite CTXFacts.remove_iff in Hin2; destruct Hin2 as [Hin2 Hin3]; apply CTXFacts.union_2; assumption
      | intros a Hin2; rewrite CTXFacts.add_iff in Hin2; destruct Hin2 as [Hin2|Hin2]; [
        subst; apply CTXFacts.union_2; assumption
        | apply CTXFacts.union_3; assumption
      ]
    ]
  ].

  eapply ctx_equal_part_3; [|symmetry; apply Hctxeq].

  inversion Hpart as [? ? ? Heq Hwf Hdisjoint]; subst.

  destruct (CTXProperties.In_dec (v, rho) GL1) as [i1|n1].

  assert (|-st rho) as Hstateless; [
    inversion Hpartunion as [? ? ? ? ? Hstat]; subst;
      specialize (Hstat v rho); destruct Hstat as [Hstat|Hstat]; [
        contradict Hstat; assumption
        | destruct Hstat as [Hstat|Hstat]; [
          contradict Hstat; assumption
          | assumption
        ]
      ]
    |
  ].
  assert (CTX.In (v, rho) G) as Hin3; [rewrite Heq; apply CTXFacts.union_2; apply CTXFacts.union_2; assumption |].
  assert (
    CTX.eq
    (CTX.union GL1 GL2')
    (CTX.union GL1 GL2)
  ) as Hctxeq2; [
    apply CTXProperties.subset_antisym; [
      apply CTXProperties.union_subset_3; [
        apply CTXProperties.union_subset_1
        | unfold GL2'; intros a Hin2; rewrite CTXFacts.remove_iff in Hin2; destruct Hin2 as [Hin2 Hin4]; apply CTXFacts.union_3; assumption
      ]
      | apply CTXProperties.union_subset_3; [
        apply CTXProperties.union_subset_1
        | unfold GL2'; intros a Hin2; destruct (CTX.E.eq_dec a (v, rho)) as [e3|n3]; [
          subst; apply CTXFacts.union_2; assumption
          | apply CTXFacts.union_3; apply CTXFacts.remove_2; [auto|assumption]
        ]
      ]
    ]
    |
  ].
  apply IHn; [
    unfold GL2'; rewrite <- (CTXProperties.remove_cardinal_1 Hin) in Heqn; injection Heqn; intros; subst; reflexivity
    | eapply ctx_equal_part_1; [|symmetry; apply Hctxeq2];
      apply partition_comm;
        unfold GL2';
          apply ctx_remove_preserves_partition_left_2; [
            assumption
            | apply partition_comm; assumption
          ]
    | apply partition_comm; apply partition_add_idem_stateless; auto; [
      apply partition_comm; eapply ctx_equal_part_2; [|symmetry; apply Hctxeq2]; assumption
      | apply LContext; auto
      | inversion Hwf as [? Hfv _ _]; subst; apply Hfv with (1:=Hin3)
    ]
  ].


  assert (
    CTX.eq (CTX.remove (v, rho) (CTX.union GL1 GL2)) (CTX.union GL1 GL2')
  ) as Heqctx3; [
    apply CTXProperties.subset_antisym; [
      intros a Hin2; rewrite CTXFacts.remove_iff in Hin2; rewrite CTXFacts.union_iff in Hin2; 
        destruct Hin2 as [Hin2 Hin3]; destruct Hin2 as [Hin2|Hin2]; [
          apply CTXFacts.union_2; assumption
          | apply CTXFacts.union_3; apply CTXFacts.remove_2; assumption
        ]
      | apply CTXProperties.union_subset_3; intros a Hin2; destruct (CTX.E.eq_dec a (v, rho)) as [e3|n3]; [
        subst; contradict n1; assumption
        | apply CTXFacts.remove_2; [
          auto
          | apply CTXFacts.union_2; assumption
        ]
        | subst; unfold GL2' in Hin2; rewrite CTXFacts.remove_iff in Hin2; destruct Hin2 as [Hin2 Hin3]; contradict Hin3; reflexivity
        | apply CTXFacts.remove_2; [
          auto
          | unfold GL2' in Hin2; rewrite CTXFacts.remove_iff in Hin2; destruct Hin2 as [Hin2 Hin3]; apply CTXFacts.union_3; assumption
        ]
      ]
    ]
    |
  ].

  apply IHn; [
    unfold GL2'; rewrite <- (CTXProperties.remove_cardinal_1 Hin) in Heqn; injection Heqn; intros; subst; reflexivity
    | apply partition_comm; unfold GL2'; 
      eapply ctx_equal_part_1; [ | apply Heqctx3]; 
        apply ctx_remove_preserves_partition_left; [ | apply partition_comm]; auto
    | apply partition_comm; 
      eapply ctx_equal_part_3; [
        apply partition_add_remove_swap; [
          apply partition_comm; apply Hpart
          | apply CTXFacts.union_3; assumption
        ]
        | apply Heqctx3
      ]
  ].
Qed.


Lemma ctx_union_swap : 
  forall G GL1 GL2 GR,
    CTX.union GL1 GL2 |-part GL1 (+) GL2
    -> 
    G |-part CTX.union GL1 GL2 (+) GR
    -> 
    G |-part GL1 (+) CTX.union GL2 GR.
Proof.
  intros G GL1 GL2 GR Hpartunion Hpart.
  eapply ctx_union_swap_aux; [
    reflexivity
    | assumption
    | assumption
  ].
Qed.

(* ============================================================================= *)

Lemma ctx_add_partition : 
  forall v rho G GL GR,
    G |-part GL (+) GR
    ->
    CTX.add (v, rho) G |-part G (+) CTX.add (v, rho) CTX.empty
    ->
    CTX.add (v, rho) G |-part CTX.add (v, rho) GL (+) GR.
Proof.
  intros v rho G GL GR Hpartunion Hpartadd.

  inversion Hpartunion as [? ? ? Heq _ _]; subst.
  assert (CTX.eq G (CTX.union GR GL)) as Heq2; [rewrite Heq; intros a; repeat rewrite CTXFacts.union_iff; tauto|].

  assert (
    CTX.eq
    (CTX.add (v, rho) GL)
    (CTX.union GL (CTX.add (v, rho) CTX.empty))
  ) as Heqctx; [
    apply CTXProperties.subset_antisym; [
      apply CTXProperties.subset_add_3; [apply CTXFacts.union_3; apply CTXFacts.add_1; reflexivity|];
        apply CTXProperties.union_subset_1
      |
    ]
    |
  ].
  apply CTXProperties.union_subset_3; [
    apply CTXProperties.subset_add_2; reflexivity
    | apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|];
      apply CTXProperties.subset_empty
  ].

  apply partition_comm.
 
  eapply ctx_equal_part_3; [|symmetry; apply Heqctx]; apply ctx_union_swap; [
    apply partition_comm; eapply ctx_equal_part_1; [
      apply Hpartunion
      | assumption
    ]
    | eapply ctx_equal_part_2; [|apply Heq2]; assumption
  ].
Qed.

(* ============================================================================= *)

Lemma SO3_value_ctx_in : 
  forall G x y w u v rho sigma,
    SO3_value x y w u v
    ->
    x <> y
    ->
    ~ In y (free_ids_value u) 
    ->
    ~ In y (free_ids_value w) 
    -> 
    CTX.In (u, rho) G
    ->
    G |-wf 
    ->
    free_value v
    -> 
    CTX.In (ValVariable (Var (Free x)), sigma) G
    ->
    CTX.In (v, rho) (ctx_add_value w sigma G).
Proof.
  intros G x y w u v rho sigma Hso3v Hneqxy Hnotinyu Hnotinyw HinuG Hwf Hfvv HinxG.
  
  assert (free_name_or_token w) as Hfnot; [apply (SO3_value_free_name_or_token _ _ _ _ _ Hso3v) |].

  destruct (SO3_value_cases _ _ _ _ _ Hso3v) as [Hu|Hu]; [
    subst; inversion Hfnot; subst; simpl; try apply CTXFacts.add_2; assumption
    | destruct Hu as [Hu|Hu]; [
      destruct Hu as [Hu1 Hu2]
      | destruct Hu as [Hu1 Hu2]; subst; 
        assert (rho = sigma); [
          inversion Hwf as [? ? Heqtypes _]; subst; apply (Heqtypes _ _ _ HinuG HinxG)
          | 
        ];
        subst; inversion Hfvv; subst; simpl; apply CTXFacts.add_1; reflexivity
    ]
  ].
  destruct (value_dec u v) as [e|n]; [
    rewrite e in *; inversion Hfnot; simpl; try apply CTXFacts.add_2; assumption
    |
  ].
  assert (In x (free_ids_value u)); [
    rewrite <- Hu2 in n; apply  freeid_rename_value_cases_contra2 in n; assumption
    |
  ].
  assert (u = ValVariable (Var (Free x))) as Hequx; [
    |
  ].
  inversion Hwf as [? _ _ Hdisjoint]; subst.
  destruct u as [nm| |var]; subst; simpl in *; try solve [destruct H]; [
    destruct nm as [i|i]
    | destruct var as [i]
  ]; subst; simpl in *; 
  destruct i as [f|b]; subst; simpl in *; try solve [destruct H]; 
    destruct H; try solve [destruct H]; subst; try solve [reflexivity];
  (specialize (Hdisjoint x); destruct Hdisjoint as [Hv|Hv]; [
    specialize (Hv sigma); contradict Hv; auto
    | destruct Hv as [Hv1 Hv2]; specialize (Hv1 rho); specialize (Hv2 rho); try solve [contradict Hv1; auto]; try solve [contradict Hv2; auto]
  ]).
  clear Hu2; subst; apply SO3_value_var_determines_subst_improved in Hso3v; auto; subst.
  assert (rho = sigma); [
    inversion Hwf as [? ? Heqtypes _]; subst; apply (Heqtypes _ _ _ HinuG HinxG)
    | 
  ];
  subst; inversion Hfvv; subst; simpl; apply CTXFacts.add_1; reflexivity.
Qed.

(* ============================================================================= *)

Lemma subst_r : 
  forall G P,
    G |-p P
    ->
    forall x rho y Q v,
      SO3 x y v P Q
      ->
      x <> y
      ->
      ~ In x (free_ids_value v)
      ->
      ~ In y (free_ids_proc P)
      ->
      ~ In y (free_ids_value v)
      ->
      CTX.In (ValVariable (Var (Free x)), rho) G
      ->
      (forall k, v = Token k -> rho = TSingleton (Token k))
      ->
      ctx_add_value v rho G |-part G (+) ctx_add_value v rho CTX.empty
      ->
      ctx_add_value v rho G |-p Q.  
Proof.
  intros G P Htyp; induction Htyp; intros x rho1 y Q1 w Hso3 Hneqxy Hnotinxv HnotinyP Hnotinyv HinxG Htoken Hpart; subst.

  Case "input"%string.
  eapply subst_r_input_new; eauto.
  eapply TypPrefixInput; eauto.


  Case "output"%string.
  rename H2 into HlookupvG.
  assert (G |-p u ! v ; P) as HtypuvP; [eapply TypPrefixOutput; eauto | ].
  assert (v = w -> |-st rho) as Heqvwstateless; [
    intros Heq; subst;
      pose (SO3_out_decompose _ _ _ _ _ Hso3 _ _ _ eq_refl) as e; destruct e as [u2 e]; destruct e as [v2 e]; destruct e as [Q2 e]; subst;
        assert (SO3_value x y w u u2) as Hso3v; [eapply SO3_value_output1; eauto|];
          assert (SO3_value x y w w v2) as Hso3vb; [eapply SO3_value_output2; eauto|];
            assert (free_name_or_token w) as Hfnot; [apply (SO3_value_free_name_or_token _ _ _ _ _ Hso3v) |];
              destruct (free_name_or_token_split _ Hfnot) as [Hfn|Htok]; [
                assert (CTX.In (w, rho) G) as Hin1a; [
                  inversion Hfn; subst; inversion HlookupvG; subst; assumption
                  |
                ];
                assert (CTX.In (w, rho) (ctx_add_value w rho1 G)) as Hin1; [
                  inversion Hfn; subst; simpl; apply CTXFacts.add_2; apply Hin1a
                  |
                ];
                assert (CTX.In (w, rho1) (ctx_add_value w rho1 G)) as Hin2; [
                  inversion Hfn; subst; simpl; apply CTXFacts.add_1; reflexivity
                  | 
                ];
                assert (rho = rho1); [ 
                  pose (partition_wf _ _ _ Hpart) as Hu; inversion Hu as [? ? Heqtypes]; subst; apply (Heqtypes _ _ _ Hin1 Hin2)
                  | subst
                ];
                inversion Hpart as [? ? ? ? ? Hdisjoint]; subst;
                  (specialize (Hdisjoint w rho1); destruct Hdisjoint as [Hnotin | Hdisjoint]; [
                    contradict Hnotin; assumption
                    | destruct Hdisjoint as [Hnotin | Hdisjoint]; [
                      contradict Hnotin; inversion Hfn; subst; apply CTXFacts.add_1; reflexivity
                      | assumption
                    ]
                  ])
                | destruct Htok as [k Heq]; subst; apply token_lookup in HlookupvG; subst; right; constructor
              ]
    |
  ].
  set (IHHtypspecialized:=fun rho0 => IHHtyp x rho0 y).
  destruct (value_dec v w) as [e|n]; [
    specialize (Heqvwstateless e); eapply subst_r_output_stateless with (15:=IHHtypspecialized); eauto 
    | 
  ].
  assert ((v = ValVariable (Var (Free x)) /\ In w (free_values_proc (u ! v; P))) -> |-st rho) as Hfreewstateless.
  intros Hin; destruct Hin as [? Hin]; subst.
  apply free_values_in_context_1 in HtypuvP.
  specialize (HtypuvP w Hin).
  destruct HtypuvP as [sigma HtypuvP].
  assert (free_name_or_token w) as Hfnot; [apply SO3_free_name_or_token with (1:= Hso3) |]. 
  inversion H1 as [? ? ? Hwf|]; subst; inversion Hwf as [? HfvG HeqtypesG HdisjointG]; subst.
  assert (rho1 = rho); [|subst].
  apply HeqtypesG with (1:=HinxG).
  inversion HlookupvG; subst; assumption.

  destruct (free_name_or_token_split _ Hfnot) as [Hfn|Htok]; [
    | destruct Htok as [k Heq]; subst; specialize (HfvG _ _ HtypuvP); inversion HfvG
  ].
  assert (CTX.In (w, sigma) (ctx_add_value w rho G)) as Hin1; [
    inversion Hfn; subst; simpl; apply CTXFacts.add_2; apply HtypuvP
    |
  ].
  assert (CTX.In (w, rho) (ctx_add_value w rho G)) as Hin2; [
    inversion Hfn; subst; simpl; apply CTXFacts.add_1; reflexivity
    | 
  ].
  assert (sigma = rho); [ 
    pose (partition_wf _ _ _ Hpart) as Hu; inversion Hu as [? ? Heqtypes]; subst; apply (Heqtypes _ _ _ Hin1 Hin2)
    | subst
  ].
  inversion Hpart as [? ? ? ? ? Hdisjoint]; subst;
    (specialize (Hdisjoint w rho); destruct Hdisjoint as [Hnotin | Hdisjoint]; [
      contradict Hnotin; assumption
      | destruct Hdisjoint as [Hnotin | Hdisjoint]; [
        contradict Hnotin; inversion Hfn; subst; apply CTXFacts.add_1; reflexivity
        | assumption
      ]
    ]).
  destruct (value_dec v (ValVariable (Var (Free x)))) as [e1|n1]; [
    subst;
    destruct (In_dec value_dec w (free_values_proc (u ! (ValVariable (Var (Free x))); P))) as [i2|n2]; [
      assert ( |-st rho ) as Hstateless; [
        apply Hfreewstateless; split; auto
        | eapply subst_r_output_stateless with (15:=IHHtypspecialized); eauto
      ]
      | assert (~ (ValVariable (Var (Free x)) = ValVariable (Var (Free x)) /\ In w (free_values_proc (u ! ValVariable (Var (Free x)); P)))) as Hnotfreew; [
        contradict n2; destruct n2; assumption
        |
      ]
    ]
    | assert (~ (v = ValVariable (Var (Free x)) /\ In w (free_values_proc (u ! v; P)))) as Hnotfreew; [
      contradict n1; destruct n1; assumption
      |
    ]
  ];
  (destruct H0 as [H0|H0]; [ 
    pose H3 as Hu; destruct H3 as [H3|H3]; [
      rewrite H3 in *; eapply subst_r_output_stateful with (17:=IHHtyp); eauto
      | eapply subst_r_output_stateless with (15:=IHHtypspecialized); eauto; destruct H3; assumption
    ]
    | eapply subst_r_output_stateless with (15:=IHHtypspecialized); eauto
  ]).




  Case "par"%string.
  assert (free_name_or_token w) as Hfnot; [apply (SO3_free_name_or_token _ _ _ _ _ Hso3) |];
  pose (SO3_par_decompose x y _ _ _ Hso3 _ _ eq_refl) as e; destruct e as [Q3 e]; destruct e as [Q4 e]; subst.
  destruct (SO3_par _ _ _ _ _ _ _ Hso3) as [Hso3a Hso3b].

  assert (~ In y (free_ids_proc P)) as HnotinyPL.
  contradict HnotinyP; simpl; rewrite in_app_iff; tauto.
  assert (~ In y (free_ids_proc Q)) as HnotinyPR.
  contradict HnotinyP; simpl; rewrite in_app_iff; tauto.

  inversion H as [? ? ? Heq Hwf Hdisjoint]; subst.

  assert ((CTX.In (ValVariable (Var (Free x)), rho1) GL) -> ctx_add_value w rho1 GL |-p Q3) as HLin; [
    intros Hin;
      apply IHHtyp1 with (1:=Hso3a); auto;
        inversion Hfnot; subst; simpl; try solve [apply partition_left_add with (1:=H) (2:=Hpart)];
          apply partition_empty; apply partition_wf_left with (1:=H); auto
    |
  ].

  assert ((CTX.In (ValVariable (Var (Free x)), rho1) GR) -> ctx_add_value w rho1 GR |-p Q4) as HRin; [
    intros Hin;
      apply IHHtyp2 with (1:=Hso3b); auto;
        inversion Hfnot; subst; simpl; try solve [apply partition_comm in H; apply partition_left_add with (1:=H) (2:=Hpart)];
          apply partition_empty; apply partition_comm in H; apply partition_wf_left with (1:=H); auto
    |
  ].

  assert ((~ CTX.In (ValVariable (Var (Free x)), rho1) GL) -> GL |-p Q3) as HLnotin; [
    intros Hnotin;
      assert (P = Q3); [
        apply SO3_proc_no_free_var with (1:=Htyp1) (2:=Hso3a);
          rewrite free_ids_context_iff; intros Hin; destruct Hin as [u Hin]; destruct Hin as [rho Hin]; destruct Hin as [Hin1 Hin2];
            destruct u as [nm | tok | var]; subst; simpl in Hin2; try solve [destruct Hin2]; [
              destruct nm as [i|i]
              | destruct var as [i]
            ]; subst; simpl in Hin2;
            (destruct i as [f|b]; subst; simpl in Hin2; try solve [destruct Hin2];
              destruct Hin2 as [Hin2|Hin2]; [
                subst
                | destruct Hin2
              ]
            ); [
              |
              | assert (rho1 = rho); [
                inversion Hwf as [? ? Heqtypes ]; subst;
                  apply Heqtypes with (1:=HinxG);
                    rewrite Heq;
                      rewrite CTXFacts.union_iff; tauto
                | subst; contradict Hnotin; assumption
              ]
            ]; 
            inversion Hwf as [? _ _ Hoverlap]; subst;
              (specialize (Hoverlap x); destruct Hoverlap as [Hoverlap|Hoverlap]; [
                specialize (Hoverlap rho1); contradict Hoverlap; assumption
                | destruct Hoverlap as [Hoverlap1 Hoverlap2]; specialize (Hoverlap1 rho); specialize (Hoverlap2 rho);
                  solve [(contradict Hoverlap1; rewrite Heq; rewrite CTXFacts.union_iff; tauto)
                    || (contradict Hoverlap2; rewrite Heq; rewrite CTXFacts.union_iff; tauto)]
              ])
        | subst; assumption
      ]
    |
  ].

  assert ((~ CTX.In (ValVariable (Var (Free x)), rho1) GR) -> GR |-p Q4) as HRnotin; [
    intros Hnotin;
      assert (Q = Q4); [
        apply SO3_proc_no_free_var with (1:=Htyp2) (2:=Hso3b);
          rewrite free_ids_context_iff; intros Hin; destruct Hin as [u Hin]; destruct Hin as [rho Hin]; destruct Hin as [Hin1 Hin2];
            destruct u as [nm | tok | var]; subst; simpl in Hin2; try solve [destruct Hin2]; [
              destruct nm as [i|i]
              | destruct var as [i]
            ]; subst; simpl in Hin2;
            (destruct i as [f|b]; subst; simpl in Hin2; try solve [destruct Hin2];
              destruct Hin2 as [Hin2|Hin2]; [
                subst
                | destruct Hin2
              ]
            ); [
              |
              | assert (rho1 = rho); [
                inversion Hwf as [? ? Heqtypes ]; subst;
                  apply Heqtypes with (1:=HinxG);
                    rewrite Heq;
                      rewrite CTXFacts.union_iff; tauto
                | subst; contradict Hnotin; assumption
              ]
            ]; 
            inversion Hwf as [? _ _ Hoverlap]; subst;
              (specialize (Hoverlap x); destruct Hoverlap as [Hoverlap|Hoverlap]; [
                specialize (Hoverlap rho1); contradict Hoverlap; assumption
                | destruct Hoverlap as [Hoverlap1 Hoverlap2]; specialize (Hoverlap1 rho); specialize (Hoverlap2 rho);
                  solve [(contradict Hoverlap1; rewrite Heq; rewrite CTXFacts.union_iff; tauto)
                    || (contradict Hoverlap2; rewrite Heq; rewrite CTXFacts.union_iff; tauto)]
              ])
        | subst; assumption
      ]
    |
  ].

  assert ((CTX.In (ValVariable (Var (Free x)), rho1) GL) -> (CTX.In (ValVariable (Var (Free x)), rho1) GR) -> |-st rho1) as Hstateless; [
    |
  ].
  intros Hin1 Hin2.
  specialize (Hdisjoint (ValVariable (Var (Free x))) rho1); destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
    | destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
      | assumption
    ]
  ]; contradict Hdisjoint; assumption.

  (destruct (CTXProperties.In_dec (ValVariable (Var (Free x)), rho1) GL) as [iL|nL]);
  (destruct (CTXProperties.In_dec (ValVariable (Var (Free x)), rho1) GR) as [iR|nR]); [
    specialize (HLin iL); clear HLnotin; specialize (HRin iR); clear HRnotin; specialize (Hstateless iL iR);
      apply TypPar with (GL:=ctx_add_value w rho1 GL) (GR:=ctx_add_value w rho1 GR); auto
    | specialize (HLin iL); clear HLnotin; specialize (HRnotin nR); clear HRin;
      apply TypPar with (GL:=ctx_add_value w rho1 GL) (GR:=GR); auto
    | specialize (HLnotin nL); clear HLin; specialize (HRin iR); clear HRnotin;
      apply TypPar with (GL:=GL) (GR:=ctx_add_value w rho1 GR); auto
    | specialize (HLnotin nL); clear HLin; specialize (HRnotin nR); clear HRin;
      apply TypPar with (GL:=ctx_add_value w rho1 GL) (GR:=GR); auto
  ]; 
  (destruct (free_name_or_token_split _ Hfnot) as [Hfn|Htok]; [
    | destruct Htok as [k Htok]; subst; simpl; assumption
  ]).

  (* iL / iR *)
  assert (ctx_add_value w rho1 G |-part GL (+) ctx_add_value w rho1 GR) as Hpart2; [
    eapply ctx_equal_part; [
      apply ctx_union_swap; [
        (eapply ctx_equal_part_1 with (G1:=G); [apply H | apply Heq])
        | eapply ctx_equal_part_2; [| apply Heq]; apply Hpart
      ]
      | reflexivity
      | reflexivity
      | apply CTXProperties.subset_antisym; [
        apply CTXProperties.union_subset_3; [
          inversion Hfn; subst; simpl; apply CTXProperties.subset_add_2; reflexivity
          | inversion Hfn; subst; simpl; (apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity | apply CTXProperties.subset_empty])
        ]
        |
          inversion Hfn; subst; simpl;
            (apply CTXProperties.subset_add_3; [apply CTXProperties.union_subset_2; apply CTXFacts.add_1; reflexivity | ]);
            apply CTXProperties.union_subset_1
      ]
    ]
    |
  ].
  inversion Hfn; 
    (subst; simpl; simpl in Hpart2; apply partition_add_idem_stateless; auto; [
      apply LContext; [
        inversion Hpart2; subst; assumption
        | apply CTXFacts.add_1; reflexivity
      ]
      | constructor
    ]).

  (* iL / nR *)
  inversion Hfn; subst; simpl; apply ctx_add_partition; auto.

  (* nL / iR *)
  inversion Hfn; subst; simpl; apply partition_comm; apply ctx_add_partition; auto; apply partition_comm; auto.

  (* nL / nR *)
  inversion Hfn; subst; simpl; apply ctx_add_partition; auto.

  (* for this typing, we use weakening to remove ctx_add_value *)
  inversion Hfn; subst; simpl in *; apply partition_left_add with (1:=H) in Hpart;
    apply partition_typed_weaken_left with (2:=Hpart); assumption.



  Case "sum"%string.
  pose (SO3_sum_decompose x y _ _ _ Hso3 _ _ eq_refl) as e; destruct e as [Q3 e]; destruct e as [Q4 e]; subst.
  apply TypSum; 
    (eapply ctx_equal_preserves_typed; [
      match goal with
        | [ |- _ |-p Q3 ] => eapply IHHtyp1
        | [ |- _ |-p Q4 ] => eapply IHHtyp2
      end; [
        apply SO3_sum in Hso3; destruct Hso3; eauto
        | eauto
        | auto
        | simpl in HnotinyP; rewrite in_app_iff in HnotinyP; contradict HnotinyP; solve [(left; assumption) || (right; assumption)]
        | auto
        | eauto
        | apply Htoken
        | auto
      ]
      | reflexivity
    ]).


  Case "IsEq"%string.
  pose (SO3_iseq_decompose x y _ _ _ Hso3 _ _ _ eq_refl) as e; destruct e as [u1 e]; destruct e as [v1 e]; destruct e as [P1 e]; subst.
  assert (SO3_value x y w u u1) as Hso3u; [eapply SO3_value_iseq1; eauto|].
  assert (SO3_value x y w v v1) as Hso3v; [eapply SO3_value_iseq2; eauto|].
  assert (SO3 x y w P P1) as Hso3a; [apply SO3_iseq in Hso3; auto|].

  apply TypIsEq with (K:=K) (L:=L).
  apply subst_r_value_alt with (x:=x) (y:=y) (u1:=u); auto; contradict HnotinyP; simpl; (repeat rewrite in_app_iff); tauto.
  apply subst_r_value_alt with (x:=x) (y:=y) (u1:=v); auto; contradict HnotinyP; simpl; (repeat rewrite in_app_iff); tauto.

  (* Note: SO3_free_values_in_context1 is unavailable since it demands typing of P, but we only have typing when K=L. *)
  intros v2 Hin2.
  assert (free_value v2) as Hfvv2; [
    apply free_values_proc_yields_free_values with (1:=Hin2); auto
    |
  ].
  apply SO3_free_values_in_context1_aux with (2:=Hso3a) in Hin2.
  destruct Hin2 as [u2 Hin2]; destruct Hin2 as [Hin2 Hin3].  
  specialize (H1 u2 Hin2).
  destruct H1 as [sigma H1].
  exists sigma.
  apply SO3_value_ctx_in with (1:=Hin3); auto; [
    contradict HnotinyP; simpl; (repeat rewrite in_app_iff); right; right; rewrite free_ids_proc_alt; rewrite in_flat_map; exists u2; split; auto
    | inversion H; subst; assumption
  ].

  intros HeqKL; apply H3 with (x:=x) (y:=y) (1:=HeqKL) (2:=Hso3a); auto; contradict HnotinyP; simpl; (repeat rewrite in_app_iff); tauto.


  Case "IsNotEq"%string.
  pose (SO3_isneq_decompose x y _ _ _ Hso3 _ _ _ eq_refl) as e; destruct e as [u1 e]; destruct e as [v1 e]; destruct e as [P1 e]; subst.
  assert (SO3_value x y w u u1) as Hso3u; [eapply SO3_value_isneq1; eauto|].
  assert (SO3_value x y w v v1) as Hso3v; [eapply SO3_value_isneq2; eauto|].
  assert (SO3 x y w P P1) as Hso3a; [apply SO3_isneq in Hso3; auto|].

  apply TypIsNotEq with (K:=K) (L:=L).
  apply subst_r_value_alt with (x:=x) (y:=y) (u1:=u); auto; contradict HnotinyP; simpl; (repeat rewrite in_app_iff); tauto.
  apply subst_r_value_alt with (x:=x) (y:=y) (u1:=v); auto; contradict HnotinyP; simpl; (repeat rewrite in_app_iff); tauto.

  intros v2 Hin2.
  assert (free_value v2) as Hfvv2; [
    apply free_values_proc_yields_free_values with (1:=Hin2); auto
    |
  ].
  apply SO3_free_values_in_context1_aux with (2:=Hso3a) in Hin2.
  destruct Hin2 as [u2 Hin2]; destruct Hin2 as [Hin2 Hin3].  
  specialize (H1 u2 Hin2).
  destruct H1 as [sigma H1].
  exists sigma.
  apply SO3_value_ctx_in with (1:=Hin3); auto; [
    contradict HnotinyP; simpl; (repeat rewrite in_app_iff); right; right; rewrite free_ids_proc_alt; rewrite in_flat_map; exists u2; split; auto
    | inversion H; subst; assumption
  ].

  intros HneqKL; apply H3 with (x:=x) (y:=y) (1:=HneqKL) (2:=Hso3a); auto; contradict HnotinyP; simpl; (repeat rewrite in_app_iff); tauto.


  Case "new"%string.
  pose (SO3_new_decompose x y _ _ _ Hso3 _ eq_refl) as e; destruct e as [Q3 e]; subst.
  apply TypNew with (s:=s) (L:=free_ids_value w ++ free_ids_proc P ++ free_ids_proc Q3 ++ L ++ free_ids_context G ++ (x::y::nil)).
  intros z G' Hnotin Heq; subst.
  assert (~ In z L) as HnotinzL; [contradict Hnotin; (repeat rewrite in_app_iff); tauto|].
  assert (z <> x) as Hneqzx; [contradict Hnotin; (repeat rewrite in_app_iff); subst; right; right; right; right; intuition|].
  assert (z <> y) as Hneqzy; [contradict Hnotin; (repeat rewrite in_app_iff); subst; right; right; right; right; intuition|].
  assert (SO3 x y w P Q3) as Hso3a; [apply SO3_new in Hso3; auto|]. 
  eapply SO3Step with (i:=z) in Hso3a; try solve [contradict Hnotin; (repeat rewrite in_app_iff); tauto].

  assert (w <> ValName (Nm (Free z))) as Hneqwnmz; [
    intros Heq; subst; contradict Hnotin; simpl; left; reflexivity
    |
  ].
  assert (w <> ValName (CoNm (Free z))) as Hneqwconmz; [
    intros Heq; subst; contradict Hnotin; simpl; left; reflexivity
    |
  ].

  assert (free_name_or_token w) as Hfnot; [apply (SO3_free_name_or_token _ _ _ _ _ Hso3) |].

  assert (
    CTX.eq
    (ctx_add_value w rho1 (CTX.add (ValName (Nm (Free z)), TChannel s) (CTX.add (ValName (CoNm (Free z)), TChannel (SDual s)) G)))
    (CTX.add (ValName (Nm (Free z)), TChannel s) (CTX.add (ValName (CoNm (Free z)), TChannel (SDual s)) (ctx_add_value w rho1 G)))
  ) as Heqctx.
  inversion Hfnot; subst; simpl; try solve [reflexivity]; 
    (apply CTXProperties.subset_antisym; [
      apply CTXProperties.subset_add_3; [apply CTXFacts.add_2; apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity|];
        apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|];
          apply CTXProperties.subset_add_3; [apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity|];
            do 3 apply CTXProperties.subset_add_2; reflexivity
      | apply CTXProperties.subset_add_3; [apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity|];
        apply CTXProperties.subset_add_3; [apply CTXFacts.add_2; apply CTXFacts.add_2; apply CTXFacts.add_1; reflexivity|];
          apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|];
            do 3 apply CTXProperties.subset_add_2; reflexivity
    ]
    ).

  eapply ctx_equal_preserves_typed; [|apply Heqctx].
  eapply H0 with (3:=Hso3a); auto; [
    contradict HnotinyP; simpl;
      apply free_ids_open_proc in HnotinyP; destruct HnotinyP as [HnotinyP|HnotinyP]; [
        contradict Hneqzy; subst; reflexivity
        | assumption
      ]
    | do 2 apply CTXFacts.add_2; assumption
    |
  ].

  eapply ctx_equal_part_1; [|symmetry; apply Heqctx].
  apply ctx_add_preserves_partition_left_dual_names; [|assumption].

  constructor; [ constructor |].
  intros v sigma.
  destruct (CTXProperties.In_dec (v, sigma) (ctx_add_value w rho1 G)) as [i|n]; [
    right
    | left; assumption
  ].
  simpl.
  inversion Hfnot; subst; simpl in i; 
    try (rewrite CTXFacts.add_iff in i;
      destruct i as [i|i]; [
        injection i; intros; subst; contradict Hnotin; (repeat rewrite in_app_iff); left; 
          simpl; simpl in Hnotin; injection Hnotin; intros; subst; left; reflexivity
        | idtac
      ]); 
    (intros Heq; contradict Hnotin; (repeat rewrite in_app_iff); right; right; right; right; left;
      rewrite free_ids_context_iff; exists v; exists sigma; split; [
        assumption
        | rewrite <- Heq; intuition
      ]).


  Case "rep"%string.
  pose (SO3_rep_decompose x y _ _ _ Hso3 _ eq_refl) as e; destruct e as [Q3 e]; subst.
  assert (SO3 x y w P Q3) as Hso3a; [apply SO3_rep in Hso3; auto|]. 
  assert (free_name_or_token w) as Hfnot; [apply (SO3_free_name_or_token _ _ _ _ _ Hso3) |].

  destruct (CTXProperties.In_dec (ValVariable (Var (Free x)), rho1) G') as [i|n].

  eapply TypRep with (G':=ctx_add_value w rho1 G'); [
    apply partition_wf in Hpart; assumption
    | inversion Hfnot; simpl; try assumption;
      (apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|];
        apply CTXProperties.subset_add_2; assumption)
    | inversion Hfnot; simpl; intros u rho Hin; 
      try (rewrite CTXFacts.add_iff in Hin; destruct Hin as [Hin|Hin]; [
        injection Hin; intros; subst; apply (H1 _ _ i)
        | 
      ]); subst; apply (H1 _ _ Hin)
    |
  ].
  apply IHHtyp with (1:=Hso3a); auto.
  apply part_inter with (G':=ctx_add_value w rho1 G') in Hpart; [
    | inversion Hfnot; simpl; try assumption;
      (apply CTXProperties.subset_add_3; [apply CTXFacts.add_1; reflexivity|];
        apply CTXProperties.subset_add_2; assumption)
  ].
  (destruct (free_name_or_token_split _ Hfnot) as [Hfn|Htok]; [
    | destruct Htok as [k Htok]; subst; simpl in *; 
      eapply ctx_equal_part with (1:=Hpart); try reflexivity; [
        apply CTXProperties.inter_subset_equal; auto
        |
      ];
      assert (CTX.Empty (CTX.inter G' CTX.empty)); [
        apply CTXProperties.empty_inter_2; apply CTX.empty_spec
        |
      ];
      apply CTXProperties.empty_is_empty_1; assumption
  ]).
  apply ctx_equal_part_3 with (GR1:=CTX.inter (ctx_add_value w rho1 G') (ctx_add_value w rho1 CTX.empty)); [
    | apply CTXProperties.subset_antisym; [
    inversion Hfn; subst; simpl; intros a Hin; (repeat rewrite CTXFacts.inter_iff in Hin || rewrite CTXFacts.add_iff in Hin); 
      (destruct Hin as [Hin1 Hin2]; destruct Hin2 as [Hin2 | Hin2]; [|rewrite CTXFacts.empty_iff in Hin2; destruct Hin2]; apply CTXFacts.add_1; assumption)
    | inversion Hfn; subst; simpl;
      (apply CTXProperties.inter_subset_3; apply CTXProperties.subset_add_3; 
        try solve [apply CTXFacts.add_1; reflexivity]; apply CTXProperties.subset_empty)
    ]
  ].
  destruct (CTXProperties.In_dec (w, rho1) G') as [i2|n2]; [
    eapply ctx_equal_part_2 with (1:=Hpart);
      apply CTXProperties.subset_antisym; [
        inversion Hfn; subst; simpl; intros a Hin; (repeat rewrite CTXFacts.inter_iff in Hin || rewrite CTXFacts.add_iff in Hin); 
          (destruct Hin as [Hin1 Hin2]; destruct Hin1 as [Hin1|Hin1]; [
            subst; assumption
            | assumption
          ])
        | apply CTXProperties.inter_subset_3; auto; inversion Hfn; subst; simpl; apply CTXProperties.subset_add_2; reflexivity
      ]
    | apply ctx_remove_preserves_partition_left_2 with (u:=w) (rho:=rho1) in Hpart; [
      | inversion Hfn; subst; simpl; apply CTXFacts.inter_3; apply CTXFacts.add_1; reflexivity
    ];
    eapply ctx_equal_part_2 with (1:=Hpart)
  ].
  apply CTXProperties.subset_antisym; [
    inversion Hfn; subst; simpl; intros a Hin; 
      (repeat rewrite CTXFacts.inter_iff in Hin || rewrite CTXFacts.add_iff in Hin || rewrite CTXFacts.remove_iff in Hin);
      (destruct Hin as [Hin1 Hin2]; destruct Hin1 as [Hin1 _]; destruct Hin1 as [Hin1|Hin1]; [
        contradict Hin2; assumption
        | assumption
      ]
      )
    | intros a Hin; destruct (CTX.E.eq_dec a (w, rho1)) as [e3|n3]; [
      subst; contradict n2; assumption
      | apply CTXFacts.remove_2; auto;
        apply CTXFacts.inter_3; [
          inversion Hfn; subst; simpl; apply CTXFacts.add_2; assumption
          | apply H0; assumption
        ]
    ]
  ].


  eapply TypRep with (G':=G'); [
    apply partition_wf in Hpart; assumption
    | inversion Hfnot; subst; simpl; try assumption; apply CTXProperties.subset_add_2; assumption
    | assumption
    | 
  ].
  apply SO3_proc_no_free_var with (1:=Htyp) in Hso3a; subst; auto.
  rewrite free_ids_context_iff; contradict n.
inversion H as [? ? Heqtypes Hdisjoint]; subst.
  destruct n as [u n]; destruct n as [rho Hin]; destruct Hin as [Hin1 Hin2].
  destruct u as [nm| |var]; simpl in Hin2; try solve [destruct Hin2]; [
    destruct nm as [i|i]
    | destruct var as [i]
  ]; destruct i as [f|b]; simpl in Hin2; try solve [destruct Hin2];
  destruct Hin2 as [Hin2|Hin2]; try solve [destruct Hin2]; subst;
    try solve [assert (rho1 = rho); [apply (Heqtypes _ _ _ HinxG); apply H0; assumption | ]; subst; assumption];
  (apply H0 in Hin1;
  specialize (Hdisjoint x); destruct Hdisjoint as [Hdisjoint|Hdisjoint]; [
    specialize (Hdisjoint rho1); contradict Hdisjoint; assumption
    | destruct Hdisjoint as [Hdisjoint1 Hdisjoint2]; 
      specialize (Hdisjoint1 rho); specialize (Hdisjoint2 rho); tauto
  ]).


  Case "zero"%string.
  pose (SO3_zero_decompose x y _ _ _ Hso3 eq_refl) as e; rewrite e in *.
  apply TypZero.
  apply partition_wf in Hpart; assumption.
Qed.


(* ============================================================================= *)
