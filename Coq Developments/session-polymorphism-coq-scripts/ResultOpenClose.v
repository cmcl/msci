Require Export Arith.EqNat.
Require Export Arith.Lt.
Require Export Arith.Compare_dec.
Require Export List.
Require Export ListLocal.
Require Import String.
Require Import Omega.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import TacticsLocal.
Require Import Process.

Lemma open_insert_id : 
  forall x i n,
    i = open_id x n (insert_id n i).
Proof.
  intros x i; elim i; [intuition|].
  intros b n; cbv beta delta [insert_id] iota zeta.
  elim (le_lt_dec n b); intros Hleq_nb.
  cbv beta delta [open_id] iota zeta. intuition.
  elim (eq_nat_decide (S b) n).
  intros Heq_Sbn; contradict Heq_Sbn.
  contradict Hleq_nb.
  replace n with (S b); [| apply eq_nat_eq; auto].
  omega.
  intros _.
  elim (le_lt_dec (S b) n); intros Hleq_Sbn.
  contradict Hleq_Sbn.
  omega.
  auto.

  cbv beta delta [open_id] iota zeta. intuition.
  elim (eq_nat_decide b n). 
  intros Heq_Sbn; contradict Heq_Sbn.
  contradict Hleq_nb.
  replace n with b; [|apply eq_nat_eq; auto].
  omega.
  intros _.
  elim (le_lt_dec b n); auto. 
  intros Hlt_nb; contradict Hlt_nb.
  omega.
Qed.

Lemma open_insert_name : 
  forall x nm n,
    nm = open_name x n (insert_name n nm).
Proof.  
  induction nm; simpl; intros n; rewrite <- (open_insert_id x i n); auto.
Qed.  

Lemma open_insert_variable : 
  forall x var n,
    var = open_variable x n (insert_variable n var).
Proof.  
  induction var; simpl; intros n; rewrite <- (open_insert_id x i n); auto.
Qed.  

Lemma open_insert_value :
  forall x v n, 
    v = open_value x n (insert_value n v).
Proof.
  induction v; simpl; auto. 
  intros b; rewrite <- (open_insert_name x n b); auto.
  intros b; rewrite <- (open_insert_variable x v b); auto.
Qed.

Theorem open_insert_proc :
  forall x P n,
    P = open_proc x n (insert_proc n P).
Proof.
  induction P; simpl; intuition;
  repeat 
    (erewrite <- (open_insert_value _ _ _)
      || erewrite <- (IHP _)
        || erewrite <- (IHP1 _)
          || erewrite <- (IHP2 _)
            || reflexivity).
Qed.

(* ============================================================================= *)

Lemma insert_open_id : 
  forall x i k n,
    k <= n -> 
    insert_id k (open_id x n i) = open_id x (S n) (insert_id k i).
Proof.
  intros f i; elim i; [intuition|]; clear i.
  intros b1 k b2 Hleq_kb2.
  cbv beta delta [insert_id open_id] iota zeta.
  elim (eq_nat_decide b1 b2);
    [intros Heq_b1b2_tmp; assert (b1=b2) as Heq_b1b2; intuition; clear Heq_b1b2_tmp 
    | intros Hneq_b1b2_tmp; assert (b1<>b2) as Hneq_b1b2; intuition; clear Hneq_b1b2_tmp];
  (elim (le_lt_dec k b1); [intros Hleq_kb1|intros Hlt_b1k]).
  elim (eq_nat_decide (S b1) (S b2)); auto.
  intros Hneq_b1b2; contradict Hneq_b1b2; rewrite Heq_b1b2; intuition.

  contradict Hleq_kb2; omega.

  elim (le_lt_dec b1 b2); intros; 
    (elim (eq_nat_decide (S b1) (S b2));
      [intros Heq_Sb1Sb2; contradict Heq_Sb1Sb2; intuition | intros _]).
  elim (le_lt_dec k b1); elim (le_lt_dec (S b1) (S b2)); intuition.
  elim (le_lt_dec k (pred b1)); elim (le_lt_dec (S b1) (S b2)); intuition.

  elim (le_lt_dec b1 b2); intros;
    (elim (eq_nat_decide b1 (S b2));
      [intros Heq_b1Sb2; contradict Heq_b1Sb2
      | intros _]).
  intros H; replace b1 with (S b2) in a;
    [omega|symmetry; apply eq_nat_eq; intuition].
  
  elim (le_lt_dec k b1); elim (le_lt_dec b1 (S b2)); intuition.
  omega.
  
  elim (le_lt_dec k (pred b1)); elim (le_lt_dec b1 (S b2)); intuition.
Qed.

Lemma insert_open_name : 
  forall x nm k n,
    k <= n ->
    insert_name k (open_name x n nm) = open_name x (S n) (insert_name k nm).
Proof.
  induction nm; simpl; intros; rewrite <- insert_open_id; auto.
Qed.  

Lemma insert_open_variable : 
  forall x var k n,
    k <= n ->
    insert_variable k (open_variable x n var) = open_variable x (S n) (insert_variable k var).
Proof.
  induction var; simpl; intros; rewrite <- insert_open_id; auto.
Qed. 

Lemma insert_open_value : 
  forall x v k n,
    k <= n ->
    insert_value k (open_value x n v) = open_value x (S n) (insert_value k v).
Proof.
  induction v; simpl; auto. 
  intros; rewrite <- insert_open_name; auto.
  intros; rewrite <- insert_open_variable; auto.
Qed.

Theorem insert_open_proc : 
  forall x P k n,
    k <= n ->
    insert_proc k (open_proc x n P) = open_proc x (S n) (insert_proc k P).
Proof.
  induction P; simpl; intuition;
  repeat 
    (erewrite <- insert_open_value
      || erewrite <- IHP
        || erewrite <- IHP1
          || erewrite <- IHP2
            || intuition).
Qed.

(* ============================================================================= *)

Lemma close_open_id : 
  forall x i n,
    (Free x) <> i ->
    close_id x n (open_id x n i) = i.
Proof.
  destruct i.
  cbv beta delta [close_id open_id] iota zeta.
  destruct (string_dec x f); intuition.
  contradict H; rewrite <- e; intuition.
  intros n _.
  cbv beta delta [close_id open_id] iota zeta.
  destruct (eq_nat_decide b n); intuition.
  destruct (string_dec x x); intuition.
  symmetry; intuition.
  destruct (le_lt_dec b n); intuition.
  destruct (le_lt_dec n b); intuition.
  contradict n0; apply eq_eq_nat; omega.
  destruct (le_lt_dec n (pred b)).
  replace (S (pred b)) with b; intuition.
  unfold bound_id in *; omega.
  contradict l.
  omega.
Qed.

Lemma close_open_name : 
  forall x n nm,
    ~ (In x (free_ids_name nm)) ->
    close_name x n (open_name x n nm) = nm.
Proof.
  destruct nm; intros H; 
  cbv beta delta [close_name open_name] iota zeta; 
  erewrite -> close_open_id; auto.
  destruct i; try discriminate;
    destruct (string_dec x f); 
      [contradict H; rewrite <- e; apply in_eq
        |injection; auto].
  destruct i; try discriminate;
    destruct (string_dec x f); 
      [contradict H; rewrite <- e; apply in_eq
        |injection; auto].
Qed.

Lemma close_open_variable : 
  forall x n var,
    ~ (In x (free_ids_variable var)) ->
    close_variable x n (open_variable x n var) = var.
Proof.
  destruct var; intros H.
  cbv beta delta [close_variable open_variable] iota zeta; 
  erewrite -> close_open_id; auto.
  destruct i; [|discriminate].
  destruct (string_dec x f); 
      [contradict H; rewrite <- e; apply in_eq
        |injection; auto].
Qed.

Lemma close_open_value : 
  forall x n v,
    ~ (In x (free_ids_value v)) ->
    close_value x n (open_value x n v) = v.
Proof.
  destruct v; intuition.
  cbv beta delta [close_value open_value] iota zeta;
  erewrite -> close_open_name; auto.
  cbv beta delta [close_value open_value] iota zeta;
  erewrite -> close_open_variable; auto.
Qed.

Theorem close_open_proc : 
  forall x P n,
    ~ (In x (free_ids_proc P)) ->
    close_proc x n (open_proc x n P) = P.
Proof.
  induction P; intuition; cbv beta delta [close_proc open_proc] iota zeta;
    repeat (erewrite -> close_open_value); 
      repeat (erewrite -> IHP || erewrite -> IHP1 || erewrite -> IHP2); 
        try reflexivity;
          fold close_proc; fold open_proc; 
            solve [
              contradict H; apply In_app1; intuition
              | contradict H; apply In_app2; intuition
              | auto
            ];
            fold free_ids_proc.
Qed.  

(* ============================================================================= *)

Lemma close_insert_id : 
  forall x m i n, 
    n <= m
    -> 
    insert_id n (close_id x m i) = close_id x (S m) (insert_id n i).
Proof.
  intros x m i n Hleq_nm.
  destruct i; cbv beta delta [close_id insert_id] iota zeta; auto.
  destruct (string_dec x f); auto.
  destruct (le_lt_dec n m); auto; contradict Hleq_nm; omega.
  destruct (le_lt_dec m b); 
    destruct (le_lt_dec n b); 
      destruct (le_lt_dec (S m) (S b)); 
        destruct (le_lt_dec n (S b)); 
          destruct (le_lt_dec (S m) b); 
            intuition.
Qed.
  
Lemma close_insert_name : 
  forall x m nm n, 
    n <= m
    -> 
    insert_name n (close_name x m nm) = close_name x (S m) (insert_name n nm).
Proof.
  intros x m nm n Hleq_nm.
  destruct nm; unfold insert_name ; unfold close_name;
    erewrite <- close_insert_id; intuition.
Qed.

Lemma close_insert_variable : 
  forall x m var n, 
    n <= m
    -> 
    insert_variable n (close_variable x m var) = close_variable x (S m) (insert_variable n var).
Proof.
  intros x m var n Hleq_nm.
  destruct var; unfold insert_variable ; unfold close_variable;
    erewrite <- close_insert_id; intuition.
Qed.

Lemma close_insert_value : 
  forall x m v n, 
    n <= m
    -> 
    insert_value n (close_value x m v) = close_value x (S m) (insert_value n v).
Proof.
  intros x m v n Hleq_nm.
  destruct v; unfold insert_value ; unfold close_value; intuition.
  erewrite <- close_insert_name; intuition.
  erewrite <- close_insert_variable; intuition.
Qed.

Theorem close_insert_proc : 
  forall P x m n, 
    n <= m 
    -> 
    insert_proc n (close_proc x m P) = close_proc x (S m) (insert_proc n P).
Proof.
  induction P; simpl; intuition;
  repeat 
    (erewrite <- close_insert_value 
      || erewrite <- IHP
        || erewrite <- IHP1
          || erewrite <- IHP2
            || auto
              || omega).
Qed.
  
(* ============================================================================= *)

Lemma open_close_id :
  forall i m n x y, 
    m <= n ->
    x <> y -> 
    open_id x m (close_id y (S n) i) = close_id y n (open_id x m i).
Proof.
  Ltac main_attack := 
    intros i; destruct i; intros m n x y Hleq_mn Hneq_xy; unfold open_id; unfold close_id;
      destruct_if; intuition.

  Ltac mop_up_contradictions := 
    match goal with 
      | [ H : ?X = ?Y |- _ ] => contradict H; omega
      | [ H : ?X <= ?Y |- _ ] => contradict H; omega
    end.

  main_attack; mop_up_contradictions.
Qed.

Lemma open_close_name :
  forall nm m n x y, 
    m <= n ->
    x <> y -> 
    open_name x m (close_name y (S n) nm) = close_name y n (open_name x m nm).
Proof.
  intros nm m n x y Hleq_mn Hneq_xy.
  destruct nm; unfold open_name ; unfold close_name;
    erewrite <- open_close_id; intuition.
Qed.

Lemma open_close_variable :
  forall var m n x y, 
    m <= n ->
    x <> y -> 
    open_variable x m (close_variable y (S n) var) = close_variable y n (open_variable x m var).
Proof.
  intros var m n x y Hleq_mn Hneq_xy.
  destruct var; unfold open_variable ; unfold close_variable;
    erewrite <- open_close_id; intuition.
Qed.

Lemma open_close_value :
  forall v m n x y, 
    m <= n ->
    x <> y -> 
    open_value x m (close_value y (S n) v) = close_value y n (open_value x m v).
Proof.
  intros v m n x y Hleq_mn Hneq_xy.
  destruct v; unfold open_value ; unfold close_value; auto.
  erewrite <- open_close_name; intuition.
  erewrite <- open_close_variable; intuition.
Qed.

Theorem open_close_proc :
  forall P m n x y, 
    m <= n ->
    x <> y -> 
    open_proc x m (close_proc y (S n) P) = close_proc y n (open_proc x m P).
Proof.
  induction P; simpl; intuition;
  repeat 
    (erewrite <- (open_close_value _ _ _)
      || erewrite <- (IHP _)
        || erewrite <- (IHP1 _)
          || erewrite <- (IHP2 _)
            || intuition).
Qed.

(* ============================================================================= *)

Lemma open_open_id : 
  forall x y i m n,
    m <= n ->
    x <> y ->
    open_id x m (open_id y (S n) i) = open_id y n (open_id x m i).
Proof.
  Ltac main_attack2 := 
    intros x y i m n Hleq_mn Hneq_xy; destruct i; unfold open_id; 
      destruct_if; intuition.

  main_attack2; mop_up_contradictions.
Qed.

Lemma open_open_name : 
  forall x y nm m n,
    m <= n ->
    x <> y ->
    open_name x m (open_name y (S n) nm) = open_name y n (open_name x m nm).
Proof.
  intros x y nm m n Hleq_mn Hneq_xy.
  destruct nm; unfold open_name ; unfold close_name;
    erewrite -> open_open_id; intuition.
Qed.

Lemma open_open_variable : 
  forall x y var m n,
    m <= n ->
    x <> y ->
    open_variable x m (open_variable y (S n) var) = open_variable y n (open_variable x m var).
Proof.
  intros x y var m n Hleq_mn Hneq_xy.
  destruct var; unfold open_variable ; unfold close_variable;
    erewrite -> open_open_id; intuition.
Qed.

Lemma open_open_value : 
  forall x y v m n,
    m <= n ->
    x <> y ->
    open_value x m (open_value y (S n) v) = open_value y n (open_value x m v).
Proof.
  intros x y v n Hneq_xy.
  destruct v; unfold open_value; unfold close_value; intuition.
  erewrite -> open_open_name; intuition.
  erewrite -> open_open_variable; intuition.
Qed.

Theorem open_open_proc : 
  forall P x y m n,
    m <= n ->
    x <> y ->
    open_proc x m (open_proc y (S n) P) = open_proc y n (open_proc x m P).
Proof.
  induction P; simpl; intuition.

  erewrite -> open_open_value; intuition.
  erewrite -> IHP; intuition.

  erewrite -> open_open_value; intuition.
  erewrite -> open_open_value; intuition.
  erewrite -> IHP; intuition.

  erewrite -> open_open_value; intuition.
  erewrite -> open_open_value; intuition.
  erewrite -> IHP; intuition.

  erewrite -> open_open_value; intuition.
  erewrite -> open_open_value; intuition.
  erewrite -> IHP; intuition.

  erewrite -> IHP; intuition.

  erewrite -> IHP1; intuition.
  erewrite -> IHP2; intuition.

  erewrite -> IHP1; intuition.
  erewrite -> IHP2; intuition.

  erewrite -> IHP; intuition.
Qed.

(* ============================================================================= *)

Lemma open_open_eq_id : 
  forall x i m n,
    m <= n ->
    open_id x m (open_id x (S n) i) = open_id x n (open_id x m i).
Proof.
  Ltac main_attack3 := 
    intros x i m n Hleq_mn; destruct i; unfold open_id; destruct_if; intuition.

  main_attack3; mop_up_contradictions.
Qed.

Lemma open_open_eq_name : 
  forall x nm m n,
    m <= n ->
    open_name x m (open_name x (S n) nm) = open_name x n (open_name x m nm).
Proof.  
  intros; destruct nm; unfold open_name;
    erewrite -> open_open_eq_id; intuition.
Qed.

Lemma open_open_eq_variable : 
  forall x var m n,
    m <= n ->
    open_variable x m (open_variable x (S n) var) = open_variable x n (open_variable x m var).
Proof.  
  intros; destruct var; unfold open_variable;
    erewrite -> open_open_eq_id; intuition.
Qed.

Lemma open_open_eq_value : 
  forall x v m n,
    m <= n ->
    open_value x m (open_value x (S n) v) = open_value x n (open_value x m v).
Proof.
  destruct v; unfold open_value; unfold close_value; intuition.
  erewrite -> open_open_eq_name; intuition.
  erewrite -> open_open_eq_variable; intuition.
Qed.

Lemma open_open_eq_proc : 
  forall P x m n,
    m <= n ->
    open_proc x m (open_proc x (S n) P) = open_proc x n (open_proc x m P).
Proof.
  induction P; intros; simpl; intuition.

  erewrite -> open_open_eq_value; intuition.
  erewrite -> IHP; intuition.

  erewrite -> open_open_eq_value; intuition.
  erewrite -> open_open_eq_value; intuition.
  erewrite -> IHP; intuition.

  erewrite -> open_open_eq_value; intuition.
  erewrite -> open_open_eq_value; intuition.
  erewrite -> IHP; intuition.

  erewrite -> open_open_eq_value; intuition.
  erewrite -> open_open_eq_value; intuition.
  erewrite -> IHP; intuition.

  erewrite -> IHP; intuition.

  erewrite -> IHP1; intuition.
  erewrite -> IHP2; intuition.

  erewrite -> IHP1; intuition.
  erewrite -> IHP2; intuition.

  erewrite -> IHP; intuition.
Qed.

(* ============================================================================= *)

Lemma free_ids_open_id : forall k i j n, 
  In j (free_ids_id (open_id i n k)) -> (j = i) \/ (In j (free_ids_id k)).
Proof.
  destruct k; intros; cbv beta delta [free_ids_id open_id] iota zeta in *.
  right; intuition.
  destruct (eq_nat_decide b n) as [e1|n1]; 
    [assert (b = n) as e1eq; [intuition|rewrite -> e1eq in *]|].
  left; apply in_cons_nil; auto.
  right.
  destruct (le_lt_dec b n); intuition.
Qed.

Lemma free_ids_open_name : forall nm i j n, 
  In j (free_ids_name (open_name i n nm)) -> (j = i) \/ (In j (free_ids_name nm)).
Proof.
  destruct nm; intros; 
    cbv beta delta [free_ids_name open_name] iota zeta in *;
      eapply free_ids_open_id; eauto.
Qed.
  
Lemma free_ids_open_variable : forall var i j n, 
  In j (free_ids_variable (open_variable i n var)) -> (j = i) \/ (In j (free_ids_variable var)).
Proof.
  destruct var; intros; 
    cbv beta delta [free_ids_variable open_variable] iota zeta in *;
      eapply free_ids_open_id; eauto.
Qed.

Lemma free_ids_open_value : forall v i j n, 
  In j (free_ids_value (open_value i n v)) -> (j = i) \/ (In j (free_ids_value v)).
Proof.
  destruct v; intros; 
    cbv beta delta [free_ids_value open_value] iota zeta in *.
  eapply free_ids_open_name; eauto.
  right; auto.
  eapply free_ids_open_variable; eauto.
Qed.

Lemma free_ids_open_proc : forall P i j n, 
  In j (free_ids_proc (open_proc i n P)) -> (j = i) \/ (In j (free_ids_proc P)).
Proof.
  induction P; intros i j n; intuition; fold open_proc in *; fold free_ids_proc in *.

  destruct (in_app_or _ _ _ H) as [Hq1|Hq1]; clear H.
  destruct (free_ids_open_value _ _ _ _ Hq1) as [Hq2|Hq2]; clear Hq1; intuition.
  right; cbv beta delta [ free_ids_proc ] iota zeta; fold free_ids_proc; apply In_app1; auto.

  fold open_proc in *; fold free_ids_proc in *.
  destruct (IHP _ _ _ Hq1); clear Hq1; clear IHP; intuition.
  right; cbv beta delta [ free_ids_proc ] iota zeta; fold free_ids_proc; apply In_app2; auto.
  
  Ltac free_ids_open_proc_aux_tac IHP H Hq1 := 
    destruct (in_app_or _ _ _ H) as [Hq1|Hq1]; clear H; [
      destruct (free_ids_open_value _ _ _ _ Hq1); intuition;
        right; 
          cbv beta delta [ free_ids_proc ] iota zeta; 
            fold free_ids_proc; apply In_app1; auto
    | fold open_proc in *; fold free_ids_proc in *;
      destruct (in_app_or _ _ _ Hq1) as [Hq2|Hq2]; clear Hq1; [
        destruct (free_ids_open_value _ _ _ _ Hq2); intuition;
          right;
            cbv beta delta [ free_ids_proc ] iota zeta; 
              fold free_ids_proc; apply In_app2; apply In_app1; auto
          | destruct (IHP _ _ _ Hq2); clear Hq2; clear IHP; intuition;
            right; cbv beta delta [ free_ids_proc ] iota zeta; 
              fold free_ids_proc; apply In_app2; apply In_app2; auto
        ]
    ].
  
  free_ids_open_proc_aux_tac IHP H Hq1.
  free_ids_open_proc_aux_tac IHP H Hq1.
  free_ids_open_proc_aux_tac IHP H Hq1.

  destruct (IHP _ _ _ H); clear H; intuition.

  cbv beta delta [ free_ids_proc open_proc ] iota zeta in *; fold free_ids_proc in *; fold open_proc in *.
  destruct (in_app_or _ _ _ H) as [Hq1|Hq2]; clear H.
  destruct (IHP1 _ _ _ Hq1); clear Hq1; clear IHP1; intuition.
  destruct (IHP2 _ _ _ Hq2); clear Hq2; clear IHP2; intuition.

  cbv beta delta [ free_ids_proc open_proc ] iota zeta in *; fold free_ids_proc in *; fold open_proc in *.
  destruct (in_app_or _ _ _ H) as [Hq1|Hq2]; clear H.
  destruct (IHP1 _ _ _ Hq1); clear Hq1; clear IHP1; intuition.
  destruct (IHP2 _ _ _ Hq2); clear Hq2; clear IHP2; intuition.

  destruct (IHP _ _ _ H); clear H; intuition.
Qed.

(* ============================================================================= *)

Lemma free_ids_open_id2 : forall k i j n,
  In j (free_ids_id k) -> In j (free_ids_id (open_id i n k)).
Proof.
  intros k i j n Hin; destruct k; simpl; destruct_if; intuition.
Qed.

Lemma free_ids_open_name2 : forall nm i j n,
  In j (free_ids_name nm) -> In j (free_ids_name (open_name i n nm)).
Proof.
  destruct nm; intros; cbv beta delta [ free_ids_name open_name ] iota zeta in *.
  apply free_ids_open_id2; intuition.
  apply free_ids_open_id2; intuition.
Qed.

Lemma free_ids_open_variable2 : forall var i j n,
  In j (free_ids_variable var) -> In j (free_ids_variable (open_variable i n var)).
Proof.
  destruct var; intros; cbv beta delta [ free_ids_variable open_variable ] iota zeta in *.
  intuition.
  apply free_ids_open_id2; intuition.
Qed.

Lemma free_ids_open_value2 : forall v i j n,
  In j (free_ids_value v) -> In j (free_ids_value (open_value i n v)).
Proof.
  destruct v; intros; cbv beta delta [ free_ids_value open_value ] iota zeta in *.
  apply free_ids_open_name2; intuition.
  auto.
  apply free_ids_open_variable2; intuition.
Qed.

Lemma free_ids_open_proc2 : forall P i j n, 
  (In j (free_ids_proc P)) -> (In j (free_ids_proc (open_proc i n P))).
Proof.
  induction P; intros; 
    cbv beta delta [ free_ids_proc open_proc ] iota zeta in *; 
      fold free_ids_proc in *; fold open_proc in *; 
        try (destruct (in_app_or _ _ _ H);clear H); 
          intuition;
            (try (solve [apply In_app1; apply free_ids_open_value2; auto]));
            apply In_app2;
              destruct (in_app_or _ _ _ H0);clear H0;
                (try (solve [apply In_app1; apply free_ids_open_value2; auto]));
                intuition.
Qed.              
  
(* ============================================================================= *)

Lemma free_values_value_1 : 
  forall u v, In v (free_values_value u) -> u = v.
Proof.
  intros u v Hin.
    destruct u as [un|ut|uv];
      [   destruct un as [i|i]; destruct i
        | 
        | destruct uv as [i]; destruct i
      ];
      cbv beta delta [free_values_value] iota zeta in Hin;
        try (solve [apply in_eq_singleton; auto]); 
          contradict Hin.
Qed.
  
(* ============================================================================= *)

Lemma free_values_value_yields_free_values : 
  forall v u, In u (free_values_value v) -> free_value u.
Proof.
  intros v u Hin.
  destruct v as [vn|vk|vv];
    [destruct vn as [i|i] ; destruct i
      | destruct vk
      | destruct vv as [i] ; destruct i];
    try (solve [
      erewrite <- in_eq_singleton; eauto; 
        ( apply FNm || apply FCoNm || apply FVariable)
    ]);
    try (solve [inversion Hin]).
Qed.

Lemma free_values_value_yields_equal_values : 
  forall v u, In u (free_values_value v) -> u = v.
Proof.
  intros v u Hin.
  destruct v as [vn|vk|vv];
    [destruct vn as [i|i] ; destruct i
      | destruct vk
      | destruct vv as [i] ; destruct i];
    try (solve [inversion Hin; intuition]).
Qed.

Lemma free_values_proc_yields_free_values : 
  forall P u, In u (free_values_proc P) -> free_value u.
Proof.
  induction P; intros u Hin.

  destruct (in_app_or _ _ _ Hin) as [Hu|Hu]; clear Hin.
  eapply free_values_value_yields_free_values; eauto.
  apply IHP; auto.

  destruct (in_app_or _ _ _ Hin) as [Hu|Hin2]; clear Hin;
    [ 
      | destruct (in_app_or _ _ _ Hin2) as [Hu|Hu]; clear Hin2
    ].
  eapply free_values_value_yields_free_values; eauto.
  eapply free_values_value_yields_free_values; eauto.
  apply IHP; auto.

  destruct (in_app_or _ _ _ Hin) as [Hu|Hin2]; clear Hin;
    [ 
      | destruct (in_app_or _ _ _ Hin2) as [Hu|Hu]; clear Hin2
    ].
  eapply free_values_value_yields_free_values; eauto.
  eapply free_values_value_yields_free_values; eauto.
  apply IHP; auto.

  destruct (in_app_or _ _ _ Hin) as [Hu|Hin2]; clear Hin;
    [ 
      | destruct (in_app_or _ _ _ Hin2) as [Hu|Hu]; clear Hin2
    ].
  eapply free_values_value_yields_free_values; eauto.
  eapply free_values_value_yields_free_values; eauto.
  apply IHP; auto.

  apply IHP; auto.

  destruct (in_app_or _ _ _ Hin) as [Hu|Hu]; clear Hin.
  apply IHP1; auto.
  apply IHP2; auto.

  destruct (in_app_or _ _ _ Hin) as [Hu|Hu]; clear Hin.
  apply IHP1; auto.
  apply IHP2; auto.

  apply IHP; auto.

  inversion Hin.
Qed.

(* ============================================================================= *)

Lemma free_values_value_open : 
  forall v u i b, 
    In u (free_values_value v) -> In u (free_values_value (open_value i b v)).
Proof.
  intros v u i b Hin.
  pose (free_values_value_yields_equal_values v u Hin) as e.
  rewrite -> e in *.
  destruct v as [vn|vk|vv]; 
    [ destruct vn as [vi|vi]
      | 
      | destruct vv as [vi]
    ]; intuition;
    destruct vi; try (solve [cbv; intuition]);
      unfold free_values_value in Hin; inversion Hin.
Qed.

Lemma free_values_proc_open : 
  forall P u i b, 
    In u (free_values_proc P) -> In u (free_values_proc (open_proc i b P)).
Proof.
  induction P; intros u i b Hin; cbv beta delta [open_proc free_values_proc] iota zeta in *; fold open_proc free_values_proc in *; try (apply in_or_app).

  destruct (in_app_or _ _ _ Hin) as [Hu|Hu]; clear Hin.
  left; apply free_values_value_open; auto.
  right; apply IHP; auto.

  destruct (in_app_or _ _ _ Hin) as [Hu|Hu]; clear Hin; 
    [ 
      | destruct (in_app_or _ _ _ Hu) as [Hu2|Hu2]; clear Hu].
  left; apply free_values_value_open; auto.
  right; apply in_or_app; left; apply free_values_value_open; auto.
  right; apply in_or_app; right; apply IHP; auto.

  destruct (in_app_or _ _ _ Hin) as [Hu|Hu]; clear Hin; 
    [ 
      | destruct (in_app_or _ _ _ Hu) as [Hu2|Hu2]; clear Hu].
  left; apply free_values_value_open; auto.
  right; apply in_or_app; left; apply free_values_value_open; auto.
  right; apply in_or_app; right; apply IHP; auto.

  destruct (in_app_or _ _ _ Hin) as [Hu|Hu]; clear Hin; 
    [ 
      | destruct (in_app_or _ _ _ Hu) as [Hu2|Hu2]; clear Hu].
  left; apply free_values_value_open; auto.
  right; apply in_or_app; left; apply free_values_value_open; auto.
  right; apply in_or_app; right; apply IHP; auto.

  apply IHP; auto.
  
  destruct (in_app_or _ _ _ Hin) as [Hu|Hu]; clear Hin. 
  left; apply IHP1; auto.
  right; apply IHP2; auto.

  destruct (in_app_or _ _ _ Hin) as [Hu|Hu]; clear Hin. 
  left; apply IHP1; auto.
  right; apply IHP2; auto.

  apply IHP; auto.
  
  auto.
Qed.

(* ============================================================================= *)

Fixpoint primes (n : nat) : string :=
  match n with
    | O => "x"%string
    | S n' => append (primes n') "'"%string
  end.

Fixpoint sumLengths (L : list free_id) : nat :=
  match L with
    | nil => O
    | x :: L' => String.length x + sumLengths L'
  end.

Definition fresh (L : list free_id) := primes (sumLengths L).

Theorem freshOk' : forall x L, String.length x > sumLengths L -> ~ In x L.
Proof.
  induction L.
  intuition.
  intros Hlen Hin.
  inversion Hin; subst.
  contradict Hlen.
  unfold sumLengths.
  generalize (length x).
  intros n.
  omega.
  apply IHL; auto.
  simpl in Hlen.
  omega.
Qed.

Lemma length_app : forall s2 s1,
  String.length (s1 ++ s2) = String.length s1 + String.length s2.
Proof.
  induction s1; intuition.
  simpl; intuition.
Qed.

Lemma length_primes : forall n, String.length (primes n) = S n.
Proof.
  induction n; intuition; subst.
  simpl; rewrite -> length_app.
  rewrite -> IHn.
  simpl.
  intuition.
Qed.

Lemma fresh_free_id_exists :  
  forall (L : list free_id), exists i, ~ In i L.
Proof.
  intros L.
  exists (fresh L).
  apply freshOk'.
  unfold fresh.
  rewrite -> length_primes.
  intuition.
Qed.

(* ============================================================================= *)

Lemma free_ids_value_alt : 
  forall v, free_ids_value v = flat_map free_ids_value (free_values_value v).
Proof.
  intros v.
  destruct v as [vn|vk|vv]; [destruct vn| |destruct vv]; 
    try (destruct i); simpl; intuition.
Qed.
  
Lemma free_ids_proc_alt : 
  forall P, free_ids_proc P = flat_map free_ids_value (free_values_proc P).
Proof.
  intros P.
  induction P; simpl;
    repeat (
         rewrite flat_map_dist_app
      || rewrite free_ids_value_alt
      || rewrite IHP
      || rewrite IHP1
      || rewrite IHP2
      || reflexivity
    ).
Qed.

(* ============================================================================= *)

Lemma is_token_dec : 
  forall u : value, 
    { is_not_token u } + { ~ is_not_token u }.
Proof.
  intros u.
  destruct u; [
    left;intros k;discriminate
    | right
    | left;intros k;discriminate].
  intros H; unfold is_not_token in *.
  apply (H t); reflexivity.
Qed.

(* ============================================================================= *)

Lemma is_not_token_value : 
  forall v,
    ~ is_not_token v
    -> 
    exists k : token, ValToken k = v.
Proof.
  intros v Hnot.
  destruct v; try (contradict Hnot; intros; discriminate).
  exists t; reflexivity.
Qed.

(* ============================================================================= *)

