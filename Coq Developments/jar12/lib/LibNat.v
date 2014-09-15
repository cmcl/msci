Set Implicit Arguments.

Require Import List.
Require Import Arith.
Require Import Max. 
Require Import LibTactics. 

(** nat *) 
Notation "k == i" := (eq_nat_dec k i) (at level 70).

Ltac case_nat :=
  let ldestr X Y := destruct (X == Y); [try subst X | idtac] in
  match goal with
  | |- context [?X == ?Y]      => ldestr X Y
  | H: context [?X == ?Y] |- _ => ldestr X Y
  end.

Notation emptyset := nil.

(** generating fresh nats *)
Section Exist_fresh.

  Fixpoint MAX (L : list nat) : nat :=
    match L with
    | nil        => O
    | cons hd tl => max hd (MAX tl)
    end.
  
  Lemma ex_fresh_var_1 : forall x L,
    In x L -> (x <= MAX L).
  Proof.
  induction L; intros.
    inversion H; simpl.
    destruct (max_dec a (MAX L)); destruct H; simpl.
        subst; rewrite e; apply le_refl.
        eapply le_trans; [ apply IHL; trivial | apply le_max_r].
        subst; apply le_max_l.
        eapply le_trans; [apply IHL; trivial | apply le_max_r].
  Qed.
      
  Lemma ex_fresh_var_2 : forall x L,
    MAX L < x -> ~ In x L.
  Proof.
  induction L; intuition; simpl.
    inversion H0; simpl; subst.
      eelim (le_not_lt). eapply ex_fresh_var_1. apply H0. trivial.
    apply IHL. apply le_lt_trans with (m := (MAX (a :: L))). simpl; apply le_max_r. assumption.
    inversion H0; subst.
      eelim le_not_lt. eapply ex_fresh_var_1. apply H0. trivial.
      trivial.
  Qed.

  Lemma pick_fresh : forall (L : list nat),
    exists n, ~ In n L.
  Proof.
  induction L; intros.
    exists O; auto.
    exists (S (MAX (a :: L))); intuition.
    elim ex_fresh_var_2 with (x := (S (MAX (a :: L)))) (L := (a :: L)).
      apply lt_n_Sn.
      trivial.
  Qed.

End Exist_fresh.

(** list nat *)
Lemma list_remove_in : forall n n0 S,
  In n S -> n <> n0 -> In n (remove eq_nat_dec n0 S).
Proof.
  induction S; intros; auto.
  simpl; case_nat.
    apply IHS; [destruct (in_inv H); congruence; auto | auto].
    destruct (n == a).
      subst; eauto with v62.
      simpl; right; apply IHS; [destruct (in_inv H); [congruence | auto] | auto].
Qed.

Lemma list_remove_in_inv: forall S n0 n, 
  In n (remove eq_nat_dec n0 S) -> In n S.
Proof.
  intros; induction S; auto.
  destruct (n == a).
    subst; auto using in_eq.
    simpl in *. 
    case_nat.
      right; auto.
      right; elim (in_inv H); intuition congruence.
Qed.

Lemma list_remove_in_inv_2: forall l n0 n, 
  In n (remove eq_nat_dec n0 l) ->
  n <> n0.
Proof.
  red; intros; subst; firstorder.
  contradict H.
  induction l; simpl; intros; auto; destruct (n0 == a); simpl; firstorder.
Qed.

Lemma in_sub_remove : forall (x y:nat) l m,
  (In x l -> In x m) ->
  In x (remove eq_nat_dec y l) ->
  In x (remove eq_nat_dec y m).
Proof.
  induction l; simpl; intros; intuition.
  destruct (y==a); simpl in *; auto.
  elim H0; intros; auto.
  subst.
  auto using list_remove_in.
Qed.

Lemma list_remove_app : forall x l l',
  remove eq_nat_dec x (l ++ l') = remove eq_nat_dec x l ++ remove eq_nat_dec x l'.
Proof.
  induction l.
  simpl; auto.
  intro; simpl.
  case_nat; auto.
  rewrite IHl; eauto using app_comm_cons.
Qed.

Lemma list_remove_repeat : forall x l,
  remove eq_nat_dec x (remove eq_nat_dec x l) = remove eq_nat_dec x l.
Proof.
  induction l.
  simpl; auto.
  simpl; case_nat; auto.
    simpl; case_nat; try congruence; auto.
Qed.

Lemma list_remove_twice : forall x y l,
  remove eq_nat_dec x (remove eq_nat_dec y l) = remove eq_nat_dec y (remove eq_nat_dec x l).
Proof.
  induction l.
  simpl; auto.
  simpl; case_nat.
    repeat case_nat; auto.
      simpl; repeat case_nat; try congruence; auto.
    repeat case_nat; simpl; repeat case_nat; try congruence; auto.
Qed.

Lemma emptyset_plus : emptyset ++ emptyset = (emptyset:list nat).
Proof.
  simpl; auto.
Qed.

(** swap_nat *)
Definition swap_nat (n m k : nat) : nat :=
  if n == k then m else if m == k then n else k.

Lemma swap_in_eq : forall n0 m k n,
  k <> n -> swap_nat n0 m k <> swap_nat n0 m n.
Proof.
  unfold swap_nat; intros.
  repeat case_nat; congruence.
Qed.

Lemma swap_map_remove : forall l m n,
  m <> n -> ~ In n l -> remove eq_nat_dec n (map (swap_nat n m) l) = remove eq_nat_dec m l.
Proof.
  induction l.
  intros; simpl; trivial.
  intros.
  assert (n <> a) by firstorder using remove_In.
  assert (~ In n l) by firstorder.
  destruct (m == a).

    simpl map at 1.
    replace (swap_nat n m a) with n.
    simpl remove at 1; case_nat; try congruence.
    simpl remove at 2; case_nat; try congruence.
    auto.
    unfold swap_nat. 
    case_nat; try congruence.
    case_nat; try congruence.
    
    simpl map at 1.
    assert (swap_nat n m a = a).
      unfold swap_nat; case_nat; try congruence; case_nat; congruence.
    rewrite H3.
    simpl remove; case_nat; try congruence; case_nat; try congruence.
    f_equal; auto.
Qed.

Lemma swap_not_in : forall m n k l,
  ~ In k l -> ~ In (swap_nat m n k) (map (swap_nat m n) l).
Proof.
  intros; induction l.
  simpl; auto.
  simpl; unfold swap_nat at 1.
  assert (k <> a) by firstorder.
  assert (~ In k l) by firstorder.
  case_nat.

    assert (n <> swap_nat a n k).
    unfold swap_nat; repeat case_nat; congruence.
    firstorder.
    
    assert ((if n == a then m else a) <> swap_nat m n k).
    unfold swap_nat; repeat case_nat; congruence.
    firstorder.
Qed.

Lemma swap_map_idem : forall l n m,
  map (swap_nat m n) (map (swap_nat m n) l) = l.
Proof.
  induction l; simpl; intros; f_equal; auto.
  intros; unfold swap_nat; repeat case_nat; congruence.
Qed.

Lemma swap_eq_remove_map : forall l m n,
  ~ In m l -> remove eq_nat_dec n l = remove eq_nat_dec m (map (swap_nat n m) l).
Proof.
  induction l; intros; simpl; auto.
  unfold swap_nat at 1.
  case_nat; case_nat; try case_nat; try congruence.
  simpl in H; intuition.
  simpl in H; intuition.
  unfold swap_nat at 1; case_nat; try congruence; case_nat; try congruence.
  erewrite IHl; firstorder.
Qed.

Lemma swap_app_remove_map : forall n m k l,
  map (swap_nat n m) (remove eq_nat_dec k l) 
    = remove eq_nat_dec (swap_nat n m k) (map (swap_nat n m) l).
Proof.
  induction l; simpl; auto.
  case_nat.
    case_nat; try congruence.
    case_nat.
      forwards H : (swap_in_eq n m n0); congruence.
      simpl; rewrite IHl; auto.
Qed.

(** remove O and then map-decrement *)
Notation map_pred_remove_zero l := (map pred (remove eq_nat_dec O l)).

Lemma swap_remove_map_pred_remove_zero : forall n L,
  remove eq_nat_dec n (map_pred_remove_zero L) = map_pred_remove_zero (remove eq_nat_dec (S n) L).
Proof.
induction L; auto.
destruct a; simpl; auto.
  destruct (n == a); simpl; auto.
    rewrite IHL; auto.
Qed.    

Lemma notIn_n_pred_notIn_S_n : forall n L,
  ~ In n (map pred L) -> ~ In (S n) L.
Proof.
induction L; simpl; intuition.
  destruct a; simpl; intuition.
    inversion H1.
Qed.   

Lemma notIn_remove_notIn : forall n m L,
  n <> m -> ~ In n (remove eq_nat_dec m L) -> ~ In n L.
Proof.
induction L; simpl.
  intuition.
  destruct (m == a); simpl; subst; intuition.
Qed.

Lemma notIn_remove_notIn_remain : forall n m L,
  ~ In n L -> ~ In n (remove eq_nat_dec m L).
Proof.
induction L; simpl.
  intuition.
  destruct (m == a); simpl; subst; intuition.
Qed.    

Lemma notIn_remove_self : forall n L,
  ~ In n (remove eq_nat_dec n L).
Proof.
  induction L; simpl; intros; auto; destruct (n == a); simpl; firstorder.
Qed.    

Lemma notIn_dist : forall A, forall (x :A) L L',
  ~ In x (L ++ L') -> ~ In x L /\ ~ In x L'.
Proof.
induction L; simpl; intuition.
Qed.

Lemma map_eq_nil : forall A, forall f (L : list A), (map f L = (nil : list A)) -> (L = nil).
Proof.
induction L; simpl; intuition.
  inversion H.
Qed.

(** list *)
Lemma list_permuting_in_app_cons_cons : forall T (x:T) l a b l',
  In x (l ++ a :: b :: l') -> 
  In x (l ++ b :: a :: l').
Proof.
  induction l; simpl; intros.
  firstorder.
  firstorder.
Qed.

Lemma list_cons_move_app : forall T (x:T) l l',
  l ++ x :: l' = (l ++ x :: nil) ++ l'.
Proof.
  induction l; intros; simpl; auto.
  f_equal; auto.
Qed.

Lemma list_cons_cons_move_app : forall T (y:T) l l',
  y :: l ++ l' = (y :: l) ++ l'.
Proof.
  simpl; auto.
Qed.

(** In *)
Ltac destructIn tac := 
  match goal with 
    | H: In ?X emptyset |- _ => inversion H
    | H: In ?X (?L1 ++ ?L2) |- _ =>
      apply in_app_or in H; destruct H; destructIn tac
    | H: In ?X (?X :: ?L) |- _ =>
      clear H; destructIn tac
    | H: In ?X (?Y :: ?L) |- _ =>
      apply in_inv in H; destruct H; destructIn tac
    | |- In ?X (?Y :: ?L) =>
      try solve [ apply in_eq; destructIn tac | apply in_cons; destructIn tac ]
    | |- In ?X (?L1 ++ ?L2) =>
      apply in_or_app; try solve [ left; destructIn tac | right; destructIn tac ]
    | _ => tac     
  end.

Tactic Notation "Destruct" "In" "by" tactic(tac) := destructIn tac.

(** notIn  *)
Lemma not_in_not_eq : forall A (X : A) (Y : A) L,
  X <> Y -> ~ In X L -> ~ In X (Y :: L).
Proof.
  firstorder.
Qed.

Lemma not_in_and_app : forall A L L' (X : A),
  ~ In X L -> ~ In X L' -> ~ In X (L ++ L').
Proof.
  induction L; firstorder.
Qed.

Lemma not_in_inv : forall A (X : A) (Y : A) L,
  ~ In X (Y :: L) -> X <> Y /\ ~ In X L.
Proof.
  firstorder.
Qed.

Lemma not_in_app_and : forall A, forall (x :A) L L',
  ~ In x (L ++ L') -> ~ In x L /\ ~ In x L'.
Proof.
  firstorder.
Qed.

Ltac destructNotIn tac := 
  let goal_destr_cons := (apply not_in_not_eq) in
  let goal_destr_concat := (apply not_in_and_app) in
  let hypo_destr_cons H := destruct (not_in_inv H); clear H in
  let hypo_destr_concat H := destruct (not_in_app_and _ _ _ H); clear H in
  match goal with
    | H: ?X <> ?X |- _ => congruence
    | H: ~ In ?X (?Y :: ?L) |- _ => hypo_destr_cons H; (destructNotIn tac)
    | H: ~ In ?X (?L1 ++ ?L2) |- _ => hypo_destr_concat H; (destructNotIn tac)
    | |- ~ In ?X (?Y :: ?L) => goal_destr_cons; [ tac | destructNotIn tac ]
    | |- ~ In ?X (?L1 ++ ?L2) => goal_destr_concat; (destructNotIn tac)
    | _ => tac
  end.

Tactic Notation "Destruct" "notIn" "by" tactic(tac) := destructNotIn tac.

Lemma list_always_incl_emptyset : forall A (l : list A), incl emptyset l.
Proof.
  induction l; eauto with v62.
Qed.
