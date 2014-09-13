Require Export Arith.EqNat.
Require Export Arith.Lt.
Require Export Arith.Compare_dec.
Require Export List.
Require Export ListLocal.
Require Import String.
Require Import TypeAssignmentPoly.
Require Import ResultOpenClose.
Require Import ResultBasics.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Import TacticsLocal.

(* ============================================================================= *)

Definition freeid_rename_id (x y : free_id) (i : id) : id := 
  match i with
    | Free z => if (string_dec z x) then (Free y) else i
    | Bound _ => i
  end.

Definition freeid_rename_name (x y : free_id) (nm : name) : name := 
  match nm with
    | Nm i => Nm (freeid_rename_id x y i)
    | CoNm i => CoNm (freeid_rename_id x y i)
  end.

Definition freeid_rename_variable (x y : free_id) (var : variable) : variable := 
  match var with
    | Var i => Var (freeid_rename_id x y i)
  end.

Definition freeid_rename_value (x y : free_id) (u : value) : value := 
  match u with
    | ValName nm => ValName (freeid_rename_name x y nm)
    | ValToken _ => u
    | ValVariable var => ValVariable (freeid_rename_variable x y var)
  end.

Fixpoint freeid_rename_proc (x y : free_id) (P1 : proc) : proc := 
  match P1 with
    | (u ? ; P) => (freeid_rename_value x y u) ? ; (freeid_rename_proc x y P)
    | (u ! v ; P) => (freeid_rename_value x y u) ! (freeid_rename_value x y v) ; (freeid_rename_proc x y P)
    | IsEq u v P => IsEq (freeid_rename_value x y u) (freeid_rename_value x y v) (freeid_rename_proc x y P)
    | IsNotEq u v P => IsNotEq (freeid_rename_value x y u) (freeid_rename_value x y v) (freeid_rename_proc x y P)
    | New P => New (freeid_rename_proc x y P)
    | (P ||| Q) => (freeid_rename_proc x y P) ||| (freeid_rename_proc x y Q) 
    | (P +++ Q) => (freeid_rename_proc x y P) +++ (freeid_rename_proc x y Q)
    | ( ! P ) => ! (freeid_rename_proc x y P)
    | Zero => Zero
  end.

(*
Fixpoint freeid_rename_ctx_list (x y : free_id) (Glist : list CTX.E.t) : ctx := 
  match Glist with
    | nil => CTX.empty
    | (u, rho) :: Glist' => 
        CTX.add
          (freeid_rename_value x y u, rho) 
          (freeid_rename_ctx_list x y Glist')
  end.

Definition freeid_rename_ctx (x y : free_id) (G : ctx) : ctx := 
  freeid_rename_ctx_list x y (CTX.elements G).
*)

Definition freeid_rename_ctx_fun (x y : free_id) (a : CTX.elt) (G : ctx) : ctx := 
  match a with (u, rho) => CTX.add (freeid_rename_value x y u, rho) G end.

Definition freeid_rename_ctx (x y : free_id) (G : ctx) : ctx := 
  CTX.fold (freeid_rename_ctx_fun x y) G CTX.empty.

(* ============================================================================= *)

Lemma freeid_rename_id_open :
  forall i x y n,
    ~ In x (free_ids_id i)
    ->
    freeid_rename_id x y (open_id x n i) = open_id y n i.
Proof.
  intros i x y n Hnotin; destruct i; simpl in *.
  destruct (string_dec f x); intuition.
  destruct (eq_nat_decide b n); destruct (le_lt_dec b n); simpl; try (destruct (string_dec x x)); intuition.
Qed.

Lemma freeid_rename_name_open :
  forall nm x y n,
    ~ In x (free_ids_name nm)
    ->
    freeid_rename_name x y (open_name x n nm) = open_name y n nm.
Proof.
  intros nm x y n Hnotin; destruct nm; simpl; rewrite freeid_rename_id_open; auto.
Qed.

Lemma freeid_rename_variable_open :
  forall v x y n,
    ~ In x (free_ids_variable v)
    ->
    freeid_rename_variable x y (open_variable x n v) = open_variable y n v.
Proof.
  intros v x y n Hnotin; destruct v; simpl; rewrite freeid_rename_id_open; auto.
Qed.

Lemma freeid_rename_value_open :
  forall v x y n,
    ~ In x (free_ids_value v)
    ->
    freeid_rename_value x y (open_value x n v) = open_value y n v.
Proof.
  intros v x y n Hnotin; destruct v; simpl; auto; (rewrite freeid_rename_name_open || rewrite freeid_rename_variable_open); auto.
Qed.

Lemma freeid_rename_proc_open :
  forall P x y n,
    ~ In x (free_ids_proc P)
    ->
    freeid_rename_proc x y (open_proc x n P) = open_proc y n P.
Proof.
  intros P; induction P; intros x y n Hnotin; simpl in *; repeat (rewrite freeid_rename_value_open); auto;
    try solve [(rewrite IHP; intuition) || intuition].
  rewrite IHP; auto.
  contradict Hnotin; intuition.
  contradict Hnotin; intuition.
  rewrite IHP; auto.
  contradict Hnotin; intuition.
  contradict Hnotin; intuition.
  rewrite IHP; auto.
  contradict Hnotin; intuition.
  contradict Hnotin; intuition.
  rewrite IHP1; auto.
  rewrite IHP2; auto.
  contradict Hnotin; intuition.
  contradict Hnotin; intuition.
  rewrite IHP1; auto.
  rewrite IHP2; auto.
  contradict Hnotin; intuition.
  contradict Hnotin; intuition.
Qed.

(* ============================================================================= *)

Lemma freeid_rename_id_open_comm :
  forall i x y z n,
    x <> z 
    -> 
    y <> z
    ->
    freeid_rename_id x y (open_id z n i) = open_id z n (freeid_rename_id x y i).
Proof.
  intros i x y z n Hneqxz Hneqyz; destruct i; simpl in *; auto.
  destruct (string_dec f x); subst; auto.
  destruct (eq_nat_decide b n); destruct (le_lt_dec  b n); simpl; auto; destruct (string_dec z x); subst; auto; contradict Hneqxz; auto.
Qed.  

Lemma freeid_rename_name_open_comm :
  forall nm x y z n,
    x <> z 
    -> 
    y <> z
    ->
    freeid_rename_name x y (open_name z n nm) = open_name z n (freeid_rename_name x y nm).
Proof.
  intros nm x y z n Hneqxz Hneqyz; destruct nm; simpl in *; auto; rewrite freeid_rename_id_open_comm; auto.
Qed.

Lemma freeid_rename_variable_open_comm :
  forall v x y z n,
    x <> z 
    -> 
    y <> z
    ->
    freeid_rename_variable x y (open_variable z n v) = open_variable z n (freeid_rename_variable x y v).
Proof.
  intros v x y z n Hneqxz Hneqyz; destruct v; simpl in *; auto; rewrite freeid_rename_id_open_comm; auto.
Qed.

Lemma freeid_rename_value_open_comm :
  forall u x y z n,
    x <> z 
    -> 
    y <> z
    ->
    freeid_rename_value x y (open_value z n u) = open_value z n (freeid_rename_value x y u).
Proof.
  intros u x y z n Hneqxz Hneqyz; destruct u; simpl in *; auto.
  rewrite freeid_rename_name_open_comm; auto.
  rewrite freeid_rename_variable_open_comm; auto.
Qed.

Lemma freeid_rename_proc_open_comm :
  forall P x y z n,
    x <> z 
    -> 
    y <> z
    ->
    freeid_rename_proc x y (open_proc z n P) = open_proc z n (freeid_rename_proc x y P).
Proof.
  intros P; induction P; intros x y z n Hneqxz Hneqyz; simpl in *; repeat (rewrite freeid_rename_value_open_comm); auto;
    try solve [(rewrite IHP; auto) || (rewrite IHP1; auto; rewrite IHP2; auto) ].
Qed.

(* ============================================================================= *)

Lemma freeid_rename_ctx_add : 
  forall G x y u rho, 
    ~ CTX.In (u, rho) G
    ->
    CTX.Equal (freeid_rename_ctx x y (CTX.add (u, rho) G)) (CTX.add (freeid_rename_value x y u, rho) (freeid_rename_ctx x y G)).
Proof.
  intros G x y u rho Hnotin.
  unfold freeid_rename_ctx.
  rewrite (@CTXProperties.fold_add _ CTX.Equal); try solve [intuition].
  
  unfold Morphisms.Proper; unfold Morphisms.respectful.
  intros a b Heqab G1 G2 HeqG1G2; destruct a; destruct b.
  injection Heqab; intros; subst.
  unfold freeid_rename_ctx_fun.
  intuition.

  unfold SetoidList.transpose.
  intros a b G1; destruct a; destruct b.
  unfold freeid_rename_ctx_fun.
  intuition.
Qed.

(* ============================================================================= *)

Lemma freeid_rename_ctx_remove_aux1 : 
  forall G x y u rho, 
    CTX.In (u, rho) G 
    ->
    CTX.Equal
    (freeid_rename_ctx_fun x y (u, rho) (freeid_rename_ctx x y (CTX.remove (u, rho) G)))
    (freeid_rename_ctx x y G).
Proof.
  intros G x y u rho Hin.
  unfold freeid_rename_ctx.
  rewrite (@CTXProperties.remove_fold_1 _ CTX.Equal); try solve [intuition].

  unfold Morphisms.Proper; unfold Morphisms.respectful.
  intros a b Heqab G1 G2 HeqG1G2; destruct a; destruct b.
  injection Heqab; intros; subst.
  unfold freeid_rename_ctx_fun.
  intuition.

  unfold SetoidList.transpose.
  intros a b G1; destruct a; destruct b.
  unfold freeid_rename_ctx_fun.
  intuition.
Qed.

Lemma freeid_rename_ctx_remove_aux2 : 
  forall G x y u rho, 
    CTX.In (u, rho) G 
    ->
    forall a,
      CTX.In a (CTX.remove (freeid_rename_value x y u, rho) (freeid_rename_ctx x y G))
      -> 
      CTX.In a (freeid_rename_ctx x y (CTX.remove (u, rho) G)).
Proof.
  intros G x y u rho Hin a.
  rewrite CTXFacts.remove_iff.
  
  pose (freeid_rename_ctx_remove_aux1 G x y u rho Hin a).
  unfold freeid_rename_ctx_fun in i.
  rewrite CTXFacts.add_iff in i.

  destruct i as [H1 H2].
  intros Hin2.
  destruct Hin2 as [Hin2 Hneq].
  specialize (H2 Hin2).
  destruct H2.
  contradict Hneq; auto.
  auto.
Qed.

(* ============================================================================= *)

Definition freeid_rename_ctx_well_defined_prop :=
  (fun G1 : CTX.t => forall G2 x y,
    CTX.Equal G1 G2 -> CTX.Equal (freeid_rename_ctx x y G1) (freeid_rename_ctx x y G2)).

Lemma freeid_rename_ctx_well_defined_inv : 
  forall G1 G2, 
    CTX.Equal G1 G2 -> freeid_rename_ctx_well_defined_prop G1 -> freeid_rename_ctx_well_defined_prop G2.
Proof.
  intros G1 G2 Heq H.
  unfold freeid_rename_ctx_well_defined_prop in *.
  intros G3 x y Heq1.
  eapply CTXProperties.equal_trans.
  eapply CTXProperties.equal_sym.
  specialize (H G2 x y Heq); eauto.
  specialize (H G3 x y ); apply H.
  eapply CTXProperties.equal_trans; eauto.
Qed.  

Lemma freeid_rename_ctx_well_defined : 
  forall G1 G2 x y, 
    CTX.Equal G1 G2 -> CTX.Equal (freeid_rename_ctx x y G1) (freeid_rename_ctx x y G2).
Proof.
  apply (@CTXProperties.set_induction freeid_rename_ctx_well_defined_prop).
  intros G1 Hempty G2 x y Heq.
  unfold freeid_rename_ctx.
  intros a.
  repeat (rewrite CTXProperties.fold_1b || intuition).
  rewrite <- Heq; auto.
  
  intros G1 G2 H a Hnotin Hadd G3 x y Heq.
  unfold freeid_rename_ctx_well_defined_prop in H.
  unfold freeid_rename_ctx.
  intros b; destruct b;
  rewrite (@CTXProperties.fold_2 G1 G2 a _ CTX.Equal); try solve [intuition].  (* fold_2 is the key to working with fold! *)
  rewrite (@CTXProperties.fold_2 G1 G3 a _ CTX.Equal); try solve [intuition].

  unfold Morphisms.Proper; unfold Morphisms.respectful.
  intros a' b' Heqab G1' G2' HeqG1G2; destruct a'; destruct b'.
  injection Heqab; intros; subst.
  unfold freeid_rename_ctx_fun.
  intuition.

  unfold SetoidList.transpose.
  intros a' b' G1'; destruct a'; destruct b'.
  unfold freeid_rename_ctx_fun.
  intuition.

  unfold CTXProperties.Add in *.
  intros a'.
  rewrite <- Heq.
  apply Hadd.

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

Lemma freeid_rename_value_inj : 
  forall x y u v,
    ~ In y (free_ids_value u)
    ->
    ~ In y (free_ids_value v)
    ->
    freeid_rename_value x y u = freeid_rename_value x y v
    ->
    u = v.
Proof.
  intros x y u v Hnotinu Hnotinv Heq.
  repeat (match goal with
            | [ x : value |- _ ] => destruct x
            | [ x : variable |- _ ] => destruct x
            | [ x : name |- _ ] => destruct x
            | [ x : id |- _ ] => destruct x
            | [ H : context[string_dec ?X ?Y] |- _ ] => destruct (string_dec X Y)
            | [ |- _ ] => try solve [discriminate Heq || (injection Heq; intros; subst; intuition)]
          end; simpl in *; subst); try solve [intuition].
Qed.

(* ============================================================================= *)

Lemma freeid_rename_ctx_characterization :
  forall G x y u rho,
    ~ In y (free_ids_context G)
    ->
    (CTX.In (u, rho) (freeid_rename_ctx x y G) <-> exists v, (u = freeid_rename_value x y v /\ CTX.In (v, rho) G)).
Proof.
  apply (@CTXProperties.set_induction (fun G : CTX.t => forall x y u rho, 
    ~ In y (free_ids_context G)
    ->
    (CTX.In (u, rho) (freeid_rename_ctx x y G) <-> exists v, (u = freeid_rename_value x y v /\ CTX.In (v, rho) G)))).

  intros G Hempty x y u rho Hnotinu. 
  unfold freeid_rename_ctx.
  rewrite CTXProperties.fold_1b.
  intuition.
  rewrite CTXFacts.empty_iff in H; intuition.
  destruct H as [v H]; destruct H as [H1 H2].
  contradict H2; apply Hempty.
  auto.

  intros G1 G2 H a Hnotin Hadd x y u rho HnotinG; destruct a.
  unfold CTXProperties.Add in Hadd.

  unfold freeid_rename_ctx.
  rewrite (@CTXProperties.fold_2 G1 G2 (v, t) _ CTX.Equal); try solve [intuition].  
  simpl.
  rewrite CTXFacts.add_iff.

  split; intros Hin.
  destruct Hin as [Heq | Hin].
  injection Heq; intros; subst; clear Heq.
  exists v; rewrite Hadd; intuition.

  rewrite (H x y u rho) in Hin.
  destruct Hin as [v0 H1]; destruct H1 as [H1 H2].
  exists v0; intuition.
  rewrite Hadd; right; auto.
  contradict HnotinG.
  apply (free_ids_context_Add _ _ _ _ _ Hadd); auto.

  destruct Hin as [w Hin]; destruct Hin as [Heq Hin]; subst.
  rewrite Hadd in Hin.
  destruct Hin as [Heq | Hin].
  injection Heq; intros; subst; clear Heq.
  left; reflexivity.
  right.

  assert (~ In y (free_ids_context G1)) as HnotinG1.
  contradict HnotinG.
  apply (free_ids_context_Add _ _ _ _ _ Hadd); auto.

  specialize (H x y (freeid_rename_value x y w) rho HnotinG1).
  rewrite H.
  exists w; intuition.

  unfold Morphisms.Proper; unfold Morphisms.respectful.
  intros a b Heqab G1' G2' HeqG1G2; destruct a; destruct b.
  injection Heqab; intros; subst.
  unfold freeid_rename_ctx_fun.
  intuition.

  unfold SetoidList.transpose.
  intros a b G1'; destruct a; destruct b.
  unfold freeid_rename_ctx_fun.
  intuition.
Qed. 
  
(* ============================================================================= *)

Lemma freeid_rename_ctx_remove : 
  forall G x y u rho, 
    ~ In y (free_ids_context G)
    ->
    (G |-v u : rho)
    ->
    CTX.Equal (freeid_rename_ctx x y (CTX.remove (u, rho) G)) (CTX.remove (freeid_rename_value x y u, rho) (freeid_rename_ctx x y G)).
Proof.
  intros G x y u rho Hnot Htyp.
  intros a; destruct a.
  rewrite CTXFacts.remove_iff.
  repeat rewrite freeid_rename_ctx_characterization; auto.
  
  split; intros H.

  destruct H as [w H]; destruct H as [Heq H]; subst.
  rewrite CTXFacts.remove_iff in H.
  destruct H as [Hin2 Hneq].
  split.
  eexists; eauto.
  contradict Hneq.
  injection Hneq; intros; subst; clear Hneq.
  assert (u = w).
  apply (freeid_rename_value_inj x y); auto.
  contradict Hnot.

  apply (free_ids_value_context_strong _ _ _ _ Htyp); auto.
  contradict Hnot.
  apply (free_ids_value_context _ _ _ _ Hin2); auto.
  subst; auto.

  destruct H as [H1 H2]; destruct H1 as [w H1]; destruct H1 as [Heq H1]; subst.
  exists w; split; auto.
  rewrite CTXFacts.remove_iff.
  split; auto.
  contradict H2.
  injection H2; intros; subst; clear H2; auto.

  contradict Hnot.
  eapply free_ids_value_context_remove; eauto.
Qed.  

(* ============================================================================= *)

Lemma freeid_rename_ctx_remove2 : 
  forall G x y u rho, 
    ~ In y (free_ids_context G)
    ->
    G |-wf 
    ->
    CTX.In (u, rho) G
    ->
    CTX.Equal (freeid_rename_ctx x y (CTX.remove (u, rho) G)) (CTX.remove (freeid_rename_value x y u, rho) (freeid_rename_ctx x y G)).
Proof.
  intros G x y u rho Hnotin Hwf Hin.
  apply freeid_rename_ctx_remove; auto.
  apply LContext; auto.
Qed.
  
(* ============================================================================= *)

Lemma ctx_rename_over_prefix_input :
  forall x y z u rho sigma1 sigma2 G,
    G |-wf
    ->
    CTX.In (u, sigma1) G
    ->
    ~ In y (free_ids_context G)
    ->
    ~ In z (free_ids_context G)
    ->
    x <> z 
    -> 
    y <> z
    -> 
    CTX.Equal
    (freeid_rename_ctx x y (CTX.add (ValVariable (Var (Free z)), rho) (ctx_replace u sigma1 sigma2 G)))
    (CTX.add (ValVariable (Var (Free z)), rho) (ctx_replace (freeid_rename_value x y u) sigma1 sigma2 (freeid_rename_ctx x y G))).
Proof.
  intros x y z u rho sigma1 sigma2 G Hwf Hin HnotinyG HnotinzG Hneqxz Hneqyz.
  rewrite freeid_rename_ctx_add.
  replace (freeid_rename_value x y (Var (Free z))) with (ValVariable (Var (Free z))).
  apply add_cong.
  unfold ctx_replace.
  rewrite freeid_rename_ctx_add.
  apply add_cong.
  rewrite freeid_rename_ctx_remove; auto.
  reflexivity.
  apply LContext; auto.

  inversion Hwf; subst.
  rewrite CTXFacts.remove_iff.
  intros Hu; destruct Hu as [Hu1 Hu2].
  rewrite (H0 u sigma1 sigma2) in Hu2.
  intuition.
  auto.
  auto.

  simpl.
  destruct (string_dec z x); auto.
  subst; contradict Hneqxz; reflexivity.

  contradict HnotinzG.
  unfold ctx_replace in HnotinzG.
  rewrite CTXFacts.add_iff in HnotinzG.
  rewrite CTXFacts.remove_iff in HnotinzG.
  destruct HnotinzG as [H1|H1].
  injection H1; intros; subst; clear H1.
  
  unfold free_ids_context.
  apply in_flat_map.
  exists (ValVariable (Var (Free z)), sigma1); simpl; split; auto.
  apply context_in_vs_elements_in; auto.

  destruct H1 as [H1 H2].
  unfold free_ids_context.
  apply in_flat_map.
  exists (ValVariable (Var (Free z)), rho); simpl; split; auto.
  apply context_in_vs_elements_in; auto.
Qed.  

(* ============================================================================= *)

Lemma ctx_rename_over_prefix_output1 :
  forall x y u v rho sigma1 sigma2 G,
    G |-wf
    ->
    CTX.In (u, sigma1) G
    ->
    (G |-v v : rho)
    ->
    u <> v
    ->
    ~ In y (free_ids_context G)
    ->
    CTX.Equal
    (freeid_rename_ctx x y (ctx_replace u (sigma1) (sigma2) (CTX.remove (v, rho) G)))
    (ctx_replace (freeid_rename_value x y u) (sigma1) (sigma2) (CTX.remove (freeid_rename_value x y v, rho) (freeid_rename_ctx x y G))).
Proof.
  intros x y u v rho sigma1 sigma2 G Hwf Hin Htyp Hneq Hnotin.
  unfold ctx_replace.
  eapply CTX_eq_trans.
  apply freeid_rename_ctx_add.
  repeat rewrite CTXFacts.remove_iff.
  inversion Hwf; subst.
  intros H2.
  rewrite (H0 u sigma1 sigma2) in H2; intuition.
  apply add_cong.
  eapply CTX_eq_trans.
  apply freeid_rename_ctx_remove2; auto.
  contradict Hnotin.
  eapply free_ids_value_context_remove; eauto.
  apply wellformed_ctx_remove_1; auto.
  rewrite CTXFacts.remove_iff.
  split; auto.
  contradict Hneq.
  injection Hneq; intros; subst; auto.
  apply remove_cong.
  apply freeid_rename_ctx_remove; auto.
Qed.

(* ============================================================================= *)

Lemma ctx_rename_over_prefix_output2 :
  forall x y u sigma1 sigma2 G,
    G |-wf
    ->
    CTX.In (u, sigma1) G
    ->
    ~ In y (free_ids_context G)
    ->
    CTX.Equal
    (freeid_rename_ctx x y (ctx_replace u sigma1 sigma2 G))
    (ctx_replace (freeid_rename_value x y u) sigma1 sigma2 (freeid_rename_ctx x y G)).
Proof.
  intros x y u sigma1 sigma2 G Hwf Hin Hnotin.
  unfold ctx_replace.
  eapply CTX_eq_trans.
  apply freeid_rename_ctx_add.
  repeat rewrite CTXFacts.remove_iff.
  inversion Hwf; subst.
  intros H2.
  rewrite (H0 u sigma1 sigma2) in H2; intuition.
  apply add_cong.
  apply freeid_rename_ctx_remove2; auto.
Qed.

(* ============================================================================= *)

Lemma ctx_rename_over_prefix_output3 : 
  forall x y v sigma1 sigma2 G,
    G |-wf
    ->
    CTX.In (v, sigma1) G
    ->
    ~ In y (free_ids_context G)
    ->
    CTX.eq
     (freeid_rename_ctx x y (ctx_replace v sigma1 sigma2 (CTX.remove (v, sigma1) G)))
     (ctx_replace (freeid_rename_value x y v) sigma1 sigma2 (CTX.remove (freeid_rename_value x y v, sigma1) (freeid_rename_ctx x y G))).
Proof.
  intros x y v sigma1 sigma2 G Hwf HinvG Hnotin a; destruct a; split; intros Hin; rewrite freeid_rename_ctx_characterization in *; 
    try solve [
      contradict Hnotin; rewrite free_ids_context_iff in *; 
        destruct Hnotin as [u Hnotin]; destruct Hnotin as [rho Hnotin]; destruct Hnotin as [Hinurho Hinyfvu];
          unfold ctx_replace in *; (repeat (rewrite CTXFacts.add_iff in * || rewrite CTXFacts.remove_iff in * ));
            destruct Hinurho as [Heq|Hinurho]; [|destruct Hinurho as [Hinurho Hneq2]; destruct Hinurho as [Hinurho Hneq1]]; [
              injection Heq; intros; subst; clear Heq; eexists; eexists; split; eauto
              | eexists; eexists; split; eauto]
    ].

  destruct Hin as [v1 Hin]; destruct Hin as [Heq Hin]; subst.
  unfold ctx_replace in *; (repeat (rewrite CTXFacts.add_iff in * || rewrite CTXFacts.remove_iff in * )).
  destruct Hin as [Heq|Hin]; [|destruct Hin as [Hin Hneq2]; destruct Hin as [Hin Hneq1]].
  injection Heq; intros; subst; clear Heq.
  left; auto.
  right.
  assert ((freeid_rename_value x y v, sigma1) <> (freeid_rename_value x y v1, t)) as Hu.
  contradict Hneq1; injection Hneq1; intros; subst; clear Hneq1;
    apply (freeid_rename_value_inj x y) in H0; auto; subst; auto; 
      contradict Hnotin; rewrite free_ids_context_iff; 
        (try solve [exists v; eexists; split; eauto]);
        (try solve [exists v1; eexists; split; eauto]).
  repeat split; auto.
  apply freeid_rename_ctx_characterization; auto.
  exists v1; split; auto.


  unfold ctx_replace in *; (repeat (rewrite CTXFacts.add_iff in * || rewrite CTXFacts.remove_iff in * )).
  destruct Hin as [Heq|Hin]; [|destruct Hin as [Hin Hneq2]; destruct Hin as [Hin Hneq1]].
  injection Heq; intros; subst; clear Heq.
  exists v; split; [reflexivity|intuition].
  
  rewrite freeid_rename_ctx_characterization in Hin.
  destruct Hin as [w Hin]; destruct Hin as [Heq Hin]; subst.
  exists w; split; [reflexivity|].
  apply CTXFacts.add_2.
  apply CTXFacts.remove_2; [contradict Hneq1; injection Hneq1; intros; subst; clear Hneq1; reflexivity|].
  apply CTXFacts.remove_2; [contradict Hneq1; injection Hneq1; intros; subst; clear Hneq1; reflexivity|].
  auto.
  auto.
Qed.

(* ============================================================================= *)

Lemma ctx_rename_over_new :
  forall x y z sigma1 sigma2 G,
    G |-wf
    ->
    ~ In y (free_ids_context G)
    ->
    ~ In z (free_ids_context G)
    ->
    z <> x
    ->
    CTX.Equal
    (freeid_rename_ctx x y (CTX.add (ValName (Nm (Free z)), sigma1) (CTX.add (ValName (CoNm (Free z)), sigma2) G)))
    (CTX.add (ValName (Nm (Free z)), sigma1) (CTX.add (ValName (CoNm (Free z)), sigma2) (freeid_rename_ctx x y G))).
Proof.
  intros x y z sigma1 sigma2 G Hwf Hnotin1 Hnotin2 Hneq.
  eapply CTX_eq_trans.
  apply freeid_rename_ctx_add.
  rewrite CTXFacts.add_iff.
  contradict Hnotin2.
  destruct Hnotin2 as [Hu|Hu].
  discriminate Hu.
  eapply free_ids_context_vs_context; eauto; auto.
  
  simpl.
  destruct (string_dec z x); [intuition|].
  apply add_cong.

  eapply CTX_eq_trans.
  apply freeid_rename_ctx_add.
  contradict Hnotin2.
  eapply free_ids_context_vs_context; eauto; auto.

  simpl.
  destruct (string_dec z x); [intuition|].
  reflexivity.
Qed.  


(* ============================================================================= *)

Lemma local_result_rename_not_in_aux : 
  forall x y z L G,
    ~ In z (x :: y :: (L ++ (free_ids_context G)))
    -> 
    (z <> x /\ z <> y /\ ~ In z L /\ ~ In z (free_ids_context G)).
Proof.
  intros x y z L G Hnotin.
  repeat split; (try solve [contradict Hnotin; subst; intuition]).
Qed.

(* ============================================================================= *)

Lemma freeid_rename_free_value : 
  forall x y u,
    free_value u <-> free_value (freeid_rename_value x y u).
Proof.
  intros x y u.
  repeat (match goal with
            | [ x : value |- _ ] => destruct x
            | [ x : variable |- _ ] => destruct x
            | [ x : name |- _ ] => destruct x
            | [ x : id |- _ ] => destruct x
            | [ |- context[string_dec ?X ?Y] ] => destruct (string_dec X Y)
          end; simpl in *; subst); try solve [intuition];
  repeat (intros; constructor).
Qed.

Lemma freeid_rename_ctx_in_all : 
  forall x y rho G,
    ~ In y (free_ids_context G)
    ->
    ((CTX.In (ValVariable (Var (Free y)), rho) (freeid_rename_ctx x y G) -> CTX.In (ValVariable (Var (Free x)), rho) G)
    /\
    (CTX.In (ValName (Nm (Free y)), rho) (freeid_rename_ctx x y G) -> CTX.In (ValName (Nm (Free x)), rho) G)
    /\
    (CTX.In (ValName (CoNm (Free y)), rho) (freeid_rename_ctx x y G) -> CTX.In (ValName (CoNm (Free x)), rho) G)).
Proof.
  intros x y rho G Hnotin.
  (repeat split); intros Hin;
    (rewrite freeid_rename_ctx_characterization in Hin; auto);
      (destruct Hin as [v Hin]; destruct Hin as [Heq Hin]);
      (repeat (match goal with
            | [ x : value |- _ ] => destruct x
            | [ x : variable |- _ ] => destruct x
            | [ x : name |- _ ] => destruct x
            | [ x : id |- _ ] => destruct x
            | [ H : context[string_dec ?X ?Y] |- _ ] => destruct (string_dec X Y)
          end; simpl in *; subst); try solve [intuition]; try solve [discriminate Heq]);
      (injection Heq; intros; subst; clear Heq);
      (contradict Hnotin; rewrite free_ids_context_iff; eexists; eexists; split; eauto; simpl; auto).
Qed.

Lemma freeid_rename_ctx_in_variable : 
  forall x y rho G,
    ~ In y (free_ids_context G)
    ->
    CTX.In (ValVariable (Var (Free y)), rho) (freeid_rename_ctx x y G)
    -> 
    CTX.In (ValVariable (Var (Free x)), rho) G.
Proof.
  intros x y rho G Hnotin Hin.
  apply (proj1 (freeid_rename_ctx_in_all x _ rho _ Hnotin)); auto.
Qed.

Lemma freeid_rename_ctx_in_name: 
  forall x y rho G,
    ~ In y (free_ids_context G)
    ->
    CTX.In (ValName (Nm (Free y)), rho) (freeid_rename_ctx x y G)
    -> 
    CTX.In (ValName (Nm (Free x)), rho) G.
Proof.
  intros x y rho G Hnotin Hin.
  apply (proj1 (proj2 (freeid_rename_ctx_in_all x _ rho _ Hnotin))); auto.
Qed.

Lemma freeid_rename_ctx_in_coname: 
  forall x y rho G,
    ~ In y (free_ids_context G)
    ->
    CTX.In (ValName (CoNm (Free y)), rho) (freeid_rename_ctx x y G)
    -> 
    CTX.In (ValName (CoNm (Free x)), rho) G.
Proof.
  intros x y rho G Hnotin Hin.
  apply (proj2 (proj2 (freeid_rename_ctx_in_all x _ rho _ Hnotin))); auto.
Qed.

Lemma freeid_rename_value_variable : 
  forall x y z v,
    y <> z 
    ->
    ValVariable (Var (Free z)) = freeid_rename_value x y v
    ->
    ValVariable (Var (Free z)) = v.
Proof.
  intros x y z v Hneq Heq.
  (repeat (match goal with
             | [ x : value |- _ ] => destruct x
             | [ x : variable |- _ ] => destruct x
             | [ x : name |- _ ] => destruct x
             | [ x : id |- _ ] => destruct x
             | [ H : context[string_dec ?X ?Y] |- _ ] => destruct (string_dec X Y)
           end; simpl in *; subst); try solve [intuition]; try solve [discriminate Heq]).
  contradict Hneq.
  injection Heq; intros; auto.
Qed.

Lemma freeid_rename_value_name : 
  forall x y z v,
    y <> z 
    ->
    ValName (Nm (Free z)) = freeid_rename_value x y v
    ->
    ValName (Nm (Free z)) = v.
Proof.
  intros x y z v Hneq Heq.
  (repeat (match goal with
             | [ x : value |- _ ] => destruct x
             | [ x : variable |- _ ] => destruct x
             | [ x : name |- _ ] => destruct x
             | [ x : id |- _ ] => destruct x
             | [ H : context[string_dec ?X ?Y] |- _ ] => destruct (string_dec X Y)
           end; simpl in *; subst); try solve [intuition]; try solve [discriminate Heq]).
  contradict Hneq.
  injection Heq; intros; auto.
Qed.

Lemma freeid_rename_value_coname : 
  forall x y z v,
    y <> z 
    ->
    ValName (CoNm (Free z)) = freeid_rename_value x y v
    ->
    ValName (CoNm (Free z)) = v.
Proof.
  intros x y z v Hneq Heq.
  (repeat (match goal with
             | [ x : value |- _ ] => destruct x
             | [ x : variable |- _ ] => destruct x
             | [ x : name |- _ ] => destruct x
             | [ x : id |- _ ] => destruct x
             | [ H : context[string_dec ?X ?Y] |- _ ] => destruct (string_dec X Y)
           end; simpl in *; subst); try solve [intuition]; try solve [discriminate Heq]).
  contradict Hneq.
  injection Heq; intros; auto.
Qed.

Lemma freeid_rename_ctx_in_variable2 : 
  forall x y z rho G,
    y <> z
    -> 
    ~ In y (free_ids_context G)
    ->
    CTX.In (ValVariable (Var (Free z)), rho) (freeid_rename_ctx x y G)
    ->
    CTX.In (ValVariable (Var (Free z)), rho) G.
Proof.
  intros x y z rho G Hneq Hnotin Hin.
  rewrite freeid_rename_ctx_characterization in Hin.
  destruct Hin as [v Hin]; destruct Hin as [Heq Hin].
  pose (freeid_rename_value_variable x y z v Hneq Heq) as e.
  rewrite e; auto.
  auto.
Qed.

Lemma freeid_rename_ctx_in_name2 : 
  forall x y z rho G,
    y <> z
    -> 
    ~ In y (free_ids_context G)
    ->
    CTX.In (ValName (Nm (Free z)), rho) (freeid_rename_ctx x y G)
    ->
    CTX.In (ValName (Nm (Free z)), rho) G.
Proof.
  intros x y z rho G Hneq Hnotin Hin.
  rewrite freeid_rename_ctx_characterization in Hin.
  destruct Hin as [v Hin]; destruct Hin as [Heq Hin].
  pose (freeid_rename_value_name x y z v Hneq Heq) as e.
  rewrite e; auto.
  auto.
Qed.

Lemma freeid_rename_ctx_in_coname2 : 
  forall x y z rho G,
    y <> z
    -> 
    ~ In y (free_ids_context G)
    ->
    CTX.In (ValName (CoNm (Free z)), rho) (freeid_rename_ctx x y G)
    ->
    CTX.In (ValName (CoNm (Free z)), rho) G.
Proof.
  intros x y z rho G Hneq Hnotin Hin.
  rewrite freeid_rename_ctx_characterization in Hin.
  destruct Hin as [v Hin]; destruct Hin as [Heq Hin].
  pose (freeid_rename_value_coname x y z v Hneq Heq) as e.
  rewrite e; auto.
  auto.
Qed.

Lemma typed_rename_wf : 
  forall G x y, 
    G |-wf
    ->
    ~ In y (free_ids_context G)
    ->
    (freeid_rename_ctx x y G) |-wf.
Proof.
  intros G x y Hwf Hnotin.
  inversion Hwf; subst.
  constructor.
  intros u rho Hin.
  rewrite freeid_rename_ctx_characterization in Hin; auto.
  destruct Hin as [v Hu]; destruct Hu as [Heq Hu]; subst.
  apply freeid_rename_free_value.
  eapply H; eauto.

  intros u rho sigma Hin1 Hin2.
  rewrite freeid_rename_ctx_characterization in Hin1; auto.
  destruct Hin1 as [v1 Hu1]; destruct Hu1 as [Heq Hu1]; subst.
  rewrite freeid_rename_ctx_characterization in Hin2; auto.
  destruct Hin2 as [v2 Hu2]; destruct Hu2 as [Heq Hu2]; subst.
  apply freeid_rename_value_inj in Heq; [subst | auto | auto].
  apply (H0 v2 rho sigma); auto.
  eapply free_ids_value_context_contra; eauto.
  eapply free_ids_value_context_contra; eauto.

  intros z.
  destruct (string_dec y z); [subst; specialize (H1 x) | specialize (H1 z)];
    (destruct H1 as [Hu1|Hu1]; [left| destruct Hu1 as [Hu1 Hu2]; right; split];
      intros rho; specialize (Hu1 rho); try (specialize (Hu2 rho))).
  contradict Hu1; eapply freeid_rename_ctx_in_variable; eauto.
  contradict Hu1; eapply freeid_rename_ctx_in_name; eauto.
  contradict Hu2; eapply freeid_rename_ctx_in_coname; eauto.

  contradict Hu1; eapply freeid_rename_ctx_in_variable2; eauto.
  contradict Hu1; eapply freeid_rename_ctx_in_name2; eauto.
  contradict Hu2; eapply freeid_rename_ctx_in_coname2; eauto.
Qed.

(* ============================================================================= *)

Lemma typed_rename_part_free_ids_context_left : 
  forall G GL GR y, 
    G |-part GL (+) GR
    ->
    ~ In y (free_ids_context G)
    ->
    ~ In y (free_ids_context GL).
Proof.
  intros G GL GR y Hpart Hnotin.
  contradict Hnotin.
  rewrite free_ids_context_iff in *.
  repeat destruct Hnotin as [? Hnotin].
  repeat eexists; eauto.
  apply part_is_subset_left in Hpart.
  apply Hpart; eauto.
Qed.

Lemma freeid_rename_value_characterization : 
  forall x y u v,
    u <> v 
    -> 
    (u = freeid_rename_value x y v <-> v = freeid_rename_value y x u).
Proof.
  intros x y u v Hneq.
  (repeat (match goal with
             | [ x : value |- _ ] => destruct x
             | [ x : variable |- _ ] => destruct x
             | [ x : name |- _ ] => destruct x
             | [ x : id |- _ ] => destruct x
             | [ |- context[string_dec ?X ?Y] ] => destruct (string_dec X Y)
             | [ |- _ <-> _ ] => split; intros H
           end; simpl in *; subst)); 
  (try solve [discriminate H]);
  (try solve [left; auto]); 
  (try solve [right; auto]); 
  (try solve [auto]);
  (try solve [contradict n; injection H; intros; subst; auto]);
  (try solve [contradict Hneq; injection H; intros; subst; auto]).
Qed.

Lemma freeid_rename_value_cases : 
  forall x y u v,
    u = freeid_rename_value x y v
    ->
    (u = v \/ v = freeid_rename_value y x u).
Proof.
  intros x y u v Heq.
  destruct (value_dec u v).
  left; auto.
  right; rewrite freeid_rename_value_characterization; auto.
Qed.

Lemma freeid_rename_value_inversion : 
  forall x y u,
    ((forall v, u = freeid_rename_value x y v -> u = v)
    \/ (forall v, ~ In y (free_ids_value v) -> u = freeid_rename_value x y v -> v = freeid_rename_value y x u)).
Proof.
  intros x y u.
  (* if y is not in u, then forall v such that (u = freeid_rename_value x y v) we have (u = v).
     if y is in u, then forall v such that (CTX.In (v, _) G) /\ (u = freeid_rename_value x y v) we have (v = freeid_rename_value y x u).
      this second property makes use of the fact that y is not in G, so y is not in v, so u<>v. *)

  destruct (In_dec string_dec y (free_ids_value u)); [right|left]; intros v; [intros Hnotin Heq | intros Heq];
  (repeat (match goal with
             | [ x : value |- _ ] => destruct x
             | [ x : variable |- _ ] => destruct x
             | [ x : name |- _ ] => destruct x
             | [ x : id |- _ ] => destruct x
             | [ H : _ \/ _ |- _ ] => destruct H
             | [ |- context[string_dec ?X ?Y] ] => destruct (string_dec X Y)
           end; simpl in *; subst)); 
  try solve [auto];
  try solve [contradict n; auto];
  try solve [contradict Hnotin; auto].
Qed.

Lemma typed_rename_part : 
  forall G GL GR x y, 
    G |-part GL (+) GR
    ->
    ~ In y (free_ids_context G)
    ->
    (freeid_rename_ctx x y G) |-part (freeid_rename_ctx x y GL) (+) (freeid_rename_ctx x y GR).
Proof.
  intros G GL GR x y Hpart Hnotin.
  inversion Hpart; subst.
  constructor; [ | apply typed_rename_wf; auto | ].
  intros a; destruct a.
  rewrite CTXFacts.union_iff.
  repeat (rewrite freeid_rename_ctx_characterization); auto.

  split; intros Hin; (repeat destruct Hin as [? Hin]); subst.

  rewrite H in Hin; rewrite CTXFacts.union_iff in Hin; 
    destruct Hin as [Hin|Hin]; [
      left; eexists; split; [reflexivity|eauto]
      | right; eexists; split; [reflexivity|eauto]].

  destruct Hin as [Hin|Hin]; destruct Hin as [? Hin]; destruct Hin as [Heq Hin]; subst; eexists; rewrite H; rewrite CTXFacts.union_iff; 
    (split; [reflexivity|eauto]).

  apply partition_comm in Hpart; eapply typed_rename_part_free_ids_context_left; eauto.
  eapply typed_rename_part_free_ids_context_left; eauto.

  intros u rho.
  repeat rewrite freeid_rename_ctx_characterization.

  destruct (freeid_rename_value_inversion x y u).

  specialize (H1 u rho); destruct H1 as [H1|H1]; [left|right;destruct H1 as [H1|H1]; [left|right;auto]].
  contradict H1; destruct H1 as [v Hin]; destruct Hin as [Heq Hin]; subst; rewrite (H2 v (eq_refl)); auto.
  contradict H1; destruct H1 as [v Hin]; destruct Hin as [Heq Hin]; subst; rewrite (H2 v (eq_refl)); auto.

  specialize (H1 (freeid_rename_value y x u) rho); destruct H1 as [H1|H1]; [left|right;destruct H1 as [H1|H1]; [left|right;auto]];
    contradict H1; destruct H1 as [v Hin]; destruct Hin as [Heq Hin]; subst;
      erewrite <- H2; eauto;
        rewrite free_ids_context_iff in Hnotin; auto;
          contradict Hnotin; eexists; eexists; split; eauto; rewrite H; rewrite CTXFacts.union_iff;
            (solve [left; eauto] || solve [right; eauto]).

  apply partition_comm in Hpart; eapply typed_rename_part_free_ids_context_left; eauto.
  eapply typed_rename_part_free_ids_context_left; eauto.
Qed.

(* ============================================================================= *)

Lemma typed_rename_ctx :
  forall G v rho x y,
    CTX.In (v, rho) G
    ->
    ~ In y (free_ids_context G)
    ->
    CTX.In (freeid_rename_value x y v, rho) (freeid_rename_ctx x y G).
Proof.
  intros G v rho x y Hin Hnotin.
  rewrite freeid_rename_ctx_characterization; auto.
  exists v; split; auto.
Qed.

(* ============================================================================= *)

Lemma typed_rename_lookup : 
  forall G v rho x y, 
    G |-v v : rho
    ->
    ~ In y (free_ids_context G)
    ->
    (freeid_rename_ctx x y G) |-v (freeid_rename_value x y v) : rho.
Proof.
  intros G v rho x y Hlookup Hnotin.
  inversion Hlookup; subst.
  apply LContext.
  apply typed_rename_wf; auto.
  apply typed_rename_ctx; auto.
  apply LToken.
  apply typed_rename_wf; auto.
Qed.

(* ============================================================================= *)

Lemma free_values_freeid_rename_value : 
  forall w x y v, 
    ~ In y (free_ids_value w)
    ->
    (In v (free_values_value (freeid_rename_value x y w)) <-> exists u, v = freeid_rename_value x y u /\ In u (free_values_value w)).
Proof.
  intros w x y v Hnotin.
  split; intros Hin.
  (repeat (match goal with
             | [ x : value |- _ ] => destruct x
             | [ x : variable |- _ ] => destruct x
             | [ x : name |- _ ] => destruct x
             | [ x : id |- _ ] => destruct x
             | [ H : context[string_dec ?X ?Y] |- _ ] => destruct (string_dec X Y)
             | [ |- context[string_dec ?X ?Y] ] => destruct (string_dec X Y)
             | [ H : _ \/ False |- _ ] => destruct H
             | [ |- exists u : value, _ /\ (_ = u \/ False) ] => eexists; split; [|left; reflexivity]
           end; simpl in *; subst
  ));
  (try solve [discriminate H]);
  (try solve [intuition]).

  destruct Hin as [u Hin]; destruct Hin as [Heq Hin]; subst.
  (repeat (match goal with
             | [ x : value |- _ ] => destruct x
             | [ x : variable |- _ ] => destruct x
             | [ x : name |- _ ] => destruct x
             | [ x : id |- _ ] => destruct x
             | [ H : context[string_dec ?X ?Y] |- _ ] => destruct (string_dec X Y) in H
             | [ |- context[string_dec ?X ?Y] ] => destruct (string_dec X Y)
             | [ H : _ \/ False |- _ ] => destruct H
           end; simpl in *; subst
  ));
  (try solve [discriminate H]);
  (try solve [contradict Hnotin; injection H; intros; subst; auto]);
  (try solve [intuition]).
Qed.

Lemma demorgan_proj_left : forall P Q, ~ (P \/ Q) -> ~P. tauto. Qed.
Lemma demorgan_proj_right : forall P Q, ~ (P \/ Q) -> ~Q. tauto. Qed.

Lemma free_values_freeid_rename_proc :
  forall P x y v,
    ~ In y (free_ids_proc P)
    ->
    (In v (free_values_proc (freeid_rename_proc x y P)) <-> exists u, v = freeid_rename_value x y u /\ In u (free_values_proc P)).
Proof.
  intros P; induction P; intros x y v1 Hnotin; simpl in *; 
    ((split; intros Hin); 
      [
        | destruct Hin as [w Hin]; destruct Hin as [Heq Hin]; subst
      ]); 
    (repeat (
      (rewrite in_app_iff in *) || 
        (destruct Hin as [Hin|Hin]) ||
          (rewrite free_values_freeid_rename_value)));
    (try solve [auto; left; eexists; split; [reflexivity|]; auto]);
    (try solve [auto; right; left; eexists; split; [reflexivity|]; auto]);
    (try solve [right; rewrite IHP; auto; eexists; split; [reflexivity|]; auto]);
    (try solve [right; right; rewrite IHP; auto; eexists; split; [reflexivity|]; auto]);
    auto;
      (try solve [
        rewrite free_values_freeid_rename_value in Hin; auto;
          destruct Hin as [w Hin]; destruct Hin as [Heq Hin]; subst;
            eexists; repeat (rewrite in_app_iff in *); split; [reflexivity|]; auto]);
      (try solve [rewrite IHP; auto; eexists; eauto]);
      (try solve [
        specialize (IHP x y v1 (Hnotin)); rewrite IHP in Hin; 
          destruct Hin as [u Hin]; destruct Hin as [Heq Hin]; subst; 
            eexists; repeat (rewrite in_app_iff); eauto]);
      (try solve [
        specialize (IHP x y v1 (demorgan_proj_right _ _ Hnotin )); rewrite IHP in Hin; 
          destruct Hin as [u Hin]; destruct Hin as [Heq Hin]; subst; 
            eexists; repeat (rewrite in_app_iff); eauto]);
      (try solve [
        specialize (IHP x y v1 (demorgan_proj_right _ _ (demorgan_proj_right _ _ Hnotin ))); rewrite IHP in Hin; 
          destruct Hin as [u Hin]; destruct Hin as [Heq Hin]; subst; 
            eexists; repeat (rewrite in_app_iff); eauto]);
      (try solve [
        rewrite IHP1 in Hin; auto; destruct Hin as [w Hin]; destruct Hin as [Heq Hin]; subst; eexists; 
          repeat (rewrite in_app_iff); split; [reflexivity|]; auto]);
      (try solve [
        rewrite IHP2 in Hin; auto; destruct Hin as [w Hin]; destruct Hin as [Heq Hin]; subst; eexists; 
          repeat (rewrite in_app_iff); split; [reflexivity|]; auto]);
      (try solve [
        rewrite IHP1; auto; left; eexists; split; [reflexivity|auto]]);
      (try solve [
        rewrite IHP2; auto; right; eexists; split; [reflexivity|auto]]).
intuition.
Qed.

(* ============================================================================= *)

Lemma typed_rename_free_values_in_context : 
  forall G P x y,
    free_values_in_context G P
    ->
    ~ In y (free_ids_context G)
    ->
    free_values_in_context (freeid_rename_ctx x y G) (freeid_rename_proc x y P).
Proof.
  intros G P x y Hfvic Hnotin.
  unfold free_values_in_context.
  intros u Hin.
  rewrite free_values_freeid_rename_proc in Hin.
  destruct Hin as [w Hin]; destruct Hin as [Heq Hin]; subst.
  apply Hfvic in Hin.
  destruct Hin as [sigma Hin]; eauto.
  eexists; auto.
  rewrite freeid_rename_ctx_characterization.
  eexists; split; [reflexivity|]; eauto.
  eauto.
  contradict Hnotin.
  rewrite free_ids_context_iff.
  apply free_ids_values_proc in Hnotin.
  destruct Hnotin as [w Hnotin]; destruct Hnotin as [Hin1 Hin2].
  apply Hfvic in Hin1.
  destruct Hin1 as [sigma Hin1].
  eexists; eexists; eauto.
Qed.

(* ============================================================================= *)

Lemma typed_rename_ctx_subst : 
  forall x y G1 G2,
    ~ In y (free_ids_context G2)
    ->
    CTX.Subset G1 G2
    ->
    CTX.Subset (freeid_rename_ctx x y G1) (freeid_rename_ctx x y G2).
Proof.
  intros x y G1 G2 Hnotin Hsubset.
  intros a Hin; destruct a.
  pose (free_ids_context_subset y _ _ Hsubset Hnotin).
  rewrite freeid_rename_ctx_characterization in *; auto.
  destruct Hin as [w Hin]; destruct Hin as [Heq Hin]; subst.
  eexists; split; [reflexivity|auto].
Qed.

(* ============================================================================= *)

Lemma typed_rename : 
  forall P G, 
    G |-p P
    ->
    forall x y,
      ~ In y (free_ids_context G)
      ->
      (freeid_rename_ctx x y G) |-p (freeid_rename_proc x y P).
Proof.
  intros P G Htyp; induction Htyp; intros x y Hnotin_yG; simpl in *.

  SCase "Input"%string.
  clear H1.
  apply TypPrefixInput with (L:=x::y::(L++(free_ids_context G))) (s:=s).  
  apply typed_rename_lookup; auto.
  apply typed_rename_free_values_in_context; auto.
  intros G' rho t z Hnotin Htrans Heq; subst.
  apply local_result_rename_not_in_aux in Hnotin; 
    destruct Hnotin as [Hv1 Hnotin]; destruct Hnotin as [Hv2 Hnotin]; destruct Hnotin as [Hv3 Hv4].
  rewrite <- freeid_rename_proc_open_comm; try solve [intuition].
  specialize (H2 _ rho t z Hv3 Htrans eq_refl x y).
  eapply ctx_equal_preserves_typed; [ | apply ctx_rename_over_prefix_input]; auto; [apply H2; auto | | ]; clear H2.

  apply free_ids_context_add_replace; auto.

  eapply lookup_wf_ctx; eauto.
  
  inversion H; auto.

  SCase "Output"%string.
  (destruct (value_dec u v) as [He|Hn]; [ SSSCase "u=v /\ |-st rho"%string | SSSCase "u<>v"%string]; [subst|]);
  (destruct H3 as [H3|H3]; [SSCase "stateful"%string | SSCase "stateless"%string];
    [|destruct H3]; subst; 
      eapply TypPrefixOutput with (s:=s) (rho:=rho) (t:=t); try solve [assumption || reflexivity]; 
        try solve [apply typed_rename_lookup; auto]).
  
  (* u = v /\ |-st rho *)
  destruct H0 as [H0|H0]; [contradict H0; reflexivity|].
  assert (rho=TChannel s); [|subst].
  inversion H1; subst.
  inversion H2; subst.
  inversion H3; subst.
  apply (H8 v rho (TChannel s)); auto.
  inversion H5; subst.
  assert (free_value k) as Hu; [eapply H6; eauto|inversion Hu].
  right; auto.
  left; reflexivity.

  eapply ctx_equal_preserves_typed; auto; [apply IHHtyp; clear IHHtyp|].
  rewrite free_ids_context_iff in *; contradict Hnotin_yG.
  destruct Hnotin_yG as [w Hnotin_yG]; destruct Hnotin_yG as [sigma Hnotin_yG]; destruct Hnotin_yG as [Hu1 Hu2].
  unfold ctx_replace in Hu1; (repeat (rewrite CTXFacts.add_iff in Hu1 || rewrite CTXFacts.remove_iff in Hu1)).
  destruct Hu1 as [Hu1 | Hu1]; [injection Hu1; intros; subst; clear Hu1 | ]. 
  inversion H1; subst; eexists; eexists; split; eauto.
  destruct Hu1 as [Hu1 Hu3]; destruct Hu1 as [Hu1 Hu4].
  eexists; eexists; split; eauto.

  assert (rho = TChannel s); [|subst].
  inversion H1; subst.
  inversion H2; subst.
  inversion H3; subst.
  apply (H8 v rho (TChannel s)); auto.
  inversion H5; subst.
  assert (free_value k) as Hu; [eapply H6; eauto|inversion Hu].
  inversion H1.
  apply ctx_rename_over_prefix_output3; auto.

  right; auto.

  right; split; auto.

  eapply ctx_equal_preserves_typed; [ | apply ctx_rename_over_prefix_output2]; auto;
    [ | try (eapply lookup_wf_ctx; eauto) | inversion H1; auto].
  apply IHHtyp; clear IHHtyp.

  apply free_ids_context_replace_other; auto.

  (* u<>v *)
  left.
  contradict Hn; apply (freeid_rename_value_inj x y); auto.
  eapply free_ids_value_context_lookup_contra; eauto.
  eapply free_ids_value_context_lookup_contra; eauto.

  left; reflexivity.

  eapply ctx_equal_preserves_typed; [ | apply ctx_rename_over_prefix_output1]; auto;
    [ | try (eapply lookup_wf_ctx; eauto) | inversion H1; auto].
  apply IHHtyp; clear IHHtyp.

  rewrite free_ids_context_iff in *; contradict Hnotin_yG.
  destruct Hnotin_yG as [w Hnotin_yG]; destruct Hnotin_yG as [sigma Hnotin_yG]; destruct Hnotin_yG as [Hu1 Hu2].
  unfold ctx_replace in Hu1; (repeat (rewrite CTXFacts.add_iff in Hu1 || rewrite CTXFacts.remove_iff in Hu1)).
  destruct Hu1 as [Hu1 | Hu1]; [injection Hu1; intros; subst; clear Hu1 | ].
  inversion H1; subst; eexists; eexists; split; eauto.
  destruct Hu1 as [Hu1 Hu3]; destruct Hu1 as [Hu1 Hu4].
  eexists; eexists; split; eauto.

  left; contradict Hn; apply (freeid_rename_value_inj x y); auto.
  eapply free_ids_value_context_lookup_contra; eauto.
  eapply free_ids_value_context_lookup_contra; eauto.

  right; split; [reflexivity|auto].

  eapply ctx_equal_preserves_typed; [ | apply ctx_rename_over_prefix_output2]; auto;
    [ | try (eapply lookup_wf_ctx; eauto) | inversion H1; auto].
  apply IHHtyp; clear IHHtyp.

  apply free_ids_context_replace_other; auto.

  
  SCase "Par"%string.
  eapply TypPar; [
    apply typed_rename_part; eauto
    | apply IHHtyp1
    | apply IHHtyp2
  ].

  eapply free_ids_context_subset; eauto; eapply part_is_subset_left; eauto.

  eapply free_ids_context_subset; eauto; eapply part_is_subset_right; eauto.

  SCase "Sum"%string.
  apply TypSum.
  apply IHHtyp1; auto.
  apply IHHtyp2; auto.

  SCase "IsEq"%string.
  apply TypIsEq with (K:=K) (L:=L).
  apply typed_rename_lookup; auto.
  apply typed_rename_lookup; auto.
  apply typed_rename_free_values_in_context; auto.
  intros Heq; subst.
  apply H3; auto.

  SCase "IsNotEq"%string.
  apply TypIsNotEq with (K:=K) (L:=L).
  apply typed_rename_lookup; auto.
  apply typed_rename_lookup; auto.
  apply typed_rename_free_values_in_context; auto.
  intros Hneq.
  apply H3; auto.

  SCase "New"%string.
  eapply TypNew with (L:=x::y::(L++(free_ids_context G))).
  intros z G2 Hnotin Heq; subst.
  apply local_result_rename_not_in_aux in Hnotin; 
    destruct Hnotin as [Hv1 Hnotin]; destruct Hnotin as [Hv2 Hnotin]; destruct Hnotin as [Hv3 Hv4].
  eapply ctx_equal_preserves_typed; [ | apply ctx_rename_over_new]; auto.
  rewrite <- freeid_rename_proc_open_comm; try solve [intuition].
  apply H0; try auto.

  apply free_ids_context_add; auto.

  eapply subset_preserves_well_formed_ctx.
  eapply typed_ctx_wf.
  apply H; [ eauto | reflexivity ].
  intuition.

  SCase "Rep"%string.
  apply TypRep with (G':=freeid_rename_ctx x y G').
  apply typed_rename_wf; auto.

  apply typed_rename_ctx_subst; auto.

  intros u rho Hin.
  rewrite freeid_rename_ctx_characterization in Hin.
  destruct Hin as [v Hin]; destruct Hin as [Heq Hin]; subst.
  eapply H1; eauto.

  eapply free_ids_context_subset; eauto.

  apply IHHtyp; auto.
  eapply free_ids_context_subset; eauto.
  
  SCase "Zero"%string.
  apply TypZero.
  apply typed_rename_wf; auto.
Qed.


(* ============================================================================= *)


Lemma freeid_rename_ctx_empty :
  forall x y, CTX.eq (freeid_rename_ctx x y CTX.empty) CTX.empty.
Proof.
  intros x y a; destruct a; split; intros Hin.
  rewrite freeid_rename_ctx_characterization in *.
  destruct Hin as [u Hin]; destruct Hin as [Hin1 Hin2];
    rewrite CTXFacts.empty_iff in Hin2; destruct Hin2.
  rewrite free_ids_context_iff.
  intros Hin2.
  destruct Hin2 as [u Hin2]; destruct Hin2 as [rho Hin2];
    destruct Hin2 as [Hin2 Hin3]; rewrite CTXFacts.empty_iff in Hin2;
    destruct Hin2.
  rewrite CTXFacts.empty_iff in Hin; destruct Hin.
Qed.


(* ============================================================================= *)

