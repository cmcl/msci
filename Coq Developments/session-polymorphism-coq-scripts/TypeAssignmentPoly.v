Require Export Arith.EqNat.
Require Export Arith.Lt.
Require Export Arith.Compare_dec.
Require Export List.
Require Import String.
Require Import TacticsSF.
Require Import TacticsCPDT.
Require Export Process.
Require Import Bool.

(* ============================================================================= *)

Inductive type : Set := 
| TChannel : session -> type
| TSingleton : token -> type

with message : Set :=
| MInp : type -> message
| MOut : type -> message

with session : Set :=
(* general purpose *)
| SEpsilon : session
| SPrefix : message -> session -> session
| SUnion : session -> session -> session
| SSeq : session -> session -> session
| SRep : session -> session
| SDual : session -> session
(* sink *)
| SSink : session
(* uni-forwarder *)
| SFwd : session -> session
| SInOut : session
| SInOut1 : session -> session
(* abp *)
| SToks : session -> session
| SNack : session -> token -> session -> token -> session
| SNack1 : session -> token -> session -> token -> session
| SAck : session -> token -> session
| SAck1 : session -> token -> session
| SAck2 : session -> token -> session
(* abp_send *)
| SSend : bool -> session (* a fresh channel for passing args *)
(* a channel for passing args where the token has been passed *)
| SSend1 : bool -> session -> session -> session
(* a channel for passing args where the token and "inp" channel has been
   passed, and "err1" is next *)
| SSend2 : bool -> session -> session
(* abp_recv *)
| SRecv : bool -> session (* a fresh channel for passing args *)
(* a channel for passing args where err2 has been passed.
  need bool to bind i, 1st session for s, and 2nd session for t *)
| SRecv1 : bool -> session -> session -> session
(* abp_lossy *)
| SLossy : session (* a fresh channel for passing args *)
(* a channel for passing args where err1 has been passed.
  need to bind s and t: 1st param is s, 2nd is t *)
| SLossy1 : session -> session -> session
.

Inductive terminates : session -> Prop := 
| TMEpsilon : terminates SEpsilon
| TMUnion1 : forall s1 s2, terminates s1 -> terminates (SUnion s1 s2)
| TMUnion2 : forall s1 s2, terminates s2 -> terminates (SUnion s1 s2)
| TMSeq : forall s1 s2, terminates s1 -> terminates s2 -> terminates (SSeq s1 s2)
| TMRep : forall s, terminates s -> terminates (SRep s)
| TMDual : forall s, terminates s -> terminates (SDual s). 

Definition m_dual (m:message) : message := 
  match m with
  | MInp a => MOut a
  | MOut a => MInp a
  end.

(* ============================================================================= *)

Require Import String.

Definition string_of_bool (b:bool) := if b then "true"%string else "false"%string.

Definition bool_of_string (s:string) :=
  match s with
    | "false"%string => false
    | _ => true
  end.

Definition string_of_negb_string (s:string) :=
  string_of_bool (negb (bool_of_string s)).

Definition token_of_negb_token (tok:token) :=
  match tok with
    | Token s => Token (string_of_negb_string s)
  end.

Definition token_of_bool (b : bool) := Token (string_of_bool b).

Reserved Notation "s -- m --> t" (no associativity, at level 90).

Inductive transition : session -> message -> session -> Prop := 
(* general purpose *)
| TRPrefix : forall s m, (SPrefix m s) --m--> s
| TRUnion1 : forall s1 s2 t1 m, s1 --m--> t1 -> (SUnion s1 s2) --m--> t1
| TRUnion2 : forall s1 s2 t2 m, s2 --m--> t2 -> (SUnion s1 s2) --m--> t2
| TRSeq1 : forall s1 s2 t1 m, s1 --m--> t1 -> (SSeq s1 s2) --m--> (SSeq t1 s2)
| TRSeq2 : forall s1 s2 t2 m, terminates s1 -> s2 --m--> t2 -> (SSeq s1 s2) --m--> t2
| TRRep : forall s t m, s --m--> t -> (SRep s) --m--> (SSeq t (SRep s))
| TRDual : forall s t m, s --m--> t -> (SDual s) --(m_dual m)--> (SDual t)
(* sink *)
| TRSink : forall s, SSink --(MInp (TChannel s))--> SSink
(* uni-forwarder *)
| TRFwd : forall s, SFwd s --(MInp (TChannel s))--> SFwd s
| TRInOut : forall s, SInOut --(MInp (TChannel s))--> SInOut1 s
| TRInOut1 : forall s, SInOut1 s --(MInp (TChannel (SDual s)))--> SEpsilon
(* abp *)
| TRToks : forall s s' tok, s --(MInp (TSingleton tok))--> s' ->
    SToks s --(MInp (TSingleton tok))--> SToks s'
| TRAckA : forall s bit, SAck s bit --(MOut (TSingleton bit))--> SAck1 s bit
| TRAck1A : forall s bit tok,
    SAck1 s bit --(MOut (TSingleton tok))--> SAck s bit
| TRAckB : forall s bit, SAck s bit --(MInp (TSingleton bit))--> SAck s bit
| TRAckC : forall s tok s' bit, s --(MInp (TSingleton tok))--> s' ->
    SAck s bit --(MOut (TSingleton (token_of_negb_token bit)))--> SAck2 s bit
| TRAck2A : forall s tok s' bit, s --(MInp (TSingleton tok))--> s' ->
    SAck2 s bit --(MOut (TSingleton tok))-->
      SNack s tok s' (token_of_negb_token bit)
| TRNackA : forall s tok s' bit, s --(MInp (TSingleton tok))--> s'
    -> SNack s tok s' bit --(MOut (TSingleton bit))--> SNack1 s tok s' bit
| TRNack1A : forall s tok s' bit, s --(MInp (TSingleton tok))--> s'
    -> SNack1 s tok s' bit --(MOut (TSingleton tok))--> SNack s tok s' bit
| TRNackB : forall s tok s' bit, SNack s tok s' bit
    --(MInp (TSingleton (token_of_negb_token bit)))--> SNack s tok s' bit
| TRNackC : forall s tok s' bit, SNack s tok s' bit
    --(MInp (TSingleton bit))--> SAck s' bit
(* abp_send *)
| TRSendA : forall i k r r', r --(MInp (TSingleton k))--> r' ->
    SSend i --(MInp (TSingleton k))-->
      SSend1 i r' (SNack r k r' (token_of_bool i))
| TRSendB : forall i k r r', r --(MInp (TSingleton k))--> r' ->
    SSend i --(MInp (TSingleton k))-->
      SSend1 i r' (SAck r (token_of_bool (negb i)))
| TRSend1A : forall i r' s, SSend1 i r' s --(MInp (TChannel (SToks r')))-->
      SSend2 i s
| TRSend2A : forall i s, SSend2 i s --(MInp (TChannel s))--> SEpsilon
(* abp_recv *)
| TRRecvA : forall i k r s t, s = (SNack r k t (token_of_bool (negb i))) ->
    SRecv i --(MInp (TChannel (SDual s)))--> SRecv1 i s t
| TRRecvB : forall i s t, s = (SAck t (token_of_bool (negb i))) ->
    SRecv i --(MInp (TChannel (SDual s)))--> SRecv1 i s t
| TRRecv1A : forall i s t,
    SRecv1 i s t --(MInp (TChannel (SDual (SToks (t)))))--> SEpsilon
(* abp_lossy *)
| TRLossyA : forall i r s t, s = (SAck r (token_of_bool i)) ->
    t = (SAck r (token_of_bool i)) ->
    SLossy --(MInp (TChannel (SDual s)))--> SLossy1 s t
| TRLossyB : forall i r k r' s t, s = (SNack r k r' (token_of_bool i)) ->
    t = (SNack r k r' (token_of_bool i)) ->
    SLossy --(MInp (TChannel (SDual s)))--> SLossy1 s t
| TRLossyC : forall i r k r' s t, s = (SNack r k r' (token_of_bool (negb i))) ->
    t = (SAck r (token_of_bool i)) ->
    SLossy --(MInp (TChannel (SDual s)))--> SLossy1 s t
| TRLossyD : forall i r k r' s t, s = (SNack r k r' (token_of_bool i)) ->
    t = (SAck r' (token_of_bool i)) ->
    SLossy --(MInp (TChannel (SDual s)))--> SLossy1 s t
| TRLossy1A : forall s t,
    SLossy1 s t --(MInp (TChannel t))--> SEpsilon
where "s -- m --> t" := (transition s m t).

(* ============================================================================= *)

Scheme 
  message_session_type_rec := Induction for message Sort Set
  with session_message_type_rec := Induction for session Sort Set
  with type_session_message_rec := Induction for type Sort Set.

Lemma type_dec : forall x y : type, {x = y} + {~ (x = y)}.
Proof.
  Ltac destruct_top_level := 
    repeat 
      match goal with 
        | [ |- forall x : _ , ( { _ } + { _ } ) ] => 
          let i := fresh "i" in intro i; destruct i 
        | [ |- forall x : _ , _ ] => intro
      end.
  Ltac decide_arg_eq_aux E F := 
    match E with 
      | F => left; reflexivity
      | ?P ?X => 
        match F with 
          | ?Q ?Y => 
            cut ({X = Y} + {X <> Y});
            [| apply token_dec || apply bool_dec || intuition];
            let i := fresh "i" in let n := fresh "n" in intro i; destruct i as [?|n]; [subst; auto | right; contradict n; injection n; intros; subst; reflexivity];
            decide_arg_eq_aux P Q
        end
      | _ => right; crush
    end.
  Ltac decide_arg_eq :=
    match goal with 
      | [ |- { ?P = ?Q } + { _ } ] => decide_arg_eq_aux P Q
    end.

  intros x.
  eapply type_session_message_rec
    with 
      (P := fun m1:message => forall m2:message, {m1=m2} + {m1<>m2} ) 
      (P0 := fun s1:session => forall s2:session, {s1=s2} + {s1<>s2} )
      (P1 := fun rho1:type => forall rho2:type, {rho1=rho2} + {rho1<>rho2} ); clear x; 
  destruct_top_level;
  decide_arg_eq.
Qed.

(* ============================================================================= *)

Lemma m_dual_is_dual : 
  forall m, m_dual (m_dual m) = m.
Proof.
  destruct m; intuition.
Qed.

(* ============================================================================= *)

Reserved Notation "|-st rho" (no associativity, at level 90).

Inductive stateless : type -> Prop := 
| STChannel : forall s, (forall m t, s --m--> t -> s = t) -> stateless (TChannel s)
| STToken : forall k, stateless (TSingleton k)
where "|-st rho" := (stateless rho).

(* ============================================================================= *)

Definition session_always (s1 s2 : session) : Prop :=
  forall m t, s1 --m--> t -> t = s2.

(* ============================================================================= *)

Definition ctx_elt : Set := (prod value type).

Require Import MSets.MSetWeakList.
Require Import MSets.MSetProperties.
Require Import Structures.Equalities.
Require Import MSets.MSetInterface.

Module ctx_elt_as_DT <: DecidableType.

  Definition t : Type := ctx_elt.

  Definition eq : t -> t -> Prop := @eq t.
  Lemma eq_dec : forall a b : ctx_elt, {a = b} + {a <> b}.
  Proof.
    decide equality.
    destruct (type_dec b0 t0); [rewrite <- e; clear e|]; intuition.
  Qed.

  Definition eq_equiv : Equivalence eq := @eq_equivalence ctx_elt.

End ctx_elt_as_DT.

(* Removed for Coq 8.3: "with Module E := ctx_elt_as_DT" *)
Module CTX : WSets with Module E := ctx_elt_as_DT :=
  MSetWeakList.Make ctx_elt_as_DT.

Module CTXFacts := MSets.MSetFacts.WFacts CTX.
Module CTXProperties := MSets.MSetProperties.WProperties CTX.

Definition ctx := CTX.t.

Definition ctx_replace (u : value) (old new : type) (G : ctx) : ctx :=
  CTX.add (u, new) (CTX.remove (u, old) G).

(* ============================================================================= *)

Inductive fresh_for_ctx : value -> ctx -> Prop := 
| FContext : 
  forall u G, 
    free_value u
    ->
    (forall v sigma, ~ CTX.In (v, sigma) G \/ ~ free_ids_value u = free_ids_value v)
    -> 
    fresh_for_ctx u G
| FToken : forall (k : token) G, fresh_for_ctx k G.

(* ============================================================================= *)

Definition free_values_in_context (G : ctx) (P : proc) : Prop := 
  forall u, In u (free_values_proc P) -> exists sigma, CTX.In (u, sigma) G.

(* ============================================================================= *)

Reserved Notation "G |-wf" (no associativity, at level 90).

Inductive wellformed_ctx : ctx -> Prop := 
| WFCtx :
  forall G, 
    (forall u rho, CTX.In (u, rho) G -> free_value u)
    ->
    (forall u rho sigma, CTX.In (u, rho) G -> CTX.In (u, sigma) G -> rho = sigma)
    ->
    (forall x, 
      (forall rho, ~ CTX.In (ValVariable (Var (Free x)), rho) G) \/
      ((forall rho, ~ CTX.In (ValName (Nm (Free x)), rho) G) /\
        (forall rho, ~ CTX.In (ValName (CoNm (Free x)), rho) G)))
    ->
    G |-wf 
where "G |-wf" := (wellformed_ctx G).

(* ============================================================================= *)

Inductive partition : ctx -> ctx -> ctx -> Prop := 
| Partition : forall G GL GR,
    (CTX.eq G (CTX.union GL GR))
    ->
    G |-wf
    ->
    (forall u rho, (~ CTX.In (u, rho) GL) \/ (~ CTX.In (u, rho) GR) \/ ( |-st rho ))
    ->
    partition G GL GR.

Notation "G |-part GL (+) GR" := (partition G GL GR) (no associativity, at level 90).

(* ============================================================================= *)

Reserved Notation "G |-v u : rho" (no associativity, at level 90, u at next level).

(* lookup_value only finds values with Free in them, not Bound. *)
Inductive lookup_value : ctx -> value -> type -> Prop :=
| LContext : forall u rho G, G |-wf -> (CTX.In (u, rho) G) -> G |-v u : rho
| LToken : forall (k : token) G, G |-wf -> G |-v k : (TSingleton k)
where "G |-v u : rho" := (lookup_value G u rho).

(* ============================================================================= *)

Lemma wellformed_lookup_is_free : 
  forall G u rho, 
    (G |-wf) -> (G |-v u : rho) -> 
    ((free_value u) \/ (exists k:token, u = k)).
Proof.
  intros G u rho Hwf Hlu_u.
  inversion Hlu_u; [left; subst | right; exists k; intuition].
  inversion Hwf; subst.
  eapply H1; eauto.
Qed.

(* ============================================================================= *)

Lemma prod_eq_elim_fst :
  forall A B (x1 x2 : A) (y1 y2:B), (x1, y1) = (x2, y2) -> x1 = x2.
Proof.
  intros.
  replace x1 with (fst (x1, y1)); intuition.
  replace x2 with (fst (x2, y2)); intuition.
  rewrite <- H; auto.
Qed.  

Lemma prod_eq_elim_snd :
  forall A B (x1 x2 : A) (y1 y2:B), (x1, y1) = (x2, y2) -> y1 = y2.
Proof.
  intros.
  replace y1 with (snd (x1, y1)); intuition.
  replace y2 with (snd (x2, y2)); intuition.
  rewrite <- H; auto.
Qed.  

(* ============================================================================= *)

Lemma list_add_4 : 
  forall a1 a2 G, CTX.In a1 (CTX.add a2 G) -> ~ CTX.In a1 G -> a1 = a2.
Proof.
  intros. 
  destruct (CTX.E.eq_dec a1 a2); subst; auto.
  contradict H0.
  eapply CTXFacts.add_3; eauto.
Qed.

(* ============================================================================= *)

Reserved Notation "G |-p P" (no associativity, at level 90).

Inductive typed : ctx -> proc -> Prop := 
| TypPrefixInput :
  forall G u P s L,
    (G |-v u : TChannel s)
    ->
    (* The following condition controls free_values when there are no transitions from s. *)
    free_values_in_context G P
    ->
    (forall G' rho t x,
      ~ (In x L) 
      ->
      (transition s (MInp rho) t)
      -> 
      G' = (CTX.add (ValVariable (Var (Free x)), rho) 
             (ctx_replace u (TChannel s) (TChannel t)
               G))
      ->
      (G' |-p (open_proc x 0 P)))
    ->
    (G |-p (u ? ; P))
| TypPrefixOutput : 
  forall G G' G'' u v P s rho t,
    (transition s (MOut rho) t)
    ->
    (u <> v \/ |-st rho)
    -> 
    (G |-v u : TChannel s)
    -> 
    (G |-v v : rho)
    -> 
    (G' = CTX.remove (v, rho) G \/ (G' = G /\ |-st rho))
    ->
    G'' = ctx_replace u (TChannel s) (TChannel t) G'
    ->
    G'' |-p P
    ->
    G |-p (u ! v ; P)
| TypPar : 
  forall G GL GR P Q,
      G |-part GL (+) GR
      ->
      GL |-p P
      ->
      GR |-p Q
      -> 
      G |-p (P ||| Q)
| TypSum : forall G P Q, G |-p P -> G |-p Q -> G |-p P +++ Q
| TypIsEq : 
    forall G P u v K L,
      G |-v u : TSingleton K
      ->
      G |-v v : TSingleton L
      ->
      free_values_in_context G P
      ->
      (K = L -> G |-p P) 
      -> 
      G |-p (IsEq u v P)
| TypIsNotEq : 
    forall G P u v K L,
      G |-v u : TSingleton K
      ->
      G |-v v : TSingleton L
      ->
      free_values_in_context G P
      ->
      (K <> L -> G |-p P) 
      -> 
      G |-p (IsNotEq u v P)
| TypNew : 
  forall G P s L,
    (forall x G',
      ~ (In x L) 
      ->
      G' = (CTX.add (ValName (Nm (Free x)), TChannel s)
             (CTX.add (ValName (CoNm (Free x)), TChannel (SDual s))
               G))
      ->
      G' |-p open_proc x 0 P)
    -> 
    G |-p (New P)
| TypRep : 
  forall G G' P,
    G |-wf
    ->
    CTX.Subset G' G
    ->
    (forall u rho, CTX.In (u, rho) G' -> |-st rho)
    ->
    G' |-p P
    ->
    G |-p (Rep P)
| TypZero : forall G, G |-wf -> G |-p Zero
where "G |-p P" := (typed G P).

(* ============================================================================= *)

Inductive dual_types : type -> type -> Prop :=
| DTLeft : forall s, dual_types (TChannel s) (TChannel (SDual s))
| DTRight : forall s, dual_types (TChannel (SDual s)) (TChannel s).

Inductive dual_types_transition : type -> type -> message -> type -> type -> Prop :=
| DTTLeft : forall s m t, (transition s m t) -> dual_types_transition (TChannel s) (TChannel (SDual s)) m (TChannel t) (TChannel (SDual t))
| DTTRight : forall s m t, (transition s (m_dual m) t) -> dual_types_transition (TChannel (SDual s)) (TChannel s) m (TChannel (SDual t)) (TChannel t).

Definition ctx_matched_names (G1 : CTX.t) : Prop := 
  forall nm1 nm2 rho sigma,
    dual_name nm1 = nm2
    ->
    CTX.In (ValName nm1, rho) G1
    ->
    CTX.In (ValName nm2, sigma) G1
    ->
    dual_types rho sigma.

Inductive is_free_name : value -> Prop :=
| ISNm : forall i, is_free_name (ValName (Nm (Free i)))
| ISCoNm : forall i, is_free_name (ValName (CoNm (Free i))).

Definition all_free_names (G1 : CTX.t) : Prop :=
  forall u rho, CTX.In (u, rho) G1 -> is_free_name u.

Definition names_channel_types (G1 : CTX.t) : Prop := 
  forall v rho, CTX.In (v, rho) G1 -> exists s, rho = TChannel s.

Definition balanced (G1 : CTX.t) : Prop :=
  ctx_matched_names G1
  /\ 
  all_free_names G1
  /\
  names_channel_types G1.

(* ============================================================================= *)

Definition mk_vis_value_type (a : type) : vis_value :=
  match a with
    | TChannel s => VVChan
    | TSingleton k => VVToken k
  end.

Inductive mk_obs_msg : name -> message -> obs -> Prop := 
| MVOMNmInp   : forall f a, mk_obs_msg   (Nm (Free f)) (MInp a) (VOInteract VDInp f (mk_vis_value_type a))
| MVOMNmOut   : forall f a, mk_obs_msg   (Nm (Free f)) (MOut a) (VOInteract VDOut f (mk_vis_value_type a))
| MVOMCoNmInp : forall f a, mk_obs_msg (CoNm (Free f)) (MOut a) (VOInteract VDInp f (mk_vis_value_type a))
| MVOMCoNmOut : forall f a, mk_obs_msg (CoNm (Free f)) (MInp a) (VOInteract VDOut f (mk_vis_value_type a)).

(* ============================================================================= *)

Inductive ctx_preservation : CTX.t -> CTX.t -> obs -> Prop :=
| CPNoInteraction : 
  forall G1 G2, 
    CTX.eq 
      G2
      G1
    ->
    ctx_preservation G1 G2 VONone
| CPInteraction : 
  forall G1 G2 nm1 nm2 s m t vv, 
    dual_name nm1 = nm2
    ->
    CTX.In (ValName nm1, TChannel s) G1
    ->
    CTX.In (ValName nm2, TChannel (SDual s)) G1
    ->
    (transition s m t)
    ->
    CTX.eq 
      G2
      (ctx_replace (ValName nm1) (TChannel s) (TChannel t) 
        ((ctx_replace (ValName nm2) (TChannel (SDual s)) (TChannel (SDual t)) G1)))
    ->
    mk_obs_msg nm1 m vv
    ->
    ctx_preservation G1 G2 vv.

(* ============================================================================= *)

Definition message_type (m : message) : type :=
  match m with 
    | MInp a => a
    | MOut a => a
  end.

Inductive obs_msg_match : obs -> message -> vis_dir -> Prop :=
| VIMMInpInp : forall f vv s, obs_msg_match (VOInteract VDInp f vv) (MInp s) VDInp
| VIMMInpOut : forall f vv s, obs_msg_match (VOInteract VDInp f vv) (MOut s) VDOut
| VIMMOutInp : forall f vv s, obs_msg_match (VOInteract VDOut f vv) (MOut s) VDInp
| VIMMOutOut : forall f vv s, obs_msg_match (VOInteract VDOut f vv) (MInp s) VDOut.

(* The first session type in dual_types_transition2 is the one on which input is occurring. *)
Inductive dual_types_transition2 : type -> type -> type -> type -> type -> Prop :=
| DTT2Left : forall s a t, (transition s (MInp a) t) -> dual_types_transition2 (TChannel s) (TChannel (SDual s)) a (TChannel t) (TChannel (SDual t))
| DTT2Right : forall s a t, (transition s (MOut a) t) -> dual_types_transition2 (TChannel (SDual s)) (TChannel s) a (TChannel (SDual t)) (TChannel t).

(* ============================================================================= *)

Inductive traces : free_id -> list obs -> session -> Prop :=
| TRCNil : forall f s, traces f nil s
| TRCCons : forall f vo vos s m t, (transition s m t) -> mk_obs_msg (Nm (Free f)) m vo -> traces f vos t -> traces f (vo :: vos) s.

Definition project (f : free_id) (vos : list obs) : list obs := filter (is_obs_free_id f) vos.

