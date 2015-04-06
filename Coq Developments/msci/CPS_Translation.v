(** Beginning of the file defining the translation from GV to CP. *)
Require Import Metatheory.
Require Import CP_Definitions CP_Typing GV_Definitions GV_Infrastructure.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Monad.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Data.Monads.OptionMonad.
Require Import Coq.Sorting.Permutation.
Import ApplicativeNotation FunctorNotation MonadNotation.
Set Implicit Arguments.

Open Scope monad_scope.

(** Translation of types. *)
Reserved Notation "'⟦' T '⟧t'" (at level 68).

Fixpoint trans_types (T:typ) : prop :=
  match T with
    | ! A # B => (¬ ⟦A⟧t) ⅋ ⟦B⟧t
    | ? A # B => ⟦A⟧t ⨂ ⟦B⟧t
    | A <+> B => ⟦A⟧t & ⟦B⟧t
    | A <&> B => ⟦A⟧t ⨁ ⟦B⟧t
    | typ_oend => pp_bot
    | typ_iend => pp_one
    | A <x> B => ⟦A⟧t ⨂ ⟦B⟧t
    | A ⊸ B => (¬⟦A⟧t) ⅋ ⟦B⟧t
    | A ⟶ B => pp_accept ((¬⟦A⟧t) ⅋ ⟦B⟧t)
    | typ_unit => pp_accept pp_top
  end
where "'⟦' T '⟧t'" := (trans_types T).

Fixpoint infer (tm:term) (G:tenv) (xs:list typ) : option typ :=
  let flip t := match t with
                   | T ⊸ U => T ⟶ U
                   | T ⟶ U => T ⊸ U
                   | _ => t
                end
  in
  let trans t := match t with
                     | ! A # B => B
                     | ? A # B => A <x> A
                     | _ => t
                 end
  in
  let choose lbl t := match t with
                        | S1 <+> S2 =>
                          match lbl with
                            | lb_inl => S1
                            | lb_inr => S2
                          end
                        | _ => t
                      end
  in
  match tm with
    | tm_var (fvar x) => get x G
    | tm_var (bvar x) => nth_error xs x
    | tm_unit => Some typ_unit
    | tm_weak x M => infer M G xs
    | tm_abs T M => fmap (fun U => T ⊸ U) (infer M G (T::xs))
    | tm_iabs M => fmap flip (infer M G xs)
    | tm_eabs M => fmap flip (infer M G xs)
    | tm_app M N => match infer M G xs with
                        | Some (T ⊸ U) => Some U
                        | _ => None
                    end
    | tm_pair M N => pure typ_tensor <*> (infer M G xs) <*> (infer N G xs)
    | tm_let T U M N => infer N G (U::T::xs)
    | tm_send M N => fmap trans (infer N G xs)
    | tm_recv M => fmap trans (infer M G xs)
    | tm_select lbl M => fmap (choose lbl) (infer M G xs)
    | tm_case M NL NR
      => T <- fmap (choose lb_inl) (infer M G xs) ;; infer NL G (T::xs)
    | tm_connect T M N => (infer N G ((dual_session T)::xs))
    | tm_end _ => Some typ_unit
  end.

Inductive inferTy : term -> tenv -> typ -> Prop :=
  | infer_fvar: forall x G T (RET: get x G = Some T),
                  inferTy (tm_var (fvar x)) G T
  | infer_unit: forall G, inferTy tm_unit G typ_unit
  | infer_weak: forall (x:atom) M G T U (INF: inferTy M G T),
                  inferTy (tm_weak x M) (x ~ U ++ G) T
  | infer_abs: forall L M G T U
                      (INF: forall x (NIN: x `notin` L),
                              inferTy (open M x) (x~T ++ G) U),
                 inferTy (tm_abs T M) G (T ⊸ U)
  | infer_iabs: forall M G T U (INF: inferTy M G (T ⊸ U)),
                  inferTy (tm_iabs M) G (T ⟶ U)
  | infer_eabs: forall M G T U (INF: inferTy M G (T ⟶ U)),
                  inferTy (tm_eabs M) G (T ⊸ U)
  | infer_app: forall M N G H T U
                      (INFM: inferTy M G (T ⊸ U))
                      (INFN: inferTy N H T),
                 inferTy (tm_app M N) (G++H) U
  | infer_pair: forall M N G H T U
                      (INFM: inferTy M G T)
                      (INFN: inferTy N H U),
                  inferTy (tm_pair M N) (G++H) (T <x> U)
  | infer_let:
      forall L M N G H T U V
             (INFM: inferTy M G (T <x> U))
             (INFN: forall x y
                           (NINX: x `notin` L)
                           (NINY: y `notin` L `union` singleton x),
                      inferTy ({1 ~> x}(open N y)) (x ~ T ++ y ~ U ++ H) V),
        inferTy (tm_let T U M N) (G++H) V
  | infer_send: forall M N G H T U
                       (INFM: inferTy M G T)
                       (INFN: inferTy N H (! T # U)),
                  inferTy (tm_send M N) (G++H) U
  | infer_recv: forall M G T U
                       (INFM: inferTy M G (? T # U)),
                  inferTy (tm_recv M) G (T <x> U)
  | infer_select_inl: forall M G S1 S2
                             (INFM: inferTy M G (S1 <+> S2)),
                    inferTy (tm_select lb_inl M) G S1
  | infer_select_inr: forall M G S1 S2
                             (INFM: inferTy M G (S1 <+> S2)),
                        inferTy (tm_select lb_inr M) G S2
  | infer_case: forall L M NL NR G H S1 S2 T
                       (INFM: inferTy M G (S1 <&> S2))
                       (INFNL: forall x (NIN: x `notin` L),
                                 inferTy (open NL x) (x ~ S1 ++ H) T)
                       (INFNR: forall x (NIN: x `notin` L),
                                 inferTy (open NR x) (x ~ S2 ++ H) T),
                  inferTy (tm_case M NL NR) (G++H) T
  | infer_connect: forall L M N G H T dT U
                          (DUA: are_dual T dT)
                          (INFM: forall x (NIN: x `notin` L),
                                   inferTy (open M x) (x ~ T ++ G) typ_oend)
                          (INFN: forall x (NIN: x `notin` L),
                                   inferTy (open N x) (x ~ dT ++ H) U),
                     inferTy (tm_connect T M N) (G++H) U
  | infer_end: forall M G (INF: inferTy M G typ_iend),
                 inferTy (tm_end M) G typ_unit.

Hint Constructors inferTy.

Lemma somm:
  forall Φ M T (WT: Φ ⊢ M ∈ T), inferTy M Φ T.
Proof.
  ii; induction WT; try (solve [eauto|constructor; ss; des; tryfalse; eauto]).
Qed.

Fixpoint trans_tm' (tm:term) (G:tenv) (xs:list typ) (z:pname) : option proc :=
  match tm with
    | tm_var (bvar x)
    | tm_var (fvar x)
      => ret $ x ⟷ z

    | tm_unit => ret $ p_accept z pp_top (0 CASE 0)

    | tm_weak (fvar x) M
    | tm_weak (bvar x) M
      => M' <- trans_tm' M G xs z ;;
         ret $ p_weak x M'

    | tm_abs T M
      => M' <- trans_tm' M G (T::xs) z ;;
         ret $ p_input z (¬⟦T⟧t) M'

    | tm_iabs M
      => T  <- infer M G xs ;;
         M' <- trans_tm' M G xs 0 ;;
         ret $ p_accept z (⟦T⟧t) M'

    | tm_eabs M
      => T  <- infer M G xs ;;
         M' <- trans_tm' M G xs 0 ;;
         ret $ p_par (pp_accept (⟦T⟧t)) M' (p_request 0 (¬⟦T⟧t) (0 ⟷ z))

    | tm_app M N
      => TM <- infer M G xs ;;
         TN <- infer N G xs ;;
         M' <- trans_tm' M G xs 0 ;;
         N' <- trans_tm' N G xs 0 ;;
         ret $ p_par (⟦TM⟧t) M' (p_output 0 (⟦TN⟧t) N' (1 ⟷ z))

    | tm_pair M N
      => TM <- infer M G xs ;;
         M' <- trans_tm' M G xs 0 ;;
         N' <- trans_tm' N G xs z ;;
         ret $ p_output z (⟦TM⟧t) M' N'

    | tm_let T U M N
      => M' <- trans_tm' M G xs 0 ;;
         N' <- trans_tm' N G (U::T::xs) z ;;
         ret $ p_par (⟦T <x> U⟧t) M' (p_input 0 (¬⟦T⟧t) N')

    | tm_send M N
      => TM <- infer M G xs ;;
         TN <- infer N G xs ;;
         M' <- trans_tm' M G xs 0 ;;
         N' <- trans_tm' N G xs 0 ;;
         ret $ p_par (¬⟦TN⟧t) (p_output 0 (⟦TM⟧t) M' (0 ⟷ z)) N'

    | tm_recv M => trans_tm' M G xs z

    | tm_select lbl M
      => let Q := match lbl with
                    | lb_inr => p_right
                    | lb_inl => p_left
                  end
         in TM <- infer M G xs ;;
            M' <- trans_tm' M G xs 0 ;;
            ret $ p_par (⟦TM⟧t) M' (Q 0 (0 ⟷ z))

    | tm_case M NL NR
      => TM  <- infer M G xs ;;
         M'  <- trans_tm' M G xs 0 ;;
         NL' <- trans_tm' NL G xs z ;;
         NR' <- trans_tm' NR G xs z ;;
         ret $ p_par (⟦TM⟧t) M' (p_choice 0 NL' NR')

    | tm_connect T M N
      => M' <- trans_tm' M G (T::xs) 0 ;;
         N' <- trans_tm' M G (T::xs) z ;;
         ret $ p_par (¬⟦T⟧t) (p_par pp_bot M' (p_empout 0)) N'

    | tm_end M
      => M' <- trans_tm' M G xs 0 ;;
         ret $ p_par pp_one M' (p_empin 0 (p_accept z pp_top (0 CASE 0)))
  end.

Inductive transTm : term -> tenv -> pname -> proc -> Prop :=
  | trans_fvar: forall x G z,
                  transTm (tm_var (fvar x)) G z (x ⟷ z)
  | trans_unit: forall G z,
                  transTm tm_unit G z (! ⟨pp_top⟩z → (0 CASE 0))
  | trans_weak: forall (x:atom) T M P G z
                       (TR: transTm M G z P),
                  transTm (tm_weak x M) (x ~ T ++ G) z (? []x → P)
  | trans_abs: forall L T M P G z
                      (TR: forall x (NIN: x `notin` L),
                             transTm (open M x) (x ~ T ++ G) z P),
                 transTm (tm_abs T M) G z (⟨¬⟦T⟧t⟩z → P)
  | trans_iabs: forall T M P G z
                       (INF: inferTy M G T)
                       (TR: transTm M G 0 P),
                  transTm (tm_iabs M) G z (! ⟨⟦T⟧t⟩z → P)
  | trans_eabs:
      forall T M P G z
             (INF: inferTy M G T)
             (TR: transTm M G 0 P),
        transTm (tm_eabs M) G z
                (ν (pp_accept (⟦T⟧t)) → P ‖ ? [¬⟦T⟧t]0 → (0 ⟷ z))
  | trans_app:
      forall T U M N P Q G H z
             (INFM: inferTy M G T)  (INFN: inferTy N H U)
             (TRM: transTm M G 0 P) (TRN: transTm N H 0 Q),
        transTm (tm_app M N) (G++H) z (ν ⟦T⟧t → P ‖ [⟦T⟧t]0 → Q ‖ 1 ⟷ z)
  | trans_pair:
      forall T M N P Q G H z
             (INFM: inferTy M G T)
             (TRM: transTm M G 0 P) (TRN: transTm N H 0 Q),
        transTm (tm_pair M N) (G++H) z ([⟦T⟧t]z → P ‖ Q)
  | trans_let:
      forall L T U M N P Q G H z
             (TR: transTm M G 0 P)
             (TRN: forall x y
                          (NINX: x `notin` L)
                          (NINY: y `notin` L `union` singleton x),
                     transTm ({1 ~> x}(open N y)) H z Q),
        transTm (tm_let T U M N) (G++H) z
                (ν ⟦T <x> U⟧t → P ‖ ⟨¬⟦T⟧t⟩0 → Q)
  | trans_send:
      forall T U M N P Q G H z
             (INFM: inferTy M G T)  (INFN: inferTy N H U)
             (TRM: transTm M G 0 P) (TRN: transTm M H 0 Q),
        transTm (tm_send M N) (G++H) z
                (ν ⟦U⟧t → ([⟦T⟧t]0 → P ‖ 0 ⟷ z) ‖ Q)
  | trans_recv:
      forall M P G z (TR: transTm M G z P),
        transTm (tm_recv M) G z P
  | trans_select_inl:
      forall T M P G z
             (INF: inferTy M G T)
             (TR: transTm M G 0 P),
        transTm (tm_select lb_inl M) G z (ν ⟦T⟧t → P ‖ 0[inl] → 0 ⟷ z)
  | trans_select_inr:
      forall T M P G z
             (INF: inferTy M G T)
             (TR: transTm M G 0 P),
        transTm (tm_select lb_inr M) G z (ν ⟦T⟧t → P ‖ 0[inr] → 0 ⟷ z)
  | trans_case:
      forall L S1 S2 M NL NR P QL QR G H z
             (INFM: inferTy M G (S1 <&> S2))
             (TRNL: forall x (NIN: x `notin` L),
                       transTm (open NL x) (x ~ S1 ++ H) z QL)
             (TRNR: forall x (NIN: x `notin` L),
                       transTm (open NR x) (x ~ S2 ++ H) z QR),
        transTm (tm_case M NL NR) (G++H) z
                (ν ⟦S1 <&> S2⟧t → P ‖ 0 CASE QL OR QR)
  | trans_connect:
      forall L T dT M N P Q G H z
             (DUA: are_dual T dT)
             (TRM: forall x (NIN: x `notin` L),
                     transTm (open M x) (x ~ T ++ G) 0 P)
             (TRN: forall x (NIN: x `notin` L),
                     transTm (open N x) (x ~ dT ++ H) z Q),
        transTm (tm_connect T M N) (G++H) z
                (ν ¬⟦T⟧t → (ν pp_bot → P ‖ 0 → 0) ‖ Q)
  | trans_end:
      forall M P G z (TR: transTm M G 0 P),
        transTm (tm_end M) G z (ν pp_one → P ‖ ⟨⟩0 → ⟨pp_top⟩z → (0 CASE 0)).

(** Translation of terms. *)
Definition trans_tm M G z := trans_tm' M G nil z.

(** Translation of environments. *)
Fixpoint trans_env (Φ:tenv) : penv :=
  match Φ with
    | nil => nil
    | (x,a) :: Φ' => (x,¬⟦a⟧t) :: trans_env Φ'
  end.

Theorem cps_trans_wt:
  forall Φ M T z P Γ Δ
         (WT: Φ ⊢ M ∈ T)
         (NIN: z `notin` GVFV M)
         (ENV: trans_env Φ = Δ)
         (PER: Permutation Γ (Δ ++ z ~ ⟦T⟧t))
         (CP: trans_tm M Φ z = Some P),
    P ⊢cp Γ.
Proof.
  introv WT; gen z P Γ Δ; induction WT; ii; unfold trans_tm in CP; ss
  ; unfold apply in CP; substs; destruct_notin; des; tryfalse; repeat injs
  ; auto.
  - apply Permutation_sym in PER; applys ignore_env_order PER.
    simpl_env; eauto.
  - apply Permutation_sym in PER; applys ignore_env_order PER.
    simpl_env.
    pick fresh y and apply cp_accept; eauto.
    rewrite /open_proc; s; simpl_env; eauto.
  - admit.
  -
Admitted.