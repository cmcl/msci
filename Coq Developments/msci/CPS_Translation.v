(** Beginning of the file defining the translation from GV to CP. *)
Require Import Metatheory.
Require Import CP_Definitions CP_Typing GV_Definitions.
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
    | A → B => pp_accept ((¬⟦A⟧t) ⅋ ⟦B⟧t)
    | typ_unit => pp_accept pp_top
  end
where "'⟦' T '⟧t'" := (trans_types T).

Fixpoint infer (tm:term) (G:tenv) (xs:list typ) : option typ :=
  let flip t := match t with
                   | T ⊸ U => T → U
                   | T → U => T ⊸ U
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

Lemma somm:
  forall Φ M T (WT: Φ ⊢ M ∈ T), infer M Φ nil = Some T.
Proof.
Admitted.

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
  -
Admitted.