(** Beginning of the file defining the translation from GV to CP. *)
Require Import Metatheory.
Require Import CP_Definitions GV_Definitions.
Set Implicit Arguments.

(** Translation of types. *)
Reserved Notation "'⟦' T '⟧t'" (at level 68).

Fixpoint trans_types {k} (T:typ k) : prop :=
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

Program Fixpoint infer (tm:term) (G:tenv) :=
  match tm with
    | tm_var (fvar x) => get x G
    | tm_abs _ T m =>
    | _ => typ_unit
  end.

(** Translation of terms. *)
Reserved Notation "'⟦' t '⟧' z" (at level 68).

Fixpoint trans_tm (tm:term) (z:pname) : proc :=
  match tm with
    | tm_var (fvar x) => x ⟷ z
    | tm_unit => p_accept z pp_top (0 CASE 0)
    | tm_weak (fvar x) m
    | tm_weak (bvar x) m =>
       p_weak x (⟦m⟧ z)
    | tm_abs _ T m => p_input z (¬⟦T⟧t) (⟦m⟧z)
    | tm_app m n
      => p_par (⟦ infer m ⟧t) (⟦m⟧ 0)
               (p_output 0 (⟦ infer n ⟧t) (⟦n⟧0) (1 ⟷ z))
    | _ => z ⟷ z
  end
where "'⟦' t '⟧' z" := (trans_tm t z).