/-
# Church-Rosser Proof

This module provides a proof of Church-Rosser (confluence) for the
HigherLambdaModel.Lambda.Term type by transferring the result from
the Metatheory library through a term isomorphism.

This removes the need for the earlier church_rosser postulate in HigherTerms.lean.
-/

import HigherLambdaModel.Lambda.Reduction
import Metatheory

namespace HigherLambdaModel.Lambda.ChurchRosserProof

open HigherLambdaModel.Lambda

/-! ## Term Isomorphism -/

/-- Convert HigherLambdaModel Term to Metatheory Term -/
def toMeta : Term → Metatheory.Lambda.Term
  | .var n => .var n
  | .app M N => .app (toMeta M) (toMeta N)
  | .lam M => .lam (toMeta M)

/-- Convert Metatheory Term to HigherLambdaModel Term -/
def fromMeta : Metatheory.Lambda.Term → Term
  | .var n => .var n
  | .app M N => .app (fromMeta M) (fromMeta N)
  | .lam M => .lam (fromMeta M)

theorem fromMeta_toMeta (M : Term) : fromMeta (toMeta M) = M := by
  induction M with
  | var n => rfl
  | app M N ihM ihN => simp only [toMeta, fromMeta, ihM, ihN]
  | lam M ih => simp only [toMeta, fromMeta, ih]

theorem toMeta_fromMeta (M : Metatheory.Lambda.Term) : toMeta (fromMeta M) = M := by
  induction M with
  | var n => rfl
  | app M N ihM ihN => simp only [fromMeta, toMeta, ihM, ihN]
  | lam M ih => simp only [fromMeta, toMeta, ih]

/-! ## Shift and Substitution Correspondence -/

theorem toMeta_shift (d : Int) (c : Nat) (M : Term) :
    toMeta (Term.shift d c M) = Metatheory.Lambda.Term.shift d c (toMeta M) := by
  induction M generalizing c with
  | var n =>
    simp only [Term.shift, Metatheory.Lambda.Term.shift, toMeta]
    split <;> rfl
  | app M N ihM ihN =>
    simp only [Term.shift, Metatheory.Lambda.Term.shift, toMeta, ihM, ihN]
  | lam M ih =>
    simp only [Term.shift, Metatheory.Lambda.Term.shift, toMeta, ih]

theorem toMeta_subst (j : Nat) (N M : Term) :
    toMeta (Term.subst j N M) = Metatheory.Lambda.Term.subst j (toMeta N) (toMeta M) := by
  induction M generalizing j N with
  | var n =>
    simp only [Term.subst, Metatheory.Lambda.Term.subst, toMeta]
    split
    · rfl
    · split <;> rfl
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [Term.subst, Metatheory.Lambda.Term.subst, toMeta, ih₁, ih₂]
  | lam M ih =>
    simp only [Term.subst, Metatheory.Lambda.Term.subst, toMeta]
    congr 1
    rw [ih]
    congr 1
    exact toMeta_shift 1 0 N

theorem fromMeta_shift (d : Int) (c : Nat) (M : Metatheory.Lambda.Term) :
    fromMeta (Metatheory.Lambda.Term.shift d c M) = Term.shift d c (fromMeta M) := by
  induction M generalizing c with
  | var n =>
    simp only [Metatheory.Lambda.Term.shift, Term.shift, fromMeta]
    split <;> rfl
  | app M N ihM ihN =>
    simp only [Metatheory.Lambda.Term.shift, Term.shift, fromMeta, ihM, ihN]
  | lam M ih =>
    simp only [Metatheory.Lambda.Term.shift, Term.shift, fromMeta, ih]

theorem fromMeta_subst (j : Nat) (N M : Metatheory.Lambda.Term) :
    fromMeta (Metatheory.Lambda.Term.subst j N M) = Term.subst j (fromMeta N) (fromMeta M) := by
  induction M generalizing j N with
  | var n =>
    simp only [Metatheory.Lambda.Term.subst, Term.subst, fromMeta]
    split
    · rfl
    · split <;> rfl
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [Metatheory.Lambda.Term.subst, Term.subst, fromMeta, ih₁, ih₂]
  | lam M ih =>
    simp only [Metatheory.Lambda.Term.subst, Term.subst, fromMeta]
    congr 1
    -- Need: fromMeta (subst (j+1) (shift1 N) M) = subst (j+1) (shift1 (fromMeta N)) (fromMeta M)
    -- Use ih with shifted argument
    rw [ih]
    congr 1
    -- Need: fromMeta (shift1 N) = shift1 (fromMeta N)
    exact fromMeta_shift 1 0 N

/-! ## BetaStep Correspondence -/

theorem betaStep_toMeta {M N : Term} (h : BetaStep M N) :
    Metatheory.Lambda.BetaStep (toMeta M) (toMeta N) := by
  induction h with
  | beta M N =>
    simp only [toMeta]
    have : toMeta (Term.subst0 N M) = Metatheory.Lambda.Term.subst0 (toMeta N) (toMeta M) :=
      toMeta_subst 0 N M
    rw [this]
    exact Metatheory.Lambda.BetaStep.beta _ _
  | appL _ ih => exact Metatheory.Lambda.BetaStep.appL ih
  | appR _ ih => exact Metatheory.Lambda.BetaStep.appR ih
  | lam _ ih => exact Metatheory.Lambda.BetaStep.lam ih

theorem betaStep_fromMeta {M N : Metatheory.Lambda.Term}
    (h : Metatheory.Lambda.BetaStep M N) : BetaStep (fromMeta M) (fromMeta N) := by
  induction h with
  | beta M N =>
    simp only [fromMeta]
    have : fromMeta (Metatheory.Lambda.Term.subst0 N M) =
           Term.subst0 (fromMeta N) (fromMeta M) := fromMeta_subst 0 N M
    rw [this]
    exact BetaStep.beta _ _
  | appL _ ih => exact BetaStep.appL ih
  | appR _ ih => exact BetaStep.appR ih
  | lam _ ih => exact BetaStep.lam ih

/-! ## Multi-step Correspondence -/

/-- Multi-step beta reduction on HigherLambdaModel terms -/
inductive BetaMulti : Term → Term → Prop where
  | refl : ∀ M, BetaMulti M M
  | step : ∀ {M N P}, BetaStep M N → BetaMulti N P → BetaMulti M P

theorem BetaMulti.trans {M N P : Term} (h1 : BetaMulti M N) (h2 : BetaMulti N P) : BetaMulti M P := by
  induction h1 with
  | refl _ => exact h2
  | step s _ ih => exact BetaMulti.step s (ih h2)

theorem betaMulti_toMeta {M N : Term} (h : BetaMulti M N) :
    Metatheory.Lambda.MultiStep (toMeta M) (toMeta N) := by
  induction h with
  | refl _ => exact Metatheory.Lambda.MultiStep.refl _
  | step s _ ih =>
    exact Metatheory.Lambda.MultiStep.trans
      (Metatheory.Lambda.MultiStep.single (betaStep_toMeta s)) ih

theorem betaMulti_fromMeta {M N : Metatheory.Lambda.Term}
    (h : Metatheory.Lambda.MultiStep M N) : BetaMulti (fromMeta M) (fromMeta N) := by
  induction h with
  | refl _ => exact BetaMulti.refl _
  | step s _ ih => exact BetaMulti.step (betaStep_fromMeta s) ih

/-! ## Church-Rosser Theorem -/

/-- Church-Rosser for β-reduction on HigherLambdaModel terms.

This is proven by transferring the confluence theorem from the Metatheory library
through the term isomorphism. -/
theorem church_rosser_beta {M N₁ N₂ : Term}
    (h1 : BetaMulti M N₁) (h2 : BetaMulti M N₂) :
    ∃ P, BetaMulti N₁ P ∧ BetaMulti N₂ P := by
  -- Transfer to Metatheory terms
  have h1' := betaMulti_toMeta h1
  have h2' := betaMulti_toMeta h2
  -- Apply Metatheory's confluence theorem
  obtain ⟨P', hP1, hP2⟩ := Metatheory.Lambda.confluence h1' h2'
  -- Transfer back
  refine ⟨fromMeta P', ?_, ?_⟩
  · have := betaMulti_fromMeta hP1
    rwa [fromMeta_toMeta] at this
  · have := betaMulti_fromMeta hP2
    rwa [fromMeta_toMeta] at this

end HigherLambdaModel.Lambda.ChurchRosserProof
