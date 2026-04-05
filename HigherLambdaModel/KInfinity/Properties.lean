import HigherLambdaModel.KInfinity.Construction
import HigherLambdaModel.Lambda.Coherence
import HigherLambdaModel.Simplicial.OmegaGroupoid

/-!
# Properties of the `K∞` Tower

This file packages the remaining Section 4 results in the chosen-data style
used throughout the repository.

The generic Section 3 layer already provides the full c.h.p.o. and continuous
map infrastructure needed for the `Kₙ` tower. What is still absent from the
library is a generic theorem identifying the inverse limit `K∞` itself as a
`HomotopyScottDomain` by way of finite-step bases for the whole tower. We
therefore record Proposition 4.1 through an explicit witness structure that
exposes the domain-theoretic data already constructed here: bounded
completeness of every stage and the continuous coordinate projections from the
inverse limit.

The non-triviality theorem and the β/η example are fully internalized using
the chosen homotopy-group data introduced in `NonTrivial.lean`.
-/

namespace HigherLambdaModel.KInfinity

open Classical
open HigherLambdaModel.Domain
open HigherLambdaModel.Lambda.HomotopyOrder

/-! ## Stage Algebraicity and Scott Domain Structure -/

/-- Every stage `Kₙ` of Definition 4.5 is algebraic at level 0. -/
theorem stage_algebraic_zero : Algebraic (K 0) :=
  Flat.algebraic SpherePoint

/-- Stage-wise bounded completeness combined with algebraicity at level 0
gives us the full Homotopy Scott Domain at level 0. -/
noncomputable def stage_scottDomain_zero : HomotopyScottDomain where
  carrier := K 0
  algebraic := stage_algebraic_zero
  boundedComplete := Flat.boundedComplete SpherePoint

/-! ## Remark 4.1 and Proposition 4.1 -/

/-- Every stage `Kₙ` of Definition 4.5 is bounded complete. This is the
bounded-complete half of the domain-theoretic content used in Proposition 4.1.
-/
theorem stage_boundedComplete : ∀ n : Nat, BoundedComplete (K n)
  | 0 => Flat.boundedComplete SpherePoint
  | n + 1 => boundedComplete_exponential (stage_boundedComplete n)

/-! ## Base Embedding and Approximation Interfaces -/

/-- The level-zero embedding `f₀,∞ : K₀ → K∞`, obtained by iterating the
recursive h-embeddings upward from `K₀`. This is the concrete part of Remark
4.2 needed by the present Section 4 development. -/
noncomputable def baseUp (x : (K 0).Obj) : (n : Nat) → (K n).Obj
  | 0 => x
  | n + 1 => (fPlus n).toFun (baseUp x n)

@[simp] theorem baseUp_zero (x : (K 0).Obj) :
    baseUp x 0 = x := rfl

@[simp] theorem baseUp_succ (x : (K 0).Obj) (n : Nat) :
    baseUp x (n + 1) = (fPlus n).toFun (baseUp x n) := rfl

private theorem fPlus_castLevel
    {a b : Nat} (h : a = b) (y : (K a).Obj) :
    (fPlus b).toFun (castLevel h y) =
      castLevel (by cases h; rfl) ((fPlus a).toFun y) := by
  cases h
  rfl

theorem baseUp_eq_projectUp_zero (x : (K 0).Obj) :
    ∀ n : Nat, baseUp x n = castLevel (Nat.zero_add n) (projectUp 0 x n)
  | 0 => by
      simp [baseUp, projectUp]
  | n + 1 => by
      rw [baseUp_succ, baseUp_eq_projectUp_zero x n]
      simpa [projectUp_succ] using
        (fPlus_castLevel (Nat.zero_add n) (projectUp 0 x n))

/-- The recursive stage maps underlying the base embedding `f₀,∞`. -/
noncomputable def baseUpContinuous : (n : Nat) → ContinuousMap (K 0) (K n)
  | 0 => ContinuousMap.id (K 0)
  | n + 1 => ContinuousMap.comp (fPlus n) (baseUpContinuous n)

@[simp] theorem baseUpContinuous_apply (x : (K 0).Obj) :
    ∀ n : Nat, baseUpContinuous n x = baseUp x n
  | 0 => rfl
  | n + 1 => by
      change (fPlus n) (baseUpContinuous n x) = (fPlus n).toFun (baseUp x n)
      rw [baseUpContinuous_apply x n]

/-- The level-zero embedding `f₀,∞ : K₀ → K∞`, obtained by iterating the
recursive h-embeddings upward from `K₀`. This is the concrete part of Remark
4.2 needed by the present Section 4 development. -/
noncomputable def embedBaseToLimit (x : (K 0).Obj) : KInfinityCHPO.Obj where
  val := baseUp x
  toPrev := by
    intro n
    change (K n).Rel ((fMinus n).toFun (baseUp x (n + 1))) (baseUp x n)
    have hEq : (fMinus n).toFun (baseUp x (n + 1)) = baseUp x n := by
      rw [baseUp_succ]
      exact congrArg (fun g => g.toFun (baseUp x n)) (fMinus_comp_fPlus n)
    rw [hEq]
    exact (K n).rel_refl (baseUp x n)
  fromPrev := by
    intro n
    change (K n).Rel (baseUp x n) ((fMinus n).toFun (baseUp x (n + 1)))
    have hEq : (fMinus n).toFun (baseUp x (n + 1)) = baseUp x n := by
      rw [baseUp_succ]
      exact congrArg (fun g => g.toFun (baseUp x n)) (fMinus_comp_fPlus n)
    rw [hEq]
    exact (K n).rel_refl (baseUp x n)

/-- The level-zero coordinate of the base embedding is the original base
element. -/
@[simp] theorem project_embedBase_self (x : (K 0).Obj) :
    projectToLevel 0 (embedBaseToLimit x) = x := by
  change baseUp x 0 = x
  simp [baseUp]

theorem project_embedBase_eq_projectUp_zero
    (x : (K 0).Obj) (n : Nat) :
    projectToLevel n (embedBaseToLimit x) =
      castLevel (Nat.zero_add n) (projectUp 0 x n) := by
  change baseUp x n = castLevel (Nat.zero_add n) (projectUp 0 x n)
  exact baseUp_eq_projectUp_zero x n

/-- The base embedding is monotone from `K₀` into the inverse limit `K∞`. -/
theorem embedBaseToLimit_monotone
    {x y : (K 0).Obj}
    (hxy : (K 0).Rel x y) :
    KInfinityCHPO.Rel (embedBaseToLimit x) (embedBaseToLimit y) := by
  exact Projective.rel_mk (S := system) (fun n => by
    simpa [baseUpContinuous_apply] using (baseUpContinuous n).monotone' hxy)

/-- The level-zero embedding `f₀,∞ : K₀ → K∞` packaged as a continuous map. -/
noncomputable def embedBaseContinuous : ContinuousMap (K 0) KInfinityCHPO where
  toFun := embedBaseToLimit
  monotone' := embedBaseToLimit_monotone
  preserves_sup := by
    intro X hX
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact Projective.rel_mk (S := system) (fun n => by
        simpa [baseUpContinuous_apply] using
          ((baseUpContinuous n).preserves_sup X hX).1 ⟨x, hx, rfl⟩)
    · intro w hw
      exact Projective.rel_mk (S := system) (fun n => by
        simpa [baseUpContinuous_apply] using
          ((baseUpContinuous n).preserves_sup X hX).2 (by
            intro a ha
            rcases ha with ⟨x, hx, rfl⟩
            simpa [baseUpContinuous_apply] using
              (Projective.rel_iff.mp (hw ⟨x, hx, rfl⟩)) n))

/-! ## Level-One Reification Shadow -/

/-- Coordinates of the canonical level-one embedding `f₁,∞ : K₁ → K∞`. -/
noncomputable def levelOneCoords (x : (K 1).Obj) : (n : Nat) → (K n).Obj
  | 0 => (fMinus 0).toFun x
  | 1 => x
  | n + 2 => (fPlus (n + 1)).toFun (levelOneCoords x (n + 1))

@[simp] theorem levelOneCoords_zero (x : (K 1).Obj) :
    levelOneCoords x 0 = (fMinus 0).toFun x := rfl

@[simp] theorem levelOneCoords_one (x : (K 1).Obj) :
    levelOneCoords x 1 = x := rfl

@[simp] theorem levelOneCoords_succ_succ (x : (K 1).Obj) (n : Nat) :
    levelOneCoords x (n + 2) =
      (fPlus (n + 1)).toFun (levelOneCoords x (n + 1)) := rfl

/-- The coordinate maps of the canonical level-one embedding are continuous. -/
noncomputable def levelOneCoordinateContinuous :
    (n : Nat) → ContinuousMap (K 1) (K n)
  | 0 => fMinus 0
  | 1 => ContinuousMap.id (K 1)
  | n + 2 => ContinuousMap.comp (fPlus (n + 1)) (levelOneCoordinateContinuous (n + 1))

@[simp] theorem levelOneCoordinateContinuous_apply
    (x : (K 1).Obj) :
    ∀ n : Nat, levelOneCoordinateContinuous n x = levelOneCoords x n
  | 0 => rfl
  | 1 => rfl
  | n + 2 => by
      change (fPlus (n + 1)) (levelOneCoordinateContinuous (n + 1) x) =
        (fPlus (n + 1)).toFun (levelOneCoords x (n + 1))
      rw [levelOneCoordinateContinuous_apply x (n + 1)]

/-- The canonical stage-one embedding `f₁,∞ : K₁ → K∞`. -/
noncomputable def embedLevelOneToLimit (x : (K 1).Obj) : KInfinityCHPO.Obj where
  val := levelOneCoords x
  toPrev := by
    intro n
    cases n with
    | zero =>
        change (K 0).Rel ((fMinus 0).toFun x) ((fMinus 0).toFun x)
        exact (K 0).rel_refl _
    | succ n =>
        change
          (K (n + 1)).Rel
            ((fMinus (n + 1)).toFun ((fPlus (n + 1)).toFun (levelOneCoords x (n + 1))))
            (levelOneCoords x (n + 1))
        have hEq :
            (fMinus (n + 1)).toFun ((fPlus (n + 1)).toFun (levelOneCoords x (n + 1))) =
              levelOneCoords x (n + 1) := by
          exact congrArg (fun g => g.toFun (levelOneCoords x (n + 1)))
            (fMinus_comp_fPlus (n + 1))
        rw [hEq]
        exact (K (n + 1)).rel_refl _
  fromPrev := by
    intro n
    cases n with
    | zero =>
        change (K 0).Rel ((fMinus 0).toFun x) ((fMinus 0).toFun x)
        exact (K 0).rel_refl _
    | succ n =>
        change
          (K (n + 1)).Rel
            (levelOneCoords x (n + 1))
            ((fMinus (n + 1)).toFun ((fPlus (n + 1)).toFun (levelOneCoords x (n + 1))))
        have hEq :
            (fMinus (n + 1)).toFun ((fPlus (n + 1)).toFun (levelOneCoords x (n + 1))) =
              levelOneCoords x (n + 1) := by
          exact congrArg (fun g => g.toFun (levelOneCoords x (n + 1)))
            (fMinus_comp_fPlus (n + 1))
        rw [hEq]
        exact (K (n + 1)).rel_refl _

@[simp] theorem project_embedLevelOne_zero (x : (K 1).Obj) :
    projectToLevel 0 (embedLevelOneToLimit x) = (fMinus 0).toFun x := rfl

@[simp] theorem project_embedLevelOne_one (x : (K 1).Obj) :
    projectToLevel 1 (embedLevelOneToLimit x) = x := rfl

/-- The stage-one embedding is monotone into `K∞`. -/
theorem embedLevelOneToLimit_monotone
    {x y : (K 1).Obj}
    (hxy : (K 1).Rel x y) :
    KInfinityCHPO.Rel (embedLevelOneToLimit x) (embedLevelOneToLimit y) := by
  exact Projective.rel_mk (S := system) (fun n => by
    simpa [levelOneCoordinateContinuous_apply] using
      (levelOneCoordinateContinuous n).monotone' hxy)

/-- The canonical stage-one embedding `f₁,∞ : K₁ → K∞` packaged as a
continuous map. -/
noncomputable def embedLevelOneContinuous : ContinuousMap (K 1) KInfinityCHPO where
  toFun := embedLevelOneToLimit
  monotone' := embedLevelOneToLimit_monotone
  preserves_sup := by
    intro X hX
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact Projective.rel_mk (S := system) (fun n => by
        simpa [levelOneCoordinateContinuous_apply] using
          ((levelOneCoordinateContinuous n).preserves_sup X hX).1 ⟨x, hx, rfl⟩)
    · intro w hw
      exact Projective.rel_mk (S := system) (fun n => by
        simpa [levelOneCoordinateContinuous_apply] using
          ((levelOneCoordinateContinuous n).preserves_sup X hX).2 (by
            intro a ha
            rcases ha with ⟨x, hx, rfl⟩
            simpa [levelOneCoordinateContinuous_apply] using
              (Projective.rel_iff.mp (hw ⟨x, hx, rfl⟩)) n))

/-! ## Level-Two Reification Shadow -/

/-- Coordinates of the canonical level-two embedding `f₂,∞ : K₂ → K∞`. -/
noncomputable def levelTwoCoords (x : (K 2).Obj) : (n : Nat) → (K n).Obj
  | 0 => (fMinus 0).toFun ((fMinus 1).toFun x)
  | 1 => (fMinus 1).toFun x
  | 2 => x
  | n + 3 => (fPlus (n + 2)).toFun (levelTwoCoords x (n + 2))

@[simp] theorem levelTwoCoords_zero (x : (K 2).Obj) :
    levelTwoCoords x 0 = (fMinus 0).toFun ((fMinus 1).toFun x) := rfl

@[simp] theorem levelTwoCoords_one (x : (K 2).Obj) :
    levelTwoCoords x 1 = (fMinus 1).toFun x := rfl

@[simp] theorem levelTwoCoords_two (x : (K 2).Obj) :
    levelTwoCoords x 2 = x := rfl

@[simp] theorem levelTwoCoords_succ_succ_succ (x : (K 2).Obj) (n : Nat) :
    levelTwoCoords x (n + 3) =
      (fPlus (n + 2)).toFun (levelTwoCoords x (n + 2)) := rfl

/-- The coordinate maps of the canonical level-two embedding are continuous. -/
noncomputable def levelTwoCoordinateContinuous :
    (n : Nat) → ContinuousMap (K 2) (K n)
  | 0 => ContinuousMap.comp (fMinus 0) (fMinus 1)
  | 1 => fMinus 1
  | 2 => ContinuousMap.id (K 2)
  | n + 3 => ContinuousMap.comp (fPlus (n + 2)) (levelTwoCoordinateContinuous (n + 2))

@[simp] theorem levelTwoCoordinateContinuous_apply
    (x : (K 2).Obj) :
    ∀ n : Nat, levelTwoCoordinateContinuous n x = levelTwoCoords x n
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | n + 3 => by
      change (fPlus (n + 2)) (levelTwoCoordinateContinuous (n + 2) x) =
        (fPlus (n + 2)).toFun (levelTwoCoords x (n + 2))
      rw [levelTwoCoordinateContinuous_apply x (n + 2)]

/-- The canonical stage-two embedding `f₂,∞ : K₂ → K∞`. -/
noncomputable def embedLevelTwoToLimit (x : (K 2).Obj) : KInfinityCHPO.Obj where
  val := levelTwoCoords x
  toPrev := by
    intro n
    cases n with
    | zero =>
        change
          (K 0).Rel
            ((fMinus 0).toFun ((fMinus 1).toFun x))
            ((fMinus 0).toFun ((fMinus 1).toFun x))
        exact (K 0).rel_refl _
    | succ n =>
        cases n with
        | zero =>
            change
              (K 1).Rel
                ((fMinus 1).toFun x)
                ((fMinus 1).toFun x)
            exact (K 1).rel_refl _
        | succ n =>
            change
              (K (n + 2)).Rel
                ((fMinus (n + 2)).toFun ((fPlus (n + 2)).toFun (levelTwoCoords x (n + 2))))
                (levelTwoCoords x (n + 2))
            have hEq :
                (fMinus (n + 2)).toFun ((fPlus (n + 2)).toFun (levelTwoCoords x (n + 2))) =
                  levelTwoCoords x (n + 2) := by
              exact congrArg (fun g => g.toFun (levelTwoCoords x (n + 2)))
                (fMinus_comp_fPlus (n + 2))
            rw [hEq]
            exact (K (n + 2)).rel_refl _
  fromPrev := by
    intro n
    cases n with
    | zero =>
        change
          (K 0).Rel
            ((fMinus 0).toFun ((fMinus 1).toFun x))
            ((fMinus 0).toFun ((fMinus 1).toFun x))
        exact (K 0).rel_refl _
    | succ n =>
        cases n with
        | zero =>
            change
              (K 1).Rel
                ((fMinus 1).toFun x)
                ((fMinus 1).toFun x)
            exact (K 1).rel_refl _
        | succ n =>
            change
              (K (n + 2)).Rel
                (levelTwoCoords x (n + 2))
                ((fMinus (n + 2)).toFun ((fPlus (n + 2)).toFun (levelTwoCoords x (n + 2))))
            have hEq :
                (fMinus (n + 2)).toFun ((fPlus (n + 2)).toFun (levelTwoCoords x (n + 2))) =
                  levelTwoCoords x (n + 2) := by
              exact congrArg (fun g => g.toFun (levelTwoCoords x (n + 2)))
                (fMinus_comp_fPlus (n + 2))
            rw [hEq]
            exact (K (n + 2)).rel_refl _

@[simp] theorem project_embedLevelTwo_zero (x : (K 2).Obj) :
    projectToLevel 0 (embedLevelTwoToLimit x) = (fMinus 0).toFun ((fMinus 1).toFun x) := rfl

@[simp] theorem project_embedLevelTwo_one (x : (K 2).Obj) :
    projectToLevel 1 (embedLevelTwoToLimit x) = (fMinus 1).toFun x := rfl

@[simp] theorem project_embedLevelTwo_two (x : (K 2).Obj) :
    projectToLevel 2 (embedLevelTwoToLimit x) = x := rfl

/-- The stage-two embedding is monotone into `K∞`. -/
theorem embedLevelTwoToLimit_monotone
    {x y : (K 2).Obj}
    (hxy : (K 2).Rel x y) :
    KInfinityCHPO.Rel (embedLevelTwoToLimit x) (embedLevelTwoToLimit y) := by
  exact Projective.rel_mk (S := system) (fun n => by
    simpa [levelTwoCoordinateContinuous_apply] using
      (levelTwoCoordinateContinuous n).monotone' hxy)

/-- The canonical stage-two embedding `f₂,∞ : K₂ → K∞` packaged as a continuous
map. -/
noncomputable def embedLevelTwoContinuous : ContinuousMap (K 2) KInfinityCHPO where
  toFun := embedLevelTwoToLimit
  monotone' := embedLevelTwoToLimit_monotone
  preserves_sup := by
    intro X hX
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact Projective.rel_mk (S := system) (fun n => by
        simpa [levelTwoCoordinateContinuous_apply] using
          ((levelTwoCoordinateContinuous n).preserves_sup X hX).1 ⟨x, hx, rfl⟩)
    · intro w hw
      exact Projective.rel_mk (S := system) (fun n => by
        simpa [levelTwoCoordinateContinuous_apply] using
          ((levelTwoCoordinateContinuous n).preserves_sup X hX).2 (by
            intro a ha
            rcases ha with ⟨x, hx, rfl⟩
            simpa [levelTwoCoordinateContinuous_apply] using
              (Projective.rel_iff.mp (hw ⟨x, hx, rfl⟩)) n))

/-! ## Level-Three Reification Shadow -/

/-- Coordinates of the canonical level-three embedding `f₃,∞ : K₃ → K∞`. -/
noncomputable def levelThreeCoords (x : (K 3).Obj) : (n : Nat) → (K n).Obj
  | 0 => (fMinus 0).toFun ((fMinus 1).toFun ((fMinus 2).toFun x))
  | 1 => (fMinus 1).toFun ((fMinus 2).toFun x)
  | 2 => (fMinus 2).toFun x
  | 3 => x
  | n + 4 => (fPlus (n + 3)).toFun (levelThreeCoords x (n + 3))

@[simp] theorem levelThreeCoords_zero (x : (K 3).Obj) :
    levelThreeCoords x 0 = (fMinus 0).toFun ((fMinus 1).toFun ((fMinus 2).toFun x)) := rfl

@[simp] theorem levelThreeCoords_one (x : (K 3).Obj) :
    levelThreeCoords x 1 = (fMinus 1).toFun ((fMinus 2).toFun x) := rfl

@[simp] theorem levelThreeCoords_two (x : (K 3).Obj) :
    levelThreeCoords x 2 = (fMinus 2).toFun x := rfl

@[simp] theorem levelThreeCoords_three (x : (K 3).Obj) :
    levelThreeCoords x 3 = x := rfl

@[simp] theorem levelThreeCoords_succ_succ_succ_succ (x : (K 3).Obj) (n : Nat) :
    levelThreeCoords x (n + 4) =
      (fPlus (n + 3)).toFun (levelThreeCoords x (n + 3)) := rfl

/-- The coordinate maps of the canonical level-three embedding are continuous. -/
noncomputable def levelThreeCoordinateContinuous :
    (n : Nat) → ContinuousMap (K 3) (K n)
  | 0 => ContinuousMap.comp (fMinus 0) (ContinuousMap.comp (fMinus 1) (fMinus 2))
  | 1 => ContinuousMap.comp (fMinus 1) (fMinus 2)
  | 2 => fMinus 2
  | 3 => ContinuousMap.id (K 3)
  | n + 4 => ContinuousMap.comp (fPlus (n + 3)) (levelThreeCoordinateContinuous (n + 3))

@[simp] theorem levelThreeCoordinateContinuous_apply
    (x : (K 3).Obj) :
    ∀ n : Nat, levelThreeCoordinateContinuous n x = levelThreeCoords x n
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | n + 4 => by
      change (fPlus (n + 3)) (levelThreeCoordinateContinuous (n + 3) x) =
        (fPlus (n + 3)).toFun (levelThreeCoords x (n + 3))
      rw [levelThreeCoordinateContinuous_apply x (n + 3)]

/-- The canonical stage-three embedding `f₃,∞ : K₃ → K∞`. -/
noncomputable def embedLevelThreeToLimit (x : (K 3).Obj) : KInfinityCHPO.Obj where
  val := levelThreeCoords x
  toPrev := by
    intro n
    cases n with
    | zero =>
        change
          (K 0).Rel
            ((fMinus 0).toFun ((fMinus 1).toFun ((fMinus 2).toFun x)))
            ((fMinus 0).toFun ((fMinus 1).toFun ((fMinus 2).toFun x)))
        exact (K 0).rel_refl _
    | succ n =>
        cases n with
        | zero =>
            change
              (K 1).Rel
                ((fMinus 1).toFun ((fMinus 2).toFun x))
                ((fMinus 1).toFun ((fMinus 2).toFun x))
            exact (K 1).rel_refl _
        | succ n =>
            cases n with
            | zero =>
                change
                  (K 2).Rel
                    ((fMinus 2).toFun x)
                    ((fMinus 2).toFun x)
                exact (K 2).rel_refl _
            | succ n =>
                change
                  (K (n + 3)).Rel
                    ((fMinus (n + 3)).toFun ((fPlus (n + 3)).toFun (levelThreeCoords x (n + 3))))
                    (levelThreeCoords x (n + 3))
                have hEq :
                    (fMinus (n + 3)).toFun ((fPlus (n + 3)).toFun (levelThreeCoords x (n + 3))) =
                      levelThreeCoords x (n + 3) := by
                  exact congrArg (fun g => g.toFun (levelThreeCoords x (n + 3)))
                    (fMinus_comp_fPlus (n + 3))
                rw [hEq]
                exact (K (n + 3)).rel_refl _
  fromPrev := by
    intro n
    cases n with
    | zero =>
        change
          (K 0).Rel
            ((fMinus 0).toFun ((fMinus 1).toFun ((fMinus 2).toFun x)))
            ((fMinus 0).toFun ((fMinus 1).toFun ((fMinus 2).toFun x)))
        exact (K 0).rel_refl _
    | succ n =>
        cases n with
        | zero =>
            change
              (K 1).Rel
                ((fMinus 1).toFun ((fMinus 2).toFun x))
                ((fMinus 1).toFun ((fMinus 2).toFun x))
            exact (K 1).rel_refl _
        | succ n =>
            cases n with
            | zero =>
                change
                  (K 2).Rel
                    ((fMinus 2).toFun x)
                    ((fMinus 2).toFun x)
                exact (K 2).rel_refl _
            | succ n =>
                change
                  (K (n + 3)).Rel
                    (levelThreeCoords x (n + 3))
                    ((fMinus (n + 3)).toFun ((fPlus (n + 3)).toFun (levelThreeCoords x (n + 3))))
                have hEq :
                    (fMinus (n + 3)).toFun ((fPlus (n + 3)).toFun (levelThreeCoords x (n + 3))) =
                      levelThreeCoords x (n + 3) := by
                  exact congrArg (fun g => g.toFun (levelThreeCoords x (n + 3)))
                    (fMinus_comp_fPlus (n + 3))
                rw [hEq]
                exact (K (n + 3)).rel_refl _

@[simp] theorem project_embedLevelThree_zero (x : (K 3).Obj) :
    projectToLevel 0 (embedLevelThreeToLimit x) =
      (fMinus 0).toFun ((fMinus 1).toFun ((fMinus 2).toFun x)) := rfl

@[simp] theorem project_embedLevelThree_one (x : (K 3).Obj) :
    projectToLevel 1 (embedLevelThreeToLimit x) = (fMinus 1).toFun ((fMinus 2).toFun x) := rfl

@[simp] theorem project_embedLevelThree_two (x : (K 3).Obj) :
    projectToLevel 2 (embedLevelThreeToLimit x) = (fMinus 2).toFun x := rfl

@[simp] theorem project_embedLevelThree_three (x : (K 3).Obj) :
    projectToLevel 3 (embedLevelThreeToLimit x) = x := rfl

/-- The stage-three embedding is monotone into `K∞`. -/
theorem embedLevelThreeToLimit_monotone
    {x y : (K 3).Obj}
    (hxy : (K 3).Rel x y) :
    KInfinityCHPO.Rel (embedLevelThreeToLimit x) (embedLevelThreeToLimit y) := by
  exact Projective.rel_mk (S := system) (fun n => by
    simpa [levelThreeCoordinateContinuous_apply] using
      (levelThreeCoordinateContinuous n).monotone' hxy)

/-- The canonical stage-three embedding `f₃,∞ : K₃ → K∞` packaged as a continuous
map. -/
noncomputable def embedLevelThreeContinuous : ContinuousMap (K 3) KInfinityCHPO where
  toFun := embedLevelThreeToLimit
  monotone' := embedLevelThreeToLimit_monotone
  preserves_sup := by
    intro X hX
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact Projective.rel_mk (S := system) (fun n => by
        simpa [levelThreeCoordinateContinuous_apply] using
          ((levelThreeCoordinateContinuous n).preserves_sup X hX).1 ⟨x, hx, rfl⟩)
    · intro w hw
      exact Projective.rel_mk (S := system) (fun n => by
        simpa [levelThreeCoordinateContinuous_apply] using
          ((levelThreeCoordinateContinuous n).preserves_sup X hX).2 (by
            intro a ha
            rcases ha with ⟨x, hx, rfl⟩
            simpa [levelThreeCoordinateContinuous_apply] using
              (Projective.rel_iff.mp (hw ⟨x, hx, rfl⟩)) n))

/-! ## Level-Four Reification Shadow -/

/-- Coordinates of the canonical level-four embedding `f₄,∞ : K₄ → K∞`. -/
noncomputable def levelFourCoords (x : (K 4).Obj) : (n : Nat) → (K n).Obj
  | 0 => (fMinus 0).toFun ((fMinus 1).toFun ((fMinus 2).toFun ((fMinus 3).toFun x)))
  | 1 => (fMinus 1).toFun ((fMinus 2).toFun ((fMinus 3).toFun x))
  | 2 => (fMinus 2).toFun ((fMinus 3).toFun x)
  | 3 => (fMinus 3).toFun x
  | 4 => x
  | n + 5 => (fPlus (n + 4)).toFun (levelFourCoords x (n + 4))

@[simp] theorem levelFourCoords_zero (x : (K 4).Obj) :
    levelFourCoords x 0 =
      (fMinus 0).toFun ((fMinus 1).toFun ((fMinus 2).toFun ((fMinus 3).toFun x))) := rfl

@[simp] theorem levelFourCoords_one (x : (K 4).Obj) :
    levelFourCoords x 1 = (fMinus 1).toFun ((fMinus 2).toFun ((fMinus 3).toFun x)) := rfl

@[simp] theorem levelFourCoords_two (x : (K 4).Obj) :
    levelFourCoords x 2 = (fMinus 2).toFun ((fMinus 3).toFun x) := rfl

@[simp] theorem levelFourCoords_three (x : (K 4).Obj) :
    levelFourCoords x 3 = (fMinus 3).toFun x := rfl

@[simp] theorem levelFourCoords_four (x : (K 4).Obj) :
    levelFourCoords x 4 = x := rfl

@[simp] theorem levelFourCoords_succ_succ_succ_succ_succ (x : (K 4).Obj) (n : Nat) :
    levelFourCoords x (n + 5) =
      (fPlus (n + 4)).toFun (levelFourCoords x (n + 4)) := rfl

/-- The coordinate maps of the canonical level-four embedding are continuous. -/
noncomputable def levelFourCoordinateContinuous :
    (n : Nat) → ContinuousMap (K 4) (K n)
  | 0 => ContinuousMap.comp (fMinus 0)
      (ContinuousMap.comp (fMinus 1) (ContinuousMap.comp (fMinus 2) (fMinus 3)))
  | 1 => ContinuousMap.comp (fMinus 1) (ContinuousMap.comp (fMinus 2) (fMinus 3))
  | 2 => ContinuousMap.comp (fMinus 2) (fMinus 3)
  | 3 => fMinus 3
  | 4 => ContinuousMap.id (K 4)
  | n + 5 => ContinuousMap.comp (fPlus (n + 4)) (levelFourCoordinateContinuous (n + 4))

@[simp] theorem levelFourCoordinateContinuous_apply
    (x : (K 4).Obj) :
    ∀ n : Nat, levelFourCoordinateContinuous n x = levelFourCoords x n
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | n + 5 => by
      change (fPlus (n + 4)) (levelFourCoordinateContinuous (n + 4) x) =
        (fPlus (n + 4)).toFun (levelFourCoords x (n + 4))
      rw [levelFourCoordinateContinuous_apply x (n + 4)]

/-- The canonical stage-four embedding `f₄,∞ : K₄ → K∞`. -/
noncomputable def embedLevelFourToLimit (x : (K 4).Obj) : KInfinityCHPO.Obj where
  val := levelFourCoords x
  toPrev := by
    intro n
    cases n with
    | zero =>
        change
          (K 0).Rel
            ((fMinus 0).toFun ((fMinus 1).toFun ((fMinus 2).toFun ((fMinus 3).toFun x))))
            ((fMinus 0).toFun ((fMinus 1).toFun ((fMinus 2).toFun ((fMinus 3).toFun x))))
        exact (K 0).rel_refl _
    | succ n =>
        cases n with
        | zero =>
            change
              (K 1).Rel
                ((fMinus 1).toFun ((fMinus 2).toFun ((fMinus 3).toFun x)))
                ((fMinus 1).toFun ((fMinus 2).toFun ((fMinus 3).toFun x)))
            exact (K 1).rel_refl _
        | succ n =>
            cases n with
            | zero =>
                change
                  (K 2).Rel
                    ((fMinus 2).toFun ((fMinus 3).toFun x))
                    ((fMinus 2).toFun ((fMinus 3).toFun x))
                exact (K 2).rel_refl _
            | succ n =>
                cases n with
                | zero =>
                    change
                      (K 3).Rel
                        ((fMinus 3).toFun x)
                        ((fMinus 3).toFun x)
                    exact (K 3).rel_refl _
                | succ n =>
                    change
                      (K (n + 4)).Rel
                        ((fMinus (n + 4)).toFun
                          ((fPlus (n + 4)).toFun (levelFourCoords x (n + 4))))
                        (levelFourCoords x (n + 4))
                    have hEq :
                        (fMinus (n + 4)).toFun
                            ((fPlus (n + 4)).toFun (levelFourCoords x (n + 4))) =
                          levelFourCoords x (n + 4) := by
                      exact congrArg (fun g => g.toFun (levelFourCoords x (n + 4)))
                        (fMinus_comp_fPlus (n + 4))
                    rw [hEq]
                    exact (K (n + 4)).rel_refl _
  fromPrev := by
    intro n
    cases n with
    | zero =>
        change
          (K 0).Rel
            ((fMinus 0).toFun ((fMinus 1).toFun ((fMinus 2).toFun ((fMinus 3).toFun x))))
            ((fMinus 0).toFun ((fMinus 1).toFun ((fMinus 2).toFun ((fMinus 3).toFun x))))
        exact (K 0).rel_refl _
    | succ n =>
        cases n with
        | zero =>
            change
              (K 1).Rel
                ((fMinus 1).toFun ((fMinus 2).toFun ((fMinus 3).toFun x)))
                ((fMinus 1).toFun ((fMinus 2).toFun ((fMinus 3).toFun x)))
            exact (K 1).rel_refl _
        | succ n =>
            cases n with
            | zero =>
                change
                  (K 2).Rel
                    ((fMinus 2).toFun ((fMinus 3).toFun x))
                    ((fMinus 2).toFun ((fMinus 3).toFun x))
                exact (K 2).rel_refl _
            | succ n =>
                cases n with
                | zero =>
                    change
                      (K 3).Rel
                        ((fMinus 3).toFun x)
                        ((fMinus 3).toFun x)
                    exact (K 3).rel_refl _
                | succ n =>
                    change
                      (K (n + 4)).Rel
                        (levelFourCoords x (n + 4))
                        ((fMinus (n + 4)).toFun
                          ((fPlus (n + 4)).toFun (levelFourCoords x (n + 4))))
                    have hEq :
                        (fMinus (n + 4)).toFun
                            ((fPlus (n + 4)).toFun (levelFourCoords x (n + 4))) =
                          levelFourCoords x (n + 4) := by
                      exact congrArg (fun g => g.toFun (levelFourCoords x (n + 4)))
                        (fMinus_comp_fPlus (n + 4))
                    rw [hEq]
                    exact (K (n + 4)).rel_refl _

@[simp] theorem project_embedLevelFour_zero (x : (K 4).Obj) :
    projectToLevel 0 (embedLevelFourToLimit x) =
      (fMinus 0).toFun ((fMinus 1).toFun ((fMinus 2).toFun ((fMinus 3).toFun x))) := rfl

@[simp] theorem project_embedLevelFour_one (x : (K 4).Obj) :
    projectToLevel 1 (embedLevelFourToLimit x) =
      (fMinus 1).toFun ((fMinus 2).toFun ((fMinus 3).toFun x)) := rfl

@[simp] theorem project_embedLevelFour_two (x : (K 4).Obj) :
    projectToLevel 2 (embedLevelFourToLimit x) = (fMinus 2).toFun ((fMinus 3).toFun x) := rfl

@[simp] theorem project_embedLevelFour_three (x : (K 4).Obj) :
    projectToLevel 3 (embedLevelFourToLimit x) = (fMinus 3).toFun x := rfl

@[simp] theorem project_embedLevelFour_four (x : (K 4).Obj) :
    projectToLevel 4 (embedLevelFourToLimit x) = x := rfl

/-- The stage-four embedding is monotone into `K∞`. -/
theorem embedLevelFourToLimit_monotone
    {x y : (K 4).Obj}
    (hxy : (K 4).Rel x y) :
    KInfinityCHPO.Rel (embedLevelFourToLimit x) (embedLevelFourToLimit y) := by
  exact Projective.rel_mk (S := system) (fun n => by
    simpa [levelFourCoordinateContinuous_apply] using
      (levelFourCoordinateContinuous n).monotone' hxy)

/-- The canonical stage-four embedding `f₄,∞ : K₄ → K∞` packaged as a continuous
map. -/
noncomputable def embedLevelFourContinuous : ContinuousMap (K 4) KInfinityCHPO where
  toFun := embedLevelFourToLimit
  monotone' := embedLevelFourToLimit_monotone
  preserves_sup := by
    intro X hX
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact Projective.rel_mk (S := system) (fun n => by
        simpa [levelFourCoordinateContinuous_apply] using
          ((levelFourCoordinateContinuous n).preserves_sup X hX).1 ⟨x, hx, rfl⟩)
    · intro w hw
      exact Projective.rel_mk (S := system) (fun n => by
        simpa [levelFourCoordinateContinuous_apply] using
          ((levelFourCoordinateContinuous n).preserves_sup X hX).2 (by
            intro a ha
            rcases ha with ⟨x, hx, rfl⟩
            simpa [levelFourCoordinateContinuous_apply] using
              (Projective.rel_iff.mp (hw ⟨x, hx, rfl⟩)) n))

/-- Restrict an endomap of `K∞` along the stage-three embedding and project back
to `K₃`, producing the stage-four approximation that feeds the next `h`-shadow. -/
noncomputable def restrictEndomapToLevelThreeContinuous :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) (K 4) :=
  ContinuousMap.comp
    (postcomposeContinuous (projectContinuous 3))
    (precomposeContinuous embedLevelThreeContinuous)

@[simp] theorem restrictEndomapToLevelThreeContinuous_apply
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj)
    (x : (K 3).Obj) :
    ((restrictEndomapToLevelThreeContinuous.toFun g).toFun x) =
      projectToLevel 3 (g.toFun (embedLevelThreeToLimit x)) := by
  rfl

/-- The current level-four shadow of Proposition 4.3 in the `h` direction. -/
noncomputable def hLevelThreeContinuous :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO :=
  ContinuousMap.comp embedLevelFourContinuous restrictEndomapToLevelThreeContinuous

@[simp] theorem project_hLevelThree_four
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj) :
    projectToLevel 4 (hLevelThreeContinuous g) = restrictEndomapToLevelThreeContinuous g := rfl

/-- Proposition 4.3, recorded at the fourth stage in the `h` direction. -/
theorem proposition_4_3_hLevelThree
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj)
    (x : (K 3).Obj) :
    ((projectToLevel 4 (hLevelThreeContinuous g)).toFun x) =
      projectToLevel 3 (g.toFun (embedLevelThreeToLimit x)) := by
  rfl

/-- Restrict an endomap of `K∞` along the stage-two embedding and project back to
`K₂`, producing the stage-three approximation that feeds the next `h`-shadow. -/
noncomputable def restrictEndomapToLevelTwoContinuous :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) (K 3) :=
  ContinuousMap.comp
    (postcomposeContinuous (projectContinuous 2))
    (precomposeContinuous embedLevelTwoContinuous)

@[simp] theorem restrictEndomapToLevelTwoContinuous_apply
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj)
    (x : (K 2).Obj) :
    ((restrictEndomapToLevelTwoContinuous.toFun g).toFun x) =
      projectToLevel 2 (g.toFun (embedLevelTwoToLimit x)) := by
  rfl

/-- The current level-three shadow of Proposition 4.3 in the `h` direction. -/
noncomputable def hLevelTwoContinuous :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO :=
  ContinuousMap.comp embedLevelThreeContinuous restrictEndomapToLevelTwoContinuous

@[simp] theorem project_hLevelTwo_three
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj) :
    projectToLevel 3 (hLevelTwoContinuous g) = restrictEndomapToLevelTwoContinuous g := rfl

/-- Proposition 4.3, recorded at the third stage in the `h` direction. -/
theorem proposition_4_3_hLevelTwo
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj)
    (x : (K 2).Obj) :
    ((projectToLevel 3 (hLevelTwoContinuous g)).toFun x) =
      projectToLevel 2 (g.toFun (embedLevelTwoToLimit x)) := by
  rfl

/-- Restrict an endomap of `K∞` along the stage-one embedding and project back
to `K₁`, producing the stage-two approximation that feeds the next `h`-shadow.
-/
noncomputable def restrictEndomapToLevelOneContinuous :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) (K 2) :=
  ContinuousMap.comp
    (postcomposeContinuous (projectContinuous 1))
    (precomposeContinuous embedLevelOneContinuous)

@[simp] theorem restrictEndomapToLevelOneContinuous_apply
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj)
    (x : (K 1).Obj) :
    ((restrictEndomapToLevelOneContinuous.toFun g).toFun x) =
      projectToLevel 1 (g.toFun (embedLevelOneToLimit x)) := by
  rfl

/-- The current level-two shadow of Proposition 4.3 in the `h` direction. -/
noncomputable def hLevelOneContinuous :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO :=
  ContinuousMap.comp embedLevelTwoContinuous restrictEndomapToLevelOneContinuous

@[simp] theorem project_hLevelOne_two
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj) :
    projectToLevel 2 (hLevelOneContinuous g) = restrictEndomapToLevelOneContinuous g := rfl

/-- Proposition 4.3, recorded at the second stage in the `h` direction. -/
theorem proposition_4_3_hLevelOne
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj)
    (x : (K 1).Obj) :
    ((projectToLevel 2 (hLevelOneContinuous g)).toFun x) =
      projectToLevel 1 (g.toFun (embedLevelOneToLimit x)) := by
  rfl

/-- Restrict an endomap of `K∞` along the base embedding and project back to
`K₀`, producing the stage-one approximation that feeds the current `h`-shadow.
-/
noncomputable def restrictEndomapToBaseContinuous :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) (K 1) :=
  ContinuousMap.comp
    (postcomposeContinuous (projectContinuous 0))
    (precomposeContinuous embedBaseContinuous)

@[simp] theorem restrictEndomapToBaseContinuous_apply
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj)
    (x : (K 0).Obj) :
    ((restrictEndomapToBaseContinuous.toFun g).toFun x) =
      projectToLevel 0 (g.toFun (embedBaseToLimit x)) := by
  rfl

/-- The current level-one shadow of Proposition 4.3 in the `h` direction. -/
noncomputable def hBaseContinuous :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO :=
  ContinuousMap.comp embedLevelOneContinuous restrictEndomapToBaseContinuous

@[simp] theorem project_hBaseContinuous_one
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj) :
    projectToLevel 1 (hBaseContinuous g) = restrictEndomapToBaseContinuous g := rfl

/-- Proposition 4.3, recorded at the first stage in the `h` direction. -/
theorem proposition_4_3_hBase
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj)
    (x : (K 0).Obj) :
    ((projectToLevel 1 (hBaseContinuous g)).toFun x) =
      projectToLevel 0 (g.toFun (embedBaseToLimit x)) := by
  rfl

/-- Chosen-data level-zero approximation of Proposition 4.2. -/
noncomputable def proposition_4_2_approximation
    (x : KInfinityCHPO.Obj) :
    KInfinityCHPO.Obj :=
  embedBaseToLimit (projectToLevel 0 x)

/-- Proposition 4.2, recorded on the base coordinate of `K∞`. -/
theorem proposition_4_2 (x : KInfinityCHPO.Obj) :
    projectToLevel 0 (proposition_4_2_approximation x) = projectToLevel 0 x := by
  simp [proposition_4_2_approximation]

private theorem baseUp_below_of_level0
    {x : (K 0).Obj} {y : KInfinityCHPO.Obj}
    (h0 : (K 0).Rel x (projectToLevel 0 y)) :
    ∀ n : Nat, (K n).Rel (baseUp x n) (projectToLevel n y)
  | 0 => by simpa [baseUp] using h0
  | n + 1 => by
      have ih : (K n).Rel (baseUp x n) (projectToLevel n y) :=
        baseUp_below_of_level0 h0 n
      have hPlus :
          (K (n + 1)).Rel
            ((fPlus n).toFun (baseUp x n))
            ((fPlus n).toFun (projectToLevel n y)) :=
        (fPlus n).monotone' ih
      have hFrom :
          (K n).Rel
            (projectToLevel n y)
            ((fMinus n).toFun (projectToLevel (n + 1) y)) :=
        y.fromPrev n
      have hLift :
          (K (n + 1)).Rel
            ((fPlus n).toFun (projectToLevel n y))
            ((fPlus n).toFun ((fMinus n).toFun (projectToLevel (n + 1) y))) :=
        (fPlus n).monotone' hFrom
      have hSection :
          (K (n + 1)).Rel
            ((fPlus n).toFun ((fMinus n).toFun (projectToLevel (n + 1) y)))
            (projectToLevel (n + 1) y) :=
        fPlus_fMinus_le n (projectToLevel (n + 1) y)
      simpa [baseUp_succ] using
        (K (n + 1)).rel_trans hPlus ((K (n + 1)).rel_trans hLift hSection)

/-- The canonical base embedding lies below any thread whose base coordinate
dominates the chosen level-zero point. -/
theorem embedBaseToLimit_below_of_level0
    {x : (K 0).Obj} {y : KInfinityCHPO.Obj}
    (h0 : (K 0).Rel x (projectToLevel 0 y)) :
    KInfinityCHPO.Rel (embedBaseToLimit x) y := by
  exact Projective.rel_mk (S := system) (baseUp_below_of_level0 h0)

/-- The base embedding of a level-zero point is compact in `K∞`. This gives a
concrete compact finite approximation for every inverse-limit thread. -/
theorem embedBaseToLimit_compact (x : (K 0).Obj) :
    IsCompact KInfinityCHPO (embedBaseToLimit x) := by
  intro X hX hSup
  let Y : (K 0).Obj → Prop := Projective.coordPred (S := system) X 0
  have hY : (K 0).Directed Y := Projective.directed_coord (S := system) hX 0
  have hxCompact : IsCompact (K 0) x := by
    simpa [K] using (Flat.isCompact (α := SpherePoint) x)
  have hxSup : (K 0).Rel x (projectToLevel 0 (KInfinityCHPO.sup X hX)) := by
    have hCoord :
        (K 0).Rel
          (projectToLevel 0 (embedBaseToLimit x))
          (projectToLevel 0 (KInfinityCHPO.sup X hX)) :=
      (Projective.rel_iff.mp hSup) 0
    simpa [project_embedBase_self] using hCoord
  have hImage :
      image (fun z : KInfinityCHPO.Obj => z.val 0) X = Y := by
    funext a
    apply propext
    constructor <;> intro ha <;> simpa [Y, Projective.coordPred] using ha
  have hCoordLub :
      (K 0).IsLeastUpperBound Y (projectToLevel 0 (KInfinityCHPO.sup X hX)) := by
    simpa [projectToLevel, Y, hImage] using (projectContinuous 0).preserves_sup X hX
  rcases hxCompact Y hY hxSup with ⟨a, ha, hxa⟩
  rcases ha with ⟨y, hy, hya⟩
  refine ⟨y, hy, ?_⟩
  apply embedBaseToLimit_below_of_level0
  simpa [projectToLevel, hya] using hxa

/-- The base approximation of any thread is below that thread. -/
theorem proposition_4_1_baseApprox_below (x : KInfinityCHPO.Obj) :
    KInfinityCHPO.Rel (proposition_4_2_approximation x) x := by
  have h0 : (K 0).Rel (projectToLevel 0 x) (projectToLevel 0 x) :=
    (K 0).rel_refl (projectToLevel 0 x)
  simpa [proposition_4_2_approximation] using
    (embedBaseToLimit_below_of_level0 (x := projectToLevel 0 x) (y := x) h0)

/-- The chosen Proposition 4.2 approximation is compact in `K∞`. -/
theorem proposition_4_1_baseApprox_compact (x : KInfinityCHPO.Obj) :
    IsCompact KInfinityCHPO (proposition_4_2_approximation x) := by
  simpa [proposition_4_2_approximation] using
    embedBaseToLimit_compact (projectToLevel 0 x)

/-- Chosen-data packaging of the Section 4.1 interface for `K∞`. Besides the
per-stage bounded-completeness data and coordinate projections, the witness
records both the compact level-zero approximation of each inverse-limit thread
and the full directed finite-stage approximation family whose least upper bound
is the original thread. This isolates the exact remaining gap to the generic
algebraicity step needed to package `K∞` itself as a `HomotopyScottDomain`. -/
structure Proposition41Witness where
  stageBoundedComplete : ∀ n : Nat, BoundedComplete (K n)
  coordinateProjection : ∀ n : Nat, ContinuousMap KInfinityCHPO (K n)
  baseApproximation : KInfinityCHPO.Obj → KInfinityCHPO.Obj
  baseApproximation_finite :
    ∀ x : KInfinityCHPO.Obj, ∃ a : (K 0).Obj, baseApproximation x = embedBaseToLimit a
  baseApproximation_compact :
    ∀ x : KInfinityCHPO.Obj, IsCompact KInfinityCHPO (baseApproximation x)
  baseApproximation_below :
    ∀ x : KInfinityCHPO.Obj, KInfinityCHPO.Rel (baseApproximation x) x
  baseApproximation_exact0 :
    ∀ x : KInfinityCHPO.Obj,
      projectToLevel 0 (baseApproximation x) = projectToLevel 0 x
  stageZeroAlgebraic : Algebraic (K 0)
  finiteStageApproximation : Nat → KInfinityCHPO.Obj → KInfinityCHPO.Obj
  finiteStageApproximation_exact :
    ∀ n : Nat, ∀ x : KInfinityCHPO.Obj,
      projectToLevel n (finiteStageApproximation n x) = projectToLevel n x
  finiteStageApproximation_below :
    ∀ n : Nat, ∀ x : KInfinityCHPO.Obj,
      KInfinityCHPO.Rel (finiteStageApproximation n x) x
  finiteStageApproximation_mono :
    ∀ {n m : Nat}, n ≤ m → ∀ x : KInfinityCHPO.Obj,
      KInfinityCHPO.Rel (finiteStageApproximation n x) (finiteStageApproximation m x)
  finiteStageApproximation_directed :
    ∀ x : KInfinityCHPO.Obj,
      KInfinityCHPO.Directed (fun y => ∃ n : Nat, y = finiteStageApproximation n x)
  finiteStageApproximation_isLub :
    ∀ x : KInfinityCHPO.Obj,
      KInfinityCHPO.IsLeastUpperBound
        (fun y => ∃ n : Nat, y = finiteStageApproximation n x) x
  baseApproximation_isStageZero :
    ∀ x : KInfinityCHPO.Obj, baseApproximation x = finiteStageApproximation 0 x

/-- A level-zero shadow of Proposition 4.3: application determined by the first
two coordinates of `K∞`. -/
noncomputable def kBase
    (x y : KInfinityCHPO.Obj) :
    KInfinityCHPO.Obj :=
  embedBaseToLimit (((projectToLevel 1 x).toFun (projectToLevel 0 y)))

/-- Proposition 4.3, recorded on the base coordinate. -/
theorem proposition_4_3 (x y : KInfinityCHPO.Obj) :
    projectToLevel 0 (kBase x y) =
      ((projectToLevel 1 x).toFun (projectToLevel 0 y)) := by
  simp [kBase]

/-- The current base-coordinate shadow of Proposition 4.3 is jointly continuous
as a binary operation on `K∞`. -/
noncomputable def kInfinityBaseApplicationContinuous :
    ContinuousMap (Product.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO :=
  ContinuousMap.comp embedBaseContinuous <|
    ContinuousMap.comp (applicationContinuous (K 0) (K 0)) <|
      ContinuousMap.pair
        (ContinuousMap.comp (projectContinuous 1)
          (fstContinuous KInfinityCHPO KInfinityCHPO))
        (ContinuousMap.comp (projectContinuous 0)
          (sndContinuous KInfinityCHPO KInfinityCHPO))

@[simp] theorem kInfinityBaseApplicationContinuous_apply
    (x y : KInfinityCHPO.Obj) :
    kInfinityBaseApplicationContinuous (x, y) = kBase x y := by
  rfl

/-- Curried continuous form of the current `K∞` base-application shadow. This
is the repository's current continuous approximation to the paper's map
`k : K∞ → [K∞ → K∞]`. -/
noncomputable def kBaseContinuous :
    ContinuousMap KInfinityCHPO (Exponential.chpo KInfinityCHPO KInfinityCHPO) :=
  curry kInfinityBaseApplicationContinuous

@[simp] theorem kBaseContinuous_apply
    (x y : KInfinityCHPO.Obj) :
    ((kBaseContinuous.toFun x).toFun y) = kBase x y := by
  change kInfinityBaseApplicationContinuous (x, y) = kBase x y
  rw [kInfinityBaseApplicationContinuous_apply]

/-- Restricting the current `k`-shadow back to the base stage recovers the
first coordinate of the original thread. -/
theorem restrictEndomapToBase_kBaseContinuous
    (x : KInfinityCHPO.Obj) :
    restrictEndomapToBaseContinuous (kBaseContinuous x) = projectToLevel 1 x := by
  apply ContinuousMap.ext
  intro y
  change ((restrictEndomapToBaseContinuous.toFun (kBaseContinuous x)).toFun y) =
    ((projectToLevel 1 x).toFun y)
  rw [restrictEndomapToBaseContinuous_apply, kBaseContinuous_apply]
  simpa [project_embedBase_self] using proposition_4_3 x (embedBaseToLimit y)

/-- The current `h`- and `k`-shadows already satisfy a first-stage retract law.
-/
theorem hBase_kBaseContinuous_stage1
    (x : KInfinityCHPO.Obj) :
    projectToLevel 1 (hBaseContinuous (kBaseContinuous x)) = projectToLevel 1 x := by
  rw [project_hBaseContinuous_one, restrictEndomapToBase_kBaseContinuous]

/-- A stage-one shadow of Proposition 4.3: application determined by the second
and first coordinates of `K∞`. -/
noncomputable def kLevelOne
    (x y : KInfinityCHPO.Obj) :
    KInfinityCHPO.Obj :=
  embedLevelOneToLimit (((projectToLevel 2 x).toFun (projectToLevel 1 y)))

/-- The stage-one application shadow records the second coordinate exactly. -/
theorem proposition_4_3_levelOne (x y : KInfinityCHPO.Obj) :
    projectToLevel 1 (kLevelOne x y) =
      ((projectToLevel 2 x).toFun (projectToLevel 1 y)) := by
  simp [kLevelOne]

/-- The stage-one application shadow is jointly continuous as a binary operation
on `K∞`. -/
noncomputable def kLevelOneBinaryContinuous :
    ContinuousMap (Product.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO :=
  ContinuousMap.comp embedLevelOneContinuous <|
    ContinuousMap.comp (applicationContinuous (K 1) (K 1)) <|
      ContinuousMap.pair
        (ContinuousMap.comp (projectContinuous 2)
          (fstContinuous KInfinityCHPO KInfinityCHPO))
        (ContinuousMap.comp (projectContinuous 1)
          (sndContinuous KInfinityCHPO KInfinityCHPO))

@[simp] theorem kLevelOneBinaryContinuous_apply
    (x y : KInfinityCHPO.Obj) :
    kLevelOneBinaryContinuous (x, y) = kLevelOne x y := by
  rfl

/-- Curried continuous form of the stage-one application shadow. -/
noncomputable def kLevelOneContinuous :
    ContinuousMap KInfinityCHPO (Exponential.chpo KInfinityCHPO KInfinityCHPO) :=
  curry kLevelOneBinaryContinuous

@[simp] theorem kLevelOneContinuous_apply
    (x y : KInfinityCHPO.Obj) :
    ((kLevelOneContinuous.toFun x).toFun y) = kLevelOne x y := by
  change kLevelOneBinaryContinuous (x, y) = kLevelOne x y
  rw [kLevelOneBinaryContinuous_apply]

/-- Restricting the stage-one `k`-shadow back to the stage-one embedding
recovers the second coordinate of the original thread. -/
theorem restrictEndomapToLevelOne_kLevelOneContinuous
    (x : KInfinityCHPO.Obj) :
    restrictEndomapToLevelOneContinuous (kLevelOneContinuous x) = projectToLevel 2 x := by
  apply ContinuousMap.ext
  intro y
  change ((restrictEndomapToLevelOneContinuous.toFun (kLevelOneContinuous x)).toFun y) =
    ((projectToLevel 2 x).toFun y)
  rw [restrictEndomapToLevelOneContinuous_apply, kLevelOneContinuous_apply]
  simpa [project_embedLevelOne_one] using proposition_4_3_levelOne x (embedLevelOneToLimit y)

/-- The stage-two `h`- and `k`-shadows already satisfy an exact stage-two
retract law. -/
theorem hLevelOne_kLevelOneContinuous_stage2
    (x : KInfinityCHPO.Obj) :
    projectToLevel 2 (hLevelOneContinuous (kLevelOneContinuous x)) = projectToLevel 2 x := by
  rw [project_hLevelOne_two, restrictEndomapToLevelOne_kLevelOneContinuous]

/-- A stage-two shadow of Proposition 4.3: application determined by the third
and second coordinates of `K∞`. -/
noncomputable def kLevelTwo
    (x y : KInfinityCHPO.Obj) :
    KInfinityCHPO.Obj :=
  embedLevelTwoToLimit (((projectToLevel 3 x).toFun (projectToLevel 2 y)))

/-- The stage-two application shadow records the third coordinate exactly. -/
theorem proposition_4_3_levelTwo (x y : KInfinityCHPO.Obj) :
    projectToLevel 2 (kLevelTwo x y) =
      ((projectToLevel 3 x).toFun (projectToLevel 2 y)) := by
  simp [kLevelTwo]

/-- The stage-two application shadow is jointly continuous as a binary operation
on `K∞`. -/
noncomputable def kLevelTwoBinaryContinuous :
    ContinuousMap (Product.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO :=
  ContinuousMap.comp embedLevelTwoContinuous <|
    ContinuousMap.comp (applicationContinuous (K 2) (K 2)) <|
      ContinuousMap.pair
        (ContinuousMap.comp (projectContinuous 3)
          (fstContinuous KInfinityCHPO KInfinityCHPO))
        (ContinuousMap.comp (projectContinuous 2)
          (sndContinuous KInfinityCHPO KInfinityCHPO))

@[simp] theorem kLevelTwoBinaryContinuous_apply
    (x y : KInfinityCHPO.Obj) :
    kLevelTwoBinaryContinuous (x, y) = kLevelTwo x y := by
  rfl

/-- Curried continuous form of the stage-two application shadow. -/
noncomputable def kLevelTwoContinuous :
    ContinuousMap KInfinityCHPO (Exponential.chpo KInfinityCHPO KInfinityCHPO) :=
  curry kLevelTwoBinaryContinuous

@[simp] theorem kLevelTwoContinuous_apply
    (x y : KInfinityCHPO.Obj) :
    ((kLevelTwoContinuous.toFun x).toFun y) = kLevelTwo x y := by
  change kLevelTwoBinaryContinuous (x, y) = kLevelTwo x y
  rw [kLevelTwoBinaryContinuous_apply]

/-- Restricting the stage-two `k`-shadow back to the stage-two embedding
recovers the third coordinate of the original thread. -/
theorem restrictEndomapToLevelTwo_kLevelTwoContinuous
    (x : KInfinityCHPO.Obj) :
    restrictEndomapToLevelTwoContinuous (kLevelTwoContinuous x) = projectToLevel 3 x := by
  apply ContinuousMap.ext
  intro y
  change ((restrictEndomapToLevelTwoContinuous.toFun (kLevelTwoContinuous x)).toFun y) =
    ((projectToLevel 3 x).toFun y)
  rw [restrictEndomapToLevelTwoContinuous_apply, kLevelTwoContinuous_apply]
  simpa [project_embedLevelTwo_two] using proposition_4_3_levelTwo x (embedLevelTwoToLimit y)

/-- The stage-three `h`- and `k`-shadows already satisfy an exact stage-three
retract law. -/
theorem hLevelTwo_kLevelTwoContinuous_stage3
    (x : KInfinityCHPO.Obj) :
    projectToLevel 3 (hLevelTwoContinuous (kLevelTwoContinuous x)) = projectToLevel 3 x := by
  rw [project_hLevelTwo_three, restrictEndomapToLevelTwo_kLevelTwoContinuous]

/-- A stage-three shadow of Proposition 4.3: application determined by the
fourth and third coordinates of `K∞`. -/
noncomputable def kLevelThree
    (x y : KInfinityCHPO.Obj) :
    KInfinityCHPO.Obj :=
  embedLevelThreeToLimit (((projectToLevel 4 x).toFun (projectToLevel 3 y)))

/-- The stage-three application shadow records the fourth coordinate exactly. -/
theorem proposition_4_3_levelThree (x y : KInfinityCHPO.Obj) :
    projectToLevel 3 (kLevelThree x y) =
      ((projectToLevel 4 x).toFun (projectToLevel 3 y)) := by
  simp [kLevelThree]

/-- The stage-three application shadow is jointly continuous as a binary
operation on `K∞`. -/
noncomputable def kLevelThreeBinaryContinuous :
    ContinuousMap (Product.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO :=
  ContinuousMap.comp embedLevelThreeContinuous <|
    ContinuousMap.comp (applicationContinuous (K 3) (K 3)) <|
      ContinuousMap.pair
        (ContinuousMap.comp (projectContinuous 4)
          (fstContinuous KInfinityCHPO KInfinityCHPO))
        (ContinuousMap.comp (projectContinuous 3)
          (sndContinuous KInfinityCHPO KInfinityCHPO))

@[simp] theorem kLevelThreeBinaryContinuous_apply
    (x y : KInfinityCHPO.Obj) :
    kLevelThreeBinaryContinuous (x, y) = kLevelThree x y := by
  rfl

/-- Curried continuous form of the stage-three application shadow. -/
noncomputable def kLevelThreeContinuous :
    ContinuousMap KInfinityCHPO (Exponential.chpo KInfinityCHPO KInfinityCHPO) :=
  curry kLevelThreeBinaryContinuous

@[simp] theorem kLevelThreeContinuous_apply
    (x y : KInfinityCHPO.Obj) :
    ((kLevelThreeContinuous.toFun x).toFun y) = kLevelThree x y := by
  change kLevelThreeBinaryContinuous (x, y) = kLevelThree x y
  rw [kLevelThreeBinaryContinuous_apply]

/-- Restricting the stage-three `k`-shadow back to the stage-three embedding
recovers the fourth coordinate of the original thread. -/
theorem restrictEndomapToLevelThree_kLevelThreeContinuous
    (x : KInfinityCHPO.Obj) :
    restrictEndomapToLevelThreeContinuous (kLevelThreeContinuous x) = projectToLevel 4 x := by
  apply ContinuousMap.ext
  intro y
  change ((restrictEndomapToLevelThreeContinuous.toFun (kLevelThreeContinuous x)).toFun y) =
    ((projectToLevel 4 x).toFun y)
  rw [restrictEndomapToLevelThreeContinuous_apply, kLevelThreeContinuous_apply]
  simpa [project_embedLevelThree_three] using proposition_4_3_levelThree x (embedLevelThreeToLimit y)

/-- The stage-four `h`- and `k`-shadows already satisfy an exact stage-four
retract law. -/
theorem hLevelThree_kLevelThreeContinuous_stage4
    (x : KInfinityCHPO.Obj) :
    projectToLevel 4 (hLevelThreeContinuous (kLevelThreeContinuous x)) = projectToLevel 4 x := by
  rw [project_hLevelThree_four, restrictEndomapToLevelThree_kLevelThreeContinuous]

/-- The original base-coordinate shadow of Remark 4.3. -/
noncomputable def baseApplicationShadow
    (x y : KInfinityCHPO.Obj) :
    KInfinityCHPO.Obj :=
  kBase x y

/-- The base-coordinate content of the original Remark 4.3 shadow. -/
theorem remark_4_3_shadow (x y : KInfinityCHPO.Obj) :
    projectToLevel 0 (baseApplicationShadow x y) =
      ((projectToLevel 1 x).toFun (projectToLevel 0 y)) := by
  simpa [baseApplicationShadow] using proposition_4_3 x y

/-- The chosen application shadow on `K∞` is jointly continuous. -/
noncomputable def applicationContinuousShadow :
    ContinuousMap (Product.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO :=
  kInfinityBaseApplicationContinuous

@[simp] theorem applicationContinuousShadow_apply
    (x y : KInfinityCHPO.Obj) :
    applicationContinuousShadow (x, y) = baseApplicationShadow x y := by
  rfl

/-! ## Generic Finite-Stage Shadow Infrastructure -/

/-- An exact continuous embedding of a finite stage `Kₙ` into the inverse limit
`K∞`. This isolates the data actually used by the current stage-by-stage
Section 4.3 shadows, so later finite-stage arguments can be phrased uniformly in
`n` rather than by hand for each concrete stage. -/
structure FiniteStageEmbedding (n : Nat) where
  embed : ContinuousMap (K n) KInfinityCHPO
  exact : ∀ x : (K n).Obj, projectToLevel n (embed x) = x

/-- The base-stage exact embedding witness. -/
noncomputable def baseStageEmbedding : FiniteStageEmbedding 0 where
  embed := embedBaseContinuous
  exact := project_embedBase_self

/-- The stage-one exact embedding witness. -/
noncomputable def levelOneStageEmbedding : FiniteStageEmbedding 1 where
  embed := embedLevelOneContinuous
  exact := project_embedLevelOne_one

/-- The stage-two exact embedding witness. -/
noncomputable def levelTwoStageEmbedding : FiniteStageEmbedding 2 where
  embed := embedLevelTwoContinuous
  exact := project_embedLevelTwo_two

/-- The stage-three exact embedding witness. -/
noncomputable def levelThreeStageEmbedding : FiniteStageEmbedding 3 where
  embed := embedLevelThreeContinuous
  exact := project_embedLevelThree_three

/-- The stage-four exact embedding witness. -/
noncomputable def levelFourStageEmbedding : FiniteStageEmbedding 4 where
  embed := embedLevelFourContinuous
  exact := project_embedLevelFour_four

/-- Coordinates of the canonical exact embedding `fₙ,∞ : Kₙ → K∞`, defined
uniformly for every finite stage by projecting downward below level `n` and
iterating the `f⁺` maps above it. -/
noncomputable def genericLevelCoords
    (n : Nat) (x : (K n).Obj) :
    (m : Nat) → (K m).Obj
  | 0 => projectDown n x 0 (Nat.zero_le n)
  | m + 1 =>
      if hm : m + 1 ≤ n then
        projectDown n x (m + 1) hm
      else
        (fPlus m).toFun (genericLevelCoords n x m)

theorem genericLevelCoords_below
    (n : Nat) (x : (K n).Obj) {m : Nat} (hm : m ≤ n) :
    genericLevelCoords n x m = projectDown n x m hm := by
  cases m with
  | zero =>
      simp [genericLevelCoords]
  | succ m =>
      simp [genericLevelCoords, hm]

@[simp] theorem genericLevelCoords_above
    (n : Nat) (x : (K n).Obj) {m : Nat} (hm : ¬ m + 1 ≤ n) :
    genericLevelCoords n x (m + 1) =
      (fPlus m).toFun (genericLevelCoords n x m) := by
  simp [genericLevelCoords, hm]

@[simp] theorem genericLevelCoords_self
    (n : Nat) (x : (K n).Obj) :
    genericLevelCoords n x n = x := by
  rw [genericLevelCoords_below n x (Nat.le_refl n)]
  exact projectDown_self n x

/-- The coordinate maps of the uniform finite-stage embedding are continuous. -/
noncomputable def genericLevelCoordinateContinuous
    (n : Nat) :
    (m : Nat) → ContinuousMap (K n) (K m)
  | 0 => projectDownContinuous n 0 (Nat.zero_le n)
  | m + 1 =>
      if hm : m + 1 ≤ n then
        projectDownContinuous n (m + 1) hm
      else
        ContinuousMap.comp (fPlus m) (genericLevelCoordinateContinuous n m)

theorem genericLevelCoordinateContinuous_apply
    (n : Nat) (x : (K n).Obj) :
    ∀ m : Nat, genericLevelCoordinateContinuous n m x = genericLevelCoords n x m
  | 0 => by
      simp [genericLevelCoordinateContinuous, genericLevelCoords, projectDownContinuous_apply]
  | m + 1 => by
      by_cases hm : m + 1 ≤ n
      · simp [genericLevelCoordinateContinuous, genericLevelCoords, hm,
          projectDownContinuous_apply]
      · conv =>
          lhs
          unfold genericLevelCoordinateContinuous
        simp [hm]
        change
          (fPlus m).toFun ((genericLevelCoordinateContinuous n m).toFun x) =
            (fPlus m).toFun (genericLevelCoords n x m)
        rw [genericLevelCoordinateContinuous_apply n x m]

/-- The canonical exact embedding `fₙ,∞ : Kₙ → K∞` for arbitrary finite stage
`n`. -/
noncomputable def embedFiniteStageToLimit
    (n : Nat) (x : (K n).Obj) : KInfinityCHPO.Obj where
  val := genericLevelCoords n x
  toPrev := by
    intro m
    by_cases hm : m < n
    · have hm_le : m ≤ n := by omega
      have hm1_le : m + 1 ≤ n := by omega
      rw [genericLevelCoords_below n x hm_le, genericLevelCoords_below n x hm1_le]
      rw [projectDown_step (n := n) (x := x) (m := m) hm]
      exact (K m).rel_refl _
    · have hm_ge : n ≤ m := by omega
      rw [genericLevelCoords_above n x (m := m) (by omega)]
      change
        (K m).Rel
          ((fMinus m).toFun ((fPlus m).toFun (genericLevelCoords n x m)))
          (genericLevelCoords n x m)
      have hEq :
          (fMinus m).toFun ((fPlus m).toFun (genericLevelCoords n x m)) =
            genericLevelCoords n x m := by
        exact congrArg (fun g => g.toFun (genericLevelCoords n x m))
          (fMinus_comp_fPlus m)
      rw [hEq]
      exact (K m).rel_refl _
  fromPrev := by
    intro m
    by_cases hm : m < n
    · have hm_le : m ≤ n := by omega
      have hm1_le : m + 1 ≤ n := by omega
      rw [genericLevelCoords_below n x hm_le, genericLevelCoords_below n x hm1_le]
      rw [projectDown_step (n := n) (x := x) (m := m) hm]
      exact (K m).rel_refl _
    · have hm_ge : n ≤ m := by omega
      rw [genericLevelCoords_above n x (m := m) (by omega)]
      change
        (K m).Rel
          (genericLevelCoords n x m)
          ((fMinus m).toFun ((fPlus m).toFun (genericLevelCoords n x m)))
      have hEq :
          (fMinus m).toFun ((fPlus m).toFun (genericLevelCoords n x m)) =
            genericLevelCoords n x m := by
        exact congrArg (fun g => g.toFun (genericLevelCoords n x m))
          (fMinus_comp_fPlus m)
      rw [hEq]
      exact (K m).rel_refl _

@[simp] theorem project_embedFiniteStage_exact
    (n : Nat) (x : (K n).Obj) :
    projectToLevel n (embedFiniteStageToLimit n x) = x := by
  exact genericLevelCoords_self n x

theorem embedFiniteStageToLimit_monotone
    (n : Nat) {x y : (K n).Obj}
    (hxy : (K n).Rel x y) :
    KInfinityCHPO.Rel (embedFiniteStageToLimit n x) (embedFiniteStageToLimit n y) := by
  exact Projective.rel_mk (S := system) (fun m => by
    simpa [genericLevelCoordinateContinuous_apply] using
      (genericLevelCoordinateContinuous n m).monotone' hxy)

/-- The canonical exact embedding `fₙ,∞ : Kₙ → K∞` packaged as a continuous map
for arbitrary finite stage `n`. -/
noncomputable def embedFiniteStageContinuous
    (n : Nat) : ContinuousMap (K n) KInfinityCHPO where
  toFun := embedFiniteStageToLimit n
  monotone' := embedFiniteStageToLimit_monotone n
  preserves_sup := by
    intro X hX
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact Projective.rel_mk (S := system) (fun m => by
        simpa [genericLevelCoordinateContinuous_apply] using
          ((genericLevelCoordinateContinuous n m).preserves_sup X hX).1 ⟨x, hx, rfl⟩)
    · intro w hw
      exact Projective.rel_mk (S := system) (fun m => by
        simpa [genericLevelCoordinateContinuous_apply] using
          ((genericLevelCoordinateContinuous n m).preserves_sup X hX).2 (by
            intro a ha
            rcases ha with ⟨x, hx, rfl⟩
            simpa [genericLevelCoordinateContinuous_apply] using
              (Projective.rel_iff.mp (hw ⟨x, hx, rfl⟩)) m))

/-- The uniform exact embedding witness for arbitrary finite stage `n`. -/
noncomputable def genericStageEmbedding
    (n : Nat) : FiniteStageEmbedding n where
  embed := embedFiniteStageContinuous n
  exact := project_embedFiniteStage_exact n

private theorem projectDown_thread
    (x : KInfinityCHPO.Obj) (n : Nat) :
    ∀ {m : Nat} (hm : m ≤ n),
      (K m).Rel (projectDown n (projectToLevel n x) m hm) (projectToLevel m x)
  | m, hm => by
      by_cases hmn : m = n
      · subst m
        simpa using (K n).rel_refl (projectToLevel n x)
      · have hlt : m < n := by omega
        rw [projectDown_step (n := n) (x := projectToLevel n x) (m := m) hlt]
        have hm' : m + 1 ≤ n := by omega
        exact (K m).rel_trans
          ((fMinus m).monotone' (projectDown_thread x n hm'))
          (x.toPrev m)
termination_by m _ => n - m
decreasing_by
  omega

private theorem stageApproximation_coord_below
    (x : KInfinityCHPO.Obj) (n : Nat) :
    ∀ m : Nat,
      (K m).Rel (genericLevelCoords n (projectToLevel n x) m) (projectToLevel m x)
  | 0 => by
      rw [genericLevelCoords_below n (projectToLevel n x) (Nat.zero_le n)]
      exact projectDown_thread x n (Nat.zero_le n)
  | m + 1 => by
      by_cases hm : m + 1 ≤ n
      · rw [genericLevelCoords_below n (projectToLevel n x) hm]
        exact projectDown_thread x n hm
      · rw [genericLevelCoords_above n (projectToLevel n x) (m := m) hm]
        exact (K (m + 1)).rel_trans
          ((fPlus m).monotone' (stageApproximation_coord_below x n m))
          ((K (m + 1)).rel_trans
            ((fPlus m).monotone' (x.fromPrev m))
            (fPlus_fMinus_le m (projectToLevel (m + 1) x)))

/-- The uniform stage-`n` approximation to a thread `x`, obtained by embedding its
`n`-th coordinate back into `K∞`. -/
noncomputable def proposition_4_2_stageApproximation
    (n : Nat) (x : KInfinityCHPO.Obj) :
    KInfinityCHPO.Obj :=
  embedFiniteStageToLimit n (projectToLevel n x)

/-- The stage-`n` approximation is exact on the `n`-th coordinate. -/
theorem proposition_4_2_stageApproximation_exact
    (n : Nat) (x : KInfinityCHPO.Obj) :
    projectToLevel n (proposition_4_2_stageApproximation n x) = projectToLevel n x := by
  simp [proposition_4_2_stageApproximation, project_embedFiniteStage_exact]

private theorem genericLevelCoords_zero_eq_baseUp
    (x : (K 0).Obj) :
    ∀ n : Nat, genericLevelCoords 0 x n = baseUp x n
  | 0 => by
      simp [genericLevelCoords, baseUp]
  | n + 1 => by
      rw [genericLevelCoords_above 0 x (m := n) (by omega), baseUp_succ]
      rw [genericLevelCoords_zero_eq_baseUp x n]

/-- Every stage-`n` approximation lies below the original thread in the inverse
limit order. -/
theorem proposition_4_2_stageApproximation_below
    (n : Nat) (x : KInfinityCHPO.Obj) :
    KInfinityCHPO.Rel (proposition_4_2_stageApproximation n x) x := by
  exact Projective.rel_mk (S := system) (stageApproximation_coord_below x n)

private theorem stageApproximation_coord_directed
    (x : KInfinityCHPO.Obj) (n : Nat) :
    ∀ m : Nat,
      (K m).Rel
        (projectToLevel m (proposition_4_2_stageApproximation n x))
        (projectToLevel m (proposition_4_2_stageApproximation (n + 1) x))
  | 0 => by
      change (K 0).Rel
        (genericLevelCoords n (projectToLevel n x) 0)
        (genericLevelCoords (n + 1) (projectToLevel (n + 1) x) 0)
      rw [genericLevelCoords_below n (projectToLevel n x) (Nat.zero_le n)]
      rw [genericLevelCoords_below (n + 1) (projectToLevel (n + 1) x) (Nat.zero_le (n + 1))]
      simp [projectDown_succ]
      simpa [projectToLevel] using projectDown_monotone n (x.fromPrev n) (m := 0) (by omega)
  | m + 1 => by
      change (K (m + 1)).Rel
        (genericLevelCoords n (projectToLevel n x) (m + 1))
        (genericLevelCoords (n + 1) (projectToLevel (n + 1) x) (m + 1))
      by_cases hm : m + 1 ≤ n
      · rw [genericLevelCoords_below n (projectToLevel n x) hm]
        rw [genericLevelCoords_below (n + 1) (projectToLevel (n + 1) x) (by omega)]
        rw [projectDown_succ n (projectToLevel (n + 1) x) (m := m + 1) hm]
        simpa [projectToLevel] using projectDown_monotone n (x.fromPrev n) (m := m + 1) hm
      · by_cases hEq : m = n
        · subst m
          rw [genericLevelCoords_above n (projectToLevel n x) (m := n) (by omega)]
          rw [genericLevelCoords_self n (projectToLevel n x)]
          rw [genericLevelCoords_self (n + 1) (projectToLevel (n + 1) x)]
          exact (K (n + 1)).rel_trans
            ((fPlus n).monotone' (x.fromPrev n))
            (fPlus_fMinus_le n (projectToLevel (n + 1) x))
        · have hm' : ¬ m + 1 ≤ n + 1 := by omega
          rw [genericLevelCoords_above n (projectToLevel n x) (m := m) hm]
          rw [genericLevelCoords_above (n + 1) (projectToLevel (n + 1) x) (m := m) hm']
          exact (fPlus m).monotone' (stageApproximation_coord_directed x n m)

/-- The uniform stage approximations form a directed chain in the inverse-limit
order. -/
theorem proposition_4_2_stageApproximation_directed
    (n : Nat) (x : KInfinityCHPO.Obj) :
    KInfinityCHPO.Rel
      (proposition_4_2_stageApproximation n x)
      (proposition_4_2_stageApproximation (n + 1) x) := by
  exact Projective.rel_mk (S := system) (stageApproximation_coord_directed x n)

/-- The uniform stage approximations are monotone in the stage index. -/
theorem proposition_4_2_stageApproximation_mono
    {n m : Nat} (h : n ≤ m) (x : KInfinityCHPO.Obj) :
    KInfinityCHPO.Rel
      (proposition_4_2_stageApproximation n x)
      (proposition_4_2_stageApproximation m x) := by
  induction h with
  | refl =>
      exact KInfinityCHPO.rel_refl _
  | @step m h ih =>
      exact KInfinityCHPO.rel_trans ih (proposition_4_2_stageApproximation_directed m x)

/-- Predicate selecting the finite-stage approximants of a fixed inverse-limit
thread. -/
def proposition_4_2_stageApproximationPred
    (x : KInfinityCHPO.Obj) :
    KInfinityCHPO.Obj → Prop :=
  fun y => ∃ n : Nat, y = proposition_4_2_stageApproximation n x

/-- The finite-stage approximants of a fixed thread form a directed predicate in
`K∞`. -/
theorem proposition_4_2_stageApproximationPred_directed
    (x : KInfinityCHPO.Obj) :
    KInfinityCHPO.Directed (proposition_4_2_stageApproximationPred x) := by
  constructor
  · exact ⟨proposition_4_2_stageApproximation 0 x, ⟨0, rfl⟩⟩
  · intro y z hy hz
    rcases hy with ⟨n, rfl⟩
    rcases hz with ⟨m, rfl⟩
    refine ⟨proposition_4_2_stageApproximation (max n m) x, ⟨max n m, rfl⟩, ?_, ?_⟩
    · exact proposition_4_2_stageApproximation_mono (Nat.le_max_left n m) x
    · exact proposition_4_2_stageApproximation_mono (Nat.le_max_right n m) x

/-- The original thread is the least upper bound of its finite-stage
approximants. -/
theorem proposition_4_2_stageApproximation_isLub
    (x : KInfinityCHPO.Obj) :
    KInfinityCHPO.IsLeastUpperBound (proposition_4_2_stageApproximationPred x) x := by
  constructor
  · intro y hy
    rcases hy with ⟨n, rfl⟩
    exact proposition_4_2_stageApproximation_below n x
  · intro w hw
    exact Projective.rel_mk (S := system) (fun n => by
      have hApprox :
          KInfinityCHPO.Rel (proposition_4_2_stageApproximation n x) w :=
        hw ⟨n, rfl⟩
      have hCoord : (K n).Rel
          (projectToLevel n (proposition_4_2_stageApproximation n x))
          (projectToLevel n w) :=
        (Projective.rel_iff.mp hApprox) n
      simpa [proposition_4_2_stageApproximation_exact n x] using hCoord)

/-- The chosen supremum of the finite-stage approximation predicate is equivalent
to the original thread in the induced homotopy order. -/
theorem proposition_4_2_stageApproximation_sup_equiv
    (x : KInfinityCHPO.Obj) :
    KInfinityCHPO.Rel
        (KInfinityCHPO.sup
          (proposition_4_2_stageApproximationPred x)
          (proposition_4_2_stageApproximationPred_directed x))
        x
      ∧
      KInfinityCHPO.Rel
        x
        (KInfinityCHPO.sup
          (proposition_4_2_stageApproximationPred x)
          (proposition_4_2_stageApproximationPred_directed x)) := by
  exact equivalent_of_isLeastUpperBound
    KInfinityCHPO.toHomotopyPartialOrder
    (KInfinityCHPO.sup_spec
      (proposition_4_2_stageApproximationPred x)
      (proposition_4_2_stageApproximationPred_directed x))
    (proposition_4_2_stageApproximation_isLub x)

/-- Chosen-data packaging of the repository's current Proposition 4.2 interface:
uniform finite-stage approximants, their directedness, and the resulting least
upper bound statement. -/
structure Proposition42Witness where
  approximation : Nat → KInfinityCHPO.Obj → KInfinityCHPO.Obj
  exactStage :
    ∀ n : Nat, ∀ x : KInfinityCHPO.Obj,
      projectToLevel n (approximation n x) = projectToLevel n x
  belowTarget :
    ∀ n : Nat, ∀ x : KInfinityCHPO.Obj,
      KInfinityCHPO.Rel (approximation n x) x
  monotoneStage :
    ∀ {n m : Nat}, n ≤ m → ∀ x : KInfinityCHPO.Obj,
      KInfinityCHPO.Rel (approximation n x) (approximation m x)
  directedFamily :
    ∀ x : KInfinityCHPO.Obj,
      KInfinityCHPO.Directed (fun y => ∃ n : Nat, y = approximation n x)
  isLub :
    ∀ x : KInfinityCHPO.Obj,
      KInfinityCHPO.IsLeastUpperBound (fun y => ∃ n : Nat, y = approximation n x) x
  chosenSupEquiv :
    ∀ x : KInfinityCHPO.Obj,
      KInfinityCHPO.Rel
          (KInfinityCHPO.sup
            (fun y => ∃ n : Nat, y = approximation n x)
            (directedFamily x))
          x
        ∧
        KInfinityCHPO.Rel
          x
          (KInfinityCHPO.sup
            (fun y => ∃ n : Nat, y = approximation n x)
            (directedFamily x))

/-- Proposition 4.2 in the repository's current chosen-data style. -/
noncomputable def proposition_4_2_shadow : Proposition42Witness where
  approximation := proposition_4_2_stageApproximation
  exactStage := proposition_4_2_stageApproximation_exact
  belowTarget := proposition_4_2_stageApproximation_below
  monotoneStage := by
    intro n m h x
    exact proposition_4_2_stageApproximation_mono h x
  directedFamily := proposition_4_2_stageApproximationPred_directed
  isLub := proposition_4_2_stageApproximation_isLub
  chosenSupEquiv := proposition_4_2_stageApproximation_sup_equiv

/-- Proposition 4.1 in the repository's current chosen-data style: bounded
completeness of each stage, continuity of the coordinate projections, the
compact level-zero approximation, and the full directed finite-stage
approximation family for every point of `K∞`. -/
noncomputable def proposition_4_1 : Proposition41Witness where
  stageBoundedComplete := stage_boundedComplete
  coordinateProjection := projectContinuous
  baseApproximation := proposition_4_2_approximation
  baseApproximation_finite := by
    intro x
    refine ⟨projectToLevel 0 x, rfl⟩
  baseApproximation_compact := proposition_4_1_baseApprox_compact
  baseApproximation_below := proposition_4_1_baseApprox_below
  baseApproximation_exact0 := proposition_4_2
  stageZeroAlgebraic := stage_algebraic_zero
  finiteStageApproximation := proposition_4_2_stageApproximation
  finiteStageApproximation_exact := proposition_4_2_stageApproximation_exact
  finiteStageApproximation_below := proposition_4_2_stageApproximation_below
  finiteStageApproximation_mono := by
    intro n m h x
    exact proposition_4_2_stageApproximation_mono h x
  finiteStageApproximation_directed := proposition_4_2_stageApproximationPred_directed
  finiteStageApproximation_isLub := proposition_4_2_stageApproximation_isLub
  baseApproximation_isStageZero := by
    intro x
    apply Projective.Thread.ext
    intro n
    change baseUp (projectToLevel 0 x) n = genericLevelCoords 0 (projectToLevel 0 x) n
    symm
    exact genericLevelCoords_zero_eq_baseUp (projectToLevel 0 x) n

/-- Restrict an endomap of `K∞` along an exact finite-stage embedding and project
back to the next stage. This is the generic form of the current ad hoc
definitions `restrictEndomapToBaseContinuous`, `restrictEndomapToLevelOneContinuous`,
and so on. -/
noncomputable def restrictEndomapToStageContinuous
    {n : Nat} (W : FiniteStageEmbedding n) :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) (K (n + 1)) :=
  ContinuousMap.comp
    (postcomposeContinuous (projectContinuous n))
    (precomposeContinuous W.embed)

@[simp] theorem restrictEndomapToStageContinuous_apply
    {n : Nat} (W : FiniteStageEmbedding n)
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj)
    (x : (K n).Obj) :
    ((restrictEndomapToStageContinuous W).toFun g).toFun x =
      projectToLevel n (g.toFun (W.embed x)) := by
  rfl

/-- The generic `h`-shadow produced by two consecutive exact finite-stage
embeddings. -/
noncomputable def finiteStageReifyContinuous
    {n : Nat} (W : FiniteStageEmbedding n)
    (WNext : FiniteStageEmbedding (n + 1)) :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO :=
  ContinuousMap.comp WNext.embed (restrictEndomapToStageContinuous W)

@[simp] theorem project_finiteStageReify
    {n : Nat} (W : FiniteStageEmbedding n)
    (WNext : FiniteStageEmbedding (n + 1))
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj) :
    projectToLevel (n + 1) (finiteStageReifyContinuous W WNext g) =
      restrictEndomapToStageContinuous W g := by
  simpa [finiteStageReifyContinuous] using
    WNext.exact ((restrictEndomapToStageContinuous W).toFun g)

/-- Exact coordinate formula for the generic finite-stage `h`-shadow. -/
theorem finiteStageReify_apply
    {n : Nat} (W : FiniteStageEmbedding n)
    (WNext : FiniteStageEmbedding (n + 1))
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj)
    (x : (K n).Obj) :
    ((projectToLevel (n + 1) (finiteStageReifyContinuous W WNext g)).toFun x) =
      projectToLevel n (g.toFun (W.embed x)) := by
  rw [project_finiteStageReify]
  exact restrictEndomapToStageContinuous_apply W g x

/-- The generic finite-stage `k`-shadow determined by an exact stage embedding. -/
noncomputable def finiteStageReflect
    {n : Nat} (W : FiniteStageEmbedding n)
    (x y : KInfinityCHPO.Obj) :
    KInfinityCHPO.Obj :=
  W.embed (((projectToLevel (n + 1) x).toFun (projectToLevel n y)))

/-- Exact coordinate formula for the generic finite-stage `k`-shadow. -/
theorem finiteStageReflect_exact
    {n : Nat} (W : FiniteStageEmbedding n)
    (x y : KInfinityCHPO.Obj) :
    projectToLevel n (finiteStageReflect W x y) =
      ((projectToLevel (n + 1) x).toFun (projectToLevel n y)) := by
  simpa [finiteStageReflect] using
    W.exact (((projectToLevel (n + 1) x).toFun (projectToLevel n y)))

/-- Jointly continuous binary form of the generic finite-stage `k`-shadow. -/
noncomputable def finiteStageReflectBinaryContinuous
    {n : Nat} (W : FiniteStageEmbedding n) :
    ContinuousMap (Product.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO :=
  ContinuousMap.comp W.embed <|
    ContinuousMap.comp (applicationContinuous (K n) (K n)) <|
      ContinuousMap.pair
        (ContinuousMap.comp (projectContinuous (n + 1))
          (fstContinuous KInfinityCHPO KInfinityCHPO))
        (ContinuousMap.comp (projectContinuous n)
          (sndContinuous KInfinityCHPO KInfinityCHPO))

@[simp] theorem finiteStageReflectBinaryContinuous_apply
    {n : Nat} (W : FiniteStageEmbedding n)
    (x y : KInfinityCHPO.Obj) :
    finiteStageReflectBinaryContinuous W (x, y) = finiteStageReflect W x y := by
  rfl

/-- Curried continuous form of the generic finite-stage `k`-shadow. -/
noncomputable def finiteStageReflectContinuous
    {n : Nat} (W : FiniteStageEmbedding n) :
    ContinuousMap KInfinityCHPO (Exponential.chpo KInfinityCHPO KInfinityCHPO) :=
  curry (finiteStageReflectBinaryContinuous W)

@[simp] theorem finiteStageReflectContinuous_apply
    {n : Nat} (W : FiniteStageEmbedding n)
    (x y : KInfinityCHPO.Obj) :
    ((finiteStageReflectContinuous W).toFun x).toFun y = finiteStageReflect W x y := by
  change finiteStageReflectBinaryContinuous W (x, y) = finiteStageReflect W x y
  rw [finiteStageReflectBinaryContinuous_apply]

/-- Restricting the generic finite-stage `k`-shadow back along the same stage
embedding recovers the next coordinate of the original thread exactly. -/
theorem restrictEndomapToStage_finiteStageReflectContinuous
    {n : Nat} (W : FiniteStageEmbedding n)
    (x : KInfinityCHPO.Obj) :
    restrictEndomapToStageContinuous W (finiteStageReflectContinuous W x) =
      projectToLevel (n + 1) x := by
  apply ContinuousMap.ext
  intro y
  change
    ((restrictEndomapToStageContinuous W).toFun
      ((finiteStageReflectContinuous W).toFun x)).toFun y =
        ((projectToLevel (n + 1) x).toFun y)
  rw [restrictEndomapToStageContinuous_apply, finiteStageReflectContinuous_apply,
    finiteStageReflect_exact]
  simpa using congrArg (fun z => (projectToLevel (n + 1) x).toFun z) (W.exact y)

/-- Generic finite-stage retract law: once we know exact embeddings of `Kₙ` and
`Kₙ₊₁` into `K∞`, the corresponding `h`- and `k`-shadows already recover the
entire `(n + 1)`-st coordinate of any inverse-limit thread. -/
theorem finiteStageRetract
    {n : Nat} (W : FiniteStageEmbedding n)
    (WNext : FiniteStageEmbedding (n + 1))
    (x : KInfinityCHPO.Obj) :
    projectToLevel (n + 1)
      (finiteStageReifyContinuous W WNext (finiteStageReflectContinuous W x)) =
        projectToLevel (n + 1) x := by
  rw [project_finiteStageReify, restrictEndomapToStage_finiteStageReflectContinuous]

/-- The uniform finite-stage `h`-shadow obtained from the exact embedding of
`Kₙ` and `Kₙ₊₁` into `K∞`. -/
noncomputable def hFiniteStageContinuous
    (n : Nat) :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO :=
  finiteStageReifyContinuous (genericStageEmbedding n) (genericStageEmbedding (n + 1))

/-- The uniform finite-stage `k`-shadow obtained from the exact embedding of
`Kₙ` into `K∞`. -/
noncomputable def kFiniteStageContinuous
    (n : Nat) :
    ContinuousMap KInfinityCHPO (Exponential.chpo KInfinityCHPO KInfinityCHPO) :=
  finiteStageReflectContinuous (genericStageEmbedding n)

/-- Uniform finite-stage retract law: for every `n`, the canonical stage-`n`
shadow pair already recovers the entire `(n + 1)`-st coordinate of an
inverse-limit thread exactly. -/
theorem hFiniteStage_kFiniteStage_exact
    (n : Nat) (x : KInfinityCHPO.Obj) :
    projectToLevel (n + 1) (hFiniteStageContinuous n (kFiniteStageContinuous n x)) =
      projectToLevel (n + 1) x := by
  exact finiteStageRetract (genericStageEmbedding n) (genericStageEmbedding (n + 1)) x

private theorem genericLevelCoords_succ_fPlus
    (n : Nat) (x : (K n).Obj) :
    ∀ m : Nat,
      genericLevelCoords (n + 1) ((fPlus n).toFun x) m =
        genericLevelCoords n x m
  | 0 => by
      rw [genericLevelCoords_below (n + 1) ((fPlus n).toFun x) (Nat.zero_le (n + 1))]
      rw [genericLevelCoords_below n x (Nat.zero_le n)]
      rw [projectDown_succ n ((fPlus n).toFun x) (m := 0) (Nat.zero_le n)]
      rw [fMinus_fPlus_apply]
  | m + 1 => by
      by_cases hm : m + 1 ≤ n
      · rw [genericLevelCoords_below (n + 1) ((fPlus n).toFun x) (by omega)]
        rw [genericLevelCoords_below n x hm]
        rw [projectDown_succ n ((fPlus n).toFun x) (m := m + 1) hm]
        rw [fMinus_fPlus_apply]
      · by_cases hEq : m = n
        · subst m
          rw [genericLevelCoords_self (n + 1) ((fPlus n).toFun x)]
          rw [genericLevelCoords_above n x (m := n) (by omega)]
          rw [genericLevelCoords_self n x]
        · have hm' : ¬ m + 1 ≤ n + 1 := by omega
          rw [genericLevelCoords_above (n + 1) ((fPlus n).toFun x) (m := m) hm']
          rw [genericLevelCoords_above n x (m := m) hm]
          rw [genericLevelCoords_succ_fPlus n x m]

/-- Successive exact finite-stage embeddings are coherent with the tower
embeddings `fₙ⁺`. -/
theorem embedFiniteStageToLimit_succ_fPlus_equiv
    (n : Nat) (x : (K n).Obj) :
    KInfinityCHPO.Rel
        (embedFiniteStageToLimit (n + 1) ((fPlus n).toFun x))
        (embedFiniteStageToLimit n x)
      ∧
      KInfinityCHPO.Rel
        (embedFiniteStageToLimit n x)
        (embedFiniteStageToLimit (n + 1) ((fPlus n).toFun x)) := by
  constructor <;>
    exact Projective.rel_mk (S := system) (fun m => by
      simpa [projectToLevel, embedFiniteStageToLimit, genericLevelCoords_succ_fPlus n x m] using
        (K m).rel_refl (genericLevelCoords n x m))

private theorem restrictEndomapToStage_succ_equiv
    (n : Nat)
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj) :
    (K (n + 1)).Rel
        ((fMinus (n + 1)).toFun
          ((restrictEndomapToStageContinuous (genericStageEmbedding (n + 1))).toFun g))
        ((restrictEndomapToStageContinuous (genericStageEmbedding n)).toFun g)
      ∧
      (K (n + 1)).Rel
        ((restrictEndomapToStageContinuous (genericStageEmbedding n)).toFun g)
        ((fMinus (n + 1)).toFun
          ((restrictEndomapToStageContinuous (genericStageEmbedding (n + 1))).toFun g)) := by
  constructor <;> refine Exponential.rel_mk ?_
  · intro x
    let y₁ :=
      g.toFun (embedFiniteStageToLimit (n + 1) ((fPlus n).toFun x))
    let y₀ :=
      g.toFun (embedFiniteStageToLimit n x)
    have hEmb :=
      embedFiniteStageToLimit_succ_fPlus_equiv n x
    have hy₁₀ : KInfinityCHPO.Rel y₁ y₀ := g.monotone' hEmb.1
    rw [fMinus_succ_apply]
    rw [restrictEndomapToStageContinuous_apply (genericStageEmbedding (n + 1)) g
      ((fPlus n).toFun x)]
    rw [restrictEndomapToStageContinuous_apply (genericStageEmbedding n) g x]
    change (K n).Rel ((fMinus n).toFun (projectToLevel (n + 1) y₁)) (projectToLevel n y₀)
    exact (K n).rel_trans (y₁.toPrev n) ((Projective.rel_iff.mp hy₁₀) n)
  · intro x
    let y₁ :=
      g.toFun (embedFiniteStageToLimit (n + 1) ((fPlus n).toFun x))
    let y₀ :=
      g.toFun (embedFiniteStageToLimit n x)
    have hEmb :=
      embedFiniteStageToLimit_succ_fPlus_equiv n x
    have hy₀₁ : KInfinityCHPO.Rel y₀ y₁ := g.monotone' hEmb.2
    rw [fMinus_succ_apply]
    rw [restrictEndomapToStageContinuous_apply (genericStageEmbedding (n + 1)) g
      ((fPlus n).toFun x)]
    rw [restrictEndomapToStageContinuous_apply (genericStageEmbedding n) g x]
    change (K n).Rel (projectToLevel n y₀) ((fMinus n).toFun (projectToLevel (n + 1) y₁))
    exact (K n).rel_trans ((Projective.rel_iff.mp hy₀₁) n) (y₁.fromPrev n)

/-- The coordinate maps of the global reification candidate `h : [K∞ → K∞] →
K∞`, built from the exact finite-stage restrictions of endomaps. -/
noncomputable def hInfinityCoordinate :
    (n : Nat) →
      ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) (K n)
  | 0 =>
      ContinuousMap.comp (fMinus 0)
        (restrictEndomapToStageContinuous (genericStageEmbedding 0))
  | n + 1 =>
      restrictEndomapToStageContinuous (genericStageEmbedding n)

/-- The global reification candidate obtained by threading together all
finite-stage restrictions of an endomap of `K∞`. -/
noncomputable def hInfinity
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj) :
    KInfinityCHPO.Obj where
  val := fun n => (hInfinityCoordinate n).toFun g
  toPrev := by
    intro n
    cases n with
    | zero =>
        exact (K 0).rel_refl _
    | succ n =>
        exact (restrictEndomapToStage_succ_equiv n g).1
  fromPrev := by
    intro n
    cases n with
    | zero =>
        exact (K 0).rel_refl _
    | succ n =>
        exact (restrictEndomapToStage_succ_equiv n g).2

/-- The global continuous reification map `h : [K∞ → K∞] → K∞` obtained from the
exact finite-stage restriction data. -/
noncomputable def hInfinityContinuous :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO where
  toFun := hInfinity
  monotone' := by
    intro g h hgh
    exact Projective.rel_mk (S := system) (fun n => by
      simpa [hInfinity, projectToLevel] using (hInfinityCoordinate n).monotone' hgh)
  preserves_sup := by
    intro X hX
    constructor
    · intro z hz
      rcases hz with ⟨g, hg, rfl⟩
      exact Projective.rel_mk (S := system) (fun n => by
        simpa [hInfinity, projectToLevel] using
          ((hInfinityCoordinate n).preserves_sup X hX).1 ⟨g, hg, rfl⟩)
    · intro w hw
      exact Projective.rel_mk (S := system) (fun n => by
        simpa [hInfinity, projectToLevel] using
          ((hInfinityCoordinate n).preserves_sup X hX).2 (by
            intro a ha
            rcases ha with ⟨g, hg, rfl⟩
            simpa [hInfinity, projectToLevel] using
              (Projective.rel_iff.mp (hw ⟨g, hg, rfl⟩)) n))

@[simp] theorem project_hInfinity_zero
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj) :
    projectToLevel 0 (hInfinity g) =
      (fMinus 0).toFun
        ((restrictEndomapToStageContinuous (genericStageEmbedding 0)).toFun g) :=
  rfl

@[simp] theorem project_hInfinity_succ
    (n : Nat)
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj) :
    projectToLevel (n + 1) (hInfinity g) =
      (restrictEndomapToStageContinuous (genericStageEmbedding n)).toFun g :=
  rfl

/-- Every finite stage `Kₙ` is antisymmetric in the induced h.p.o. relation. -/
theorem stage_antisymmetric :
    ∀ n : Nat, ∀ {x y : (K n).Obj}, (K n).Rel x y → (K n).Rel y x → x = y
  | 0, none, none, _, _ => rfl
  | 0, none, some y, _, hyx => by
      have : False := by
        simpa [K, NPlus, Flat.hpo_rel_iff] using hyx
      cases this
  | 0, some x, none, hxy, _ => by
      have : False := by
        simpa [K, NPlus, Flat.hpo_rel_iff] using hxy
      cases this
  | 0, some x, some y, hxy, _ => by
      have hEq : x = y := by
        simpa [K, NPlus, Flat.hpo_rel_iff, Flat.rel] using hxy
      exact congrArg some hEq
  | n + 1, x, y, hxy, hyx => by
      apply ContinuousMap.ext
      intro z
      exact stage_antisymmetric n
        ((Exponential.rel_iff.mp hxy) z)
        ((Exponential.rel_iff.mp hyx) z)

private theorem project_embedFiniteStage_prev
    (n : Nat) (x : (K (n + 1)).Obj) :
    projectToLevel n (embedFiniteStageToLimit (n + 1) x) = (fMinus n).toFun x := by
  change genericLevelCoords (n + 1) x n = (fMinus n).toFun x
  rw [genericLevelCoords_below (n + 1) x (by omega)]
  rw [projectDown_succ n x (m := n) (by omega)]
  simp [projectDown_self]

private theorem embedFiniteStageToLimit_succ_of_rel
    (n : Nat) {x : (K n).Obj} {y : (K (n + 1)).Obj}
    (hxy : (K n).Rel x ((fMinus n).toFun y)) :
    KInfinityCHPO.Rel (embedFiniteStageToLimit n x) (embedFiniteStageToLimit (n + 1) y) := by
  exact KInfinityCHPO.rel_trans
    (embedFiniteStageToLimit_monotone n hxy)
    (by
      simpa [proposition_4_2_stageApproximation, project_embedFiniteStage_prev] using
        (proposition_4_2_stageApproximation_below n (embedFiniteStageToLimit (n + 1) y)))

private theorem finiteStageReflect_step_input
    (n : Nat) (x y : KInfinityCHPO.Obj) :
    (K n).Rel
      (((projectToLevel (n + 1) x).toFun (projectToLevel n y)))
      ((fMinus n).toFun (((projectToLevel (n + 2) x).toFun (projectToLevel (n + 1) y)))) := by
  have hx :
      (K (n + 1)).Rel
        (projectToLevel (n + 1) x)
        ((fMinus (n + 1)).toFun (projectToLevel (n + 2) x)) :=
    x.fromPrev (n + 1)
  have hxEval :
      (K n).Rel
        (((projectToLevel (n + 1) x).toFun (projectToLevel n y)))
        (((fMinus (n + 1)).toFun (projectToLevel (n + 2) x)).toFun (projectToLevel n y)) :=
    (Exponential.rel_iff.mp hx) (projectToLevel n y)
  rw [fMinus_succ_apply] at hxEval
  have hyLift :
      (K (n + 1)).Rel
        ((fPlus n).toFun (projectToLevel n y))
        (projectToLevel (n + 1) y) := by
    exact (K (n + 1)).rel_trans
      ((fPlus n).monotone' (y.fromPrev n))
      (fPlus_fMinus_le n (projectToLevel (n + 1) y))
  have hMon :
      (K n).Rel
        ((fMinus n).toFun (((projectToLevel (n + 2) x).toFun
          ((fPlus n).toFun (projectToLevel n y)))))
        ((fMinus n).toFun (((projectToLevel (n + 2) x).toFun
          (projectToLevel (n + 1) y)))) := by
    exact (fMinus n).monotone' ((projectToLevel (n + 2) x).monotone' hyLift)
  exact (K n).rel_trans hxEval hMon

private theorem finiteStageReflectBinaryContinuous_step
    (n : Nat) :
    (Exponential.chpo (Product.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO).Rel
      (finiteStageReflectBinaryContinuous (genericStageEmbedding n))
      (finiteStageReflectBinaryContinuous (genericStageEmbedding (n + 1))) := by
  refine Exponential.rel_mk ?_
  intro xy
  rcases xy with ⟨x, y⟩
  change KInfinityCHPO.Rel
    (finiteStageReflect (genericStageEmbedding n) x y)
    (finiteStageReflect (genericStageEmbedding (n + 1)) x y)
  exact embedFiniteStageToLimit_succ_of_rel n (finiteStageReflect_step_input n x y)

/-- The generic finite-stage binary `k`-shadows form a monotone chain in the
function-space order. -/
theorem finiteStageReflectBinaryContinuous_mono
    {n m : Nat} (h : n ≤ m) :
    (Exponential.chpo (Product.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO).Rel
      (finiteStageReflectBinaryContinuous (genericStageEmbedding n))
      (finiteStageReflectBinaryContinuous (genericStageEmbedding m)) := by
  induction h with
  | refl =>
      exact (Exponential.chpo (Product.chpo KInfinityCHPO KInfinityCHPO)
        KInfinityCHPO).rel_refl _
  | @step m h ih =>
      exact (Exponential.chpo (Product.chpo KInfinityCHPO KInfinityCHPO)
        KInfinityCHPO).rel_trans ih (finiteStageReflectBinaryContinuous_step m)

private def kInfinityApproxPred :
    ContinuousMap (Product.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO → Prop :=
  fun f => ∃ n : Nat, f = finiteStageReflectBinaryContinuous (genericStageEmbedding n)

private theorem kInfinityApproxPred_directed :
    (Exponential.chpo (Product.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO).Directed
      kInfinityApproxPred := by
  constructor
  · exact ⟨finiteStageReflectBinaryContinuous (genericStageEmbedding 0), ⟨0, rfl⟩⟩
  · intro f g hf hg
    rcases hf with ⟨n, rfl⟩
    rcases hg with ⟨m, rfl⟩
    refine ⟨finiteStageReflectBinaryContinuous (genericStageEmbedding (max n m)),
      ⟨max n m, rfl⟩, ?_, ?_⟩
    · exact finiteStageReflectBinaryContinuous_mono (Nat.le_max_left n m)
    · exact finiteStageReflectBinaryContinuous_mono (Nat.le_max_right n m)

/-- The global binary reflection candidate `k : K∞ × K∞ → K∞`, defined as the
chosen supremum of the increasing chain of finite-stage application shadows. -/
noncomputable def kInfinityBinaryContinuous :
    ContinuousMap (Product.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO :=
  Exponential.directedSupMap kInfinityApproxPred kInfinityApproxPred_directed

/-- The curried global reflection candidate `k : K∞ → [K∞ → K∞]`. -/
noncomputable def kInfinityContinuous :
    ContinuousMap KInfinityCHPO (Exponential.chpo KInfinityCHPO KInfinityCHPO) :=
  curry kInfinityBinaryContinuous

private theorem project_embedFiniteStage_above
    {n m : Nat} (hnm : n ≤ m) (y : (K n).Obj) :
    projectToLevel (m + 1) (embedFiniteStageToLimit n y) =
      (fPlus m).toFun (projectToLevel m (embedFiniteStageToLimit n y)) := by
  change genericLevelCoords n y (m + 1) =
    (fPlus m).toFun (genericLevelCoords n y m)
  rw [genericLevelCoords_above n y (m := m) (by omega)]

private theorem finiteStageReflect_coord_exact
    (n : Nat) (x : KInfinityCHPO.Obj) (y : (K n).Obj) :
    projectToLevel n
      (finiteStageReflect (genericStageEmbedding n) x (embedFiniteStageToLimit n y)) =
        ((projectToLevel (n + 1) x).toFun y) := by
  rw [finiteStageReflect_exact]
  simpa using congrArg (fun z => (projectToLevel (n + 1) x).toFun z)
    (project_embedFiniteStage_exact n y)

private theorem finiteStageReflect_coord_le_target_of_le
    {m n : Nat} (hmn : m ≤ n)
    (x : KInfinityCHPO.Obj) (y : (K n).Obj) :
    (K n).Rel
      (projectToLevel n
        (finiteStageReflect (genericStageEmbedding m) x (embedFiniteStageToLimit n y)))
      ((projectToLevel (n + 1) x).toFun y) := by
  have hMono :
      KInfinityCHPO.Rel
        (finiteStageReflect (genericStageEmbedding m) x (embedFiniteStageToLimit n y))
        (finiteStageReflect (genericStageEmbedding n) x (embedFiniteStageToLimit n y)) :=
    (Exponential.rel_iff.mp (finiteStageReflectBinaryContinuous_mono hmn))
      (x, embedFiniteStageToLimit n y)
  exact (K n).rel_trans
    ((Projective.rel_iff.mp hMono) n)
    (by
      change (K n).Rel
        (projectToLevel n
          (finiteStageReflect (genericStageEmbedding n) x (embedFiniteStageToLimit n y)))
        ((projectToLevel (n + 1) x).toFun y)
      rw [finiteStageReflect_coord_exact n x y]
      exact (K n).rel_refl _)

private theorem finiteStageReflect_coord_le_prev
    {n m : Nat} (hnm : n ≤ m)
    (x : KInfinityCHPO.Obj) (y : (K n).Obj) :
    (K n).Rel
      (projectToLevel n
        (finiteStageReflect (genericStageEmbedding (m + 1)) x (embedFiniteStageToLimit n y)))
      (projectToLevel n
        (finiteStageReflect (genericStageEmbedding m) x (embedFiniteStageToLimit n y))) := by
  let argm : (K m).Obj := projectToLevel m (embedFiniteStageToLimit n y)
  let targetm : (K m).Obj := ((projectToLevel (m + 1) x).toFun argm)
  let targetSucc : (K (m + 1)).Obj :=
    ((projectToLevel (m + 2) x).toFun (projectToLevel (m + 1) (embedFiniteStageToLimit n y)))
  have hxPrev :
      (K m).Rel
        ((fMinus m).toFun targetSucc)
        targetm := by
    have hToPrev :
        (K (m + 1)).Rel
          ((fMinus (m + 1)).toFun (projectToLevel (m + 2) x))
          (projectToLevel (m + 1) x) :=
      x.toPrev (m + 1)
    have hEval :
        (K m).Rel
          (((fMinus (m + 1)).toFun (projectToLevel (m + 2) x)).toFun argm)
          (((projectToLevel (m + 1) x).toFun argm)) :=
      (Exponential.rel_iff.mp hToPrev) argm
    have hArg :
        projectToLevel (m + 1) (embedFiniteStageToLimit n y) =
          (fPlus m).toFun argm := by
      simpa [argm] using project_embedFiniteStage_above hnm y
    simpa [targetSucc, targetm, argm, hArg, fMinus_succ_apply] using hEval
  have hCoordSucc :
      projectToLevel n
        (finiteStageReflect (genericStageEmbedding (m + 1)) x
          (embedFiniteStageToLimit n y)) =
        projectDown m ((fMinus m).toFun targetSucc) n hnm := by
    change genericLevelCoords (m + 1) targetSucc n =
      projectDown m ((fMinus m).toFun targetSucc) n hnm
    rw [genericLevelCoords_below (m + 1) targetSucc (by omega)]
    rw [projectDown_succ m targetSucc (m := n) hnm]
  have hCoord :
      projectToLevel n
        (finiteStageReflect (genericStageEmbedding m) x
          (embedFiniteStageToLimit n y)) =
        projectDown m targetm n hnm := by
    change genericLevelCoords m targetm n = projectDown m targetm n hnm
    rw [genericLevelCoords_below m targetm hnm]
  rw [hCoordSucc, hCoord]
  exact projectDown_monotone m hxPrev (m := n) hnm

private theorem finiteStageReflect_coord_le_target_of_ge
    {n m : Nat} (hnm : n ≤ m)
    (x : KInfinityCHPO.Obj) (y : (K n).Obj) :
    (K n).Rel
      (projectToLevel n
        (finiteStageReflect (genericStageEmbedding m) x (embedFiniteStageToLimit n y)))
      ((projectToLevel (n + 1) x).toFun y) := by
  induction hnm with
  | refl =>
      rw [finiteStageReflect_coord_exact n x y]
      exact (K n).rel_refl _
  | @step m h ih =>
      exact (K n).rel_trans
        (finiteStageReflect_coord_le_prev h x y)
        ih

/-- Restricting the global reflection candidate back to any finite stage recovers
the exact next coordinate of the original inverse-limit thread. -/
theorem restrictEndomapToStage_kInfinityContinuous
    (n : Nat) (x : KInfinityCHPO.Obj) :
    restrictEndomapToStageContinuous (genericStageEmbedding n) (kInfinityContinuous x) =
      projectToLevel (n + 1) x := by
  apply ContinuousMap.ext
  intro y
  rw [restrictEndomapToStageContinuous_apply]
  change projectToLevel n (((kInfinityContinuous.toFun x).toFun (embedFiniteStageToLimit n y))) =
    ((projectToLevel (n + 1) x).toFun y)
  let xy : (Product.chpo KInfinityCHPO KInfinityCHPO).Obj :=
    (x, embedFiniteStageToLimit n y)
  have hChosen :=
    (projectContinuous n).preserves_sup
      (Exponential.evalPred kInfinityApproxPred xy)
      (Exponential.directed_eval kInfinityApproxPred_directed xy)
  have hUpper :
      (K n).IsUpperBound
        (image (fun z : KInfinityCHPO.Obj => projectToLevel n z)
          (Exponential.evalPred kInfinityApproxPred xy))
        ((projectToLevel (n + 1) x).toFun y) := by
    intro a ha
    rcases ha with ⟨z, hz, rfl⟩
    rcases hz with ⟨f, hf, hz⟩
    rcases hf with ⟨m, rfl⟩
    have hz' : finiteStageReflect (genericStageEmbedding m) x (embedFiniteStageToLimit n y) = z := by
      simpa [xy] using hz
    subst z
    by_cases hm : m ≤ n
    · exact finiteStageReflect_coord_le_target_of_le hm x y
    · exact finiteStageReflect_coord_le_target_of_ge (by omega) x y
  have hLower :
      (K n).Rel
        ((projectToLevel (n + 1) x).toFun y)
        (projectToLevel n (kInfinityBinaryContinuous xy)) := by
    refine hChosen.1 ?_
    refine ⟨finiteStageReflect (genericStageEmbedding n) x (embedFiniteStageToLimit n y), ?_, ?_⟩
    · refine ⟨finiteStageReflectBinaryContinuous (genericStageEmbedding n), ?_, ?_⟩
      · exact ⟨n, rfl⟩
      · simpa [xy] using
          (finiteStageReflectBinaryContinuous_apply (genericStageEmbedding n)
            x (embedFiniteStageToLimit n y))
    · exact finiteStageReflect_coord_exact n x y
  have hUpperChosen :
      (K n).Rel
        (projectToLevel n (kInfinityBinaryContinuous xy))
        ((projectToLevel (n + 1) x).toFun y) :=
    hChosen.2 hUpper
  have hEq :
      projectToLevel n (kInfinityBinaryContinuous xy) =
        ((projectToLevel (n + 1) x).toFun y) :=
    stage_antisymmetric n hUpperChosen hLower
  simpa [xy, kInfinityContinuous, curry, ContinuousMap.sliceRight_apply] using hEq

/-- Successor-coordinate retract law for the global `h`/`k` candidates. -/
theorem hInfinity_kInfinityContinuous_succ
    (n : Nat) (x : KInfinityCHPO.Obj) :
    projectToLevel (n + 1) (hInfinityContinuous (kInfinityContinuous x)) =
      projectToLevel (n + 1) x := by
  simpa [hInfinityContinuous] using
    (show projectToLevel (n + 1) (hInfinity (kInfinityContinuous x)) =
      projectToLevel (n + 1) x by
  rw [project_hInfinity_succ, restrictEndomapToStage_kInfinityContinuous]
    )

/-- Base-coordinate retract law for the global `h`/`k` candidates. -/
theorem hInfinity_kInfinityContinuous_zero
    (x : KInfinityCHPO.Obj) :
    projectToLevel 0 (hInfinityContinuous (kInfinityContinuous x)) =
      projectToLevel 0 x := by
  simpa [hInfinityContinuous] using
    (show projectToLevel 0 (hInfinity (kInfinityContinuous x)) =
      projectToLevel 0 x by
  rw [project_hInfinity_zero, restrictEndomapToStage_kInfinityContinuous]
  exact stage_antisymmetric 0 (x.toPrev 0) (x.fromPrev 0)
    )

/-- Pointwise retract law for the global `h`/`k` candidates. -/
theorem hInfinity_kInfinityContinuous_apply
    (x : KInfinityCHPO.Obj) :
    hInfinityContinuous (kInfinityContinuous x) = x := by
  apply Projective.Thread.ext
  intro n
  cases n with
  | zero =>
      exact hInfinity_kInfinityContinuous_zero x
  | succ n =>
      exact hInfinity_kInfinityContinuous_succ n x

/-- The global reflection candidate completes the actual `K∞` reflexivity
package. -/
noncomputable def kInfinityReflexiveCHPO : ReflexiveCHPO KInfinityCHPO where
  reify := hInfinityContinuous
  reflect := kInfinityContinuous
  retract := by
    ext x
    exact hInfinity_kInfinityContinuous_apply x

/-- Remark 4.3: the exact application induced by the completed global reflection
map `k : K∞ → [K∞ → K∞]`. -/
noncomputable def application
    (x y : KInfinityCHPO.Obj) :
    KInfinityCHPO.Obj :=
  ((kInfinityContinuous.toFun x).toFun y)

/-- The exact Remark 4.3 application is jointly continuous. -/
noncomputable def applicationContinuous :
    ContinuousMap (Product.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO :=
  ContinuousMap.comp
    (HigherLambdaModel.Domain.applicationContinuous KInfinityCHPO KInfinityCHPO) <|
      ContinuousMap.pair
        (ContinuousMap.comp kInfinityContinuous
          (fstContinuous KInfinityCHPO KInfinityCHPO))
        (sndContinuous KInfinityCHPO KInfinityCHPO)

@[simp] theorem applicationContinuous_apply
    (x y : KInfinityCHPO.Obj) :
    applicationContinuous (x, y) = application x y := by
  rfl

/-- Restricting the exact Remark 4.3 application along the canonical embedding
of a finite stage recovers the corresponding stage action of the reflected
endomap exactly. -/
theorem remark_4_3
    (n : Nat) (x : KInfinityCHPO.Obj) (y : (K n).Obj) :
    projectToLevel n (application x (embedFiniteStageToLimit n y)) =
      ((projectToLevel (n + 1) x).toFun y) := by
  have h :=
    congrArg
      (fun g : ContinuousMap (K n) (K n) => g.toFun y)
      (restrictEndomapToStage_kInfinityContinuous n x)
  simpa [application, genericStageEmbedding, embedFiniteStageContinuous,
    restrictEndomapToStageContinuous_apply] using h

/-- Chosen-data packaging of Proposition 4.3 and Remark 4.3: the exact global
`h`, `k`, and application operations together with the older finite-stage shadow
API and the exact coordinate formulas already proved for it. -/
structure Proposition43Witness where
  reifyShadow :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO
  reflectShadow :
    ContinuousMap KInfinityCHPO (Exponential.chpo KInfinityCHPO KInfinityCHPO)
  applicationShadow :
    ContinuousMap (Product.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO
  reifyShadow_exact1 :
    ∀ g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj,
      projectToLevel 1 (reifyShadow g) = restrictEndomapToBaseContinuous g
  reifyShadow_exact1_apply :
    ∀ (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj) (x : (K 0).Obj),
      ((projectToLevel 1 (reifyShadow g)).toFun x) =
        projectToLevel 0 (g.toFun (embedBaseToLimit x))
  reflectShadow_apply :
    ∀ x y : KInfinityCHPO.Obj,
      ((reflectShadow.toFun x).toFun y) = kBase x y
  reflectShadow_exact0 :
    ∀ x y : KInfinityCHPO.Obj,
      projectToLevel 0 ((reflectShadow.toFun x).toFun y) =
        ((projectToLevel 1 x).toFun (projectToLevel 0 y))
  retractShadow_stage1 :
    ∀ x : KInfinityCHPO.Obj,
      projectToLevel 1 (reifyShadow (reflectShadow x)) = projectToLevel 1 x
  reifyShadowLevelOne :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO
  reflectShadowLevelOne :
    ContinuousMap KInfinityCHPO (Exponential.chpo KInfinityCHPO KInfinityCHPO)
  reifyShadowLevelOne_exact2 :
    ∀ g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj,
      projectToLevel 2 (reifyShadowLevelOne g) = restrictEndomapToLevelOneContinuous g
  reifyShadowLevelOne_exact2_apply :
    ∀ (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj) (x : (K 1).Obj),
      ((projectToLevel 2 (reifyShadowLevelOne g)).toFun x) =
        projectToLevel 1 (g.toFun (embedLevelOneToLimit x))
  reflectShadowLevelOne_apply :
    ∀ x y : KInfinityCHPO.Obj,
      ((reflectShadowLevelOne.toFun x).toFun y) = kLevelOne x y
  reflectShadowLevelOne_exact1 :
    ∀ x y : KInfinityCHPO.Obj,
      projectToLevel 1 ((reflectShadowLevelOne.toFun x).toFun y) =
        ((projectToLevel 2 x).toFun (projectToLevel 1 y))
  retractShadow_stage2 :
    ∀ x : KInfinityCHPO.Obj,
      projectToLevel 2 (reifyShadowLevelOne (reflectShadowLevelOne x)) = projectToLevel 2 x
  reifyShadowLevelTwo :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO
  reflectShadowLevelTwo :
    ContinuousMap KInfinityCHPO (Exponential.chpo KInfinityCHPO KInfinityCHPO)
  reifyShadowLevelTwo_exact3 :
    ∀ g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj,
      projectToLevel 3 (reifyShadowLevelTwo g) = restrictEndomapToLevelTwoContinuous g
  reifyShadowLevelTwo_exact3_apply :
    ∀ (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj) (x : (K 2).Obj),
      ((projectToLevel 3 (reifyShadowLevelTwo g)).toFun x) =
        projectToLevel 2 (g.toFun (embedLevelTwoToLimit x))
  reflectShadowLevelTwo_apply :
    ∀ x y : KInfinityCHPO.Obj,
      ((reflectShadowLevelTwo.toFun x).toFun y) = kLevelTwo x y
  reflectShadowLevelTwo_exact2 :
    ∀ x y : KInfinityCHPO.Obj,
      projectToLevel 2 ((reflectShadowLevelTwo.toFun x).toFun y) =
        ((projectToLevel 3 x).toFun (projectToLevel 2 y))
  retractShadow_stage3 :
    ∀ x : KInfinityCHPO.Obj,
      projectToLevel 3 (reifyShadowLevelTwo (reflectShadowLevelTwo x)) = projectToLevel 3 x
  reifyShadowLevelThree :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO
  reflectShadowLevelThree :
    ContinuousMap KInfinityCHPO (Exponential.chpo KInfinityCHPO KInfinityCHPO)
  reifyShadowLevelThree_exact4 :
    ∀ g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj,
      projectToLevel 4 (reifyShadowLevelThree g) = restrictEndomapToLevelThreeContinuous g
  reifyShadowLevelThree_exact4_apply :
    ∀ (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj) (x : (K 3).Obj),
      ((projectToLevel 4 (reifyShadowLevelThree g)).toFun x) =
        projectToLevel 3 (g.toFun (embedLevelThreeToLimit x))
  reflectShadowLevelThree_apply :
    ∀ x y : KInfinityCHPO.Obj,
      ((reflectShadowLevelThree.toFun x).toFun y) = kLevelThree x y
  reflectShadowLevelThree_exact3 :
    ∀ x y : KInfinityCHPO.Obj,
      projectToLevel 3 ((reflectShadowLevelThree.toFun x).toFun y) =
        ((projectToLevel 4 x).toFun (projectToLevel 3 y))
  retractShadow_stage4 :
    ∀ x : KInfinityCHPO.Obj,
      projectToLevel 4 (reifyShadowLevelThree (reflectShadowLevelThree x)) = projectToLevel 4 x
  genericStageEmbedding :
    ∀ n : Nat, FiniteStageEmbedding n
  globalReify :
    ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO
  globalReify_exact0 :
    ∀ g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj,
      projectToLevel 0 (globalReify g) =
        (fMinus 0).toFun
          ((restrictEndomapToStageContinuous (genericStageEmbedding 0)).toFun g)
  globalReify_exactSucc :
    ∀ (n : Nat) (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj),
      projectToLevel (n + 1) (globalReify g) =
        (restrictEndomapToStageContinuous (genericStageEmbedding n)).toFun g
  globalReflect :
    ContinuousMap KInfinityCHPO (Exponential.chpo KInfinityCHPO KInfinityCHPO)
  globalReflect_restrict :
    ∀ (n : Nat) (x : KInfinityCHPO.Obj),
      restrictEndomapToStageContinuous (genericStageEmbedding n) (globalReflect x) =
        projectToLevel (n + 1) x
  globalApplication :
    ContinuousMap (Product.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO
  globalApplication_apply :
    ∀ x y : KInfinityCHPO.Obj, globalApplication (x, y) = application x y
  globalApplication_restrict :
    ∀ (n : Nat) (x : KInfinityCHPO.Obj) (y : (K n).Obj),
      projectToLevel n (globalApplication (x, embedFiniteStageToLimit n y)) =
        ((projectToLevel (n + 1) x).toFun y)
  globalRetract :
    ContinuousMap.comp globalReify globalReflect = ContinuousMap.id KInfinityCHPO
  genericReifyShadow :
    Nat → ContinuousMap (Exponential.chpo KInfinityCHPO KInfinityCHPO) KInfinityCHPO
  genericReflectShadow :
    Nat → ContinuousMap KInfinityCHPO (Exponential.chpo KInfinityCHPO KInfinityCHPO)
  genericRetractShadow :
    ∀ (n : Nat) (x : KInfinityCHPO.Obj),
      projectToLevel (n + 1) (genericReifyShadow n (genericReflectShadow n x)) =
        projectToLevel (n + 1) x
  applicationShadow_apply :
    ∀ x y : KInfinityCHPO.Obj, applicationShadow (x, y) = baseApplicationShadow x y

/-- Proposition 4.3 and Remark 4.3 in the repository's chosen-data style. The
exact global maps `h`, `k`, and application are packaged alongside the older
finite-stage shadow API. -/
noncomputable def proposition_4_3_shadow : Proposition43Witness where
  reifyShadow := hBaseContinuous
  reflectShadow := kBaseContinuous
  applicationShadow := applicationContinuousShadow
  reifyShadow_exact1 := project_hBaseContinuous_one
  reifyShadow_exact1_apply := proposition_4_3_hBase
  reflectShadow_apply := kBaseContinuous_apply
  reflectShadow_exact0 := by
    intro x y
    rw [kBaseContinuous_apply]
    exact proposition_4_3 x y
  retractShadow_stage1 := hBase_kBaseContinuous_stage1
  reifyShadowLevelOne := hLevelOneContinuous
  reflectShadowLevelOne := kLevelOneContinuous
  reifyShadowLevelOne_exact2 := project_hLevelOne_two
  reifyShadowLevelOne_exact2_apply := proposition_4_3_hLevelOne
  reflectShadowLevelOne_apply := kLevelOneContinuous_apply
  reflectShadowLevelOne_exact1 := by
    intro x y
    rw [kLevelOneContinuous_apply]
    exact proposition_4_3_levelOne x y
  retractShadow_stage2 := hLevelOne_kLevelOneContinuous_stage2
  reifyShadowLevelTwo := hLevelTwoContinuous
  reflectShadowLevelTwo := kLevelTwoContinuous
  reifyShadowLevelTwo_exact3 := project_hLevelTwo_three
  reifyShadowLevelTwo_exact3_apply := proposition_4_3_hLevelTwo
  reflectShadowLevelTwo_apply := kLevelTwoContinuous_apply
  reflectShadowLevelTwo_exact2 := by
    intro x y
    rw [kLevelTwoContinuous_apply]
    exact proposition_4_3_levelTwo x y
  retractShadow_stage3 := hLevelTwo_kLevelTwoContinuous_stage3
  reifyShadowLevelThree := hLevelThreeContinuous
  reflectShadowLevelThree := kLevelThreeContinuous
  reifyShadowLevelThree_exact4 := project_hLevelThree_four
  reifyShadowLevelThree_exact4_apply := proposition_4_3_hLevelThree
  reflectShadowLevelThree_apply := kLevelThreeContinuous_apply
  reflectShadowLevelThree_exact3 := by
    intro x y
    rw [kLevelThreeContinuous_apply]
    exact proposition_4_3_levelThree x y
  retractShadow_stage4 := hLevelThree_kLevelThreeContinuous_stage4
  genericStageEmbedding := genericStageEmbedding
  globalReify := hInfinityContinuous
  globalReify_exact0 := project_hInfinity_zero
  globalReify_exactSucc := project_hInfinity_succ
  globalReflect := kInfinityContinuous
  globalReflect_restrict := restrictEndomapToStage_kInfinityContinuous
  globalApplication := applicationContinuous
  globalApplication_apply := applicationContinuous_apply
  globalApplication_restrict := remark_4_3
  globalRetract := by
    ext x
    exact hInfinity_kInfinityContinuous_apply x
  genericReifyShadow := hFiniteStageContinuous
  genericReflectShadow := kFiniteStageContinuous
  genericRetractShadow := hFiniteStage_kFiniteStage_exact
  applicationShadow_apply := applicationContinuousShadow_apply

/-! ## Generic Coherence Instance -/

/-- The canonical weak omega-groupoid on the concrete carrier of `K∞`, with
all higher cells above dimension `1` given by iterated identity types. This
lets the concrete model inherit the generic coherence theorem stack without
adding any `K∞`-specific higher-conversion axioms. -/
def kInfinityOmegaGroupoid : HigherLambdaModel.Simplicial.OmegaGroupoid :=
  HigherLambdaModel.Simplicial.equalityOmegaGroupoid KInfinityCHPO.Obj

private abbrev KInfinityReflexiveTower :=
  kInfinityOmegaGroupoid.toReflexiveGlobularTower

/-- The all-dimensional conversion tower on `K∞`, expressed through the packed
low-dimensional cells of its canonical identity-type omega-groupoid. -/
def kInfinityTower : HigherLambdaModel.Simplicial.GlobularTower :=
  HigherLambdaModel.Lambda.Coherence.omegaGroupoidTower kInfinityOmegaGroupoid

private def kInfinityCell0Equiv :
    HigherLambdaModel.Lambda.Coherence.SortEquiv
      (kInfinityTower.Cell 0)
      (HigherLambdaModel.Lambda.Coherence.Tower0 KInfinityReflexiveTower) where
  toFun := fun x => x.down
  invFun := fun x => ⟨x⟩
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro x
    rfl

private def kInfinityCell1Equiv :
    HigherLambdaModel.Lambda.Coherence.SortEquiv
      (kInfinityTower.Cell 1)
      (HigherLambdaModel.Lambda.Coherence.Tower1 KInfinityReflexiveTower) where
  toFun := fun ⟨M, N, p⟩ => ⟨M.down, N.down, p.down⟩
  invFun := fun ⟨M, N, p⟩ => ⟨⟨M⟩, ⟨N⟩, ⟨p⟩⟩
  left_inv := by
    intro x
    cases x with
    | mk M rest =>
        cases rest with
        | mk N p =>
            cases M
            cases N
            cases p
            rfl
  right_inv := by
    intro x
    cases x
    rfl

private def kInfinityCell2Equiv :
    HigherLambdaModel.Lambda.Coherence.SortEquiv
      (kInfinityTower.Cell 2)
      (HigherLambdaModel.Lambda.Coherence.Tower2 KInfinityReflexiveTower) where
  toFun := fun ⟨M, N, p, q, α⟩ => ⟨M.down, N.down, p.down, q.down, α.down⟩
  invFun := fun ⟨M, N, p, q, α⟩ => ⟨⟨M⟩, ⟨N⟩, ⟨p⟩, ⟨q⟩, ⟨α⟩⟩
  left_inv := by
    intro x
    cases x with
    | mk M rest =>
        cases rest with
        | mk N rest =>
            cases rest with
            | mk p rest =>
                cases rest with
                | mk q α =>
                    cases M
                    cases N
                    cases p
                    cases q
                    cases α
                    rfl
  right_inv := by
    intro x
    cases x
    rfl

private def kInfinityCell3Equiv :
    HigherLambdaModel.Lambda.Coherence.SortEquiv
      (kInfinityTower.Cell 3)
      (HigherLambdaModel.Lambda.Coherence.Tower3 KInfinityReflexiveTower) where
  toFun := fun ⟨M, N, p, q, α, β, η⟩ =>
    ⟨M.down, N.down, p.down, q.down, α.down, β.down, η.down⟩
  invFun := fun ⟨M, N, p, q, α, β, η⟩ =>
    ⟨⟨M⟩, ⟨N⟩, ⟨p⟩, ⟨q⟩, ⟨α⟩, ⟨β⟩, ⟨η⟩⟩
  left_inv := by
    intro x
    cases x with
    | mk M rest =>
        cases rest with
        | mk N rest =>
            cases rest with
            | mk p rest =>
                cases rest with
                | mk q rest =>
                    cases rest with
                    | mk α rest =>
                        cases rest with
                        | mk β η =>
                            cases M
                            cases N
                            cases p
                            cases q
                            cases α
                            cases β
                            cases η
                            rfl
  right_inv := by
    intro x
    cases x
    rfl

private def kInfinityRealize4 :
    HigherLambdaModel.Lambda.Coherence.Tower4 KInfinityReflexiveTower →
      kInfinityTower.Cell 4
  | ⟨M, N, p, q, α, β, η, θ, ω⟩ =>
      ⟨⟨M⟩, ⟨N⟩, ⟨p⟩, ⟨q⟩, ⟨α⟩, ⟨β⟩, ⟨η⟩, ⟨θ⟩, ⟨ω⟩⟩

private def kInfinityRealize5 :
    HigherLambdaModel.Lambda.Coherence.Tower5 KInfinityReflexiveTower →
      kInfinityTower.Cell 5
  | ⟨M, N, p, q, α, β, η, θ, ω, ξ, μ⟩ =>
      ⟨⟨M⟩, ⟨N⟩, ⟨p⟩, ⟨q⟩, ⟨α⟩, ⟨β⟩, ⟨η⟩, ⟨θ⟩, ⟨ω⟩, ⟨ξ⟩, ⟨μ⟩⟩

/-- The concrete `K∞` model satisfies the generic admissibility hypotheses. -/
def kInfinityAdmissibleHigherLambdaModel :
    HigherLambdaModel.Lambda.Coherence.AdmissibleHigherLambdaModel where
  tower := kInfinityTower
  omegaGroupoid := kInfinityOmegaGroupoid
  cell0Equiv := kInfinityCell0Equiv
  cell1Equiv := kInfinityCell1Equiv
  cell2Equiv := kInfinityCell2Equiv
  cell3Equiv := kInfinityCell3Equiv
  realize4 := kInfinityRealize4
  realize5 := kInfinityRealize5

/-- The generic coherence theorem specialized to the concrete `K∞` model. -/
def kInfinityHigherConversionCoherence :
    HigherLambdaModel.Lambda.Coherence.HigherConversionCoherence
      kInfinityAdmissibleHigherLambdaModel :=
  HigherLambdaModel.Lambda.Coherence.higherConversionCoherenceData
    kInfinityAdmissibleHigherLambdaModel

/-- `K∞` inherits the full generic omega-groupoid coherence package. -/
theorem kInfinity_higher_conversions_form_omegaGroupoid :
    Nonempty
      (HigherLambdaModel.Lambda.Coherence.HigherConversionCoherence
        kInfinityAdmissibleHigherLambdaModel) :=
  HigherLambdaModel.Lambda.Coherence.higherConversions_form_omegaGroupoid
    kInfinityAdmissibleHigherLambdaModel

/-- The reflexive tower recovered from the generic coherence theorem for `K∞`.
-/
abbrev reflexiveKInfinityTower :
    HigherLambdaModel.Simplicial.ReflexiveGlobularTower :=
  HigherLambdaModel.Lambda.Coherence.realizedTower
    kInfinityAdmissibleHigherLambdaModel

/-- The `K∞` tower packaged above is definitionally the realized tower of its
specialized coherence theorem. -/
theorem kInfinityHigherConversionCoherence_realizedTower :
    HigherLambdaModel.Lambda.Coherence.realizedTower
      kInfinityAdmissibleHigherLambdaModel = reflexiveKInfinityTower :=
  rfl

/-- Paths in the canonical `K∞` omega-groupoid. -/
abbrev KInfinityPath (A B : KInfinityCHPO.Obj) : Type :=
  kInfinityOmegaGroupoid.Hom A B

/-- Two-cells between parallel `K∞` paths. -/
abbrev KInfinityPath2
    {A B : KInfinityCHPO.Obj} (p q : KInfinityPath A B) : Type :=
  kInfinityOmegaGroupoid.Hom2 p q

/-- Three-cells between parallel `K∞` 2-cells. -/
abbrev KInfinityPath3
    {A B : KInfinityCHPO.Obj} {p q : KInfinityPath A B}
    (α β : KInfinityPath2 p q) : Type :=
  kInfinityOmegaGroupoid.Hom3 α β

/-- Four-cells between parallel `K∞` 3-cells. -/
abbrev KInfinityPath4
    {A B : KInfinityCHPO.Obj} {p q : KInfinityPath A B}
    {α β : KInfinityPath2 p q} (η θ : KInfinityPath3 α β) : Type :=
  kInfinityOmegaGroupoid.Hom4 η θ

/-- Five-cells between parallel `K∞` 4-cells. -/
abbrev KInfinityPath5
    {A B : KInfinityCHPO.Obj} {p q : KInfinityPath A B}
    {α β : KInfinityPath2 p q} {η θ : KInfinityPath3 α β}
    (ω ξ : KInfinityPath4 η θ) : Type :=
  kInfinityOmegaGroupoid.Hom5 ω ξ

/-- Lift an ordinary equality of `K∞` points to a 1-cell in the canonical
omega-groupoid. -/
def kInfinityPathOfEq {A B : KInfinityCHPO.Obj} (h : A = B) : KInfinityPath A B :=
  ⟨h⟩

/-- Lift an equality of parallel `K∞` paths to a 2-cell in the canonical
omega-groupoid. -/
def kInfinityPath2OfEq
    {A B : KInfinityCHPO.Obj} {p q : KInfinityPath A B}
    (h : p = q) : KInfinityPath2 p q :=
  ⟨h⟩

/-- The generic pentagon 4-cell specialized to the `K∞` omega-groupoid. -/
def kInfinityPentagon4
    {A B C D E : KInfinityCHPO.Obj}
    (p : KInfinityPath A B) (q : KInfinityPath B C)
    (r : KInfinityPath C D) (s : KInfinityPath D E) :=
  HigherLambdaModel.Simplicial.OmegaGroupoid.pentagon4
    kInfinityOmegaGroupoid p q r s

/-- The generic pentagon 5-cell specialized to the `K∞` omega-groupoid. -/
def kInfinityPentagon5
    {A B C D E : KInfinityCHPO.Obj}
    (p : KInfinityPath A B) (q : KInfinityPath B C)
    (r : KInfinityPath C D) (s : KInfinityPath D E) :=
  HigherLambdaModel.Simplicial.OmegaGroupoid.pentagon5
    kInfinityOmegaGroupoid p q r s

/-- The generic interchange 4-cell specialized to the `K∞` omega-groupoid. -/
def kInfinityHexagon4
    {A B C : KInfinityCHPO.Obj}
    {p p' : KInfinityPath A B} {q q' : KInfinityPath B C}
    (α : KInfinityPath2 p p') (β : KInfinityPath2 q q') :=
  HigherLambdaModel.Simplicial.OmegaGroupoid.hexagon4
    kInfinityOmegaGroupoid α β

/-- The generic interchange 5-cell specialized to the `K∞` omega-groupoid. -/
def kInfinityHexagon5
    {A B C : KInfinityCHPO.Obj}
    {p p' : KInfinityPath A B} {q q' : KInfinityPath B C}
    (α : KInfinityPath2 p p') (β : KInfinityPath2 q q') :=
  HigherLambdaModel.Simplicial.OmegaGroupoid.hexagon5
    kInfinityOmegaGroupoid α β

/-! ## Proposition 4.4 -/

/-- The chosen homotopy-group presentation of `K∞`, obtained by reading the
non-trivial homotopy information from the base coordinate `K₀ = N⁺`. -/
noncomputable def KInfinityKanComplex : HomotopyGroupKanComplex where
  carrier := constantKanComplex KInfinityCHPO.Obj
  pi0 := Nat
  pi := fun n x =>
    match projectToLevel 0 x with
    | some a => sphereHomotopyGroup n a
    | none => PUnit
  component := fun x =>
    match projectToLevel 0 x with
    | some a => a.dim
    | none => 0
  hornVertex := fun x => ∃ a : SpherePoint, projectToLevel 0 x = some a

private theorem kInfinitySphereGroup_nontrivial_at_dim (a : SpherePoint) :
    TypeNontrivial (sphereHomotopyGroup a.dim.succ a) := by
  simpa [sphereHomotopyGroup] using bool_typeNontrivial

/-- Proposition 4.4: the chosen-data `K∞` model is non-trivial. -/
theorem proposition_4_4 : IsNonTrivialKanComplex KInfinityKanComplex := by
  refine ⟨nat_typeInfinite, ?_, ?_⟩
  · intro n hn
    let x : KInfinityCHPO.Obj := embedBaseToLimit (some ⟨n - 1, false⟩)
    refine ⟨x, ?_⟩
    have hpos : 0 < n := by omega
    have hpred : (n - 1).succ = n := Nat.succ_pred_eq_of_pos hpos
    have hEq : n = (n - 1).succ := hpred.symm
    have hpred' : (((n - 1).succ - 1).succ) = (n - 1).succ := by
      exact Nat.succ_pred_eq_of_pos (Nat.succ_pos (n - 1))
    have hx0 : projectToLevel 0 x = some ⟨n - 1, false⟩ := by
      simp [x]
    have hGroup : TypeNontrivial (sphereHomotopyGroup n ⟨n - 1, false⟩) := by
      rw [sphereHomotopyGroup, hEq, hpred']
      simpa using bool_typeNontrivial
    simpa [KInfinityKanComplex, piN, hx0] using hGroup
  · intro x hx
    rcases hx with ⟨a, ha⟩
    refine ⟨a.dim.succ, by omega, ?_⟩
    simpa [KInfinityKanComplex, piN, ha] using kInfinitySphereGroup_nontrivial_at_dim a

/-- Proposition 4.4 packaged as an actual non-trivial homotopy lambda model:
the concrete `K∞` Kan-complex witness together with the newly completed
reflexive c.h.p.o. structure. -/
noncomputable def proposition_4_4_model : NonTrivialHomotopyLambdaModel where
  kan := KInfinityKanComplex
  chpo := KInfinityCHPO
  nontrivial := proposition_4_4
  reflexive := kInfinityReflexiveCHPO

/-! ## Example 4.2 -/

/-- The two distinguished `S¹`-vertices used in the β/η example. -/
def s1Left : SpherePoint := ⟨1, false⟩
def s1Right : SpherePoint := ⟨1, true⟩

/-- The chosen interpretation of the η-side point in Example 4.2. -/
noncomputable def interp1Eta : KInfinityCHPO.Obj :=
  embedBaseToLimit (some s1Left)

/-- The chosen interpretation of the β-side point in Example 4.2. -/
noncomputable def interp1Beta : KInfinityCHPO.Obj :=
  embedBaseToLimit (some s1Right)

@[simp] theorem interp1Eta_level0 :
    projectToLevel 0 interp1Eta = some s1Left := by
  simp [interp1Eta]

@[simp] theorem interp1Beta_level0 :
    projectToLevel 0 interp1Beta = some s1Right := by
  simp [interp1Beta]

/-- Example 4.2: the chosen β/η interpretations are distinct in `K∞`. -/
theorem example_4_2 : interp1Beta ≠ interp1Eta := by
  intro h
  have h0 := congrArg (projectToLevel 0) h
  have hPoint : s1Right = s1Left := by
    injection h0 with hPoint
  have hPole : true = false := by
    simpa [s1Left, s1Right] using congrArg SpherePoint.pole hPoint
  cases hPole

/-- In the canonical `K∞` omega-groupoid, the chosen β-side and η-side points
admit no 1-cell. -/
theorem example_4_2_no_path :
    KInfinityPath interp1Beta interp1Eta → False := by
  intro p
  exact example_4_2 p.down

/-- Equivalently, the chosen β-side and η-side points are disconnected at the
0-truncation level of the canonical `K∞` omega-groupoid. -/
theorem example_4_2_not_connected :
    ¬ Nonempty (KInfinityPath interp1Beta interp1Eta) := by
  intro h
  rcases h with ⟨p⟩
  exact example_4_2_no_path p

/-- Since the chosen β-side and η-side points admit no 1-cell in the canonical
`K∞` omega-groupoid, they admit no parallel 2-cell either. -/
theorem example_4_2_no_path2
    {p q : KInfinityPath interp1Beta interp1Eta} :
    KInfinityPath2 p q → False := by
  intro α
  exact example_4_2_no_path p

/-- The chosen β-side and η-side points admit no parallel 3-cell in the
canonical `K∞` omega-groupoid either. -/
theorem example_4_2_no_path3
    {p q : KInfinityPath interp1Beta interp1Eta}
    {α β : KInfinityPath2 p q} :
    KInfinityPath3 α β → False := by
  intro η
  exact example_4_2_no_path2 α

/-- The chosen β-side and η-side points admit no parallel 4-cell in the
canonical `K∞` omega-groupoid. -/
theorem example_4_2_no_path4
    {p q : KInfinityPath interp1Beta interp1Eta}
    {α β : KInfinityPath2 p q} {η θ : KInfinityPath3 α β} :
    KInfinityPath4 η θ → False := by
  intro ω
  exact example_4_2_no_path3 η

/-- The chosen β-side and η-side points admit no parallel 5-cell in the
canonical `K∞` omega-groupoid. -/
theorem example_4_2_no_path5
    {p q : KInfinityPath interp1Beta interp1Eta}
    {α β : KInfinityPath2 p q} {η θ : KInfinityPath3 α β}
    {ω ξ : KInfinityPath4 η θ} :
    KInfinityPath5 ω ξ → False := by
  intro μ
  exact example_4_2_no_path4 ω

end HigherLambdaModel.KInfinity
