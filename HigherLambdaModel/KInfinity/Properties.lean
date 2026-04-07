import HigherLambdaModel.KInfinity.Construction
import HigherLambdaModel.Lambda.Coherence
import HigherLambdaModel.Simplicial.OmegaGroupoid

/-!
# Properties of the `K∞` Tower

This file packages the remaining Section 4 results in the chosen-data style
used throughout the repository.

The generic Section 3 layer already provides the full c.h.p.o. and continuous
map infrastructure needed for the `Kₙ` tower. The library still does not offer
a completely generic inverse-limit Scott-domain theorem for arbitrary towers,
but this file now proves Proposition 4.1 directly for the concrete `K∞`
construction and records the resulting domain-theoretic witness data alongside
the remaining Section 4 results.

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

/-- The canonical stage-by-stage image of a base point remains compact at every
finite level of the Section 4 tower. -/
theorem baseUp_compact (x : (K 0).Obj) :
    ∀ n : Nat, IsCompact (K n) (baseUp x n)
  | 0 => by
      simpa [K] using (Flat.isCompact (α := SpherePoint) x)
  | n + 1 => by
      simpa [baseUp_succ] using fPlus_compact n (baseUp_compact x n)

/-- Compact stage points generate compact step functions in the next stage of
the `K∞` tower. This gives a uniform concrete family of compact endomaps above
every finite level. -/
theorem stage_stepFunction_compact (n : Nat) {a b : (K n).Obj}
    (ha : IsCompact (K n) a) (hb : IsCompact (K n) b) :
    IsCompact (K (n + 1)) (stepFunction a ha b) := by
  simpa [K] using
    (stepFunction_compact (K := K n) (L := K n) a ha b hb)

/-- A chosen compact step-approximation datum for a target endomap of the
stage-`n` domain. This is the stage-specialized form of the generic
`StepApproxDatum` interface from the Scott-domain layer. -/
abbrev StageStepApproxDatum (n : Nat) (f : (K (n + 1)).Obj) :=
  StepApproxDatum (K := K n) (L := K n) f

/-- Any finite family of chosen compact step approximants below a stage-`n + 1`
endomap admits a chosen compact-below least upper bound at that same stage. -/
theorem exists_listStageStepApproxDatum_compactBelow_isLeastUpperBound
    (n : Nat) (f : (K (n + 1)).Obj)
    (steps : List (StageStepApproxDatum n f)) :
    ∃ h : (K (n + 1)).Obj,
      compactBelow (K (n + 1)) f h ∧
      (K (n + 1)).IsLeastUpperBound
        (fun g => g ∈ steps.map StepApproxDatum.toMap) h := by
  simpa [K] using
    (exists_listStepApproxDatum_compactBelow_isLeastUpperBound
      (K := K n)
      (L := K n)
      (hL := stage_boundedComplete n)
      f
      steps)

/-- A chosen stage-`n + 1` finite-step approximant assembled from a finite list
of compact step data below a target endomap. -/
noncomputable def assembleStageStepApproximants
    (n : Nat) (f : (K (n + 1)).Obj)
    (steps : List (StageStepApproxDatum n f)) :
    (K (n + 1)).Obj :=
  assembleStepApproximants (K := K n) (L := K n) (stage_boundedComplete n) f steps

/-- The chosen assembled stage approximant remains compact-below the target
endomap. -/
theorem assembleStageStepApproximants_compactBelow
    (n : Nat) (f : (K (n + 1)).Obj)
    (steps : List (StageStepApproxDatum n f)) :
    compactBelow (K (n + 1)) f (assembleStageStepApproximants n f steps) := by
  simpa [assembleStageStepApproximants, K] using
    (assembleStepApproximants_compactBelow
      (K := K n)
      (L := K n)
      (hL := stage_boundedComplete n)
      f
      steps)

/-- The chosen assembled stage approximant is the least upper bound of the
finite family of step maps from which it is built. -/
theorem assembleStageStepApproximants_isLeastUpperBound
    (n : Nat) (f : (K (n + 1)).Obj)
    (steps : List (StageStepApproxDatum n f)) :
    (K (n + 1)).IsLeastUpperBound
      (fun g => g ∈ steps.map StepApproxDatum.toMap)
      (assembleStageStepApproximants n f steps) := by
  simpa [assembleStageStepApproximants, K] using
    (assembleStepApproximants_isLeastUpperBound
      (K := K n)
      (L := K n)
      (hL := stage_boundedComplete n)
      f
      steps)

/-- Enlarging the finite list of stage-step data enlarges the chosen assembled
stage approximant. -/
theorem assembleStageStepApproximants_mono
    (n : Nat) (f : (K (n + 1)).Obj)
    {steps₁ steps₂ : List (StageStepApproxDatum n f)}
    (hsubset : ∀ d : StageStepApproxDatum n f, d ∈ steps₁ → d ∈ steps₂) :
    (K (n + 1)).Rel
      (assembleStageStepApproximants n f steps₁)
      (assembleStageStepApproximants n f steps₂) := by
  simpa [assembleStageStepApproximants, K] using
    (assembleStepApproximants_mono
      (K := K n)
      (L := K n)
      (hL := stage_boundedComplete n)
      (f := f)
      (steps₁ := steps₁)
      (steps₂ := steps₂)
      hsubset)

/-- The assembled stage approximant for a list is below the one assembled from
any append-extension of that list on the right. -/
theorem assembleStageStepApproximants_le_append_right
    (n : Nat) (f : (K (n + 1)).Obj)
    (steps₁ steps₂ : List (StageStepApproxDatum n f)) :
    (K (n + 1)).Rel
      (assembleStageStepApproximants n f steps₁)
      (assembleStageStepApproximants n f (steps₁ ++ steps₂)) := by
  refine assembleStageStepApproximants_mono n f ?_
  intro d hd
  exact List.mem_append.mpr (Or.inl hd)

/-- The assembled stage approximant for a list is below the one assembled from
any append-extension of that list on the left. -/
theorem assembleStageStepApproximants_le_append_left
    (n : Nat) (f : (K (n + 1)).Obj)
    (steps₁ steps₂ : List (StageStepApproxDatum n f)) :
    (K (n + 1)).Rel
      (assembleStageStepApproximants n f steps₂)
      (assembleStageStepApproximants n f (steps₁ ++ steps₂)) := by
  refine assembleStageStepApproximants_mono n f ?_
  intro d hd
  exact List.mem_append.mpr (Or.inr hd)

/-- The predicate of finite stage-step approximants assembled from finite lists
of compact step data below a fixed target endomap. -/
private def stageFiniteStepApproxPred
    (n : Nat) (f : (K (n + 1)).Obj) :
    (K (n + 1)).Obj → Prop :=
  fun g => ∃ steps : List (StageStepApproxDatum n f),
    g = assembleStageStepApproximants n f steps

/-- Every assembled finite stage-step approximant lies compact-below the target
endomap from which it is built. -/
private theorem stageFiniteStepApproxPred_compactBelow
    (n : Nat) (f : (K (n + 1)).Obj)
    {g : (K (n + 1)).Obj}
    (hg : stageFiniteStepApproxPred n f g) :
    compactBelow (K (n + 1)) f g := by
  rcases hg with ⟨steps, rfl⟩
  exact assembleStageStepApproximants_compactBelow n f steps

/-- The assembled finite stage-step approximants form a directed family under
list concatenation. -/
private theorem stageFiniteStepApproxPred_directed
    (n : Nat) (f : (K (n + 1)).Obj) :
    (K (n + 1)).Directed (stageFiniteStepApproxPred n f) := by
  refine ⟨⟨assembleStageStepApproximants n f [], ⟨[], rfl⟩⟩, ?_⟩
  intro g h hg hh
  rcases hg with ⟨stepsG, rfl⟩
  rcases hh with ⟨stepsH, rfl⟩
  refine ⟨assembleStageStepApproximants n f (stepsG ++ stepsH), ⟨stepsG ++ stepsH, rfl⟩, ?_, ?_⟩
  · exact assembleStageStepApproximants_le_append_right n f stepsG stepsH
  · exact assembleStageStepApproximants_le_append_left n f stepsG stepsH

/-- If stage `Kₙ` is algebraic, the finite stage-step approximants assembled
below a stage-`n + 1` endomap already have that endomap as their least upper
bound. -/
private theorem stageFiniteStepApproxPred_isLub_of_stageAlgebraic
    (n : Nat) (hAlg : Algebraic (K n))
    (f : (K (n + 1)).Obj) :
    (K (n + 1)).IsLeastUpperBound (stageFiniteStepApproxPred n f) f := by
  constructor
  · intro g hg
    exact (stageFiniteStepApproxPred_compactBelow n f hg).2
  · intro w hw
    refine Exponential.rel_mk ?_
    intro x
    have hUpperCompactBelow :
        (K n).IsUpperBound (compactBelow (K n) (f.toFun x)) (w.toFun x) := by
      intro b hb
      let X : (K n).Obj → Prop := image f.toFun (compactBelow (K n) x)
      have hDirX : (K n).Directed X := f.directed_image ((hAlg x).1)
      have hChosenX :
          (K n).IsLeastUpperBound X ((K n).sup X hDirX) :=
        (K n).sup_spec X hDirX
      have hExactX :
          (K n).IsLeastUpperBound X (f.toFun x) :=
        (ContinuousMap.compactApproximation (K := K n) (L := K n) (hK := hAlg) f) x
      have hEqvX :
          (K n).Rel ((K n).sup X hDirX) (f.toFun x) ∧
            (K n).Rel (f.toFun x) ((K n).sup X hDirX) :=
        equivalent_of_isLeastUpperBound
          (K n).toHomotopyPartialOrder
          hChosenX
          hExactX
      have hbSupX : (K n).Rel b ((K n).sup X hDirX) :=
        (K n).rel_trans hb.2 hEqvX.2
      rcases hb.1 X hDirX hbSupX with ⟨y, hy, hby⟩
      rcases hy with ⟨c, hc, rfl⟩
      let d : StageStepApproxDatum n f := {
        source := c
        sourceCompact := hc.1
        target := b
        targetCompactBelow := ⟨hb.1, hby⟩
      }
      have hStepBelow :
          (K (n + 1)).Rel d.toMap (assembleStageStepApproximants n f [d]) := by
        exact (assembleStageStepApproximants_isLeastUpperBound n f [d]).1 (by
          simp)
      have hAssembledBelowW :
          (K (n + 1)).Rel (assembleStageStepApproximants n f [d]) w :=
        hw ⟨[d], rfl⟩
      have hbx :
          (K n).Rel b (w.toFun x) := by
        have hStepAtX :
            (K n).Rel (d.toMap.toFun x) (w.toFun x) :=
          (Exponential.rel_iff.mp
            ((K (n + 1)).rel_trans hStepBelow hAssembledBelowW)) x
        simpa [d, StepApproxDatum.toMap, stepFunction, hc.2] using hStepAtX
      exact hbx
    exact (hAlg (f.toFun x)).2.2 hUpperCompactBelow

/-- Under algebraicity of stage `Kₙ`, every compact-below approximant of a
stage-`n + 1` endomap is dominated by one of the assembled finite-step
approximants below that endomap. -/
private theorem stageFiniteStepApproxPred_cofinal_compactBelow
    (n : Nat) (hAlg : Algebraic (K n))
    (f : (K (n + 1)).Obj)
    {g : (K (n + 1)).Obj}
    (hg : compactBelow (K (n + 1)) f g) :
    ∃ h : (K (n + 1)).Obj,
      stageFiniteStepApproxPred n f h ∧ (K (n + 1)).Rel g h := by
  let X : (K (n + 1)).Obj → Prop := stageFiniteStepApproxPred n f
  have hDir : (K (n + 1)).Directed X := stageFiniteStepApproxPred_directed n f
  have hChosen :
      (K (n + 1)).IsLeastUpperBound X ((K (n + 1)).sup X hDir) :=
    (K (n + 1)).sup_spec X hDir
  have hExact :
      (K (n + 1)).IsLeastUpperBound X f :=
    stageFiniteStepApproxPred_isLub_of_stageAlgebraic n hAlg f
  have hEqv :
      (K (n + 1)).Rel ((K (n + 1)).sup X hDir) f ∧
        (K (n + 1)).Rel f ((K (n + 1)).sup X hDir) :=
    equivalent_of_isLeastUpperBound
      (K (n + 1)).toHomotopyPartialOrder
      hChosen
      hExact
  have hgSup : (K (n + 1)).Rel g ((K (n + 1)).sup X hDir) :=
    (K (n + 1)).rel_trans hg.2 hEqv.2
  rcases hg.1 X hDir hgSup with ⟨h, hhX, hgh⟩
  exact ⟨h, hhX, hgh⟩

/-- Algebraicity propagates one step up the `K` tower once the previous stage is
known algebraic. -/
private theorem stage_algebraic_succ
    (n : Nat) (hAlg : Algebraic (K n)) :
    Algebraic (K (n + 1)) := by
  intro f
  constructor
  · refine ⟨⟨assembleStageStepApproximants n f [], ?_⟩, ?_⟩
    · exact stageFiniteStepApproxPred_compactBelow n f ⟨[], rfl⟩
    · intro g h hg hh
      rcases stageFiniteStepApproxPred_cofinal_compactBelow n hAlg f hg with
        ⟨g', hg'X, hgg'⟩
      rcases stageFiniteStepApproxPred_cofinal_compactBelow n hAlg f hh with
        ⟨h', hh'X, hhh'⟩
      rcases hg'X with ⟨stepsG, rfl⟩
      rcases hh'X with ⟨stepsH, rfl⟩
      refine ⟨assembleStageStepApproximants n f (stepsG ++ stepsH), ?_, ?_, ?_⟩
      · exact stageFiniteStepApproxPred_compactBelow n f ⟨stepsG ++ stepsH, rfl⟩
      · exact (K (n + 1)).rel_trans hgg'
          (assembleStageStepApproximants_le_append_right n f stepsG stepsH)
      · exact (K (n + 1)).rel_trans hhh'
          (assembleStageStepApproximants_le_append_left n f stepsG stepsH)
  · constructor
    · intro g hg
      exact hg.2
    · intro w hw
      have hBasisUpper : (K (n + 1)).IsUpperBound (stageFiniteStepApproxPred n f) w := by
        intro g hg
        exact hw (stageFiniteStepApproxPred_compactBelow n f hg)
      exact (stageFiniteStepApproxPred_isLub_of_stageAlgebraic n hAlg f).2 hBasisUpper

private theorem stageOne_directed_unique_some
    {X : (K 0).Obj → Prop}
    (hX : (K 0).Directed X)
    {a b : SpherePoint}
    (ha : X (some a)) (hb : X (some b)) :
    a = b := by
  simpa [K, NPlus] using
    (Flat.directed_unique_some (α := SpherePoint) hX ha hb)

private def stageOneFiniteApproxFun
    (f : (K 1).Obj)
    (support : List SpherePoint) :
    (K 0).Obj → (K 0).Obj
  | none => f.toFun none
  | some a => if a ∈ support then f.toFun (some a) else f.toFun none

/-- A finite-support approximant for endomaps of the flat base stage `K₀`. It
keeps the exact values of `f` on the chosen support and otherwise falls back to
the bottom value `f ⊥₀`. -/
private noncomputable def stageOneFiniteApprox
    (f : (K 1).Obj)
    (support : List SpherePoint) :
    (K 1).Obj where
  toFun := stageOneFiniteApproxFun f support
  monotone' := by
    intro x y hxy
    cases x with
    | none =>
        cases y with
        | none =>
            simpa [stageOneFiniteApproxFun] using (K 0).rel_refl (f.toFun none)
        | some a =>
            by_cases ha : a ∈ support
            · simpa [stageOneFiniteApproxFun, ha] using f.monotone' hxy
            · simpa [stageOneFiniteApproxFun, ha] using (K 0).rel_refl (f.toFun none)
    | some a =>
        cases y with
        | none =>
            have : False := by
              simpa [K, NPlus, Flat.chpo_rel_iff, Flat.rel] using hxy
            cases this
        | some b =>
            have hab : a = b := by
              simpa [K, NPlus, Flat.chpo_rel_iff, Flat.rel] using hxy
            subst hab
            by_cases ha : a ∈ support <;> simp [stageOneFiniteApproxFun, ha]
  preserves_sup := by
    intro X hX
    by_cases hSome : ∃ a : SpherePoint, X (some a)
    · let a : SpherePoint := Classical.choose hSome
      have ha : X (some a) := Classical.choose_spec hSome
      have hSupEq : (K 0).sup X hX = some a := by
        have hSup : (K 0).Rel (some a) ((K 0).sup X hX) :=
          ((K 0).sup_spec X hX).1 ha
        cases hEq : (K 0).sup X hX with
        | none =>
            have hSupNone := hSup
            rw [hEq] at hSupNone
            have : False := by
              simpa [K, NPlus, Flat.chpo_rel_iff, Flat.rel] using hSupNone
            cases this
        | some b =>
            have hSupSome := hSup
            rw [hEq] at hSupSome
            have hab : a = b := by
              simpa [K, NPlus, Flat.chpo_rel_iff, Flat.rel] using hSupSome
            simpa [hab] using hEq
      by_cases haSupport : a ∈ support
      · have hPoint :
          ∀ x : (K 0).Obj, X x → stageOneFiniteApproxFun f support x = f.toFun x := by
            intro x hx
            cases x with
            | none => rfl
            | some b =>
                have hba : b = a := stageOne_directed_unique_some hX hx ha
                subst hba
                simp [stageOneFiniteApproxFun, haSupport]
        have hSupPoint :
            stageOneFiniteApproxFun f support ((K 0).sup X hX) =
              f.toFun ((K 0).sup X hX) := by
          rw [hSupEq]
          simp [stageOneFiniteApproxFun, haSupport]
        constructor
        · intro z hz
          rcases hz with ⟨x, hx, rfl⟩
          rw [hPoint x hx, hSupPoint]
          exact (f.preserves_sup X hX).1 ⟨x, hx, rfl⟩
        · intro w hw
          rw [hSupPoint]
          exact (f.preserves_sup X hX).2 <| by
            intro z hz
            rcases hz with ⟨x, hx, rfl⟩
            simpa [hPoint x hx] using hw ⟨x, hx, rfl⟩
      · have hPoint :
          ∀ x : (K 0).Obj, X x → stageOneFiniteApproxFun f support x = f.toFun none := by
            intro x hx
            cases x with
            | none => rfl
            | some b =>
                have hba : b = a := stageOne_directed_unique_some hX hx ha
                subst hba
                simp [stageOneFiniteApproxFun, haSupport]
        have hSupPoint :
            stageOneFiniteApproxFun f support ((K 0).sup X hX) = f.toFun none := by
          rw [hSupEq]
          simp [stageOneFiniteApproxFun, haSupport]
        constructor
        · intro z hz
          rcases hz with ⟨x, hx, rfl⟩
          rw [hPoint x hx, hSupPoint]
          exact (K 0).rel_refl (f.toFun none)
        · intro w hw
          rw [hSupPoint]
          exact hw ⟨some a, ha, by simp [stageOneFiniteApproxFun, haSupport]⟩
    · have hSupEq : (K 0).sup X hX = none := by
        have hUpper : (K 0).IsUpperBound X none := by
          intro x hx
          cases x with
          | none =>
              exact (K 0).rel_refl none
          | some a =>
              exact False.elim (hSome ⟨a, hx⟩)
        have hSupLe : (K 0).Rel ((K 0).sup X hX) none :=
          ((K 0).sup_spec X hX).2 hUpper
        cases hEq : (K 0).sup X hX with
        | none => rfl
        | some a =>
            have hSupLeSome := hSupLe
            rw [hEq] at hSupLeSome
            have : False := by
              simpa [K, NPlus, Flat.chpo_rel_iff, Flat.rel] using hSupLeSome
            cases this
      have hPoint :
          ∀ x : (K 0).Obj, X x → stageOneFiniteApproxFun f support x = f.toFun none := by
            intro x hx
            cases x with
            | none => rfl
            | some a =>
                exact False.elim (hSome ⟨a, hx⟩)
      have hSupPoint :
          stageOneFiniteApproxFun f support ((K 0).sup X hX) = f.toFun none := by
        rw [hSupEq]
        rfl
      rcases hX.1 with ⟨x, hx⟩
      have hxNone : x = none := by
        cases x with
        | none => rfl
        | some a =>
            exact False.elim (hSome ⟨a, hx⟩)
      subst hxNone
      constructor
      · intro z hz
        rcases hz with ⟨x, hxX, rfl⟩
        rw [hPoint x hxX, hSupPoint]
        exact (K 0).rel_refl (f.toFun none)
      · intro w hw
        rw [hSupPoint]
        exact hw ⟨none, hx, rfl⟩

@[simp] private theorem stageOneFiniteApprox_none
    (f : (K 1).Obj) (support : List SpherePoint) :
    (stageOneFiniteApprox f support).toFun none = f.toFun none := rfl

@[simp] private theorem stageOneFiniteApprox_some
    (f : (K 1).Obj) (support : List SpherePoint) (a : SpherePoint) :
    (stageOneFiniteApprox f support).toFun (some a) =
      if a ∈ support then f.toFun (some a) else f.toFun none := rfl

private theorem stageOneFiniteApprox_below
    (f : (K 1).Obj)
    (support : List SpherePoint) :
    (K 1).Rel (stageOneFiniteApprox f support) f := by
  refine Exponential.rel_mk ?_
  intro x
  cases x with
  | none =>
      simpa using (K 0).rel_refl (f.toFun none)
  | some a =>
      by_cases ha : a ∈ support
      · simpa [stageOneFiniteApprox_some, ha] using
          (K 0).rel_refl (f.toFun (some a))
      · simpa [stageOneFiniteApprox_some, ha] using
          f.monotone' ((K 0).bottom_le (some a))

private theorem stageOneFiniteApprox_support_mono
    (f : (K 1).Obj)
    {support support' : List SpherePoint}
    (hsub : ∀ a : SpherePoint, a ∈ support → a ∈ support') :
    (K 1).Rel (stageOneFiniteApprox f support) (stageOneFiniteApprox f support') := by
  refine Exponential.rel_mk ?_
  intro x
  cases x with
  | none =>
      simpa using (K 0).rel_refl (f.toFun none)
  | some a =>
      by_cases ha : a ∈ support
      · have ha' : a ∈ support' := hsub a ha
        simpa [stageOneFiniteApprox_some, ha, ha'] using
          (K 0).rel_refl (f.toFun (some a))
      · by_cases ha' : a ∈ support'
        · simpa [stageOneFiniteApprox_some, ha, ha'] using
            f.monotone' ((K 0).bottom_le (some a))
        · simpa [stageOneFiniteApprox_some, ha, ha'] using
            (K 0).rel_refl (f.toFun none)

private theorem stageOneFiniteApprox_map_mono
    {g f : (K 1).Obj}
    (hgf : (K 1).Rel g f)
    (support : List SpherePoint) :
    (K 1).Rel (stageOneFiniteApprox g support) (stageOneFiniteApprox f support) := by
  refine Exponential.rel_mk ?_
  intro x
  cases x with
  | none =>
      simpa using (Exponential.rel_iff.mp hgf) none
  | some a =>
      by_cases ha : a ∈ support
      · simpa [stageOneFiniteApprox_some, ha] using
          (Exponential.rel_iff.mp hgf) (some a)
      · simpa [stageOneFiniteApprox_some, ha] using
          (Exponential.rel_iff.mp hgf) none

private theorem stageOneFiniteApprox_compact_aux
    {F : (K 1).Obj → Prop}
    (hF : (K 1).Directed F)
    (approx : (K 1).Obj) :
    ∀ xs : List (K 0).Obj,
      (∀ x, x ∈ xs → ∃ g, F g ∧ (K 0).Rel (approx.toFun x) (g.toFun x)) →
      ∃ g, F g ∧ ∀ x, x ∈ xs → (K 0).Rel (approx.toFun x) (g.toFun x)
  | [], _ => by
      rcases hF.1 with ⟨g, hg⟩
      exact ⟨g, hg, by intro x hx; cases hx⟩
  | x :: xs, hxs => by
      rcases hxs x (by simp) with ⟨gx, hgx, hxgx⟩
      rcases stageOneFiniteApprox_compact_aux hF approx xs
          (by
            intro y hy
            exact hxs y (by simp [hy])) with
        ⟨gxs, hgxs, hxsUpper⟩
      rcases hF.2 hgx hgxs with ⟨g, hg, hgxg, hgxsg⟩
      refine ⟨g, hg, ?_⟩
      intro y hy
      simp at hy
      cases hy with
      | inl hyEq =>
          simpa [hyEq] using
            (K 0).rel_trans hxgx ((Exponential.rel_iff.mp hgxg) x)
      | inr hyTail =>
          exact (K 0).rel_trans
            (hxsUpper y hyTail)
            ((Exponential.rel_iff.mp hgxsg) y)

private theorem stageOneFiniteApprox_compact
    (f : (K 1).Obj)
    (support : List SpherePoint) :
    IsCompact (K 1) (stageOneFiniteApprox f support) := by
  intro F hF hApproxSup
  let approx := stageOneFiniteApprox f support
  let tracked : List (K 0).Obj := none :: support.map some
  have hTracked :
      ∀ x, x ∈ tracked → ∃ g, F g ∧ (K 0).Rel (approx.toFun x) (g.toFun x) := by
        intro x hx
        have hxCompact : IsCompact (K 0) (approx.toFun x) := by
          simpa [K] using (Flat.isCompact (α := SpherePoint) (approx.toFun x))
        have hxSup : (K 0).Rel (approx.toFun x) (((K 1).sup F hF).toFun x) :=
          (Exponential.rel_iff.mp hApproxSup) x
        rcases hxCompact (Exponential.evalPred F x) (Exponential.directed_eval hF x) hxSup with
          ⟨y, hy, hxy⟩
        rcases hy with ⟨g, hg, rfl⟩
        exact ⟨g, hg, hxy⟩
  rcases stageOneFiniteApprox_compact_aux hF approx tracked hTracked with
    ⟨g, hg, hgTracked⟩
  refine ⟨g, hg, Exponential.rel_mk ?_⟩
  intro x
  cases x with
  | none =>
      exact hgTracked none (by simp [tracked])
  | some a =>
      by_cases ha : a ∈ support
      · have hMem : some a ∈ tracked := by
          simp [tracked, List.mem_map, ha]
        exact hgTracked (some a) hMem
      · have hNone : (K 0).Rel (approx.toFun none) (g.toFun none) :=
          hgTracked none (by simp [tracked])
        have hMono : (K 0).Rel (g.toFun none) (g.toFun (some a)) :=
          g.monotone' ((K 0).bottom_le (some a))
        simpa [approx, stageOneFiniteApproxFun, ha] using
          (K 0).rel_trans hNone hMono

private def stageOneApproxPred
    (f : (K 1).Obj) :
    (K 1).Obj → Prop :=
  fun g => ∃ support : List SpherePoint, g = stageOneFiniteApprox f support

private theorem stageOneApproxPred_compactBelow
    (f : (K 1).Obj)
    {g : (K 1).Obj}
    (hg : stageOneApproxPred f g) :
    compactBelow (K 1) f g := by
  rcases hg with ⟨support, rfl⟩
  exact ⟨stageOneFiniteApprox_compact f support, stageOneFiniteApprox_below f support⟩

private theorem stageOneApproxPred_directed
    (f : (K 1).Obj) :
    (K 1).Directed (stageOneApproxPred f) := by
  refine ⟨⟨stageOneFiniteApprox f [], ⟨[], rfl⟩⟩, ?_⟩
  intro g h hg hh
  rcases hg with ⟨supportG, rfl⟩
  rcases hh with ⟨supportH, rfl⟩
  refine ⟨stageOneFiniteApprox f (supportG ++ supportH), ⟨supportG ++ supportH, rfl⟩, ?_, ?_⟩
  · exact stageOneFiniteApprox_support_mono f
      (support := supportG)
      (support' := supportG ++ supportH)
      (by
        intro a ha
        exact List.mem_append.mpr (Or.inl ha))
  · exact stageOneFiniteApprox_support_mono f
      (support := supportH)
      (support' := supportG ++ supportH)
      (by
        intro a ha
        exact List.mem_append.mpr (Or.inr ha))

private theorem stageOneApproxPred_isLub
    (f : (K 1).Obj) :
    (K 1).IsLeastUpperBound (stageOneApproxPred f) f := by
  constructor
  · intro g hg
    rcases hg with ⟨support, rfl⟩
    exact stageOneFiniteApprox_below f support
  · intro w hw
    refine Exponential.rel_mk ?_
    intro x
    cases x with
    | none =>
        exact (Exponential.rel_iff.mp (hw ⟨[], rfl⟩)) none
    | some a =>
        simpa [stageOneFiniteApprox_some] using
          (Exponential.rel_iff.mp (hw ⟨[a], rfl⟩)) (some a)

private theorem stageOneApproxPred_cofinal_compactBelow
    (f : (K 1).Obj)
    {g : (K 1).Obj}
    (hg : compactBelow (K 1) f g) :
    ∃ h : (K 1).Obj, stageOneApproxPred f h ∧ (K 1).Rel g h := by
  let X : (K 1).Obj → Prop := stageOneApproxPred g
  have hDir : (K 1).Directed X := stageOneApproxPred_directed g
  have hChosen :
      (K 1).IsLeastUpperBound X ((K 1).sup X hDir) :=
    (K 1).sup_spec X hDir
  have hExact : (K 1).IsLeastUpperBound X g :=
    stageOneApproxPred_isLub g
  have hEqv :
      (K 1).Rel ((K 1).sup X hDir) g ∧
        (K 1).Rel g ((K 1).sup X hDir) :=
    equivalent_of_isLeastUpperBound
      (K 1).toHomotopyPartialOrder
      hChosen
      hExact
  rcases hg.1 X hDir hEqv.2 with ⟨h, hhX, hgh⟩
  rcases hhX with ⟨support, rfl⟩
  refine ⟨stageOneFiniteApprox f support, ⟨support, rfl⟩, ?_⟩
  exact (K 1).rel_trans hgh (stageOneFiniteApprox_map_mono hg.2 support)

/-- The first successor stage `K₁ = [K₀ → K₀]` is algebraic: every continuous
endomap of the flat base stage is the least upper bound of its finite-support
approximants. -/
theorem stage_algebraic_one : Algebraic (K 1) := by
  intro f
  constructor
  · refine ⟨⟨stageOneFiniteApprox f [], ?_⟩, ?_⟩
    · exact stageOneApproxPred_compactBelow f ⟨[], rfl⟩
    · intro g h hg hh
      rcases stageOneApproxPred_cofinal_compactBelow f hg with
        ⟨g', ⟨supportG, rfl⟩, hgg'⟩
      rcases stageOneApproxPred_cofinal_compactBelow f hh with
        ⟨h', ⟨supportH, rfl⟩, hhh'⟩
      refine ⟨stageOneFiniteApprox f (supportG ++ supportH), ?_, ?_, ?_⟩
      · exact stageOneApproxPred_compactBelow f ⟨supportG ++ supportH, rfl⟩
      · exact (K 1).rel_trans hgg'
          (stageOneFiniteApprox_support_mono f
            (support := supportG)
            (support' := supportG ++ supportH)
            (by
              intro a ha
              exact List.mem_append.mpr (Or.inl ha)))
      · exact (K 1).rel_trans hhh'
          (stageOneFiniteApprox_support_mono f
            (support := supportH)
            (support' := supportG ++ supportH)
            (by
              intro a ha
              exact List.mem_append.mpr (Or.inr ha)))
  · constructor
    · intro g hg
      exact hg.2
    · intro w hw
      have hBasisUpper : (K 1).IsUpperBound (stageOneApproxPred f) w := by
        intro g hg
        exact hw (stageOneApproxPred_compactBelow f hg)
      exact (stageOneApproxPred_isLub f).2 hBasisUpper

/-- Stage-wise bounded completeness together with the explicit finite-support
approximation theorem gives the full Homotopy Scott Domain structure at level
one. -/
noncomputable def stage_scottDomain_one : HomotopyScottDomain where
  carrier := K 1
  algebraic := stage_algebraic_one
  boundedComplete := stage_boundedComplete 1

/-- The second successor stage `K₂ = [K₁ → K₁]` is algebraic, obtained from the
generic finite-step successor construction over the already algebraic stage
`K₁`. -/
theorem stage_algebraic_two : Algebraic (K 2) :=
  stage_algebraic_succ 1 stage_algebraic_one

/-- The same successor-stage construction upgrades `K₂` to a full Homotopy
Scott Domain. -/
noncomputable def stage_scottDomain_two : HomotopyScottDomain where
  carrier := K 2
  algebraic := stage_algebraic_two
  boundedComplete := stage_boundedComplete 2

/-- All finite stages in the `K` tower are algebraic. -/
theorem stage_algebraic : ∀ n : Nat, Algebraic (K n)
  | 0 => stage_algebraic_zero
  | n + 1 => stage_algebraic_succ n (stage_algebraic n)

/-- All finite stages in the `K` tower are Homotopy Scott Domains. -/
noncomputable def stage_scottDomain (n : Nat) : HomotopyScottDomain where
  carrier := K n
  algebraic := stage_algebraic n
  boundedComplete := stage_boundedComplete n

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

/-- The base-stage approximation is already the least upper bound of the image of
compact base-stage approximants under the canonical embedding into `K∞`. This is
the first Proposition 4.1 statement phrased directly in Scott-domain language
rather than only as a compact single approximant. -/
theorem proposition_4_1_baseApproximation_isLub (x : KInfinityCHPO.Obj) :
    KInfinityCHPO.IsLeastUpperBound
      (image embedBaseToLimit (compactBelow (K 0) (projectToLevel 0 x)))
      (proposition_4_2_approximation x) := by
  simpa [CompactApproximation, proposition_4_2_approximation] using
    (ContinuousMap.compactApproximation
      (hK := stage_algebraic_zero)
      embedBaseContinuous
      (projectToLevel 0 x))

/-- Chosen-data packaging of the Section 4.1 interface for `K∞`. Besides the
per-stage Scott-domain data and coordinate projections, the witness records
both the compact level-zero approximation of each inverse-limit thread and the
full directed finite-stage approximation family whose least upper bound is the
original thread. It also records the concrete compact step-function endomaps
available uniformly at every successor stage, together with the final
inverse-limit algebraic and bounded-complete witnesses that package `K∞`
itself as a Homotopy Scott Domain. -/
structure Proposition41Witness where
  stageBoundedComplete : ∀ n : Nat, BoundedComplete (K n)
  coordinateProjection : ∀ n : Nat, ContinuousMap KInfinityCHPO (K n)
  finiteStageEmbedding : ∀ n : Nat, ContinuousMap (K n) KInfinityCHPO
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
  baseApproximation_isLub :
    ∀ x : KInfinityCHPO.Obj,
      KInfinityCHPO.IsLeastUpperBound
        (image embedBaseToLimit (compactBelow (K 0) (projectToLevel 0 x)))
        (baseApproximation x)
  stageZeroAlgebraic : Algebraic (K 0)
  stageOneAlgebraic : Algebraic (K 1)
  stageTwoAlgebraic : Algebraic (K 2)
  allFiniteStagesAlgebraic : ∀ n : Nat, Algebraic (K n)
  kInfinityAlgebraic : Algebraic KInfinityCHPO
  kInfinityBoundedComplete : BoundedComplete KInfinityCHPO
  baseChainCompact :
    ∀ x : (K 0).Obj, ∀ n : Nat, IsCompact (K n) (baseUp x n)
  successorStageStepCompact :
    ∀ n : Nat, ∀ {a b : (K n).Obj},
      ∀ (ha : IsCompact (K n) a) (_hb : IsCompact (K n) b),
        IsCompact (K (n + 1)) (stepFunction a ha b)
  finiteStageApproximation : Nat → KInfinityCHPO.Obj → KInfinityCHPO.Obj
  finiteStageApproximation_exact :
    ∀ n : Nat, ∀ x : KInfinityCHPO.Obj,
      projectToLevel n (finiteStageApproximation n x) = projectToLevel n x
  finiteStageApproximation_exact_le :
    ∀ {m n : Nat}, m ≤ n → ∀ x : KInfinityCHPO.Obj,
      projectToLevel m (finiteStageApproximation n x) = projectToLevel m x
  finiteStageApproximation_stable :
    ∀ {m n : Nat}, m ≤ n → ∀ x : KInfinityCHPO.Obj,
      finiteStageApproximation m (finiteStageApproximation n x) =
        finiteStageApproximation m x
  finiteStageCompactBelow_lift :
    ∀ n : Nat, ∀ {x : KInfinityCHPO.Obj} {y : (K n).Obj},
      compactBelow (K n) (projectToLevel n x) y →
        compactBelow KInfinityCHPO x ((finiteStageEmbedding n) y)
  finiteStageApproximation_compact_of_stageCompact :
    ∀ n : Nat, ∀ x : KInfinityCHPO.Obj,
      IsCompact (K n) (projectToLevel n x) →
        IsCompact KInfinityCHPO (finiteStageApproximation n x)
  finiteStageApproximation_isLub_of_stageAlgebraic :
    ∀ n : Nat, Algebraic (K n) → ∀ x : KInfinityCHPO.Obj,
      KInfinityCHPO.IsLeastUpperBound
        (image (fun y => (finiteStageEmbedding n) y)
          (compactBelow (K n) (projectToLevel n x)))
        (finiteStageApproximation n x)
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

private theorem thread_projectDown
    (x : KInfinityCHPO.Obj) (n : Nat) :
    ∀ {m : Nat} (hm : m ≤ n),
      (K m).Rel (projectToLevel m x) (projectDown n (projectToLevel n x) m hm)
  | m, hm => by
      by_cases hmn : m = n
      · subst m
        simpa using (K n).rel_refl (projectToLevel n x)
      · have hlt : m < n := by omega
        rw [projectDown_step (n := n) (x := projectToLevel n x) (m := m) hlt]
        have hm' : m + 1 ≤ n := by omega
        exact (K m).rel_trans
          (x.fromPrev m)
          ((fMinus m).monotone' (thread_projectDown x n hm'))
termination_by m _ => n - m
decreasing_by
  omega

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

/-- The stage-`n` approximation is already exact on every lower coordinate. -/
theorem proposition_4_2_stageApproximation_exact_le
    {m n : Nat} (hmn : m ≤ n) (x : KInfinityCHPO.Obj) :
    projectToLevel m (proposition_4_2_stageApproximation n x) = projectToLevel m x := by
  change genericLevelCoords n (projectToLevel n x) m = projectToLevel m x
  rw [genericLevelCoords_below n (projectToLevel n x) hmn]
  apply stage_antisymmetric m
  · exact projectDown_thread x n hmn
  · exact thread_projectDown x n hmn

/-- Truncating first to stage `n` and then to any lower stage `m ≤ n` is stable:
it agrees with the direct stage-`m` approximation of the original thread. -/
theorem proposition_4_2_stageApproximation_stable
    {m n : Nat} (hmn : m ≤ n) (x : KInfinityCHPO.Obj) :
    proposition_4_2_stageApproximation m (proposition_4_2_stageApproximation n x) =
      proposition_4_2_stageApproximation m x := by
  simpa [proposition_4_2_stageApproximation] using
    congrArg (embedFiniteStageToLimit m)
      (proposition_4_2_stageApproximation_exact_le hmn x)

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

/-- Any embedded stage element lies below a thread whose matching coordinate
dominates it. -/
theorem embedFiniteStageToLimit_below_of_level
    (n : Nat) {a : (K n).Obj} {x : KInfinityCHPO.Obj}
    (ha : (K n).Rel a (projectToLevel n x)) :
    KInfinityCHPO.Rel (embedFiniteStageToLimit n a) x := by
  exact KInfinityCHPO.rel_trans
    (embedFiniteStageToLimit_monotone n ha)
    (proposition_4_2_stageApproximation_below n x)

/-- If a finite-stage point is compact in `Kₙ`, its canonical embedding
`fₙ,∞(x)` is compact in the inverse limit `K∞`. -/
theorem embedFiniteStageToLimit_compact
    (n : Nat) {x : (K n).Obj}
    (hx : IsCompact (K n) x) :
    IsCompact KInfinityCHPO (embedFiniteStageToLimit n x) := by
  have hret :
      ∀ z : (K n).Obj,
        (K n).Rel
            ((projectContinuous n).toFun ((embedFiniteStageContinuous n).toFun z))
            z ∧
          (K n).Rel z
            ((projectContinuous n).toFun ((embedFiniteStageContinuous n).toFun z)) := by
    intro z
    change (K n).Rel (projectToLevel n (embedFiniteStageToLimit n z)) z ∧
      (K n).Rel z (projectToLevel n (embedFiniteStageToLimit n z))
    rw [project_embedFiniteStage_exact n z]
    exact ⟨(K n).rel_refl z, (K n).rel_refl z⟩
  have hsec :
      ∀ y : KInfinityCHPO.Obj,
        KInfinityCHPO.Rel
          ((embedFiniteStageContinuous n).toFun ((projectContinuous n).toFun y))
          y := by
    intro y
    change KInfinityCHPO.Rel (embedFiniteStageToLimit n (projectToLevel n y)) y
    simpa [proposition_4_2_stageApproximation] using
      proposition_4_2_stageApproximation_below n y
  simpa using
    compact_of_retraction
      (embedFiniteStageContinuous n)
      (projectContinuous n)
      hret
      hsec
      hx

/-- Any stage approximation is compact in `K∞` once its chosen stage coordinate
is compact in `Kₙ`. -/
theorem proposition_4_2_stageApproximation_compact_of_stageCompact
    (n : Nat) (x : KInfinityCHPO.Obj)
    (hx : IsCompact (K n) (projectToLevel n x)) :
    IsCompact KInfinityCHPO (proposition_4_2_stageApproximation n x) := by
  simpa [proposition_4_2_stageApproximation] using
    embedFiniteStageToLimit_compact (n := n) hx

/-- Any compact-below finite-stage approximant lifts to a compact-below
approximant in the inverse limit `K∞`. -/
theorem proposition_4_1_stageCompactBelow_lift
    (n : Nat) {x : KInfinityCHPO.Obj} {y : (K n).Obj}
    (hy : compactBelow (K n) (projectToLevel n x) y) :
    compactBelow KInfinityCHPO x (embedFiniteStageToLimit n y) := by
  refine ⟨embedFiniteStageToLimit_compact (n := n) hy.1, ?_⟩
  exact KInfinityCHPO.rel_trans
    (embedFiniteStageToLimit_monotone n hy.2)
    (proposition_4_2_stageApproximation_below n x)

/-- Whenever a finite stage `Kₙ` is algebraic, the stage-`n` approximation of a
thread is already the least upper bound of the embedded compact-below
approximants coming from that stage. -/
theorem proposition_4_1_stageApproximation_isLub_of_stageAlgebraic
    (n : Nat) (hAlg : Algebraic (K n)) (x : KInfinityCHPO.Obj) :
    KInfinityCHPO.IsLeastUpperBound
      (image (embedFiniteStageToLimit n) (compactBelow (K n) (projectToLevel n x)))
      (proposition_4_2_stageApproximation n x) := by
  simpa [CompactApproximation, proposition_4_2_stageApproximation] using
    (ContinuousMap.compactApproximation
      (hK := hAlg)
      (embedFiniteStageContinuous n)
      (projectToLevel n x))

/-- The compact step-function witnesses from any finite stage remain compact
after embedding into the inverse limit `K∞`. -/
theorem embedFiniteStageStepFunctionToLimit_compact
    (n : Nat) {a b : (K n).Obj}
    (ha : IsCompact (K n) a) (hb : IsCompact (K n) b) :
    IsCompact KInfinityCHPO
      (embedFiniteStageToLimit (n + 1) (stepFunction a ha b)) := by
  exact embedFiniteStageToLimit_compact (n := n + 1)
    (stage_stepFunction_compact n ha hb)

/-- In particular, the compact base chain yields compact successor-stage step
functions in the inverse limit. -/
theorem embedBaseStepFunctionToLimit_compact
    (x y : (K 0).Obj) (n : Nat) :
    IsCompact KInfinityCHPO
      (embedFiniteStageToLimit (n + 1)
        (stepFunction (baseUp x n) (baseUp_compact x n) (baseUp y n))) := by
  exact embedFiniteStageStepFunctionToLimit_compact (n := n)
    (a := baseUp x n) (b := baseUp y n)
    (baseUp_compact x n) (baseUp_compact y n)

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

/-- Predicate selecting the embedded compact-below finite-stage approximants of
a fixed inverse-limit thread. -/
private def kInfinityCompactApproxPred
    (x : KInfinityCHPO.Obj) :
    KInfinityCHPO.Obj → Prop :=
  fun z =>
    ∃ n : Nat, ∃ a : (K n).Obj,
      compactBelow (K n) (projectToLevel n x) a ∧
        z = embedFiniteStageToLimit n a

private theorem kInfinityCompactApproxPred_compactBelow
    (x : KInfinityCHPO.Obj)
    {z : KInfinityCHPO.Obj}
    (hz : kInfinityCompactApproxPred x z) :
    compactBelow KInfinityCHPO x z := by
  rcases hz with ⟨n, a, ha, rfl⟩
  exact proposition_4_1_stageCompactBelow_lift n ha

private theorem kInfinityCompactApproxPred_of_stageImage
    (x : KInfinityCHPO.Obj) (n : Nat)
    {z : KInfinityCHPO.Obj}
    (hz : image (embedFiniteStageToLimit n)
      (compactBelow (K n) (projectToLevel n x)) z) :
    kInfinityCompactApproxPred x z := by
  rcases hz with ⟨a, ha, rfl⟩
  exact ⟨n, a, ha, rfl⟩

/-- The embedded finite-stage compact-below approximants of a thread form a
directed family in the inverse limit. -/
private theorem kInfinityCompactApproxPred_directed
    (x : KInfinityCHPO.Obj) :
    KInfinityCHPO.Directed (kInfinityCompactApproxPred x) := by
  constructor
  · refine ⟨embedFiniteStageToLimit 0 (projectToLevel 0 x), ?_⟩
    refine ⟨0, projectToLevel 0 x, ?_, rfl⟩
    refine ⟨?_, (K 0).rel_refl _⟩
    simpa [K] using (Flat.isCompact (α := SpherePoint) (projectToLevel 0 x))
  · intro y z hy hz
    rcases hy with ⟨n, a, ha, rfl⟩
    rcases hz with ⟨m, b, hb, rfl⟩
    let k := max n m
    let Pk : KInfinityCHPO.Obj → Prop :=
      image (embedFiniteStageToLimit k)
        (compactBelow (K k) (projectToLevel k x))
    have hDirPk : KInfinityCHPO.Directed Pk :=
      (embedFiniteStageContinuous k).directed_image
        ((stage_algebraic k (projectToLevel k x)).1)
    have hExactPk :
        KInfinityCHPO.IsLeastUpperBound Pk
          (proposition_4_2_stageApproximation k x) :=
      proposition_4_1_stageApproximation_isLub_of_stageAlgebraic
        k (stage_algebraic k) x
    have hEqvPk :
        KInfinityCHPO.Rel
            (KInfinityCHPO.sup Pk hDirPk)
            (proposition_4_2_stageApproximation k x)
          ∧
          KInfinityCHPO.Rel
            (proposition_4_2_stageApproximation k x)
            (KInfinityCHPO.sup Pk hDirPk) :=
      equivalent_of_isLeastUpperBound
        KInfinityCHPO.toHomotopyPartialOrder
        (KInfinityCHPO.sup_spec Pk hDirPk)
        hExactPk
    have hyBelowApprox :
        KInfinityCHPO.Rel
          (embedFiniteStageToLimit n a)
          (proposition_4_2_stageApproximation k x) := by
      apply embedFiniteStageToLimit_below_of_level n
      rw [proposition_4_2_stageApproximation_exact_le
        (m := n) (n := k) (Nat.le_max_left n m) x]
      exact ha.2
    have hzBelowApprox :
        KInfinityCHPO.Rel
          (embedFiniteStageToLimit m b)
          (proposition_4_2_stageApproximation k x) := by
      apply embedFiniteStageToLimit_below_of_level m
      rw [proposition_4_2_stageApproximation_exact_le
        (m := m) (n := k) (Nat.le_max_right n m) x]
      exact hb.2
    have hyBelowChosen :
        KInfinityCHPO.Rel
          (embedFiniteStageToLimit n a)
          (KInfinityCHPO.sup Pk hDirPk) :=
      KInfinityCHPO.rel_trans hyBelowApprox hEqvPk.2
    have hzBelowChosen :
        KInfinityCHPO.Rel
          (embedFiniteStageToLimit m b)
          (KInfinityCHPO.sup Pk hDirPk) :=
      KInfinityCHPO.rel_trans hzBelowApprox hEqvPk.2
    have hyCompact : IsCompact KInfinityCHPO (embedFiniteStageToLimit n a) :=
      (proposition_4_1_stageCompactBelow_lift n ha).1
    have hzCompact : IsCompact KInfinityCHPO (embedFiniteStageToLimit m b) :=
      (proposition_4_1_stageCompactBelow_lift m hb).1
    rcases hyCompact Pk hDirPk hyBelowChosen with ⟨y', hy'Pk, hyy'⟩
    rcases hzCompact Pk hDirPk hzBelowChosen with ⟨z', hz'Pk, hzz'⟩
    rcases hDirPk.2 hy'Pk hz'Pk with ⟨w, hwPk, hyw, hzw⟩
    rcases hwPk with ⟨c, hc, rfl⟩
    refine ⟨embedFiniteStageToLimit k c, ⟨k, c, hc, rfl⟩, ?_, ?_⟩
    · exact KInfinityCHPO.rel_trans hyy' hyw
    · exact KInfinityCHPO.rel_trans hzz' hzw

/-- The embedded compact-below finite-stage approximants of a thread have that
thread as their least upper bound in the inverse limit. -/
private theorem kInfinityCompactApproxPred_isLub
    (x : KInfinityCHPO.Obj) :
    KInfinityCHPO.IsLeastUpperBound (kInfinityCompactApproxPred x) x := by
  constructor
  · intro y hy
    exact (kInfinityCompactApproxPred_compactBelow x hy).2
  · intro w hw
    have hStageUpper :
        ∀ n : Nat, KInfinityCHPO.Rel (proposition_4_2_stageApproximation n x) w := by
      intro n
      let Pn : KInfinityCHPO.Obj → Prop :=
        image (embedFiniteStageToLimit n)
          (compactBelow (K n) (projectToLevel n x))
      have hUpperPn : KInfinityCHPO.IsUpperBound Pn w := by
        intro y hy
        exact hw (kInfinityCompactApproxPred_of_stageImage x n hy)
      exact (proposition_4_1_stageApproximation_isLub_of_stageAlgebraic
        n (stage_algebraic n) x).2 hUpperPn
    exact (proposition_4_2_stageApproximation_isLub x).2 (by
      intro y hy
      rcases hy with ⟨n, rfl⟩
      exact hStageUpper n)

/-- Any compact-below approximant of a thread is dominated by an embedded
compact-below finite-stage approximant. -/
private theorem kInfinityCompactApproxPred_cofinal_compactBelow
    (x : KInfinityCHPO.Obj)
    {g : KInfinityCHPO.Obj}
    (hg : compactBelow KInfinityCHPO x g) :
    ∃ h : KInfinityCHPO.Obj,
      kInfinityCompactApproxPred x h ∧ KInfinityCHPO.Rel g h := by
  let X : KInfinityCHPO.Obj → Prop := kInfinityCompactApproxPred x
  have hDir : KInfinityCHPO.Directed X := kInfinityCompactApproxPred_directed x
  have hChosen :
      KInfinityCHPO.IsLeastUpperBound X (KInfinityCHPO.sup X hDir) :=
    KInfinityCHPO.sup_spec X hDir
  have hExact :
      KInfinityCHPO.IsLeastUpperBound X x :=
    kInfinityCompactApproxPred_isLub x
  have hEqv :
      KInfinityCHPO.Rel (KInfinityCHPO.sup X hDir) x ∧
        KInfinityCHPO.Rel x (KInfinityCHPO.sup X hDir) :=
    equivalent_of_isLeastUpperBound
      KInfinityCHPO.toHomotopyPartialOrder
      hChosen
      hExact
  have hgSup : KInfinityCHPO.Rel g (KInfinityCHPO.sup X hDir) :=
    KInfinityCHPO.rel_trans hg.2 hEqv.2
  rcases hg.1 X hDir hgSup with ⟨h, hhX, hgh⟩
  exact ⟨h, hhX, hgh⟩

/-- The inverse limit `K∞` is algebraic: every thread is the least upper bound
of its embedded compact-below finite-stage approximants. -/
theorem kInfinity_algebraic : Algebraic KInfinityCHPO := by
  intro x
  constructor
  · refine ⟨⟨embedFiniteStageToLimit 0 (projectToLevel 0 x), ?_⟩, ?_⟩
    · exact kInfinityCompactApproxPred_compactBelow x
        ⟨0, projectToLevel 0 x,
          ⟨by simpa [K] using (Flat.isCompact (α := SpherePoint) (projectToLevel 0 x)),
            (K 0).rel_refl _⟩,
          rfl⟩
    · intro g h hg hh
      rcases kInfinityCompactApproxPred_cofinal_compactBelow x hg with
        ⟨g', hg'X, hgg'⟩
      rcases kInfinityCompactApproxPred_cofinal_compactBelow x hh with
        ⟨h', hh'X, hhh'⟩
      rcases (kInfinityCompactApproxPred_directed x).2 hg'X hh'X with
        ⟨z, hzX, hg'z, hh'z⟩
      refine ⟨z, kInfinityCompactApproxPred_compactBelow x hzX, ?_, ?_⟩
      · exact KInfinityCHPO.rel_trans hgg' hg'z
      · exact KInfinityCHPO.rel_trans hhh' hh'z
  · constructor
    · intro y hy
      exact hy.2
    · intro w hw
      have hPredUpper : KInfinityCHPO.IsUpperBound (kInfinityCompactApproxPred x) w := by
        intro y hy
        exact hw (kInfinityCompactApproxPred_compactBelow x hy)
      exact (kInfinityCompactApproxPred_isLub x).2 hPredUpper

private def PreservesUpperBoundedLub
    {A : CompleteHomotopyPartialOrder}
    {B : CompleteHomotopyPartialOrder}
    (f : ContinuousMap A B) : Prop :=
  ∀ {X : A.Obj → Prop} {u z : A.Obj},
    A.IsUpperBound X u →
    A.IsLeastUpperBound X z →
    B.IsLeastUpperBound (image f X) (f z)

private theorem evalContinuous_preservesUpperBoundedLub
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (hL : BoundedComplete L)
    (x : K.Obj) :
    PreservesUpperBoundedLub (evalContinuous K L x) := by
  intro F u z hu hz
  let gx : L.Obj :=
    Classical.choose <|
      hL (Exponential.evalPred F x) ⟨u.toFun x, by
        intro a ha
        rcases ha with ⟨f, hf, rfl⟩
        exact (Exponential.rel_iff.mp (hu hf)) x⟩
  have hChosen :
      L.IsLeastUpperBound (Exponential.evalPred F x) gx :=
    Classical.choose_spec <|
      hL (Exponential.evalPred F x) ⟨u.toFun x, by
        intro a ha
        rcases ha with ⟨f, hf, rfl⟩
        exact (Exponential.rel_iff.mp (hu hf)) x⟩
  have hBounded :
      (Exponential.chpo K L).IsLeastUpperBound F (boundedSupMap hL F u hu) :=
    boundedSupMap_spec hL F u hu
  have hEqv :
      (Exponential.chpo K L).Rel (boundedSupMap hL F u hu) z ∧
        (Exponential.chpo K L).Rel z (boundedSupMap hL F u hu) :=
    equivalent_of_isLeastUpperBound
      (Exponential.chpo K L).toHomotopyPartialOrder
      hBounded
      hz
  constructor
  · intro a ha
    rcases ha with ⟨f, hf, rfl⟩
    exact (Exponential.rel_iff.mp (hz.1 hf)) x
  · intro w hw
    exact L.rel_trans
      ((Exponential.rel_iff.mp hEqv.2) x)
      (hChosen.2 hw)

private theorem precomposeContinuous_preservesUpperBoundedLub
    {A : CompleteHomotopyPartialOrder}
    {B : CompleteHomotopyPartialOrder}
    {C : CompleteHomotopyPartialOrder}
    (hC : BoundedComplete C)
    (f : ContinuousMap A B) :
    PreservesUpperBoundedLub (precomposeContinuous (M := C) f) := by
  intro F u z hu hz
  constructor
  · intro g hg
    rcases hg with ⟨h, hh, rfl⟩
    refine Exponential.rel_mk ?_
    intro x
    exact (Exponential.rel_iff.mp (hz.1 hh)) (f.toFun x)
  · intro w hw
    refine Exponential.rel_mk ?_
    intro x
    have hEval :=
      evalContinuous_preservesUpperBoundedLub (hL := hC) (f.toFun x)
        (X := F) (u := u) (z := z) hu hz
    exact hEval.2 (by
      intro a ha
      rcases ha with ⟨g, hg, rfl⟩
      exact (Exponential.rel_iff.mp (hw ⟨g, hg, rfl⟩)) x)

private theorem postcomposeContinuous_preservesUpperBoundedLub
    {A : CompleteHomotopyPartialOrder}
    {B : CompleteHomotopyPartialOrder}
    {C : CompleteHomotopyPartialOrder}
    (hB : BoundedComplete B)
    {g : ContinuousMap B C}
    (hg : PreservesUpperBoundedLub g) :
    PreservesUpperBoundedLub (postcomposeContinuous (K := A) g) := by
  intro F u z hu hz
  constructor
  · intro h hh
    rcases hh with ⟨f, hf, rfl⟩
    refine Exponential.rel_mk ?_
    intro x
    have hEval :=
      evalContinuous_preservesUpperBoundedLub (hL := hB) x
        (X := F) (u := u) (z := z) hu hz
    exact (hg
      (u := u.toFun x)
      (z := z.toFun x)
      (X := Exponential.evalPred F x)
      (by
        intro a ha
        rcases ha with ⟨f', hf', rfl⟩
        exact (Exponential.rel_iff.mp (hu hf')) x)
      (by simpa [Exponential.evalPred, evalContinuous] using hEval)).1
        ⟨f.toFun x, ⟨f, hf, rfl⟩, rfl⟩
  · intro w hw
    refine Exponential.rel_mk ?_
    intro x
    have hEval :=
      evalContinuous_preservesUpperBoundedLub (hL := hB) x
        (X := F) (u := u) (z := z) hu hz
    exact (hg
      (u := u.toFun x)
      (z := z.toFun x)
      (X := Exponential.evalPred F x)
      (by
        intro a ha
        rcases ha with ⟨f, hf, rfl⟩
        exact (Exponential.rel_iff.mp (hu hf)) x)
      (by simpa [Exponential.evalPred, evalContinuous] using hEval)).2 (by
        intro a ha
        rcases ha with ⟨b, hb, rfl⟩
        rcases hb with ⟨f, hf, rfl⟩
        exact (Exponential.rel_iff.mp (hw ⟨f, hf, rfl⟩)) x)

private theorem mapMinus_preservesUpperBoundedLub
    {A : CompleteHomotopyPartialOrder}
    {B : CompleteHomotopyPartialOrder}
    (hB : BoundedComplete B)
    (p : ProjectionPair A B)
    (hproj : PreservesUpperBoundedLub p.proj) :
    PreservesUpperBoundedLub (mapMinus p) := by
  intro F u z hu hz
  let G : (Exponential.chpo A B).Obj → Prop :=
    image (precomposeContinuous (M := B) p.emb) F
  have hUpperG :
      (Exponential.chpo A B).IsUpperBound G ((precomposeContinuous (M := B) p.emb).toFun u) := by
    intro g hg
    rcases hg with ⟨f, hf, rfl⟩
    exact (precomposeContinuous (M := B) p.emb).monotone' (hu hf)
  have hLubG :
      (Exponential.chpo A B).IsLeastUpperBound
        G
        ((precomposeContinuous (M := B) p.emb).toFun z) :=
    (precomposeContinuous_preservesUpperBoundedLub (hC := hB) p.emb) hu hz
  have hImageEq :
      ∀ h : (Exponential.chpo A A).Obj,
        image (postcomposeContinuous (K := A) p.proj) G h ↔
          image
            (fun f : (Exponential.chpo B B).Obj =>
              (postcomposeContinuous (K := A) p.proj).toFun
                ((precomposeContinuous (M := B) p.emb).toFun f))
            F h := by
    intro h
    constructor
    · intro hh
      rcases hh with ⟨g, hg, rfl⟩
      rcases hg with ⟨f, hf, rfl⟩
      exact ⟨f, hf, rfl⟩
    · intro hh
      rcases hh with ⟨f, hf, rfl⟩
      exact ⟨(precomposeContinuous (M := B) p.emb).toFun f, ⟨f, hf, rfl⟩, rfl⟩
  exact (isLeastUpperBound_congr
    (Exponential.chpo A A).toHomotopyPartialOrder
    hImageEq).mp <|
      (postcomposeContinuous_preservesUpperBoundedLub
        (hB := hB) (g := p.proj) hproj) hUpperG hLubG

private theorem fMinus_preservesUpperBoundedLub :
    ∀ n : Nat, PreservesUpperBoundedLub (fMinus n)
  | 0 => by
      simpa [fMinus, pair, initialPair, f0Minus] using
        (evalContinuous_preservesUpperBoundedLub
          (hL := stage_boundedComplete 0) bottom0)
  | n + 1 => by
      simpa [fMinus, pair, K] using
        (mapMinus_preservesUpperBoundedLub
          (hB := stage_boundedComplete (n + 1))
          (p := pair n)
          (fMinus_preservesUpperBoundedLub n))

/-- The inverse limit `K∞` is bounded complete: any upper-bounded family of
threads admits a least upper bound obtained coordinatewise from the finite
stages. -/
theorem kInfinity_boundedComplete : BoundedComplete KInfinityCHPO := by
  intro X hUpper
  rcases hUpper with ⟨u, hu⟩
  let zVal : ∀ n : Nat, (K n).Obj := fun n =>
    Classical.choose
      (stage_boundedComplete n (Projective.coordPred (S := system) X n) ⟨projectToLevel n u, by
        intro a ha
        rcases ha with ⟨x, hx, rfl⟩
        exact (Projective.rel_iff.mp (hu hx)) n⟩)
  let coordUpper : ∀ n : Nat,
      ∃ w : (K n).Obj, (K n).IsUpperBound (Projective.coordPred (S := system) X n) w :=
    fun n => ⟨projectToLevel n u, by
      intro a ha
      rcases ha with ⟨x, hx, rfl⟩
      exact (Projective.rel_iff.mp (hu hx)) n⟩
  let coordLub :
      ∀ n : Nat,
        (K n).IsLeastUpperBound
          (Projective.coordPred (S := system) X n)
          (Classical.choose (stage_boundedComplete n (Projective.coordPred (S := system) X n) (coordUpper n))) :=
    fun n => Classical.choose_spec
      (stage_boundedComplete n (Projective.coordPred (S := system) X n) (coordUpper n))
  let z : KInfinityCHPO.Obj := {
    val := zVal
    toPrev := by
      intro n
      let Yn : (K n).Obj → Prop := Projective.coordPred (S := system) X n
      let Yn1 : (K (n + 1)).Obj → Prop := Projective.coordPred (S := system) X (n + 1)
      have hImageLub :
          (K n).IsLeastUpperBound
            (image (fMinus n) Yn1)
            ((fMinus n).toFun (zVal (n + 1))) := by
        have hPres : PreservesUpperBoundedLub (fMinus n) :=
          fMinus_preservesUpperBoundedLub n
        exact hPres
          (X := Yn1)
          (u := projectToLevel (n + 1) u)
          (z := zVal (n + 1))
          (by
            intro a ha
            rcases ha with ⟨x, hx, rfl⟩
            exact (Projective.rel_iff.mp (hu hx)) (n + 1))
          (coordLub (n + 1))
      have hCoordLub :
          (K n).IsLeastUpperBound
            Yn
            ((fMinus n).toFun (zVal (n + 1))) := by
        constructor
        · intro a ha
          rcases ha with ⟨x, hx, rfl⟩
          exact (K n).rel_trans
            (x.fromPrev n)
            (hImageLub.1 ⟨x.val (n + 1), ⟨x, hx, rfl⟩, rfl⟩)
        · intro w hw
          refine hImageLub.2 ?_
          intro a ha
          rcases ha with ⟨b, hb, rfl⟩
          rcases hb with ⟨x, hx, rfl⟩
          exact (K n).rel_trans (x.toPrev n) (hw ⟨x, hx, rfl⟩)
      exact (equivalent_of_isLeastUpperBound
        (K n).toHomotopyPartialOrder
        hCoordLub
        (coordLub n)).1
    fromPrev := by
      intro n
      let Yn : (K n).Obj → Prop := Projective.coordPred (S := system) X n
      let Yn1 : (K (n + 1)).Obj → Prop := Projective.coordPred (S := system) X (n + 1)
      have hImageLub :
          (K n).IsLeastUpperBound
            (image (fMinus n) Yn1)
            ((fMinus n).toFun (zVal (n + 1))) := by
        have hPres : PreservesUpperBoundedLub (fMinus n) :=
          fMinus_preservesUpperBoundedLub n
        exact hPres
          (X := Yn1)
          (u := projectToLevel (n + 1) u)
          (z := zVal (n + 1))
          (by
            intro a ha
            rcases ha with ⟨x, hx, rfl⟩
            exact (Projective.rel_iff.mp (hu hx)) (n + 1))
          (coordLub (n + 1))
      have hCoordLub :
          (K n).IsLeastUpperBound
            Yn
            ((fMinus n).toFun (zVal (n + 1))) := by
        constructor
        · intro a ha
          rcases ha with ⟨x, hx, rfl⟩
          exact (K n).rel_trans
            (x.fromPrev n)
            (hImageLub.1 ⟨x.val (n + 1), ⟨x, hx, rfl⟩, rfl⟩)
        · intro w hw
          refine hImageLub.2 ?_
          intro a ha
          rcases ha with ⟨b, hb, rfl⟩
          rcases hb with ⟨x, hx, rfl⟩
          exact (K n).rel_trans (x.toPrev n) (hw ⟨x, hx, rfl⟩)
      exact (equivalent_of_isLeastUpperBound
        (K n).toHomotopyPartialOrder
        hCoordLub
        (coordLub n)).2
  }
  refine ⟨z, ?_⟩
  constructor
  · intro x hx
    exact Projective.rel_mk (S := system) (fun n =>
      (coordLub n).1 ⟨x, hx, rfl⟩)
  · intro w hw
    exact Projective.rel_mk (S := system) (fun n =>
      (coordLub n).2 (by
        intro a ha
        rcases ha with ⟨x, hx, rfl⟩
        exact (Projective.rel_iff.mp (hw hx)) n))

/-- Proposition 4.1 is now fully packaged at the inverse-limit level: `K∞`
itself is a Homotopy Scott Domain. -/
noncomputable def kInfinityScottDomain : HomotopyScottDomain where
  carrier := KInfinityCHPO
  algebraic := kInfinity_algebraic
  boundedComplete := kInfinity_boundedComplete

/-- Chosen-data packaging of the repository's current Proposition 4.2 interface:
uniform finite-stage approximants, their directedness, and the resulting least
upper bound statement. -/
structure Proposition42Witness where
  approximation : Nat → KInfinityCHPO.Obj → KInfinityCHPO.Obj
  exactStage :
    ∀ n : Nat, ∀ x : KInfinityCHPO.Obj,
      projectToLevel n (approximation n x) = projectToLevel n x
  exactStageLe :
    ∀ {m n : Nat}, m ≤ n → ∀ x : KInfinityCHPO.Obj,
      projectToLevel m (approximation n x) = projectToLevel m x
  stableStage :
    ∀ {m n : Nat}, m ≤ n → ∀ x : KInfinityCHPO.Obj,
      approximation m (approximation n x) = approximation m x
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
  exactStageLe := by
    intro m n hmn x
    exact proposition_4_2_stageApproximation_exact_le hmn x
  stableStage := by
    intro m n hmn x
    exact proposition_4_2_stageApproximation_stable hmn x
  belowTarget := proposition_4_2_stageApproximation_below
  monotoneStage := by
    intro n m h x
    exact proposition_4_2_stageApproximation_mono h x
  directedFamily := proposition_4_2_stageApproximationPred_directed
  isLub := proposition_4_2_stageApproximation_isLub
  chosenSupEquiv := proposition_4_2_stageApproximation_sup_equiv

/-- Proposition 4.1 in the repository's chosen-data style: stagewise Scott
domain data, inverse-limit approximants, and the final algebraic and
bounded-complete witnesses showing that `K∞` itself is a Homotopy Scott
Domain. -/
noncomputable def proposition_4_1 : Proposition41Witness where
  stageBoundedComplete := stage_boundedComplete
  coordinateProjection := projectContinuous
  finiteStageEmbedding := embedFiniteStageContinuous
  baseApproximation := proposition_4_2_approximation
  baseApproximation_finite := by
    intro x
    refine ⟨projectToLevel 0 x, rfl⟩
  baseApproximation_compact := proposition_4_1_baseApprox_compact
  baseApproximation_below := proposition_4_1_baseApprox_below
  baseApproximation_exact0 := proposition_4_2
  baseApproximation_isLub := proposition_4_1_baseApproximation_isLub
  stageZeroAlgebraic := stage_algebraic_zero
  stageOneAlgebraic := stage_algebraic_one
  stageTwoAlgebraic := stage_algebraic_two
  allFiniteStagesAlgebraic := stage_algebraic
  kInfinityAlgebraic := kInfinity_algebraic
  kInfinityBoundedComplete := kInfinity_boundedComplete
  baseChainCompact := baseUp_compact
  successorStageStepCompact := by
    intro n a b ha hb
    exact stage_stepFunction_compact n ha hb
  finiteStageApproximation := proposition_4_2_stageApproximation
  finiteStageApproximation_exact := proposition_4_2_stageApproximation_exact
  finiteStageApproximation_exact_le := by
    intro m n hmn x
    exact proposition_4_2_stageApproximation_exact_le hmn x
  finiteStageApproximation_stable := by
    intro m n hmn x
    exact proposition_4_2_stageApproximation_stable hmn x
  finiteStageCompactBelow_lift := proposition_4_1_stageCompactBelow_lift
  finiteStageApproximation_compact_of_stageCompact :=
    proposition_4_2_stageApproximation_compact_of_stageCompact
  finiteStageApproximation_isLub_of_stageAlgebraic := by
    intro n hAlg x
    simpa using proposition_4_1_stageApproximation_isLub_of_stageAlgebraic n hAlg x
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

/-- Finite-stage section shadow for the global `k`/`h` candidates. Although the
full reverse equation `k ∘ h = id` on the continuous function space is still
open, every finite-stage restriction is already recovered exactly. -/
theorem kInfinityContinuous_hInfinityContinuous_restrict
    (n : Nat) (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj) :
    restrictEndomapToStageContinuous (genericStageEmbedding n)
      (kInfinityContinuous (hInfinityContinuous g)) =
        restrictEndomapToStageContinuous (genericStageEmbedding n) g := by
  rw [restrictEndomapToStage_kInfinityContinuous]
  simpa [hInfinityContinuous] using project_hInfinity_succ n g

/-- Evaluating the finite-stage section shadow on the canonical stage embedding
recovers the original endomap exactly at that stage. -/
theorem kInfinityContinuous_hInfinityContinuous_restrict_apply
    (n : Nat) (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj)
    (x : (K n).Obj) :
    projectToLevel n
        ((kInfinityContinuous (hInfinityContinuous g)).toFun
          (embedFiniteStageToLimit n x)) =
      projectToLevel n (g.toFun (embedFiniteStageToLimit n x)) := by
  have h :=
    congrArg
      (fun f : ContinuousMap (K n) (K n) => f.toFun x)
      (kInfinityContinuous_hInfinityContinuous_restrict n g)
  simpa [genericStageEmbedding, embedFiniteStageContinuous,
    restrictEndomapToStageContinuous_apply] using h

private theorem genericLevelCoords_rebase
    {n m : Nat} (hnm : n ≤ m) (x : (K n).Obj) :
    ∀ k : Nat,
      genericLevelCoords m (projectToLevel m (embedFiniteStageToLimit n x)) k =
        genericLevelCoords n x k := by
  intro k
  induction k with
  | zero =>
      have hk : 0 ≤ m := Nat.zero_le m
      rw [genericLevelCoords_below m
        (projectToLevel m (embedFiniteStageToLimit n x)) hk]
      change
        projectDown m (projectToLevel m (embedFiniteStageToLimit n x)) 0 hk =
          projectToLevel 0 (embedFiniteStageToLimit n x)
      apply stage_antisymmetric 0
      · simpa using projectDown_thread (embedFiniteStageToLimit n x) m hk
      · simpa using thread_projectDown (embedFiniteStageToLimit n x) m hk
  | succ k ih =>
      by_cases hk : k + 1 ≤ m
      · rw [genericLevelCoords_below m
          (projectToLevel m (embedFiniteStageToLimit n x)) hk]
        change
          projectDown m (projectToLevel m (embedFiniteStageToLimit n x)) (k + 1) hk =
            projectToLevel (k + 1) (embedFiniteStageToLimit n x)
        apply stage_antisymmetric (k + 1)
        · simpa using projectDown_thread (embedFiniteStageToLimit n x) m hk
        · simpa using thread_projectDown (embedFiniteStageToLimit n x) m hk
      · have hkn : ¬ k + 1 ≤ n := by omega
        rw [genericLevelCoords_above m
          (projectToLevel m (embedFiniteStageToLimit n x)) (m := k) hk]
        rw [genericLevelCoords_above n x (m := k) hkn]
        simpa using congrArg (fun z => (fPlus k).toFun z) ih

private theorem embedFiniteStageToLimit_rebase
    {n m : Nat} (hnm : n ≤ m) (x : (K n).Obj) :
    embedFiniteStageToLimit m (projectToLevel m (embedFiniteStageToLimit n x)) =
      embedFiniteStageToLimit n x := by
  apply Projective.Thread.ext
  intro k
  simpa [projectToLevel] using genericLevelCoords_rebase hnm x k

private theorem kInfinityContinuous_hInfinityContinuous_onStage
    (n : Nat) (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj)
    (x : (K n).Obj) :
    (kInfinityContinuous (hInfinityContinuous g)).toFun (embedFiniteStageToLimit n x) =
      g.toFun (embedFiniteStageToLimit n x) := by
  apply Projective.Thread.ext
  intro m
  by_cases hmn : m ≤ n
  · let lhs :=
      (kInfinityContinuous (hInfinityContinuous g)).toFun
        (embedFiniteStageToLimit n x)
    let rhs := g.toFun (embedFiniteStageToLimit n x)
    have hTop :
        projectToLevel n lhs = projectToLevel n rhs := by
      simpa [lhs, rhs] using
        kInfinityContinuous_hInfinityContinuous_restrict_apply n g x
    apply stage_antisymmetric m
    · exact (K m).rel_trans
        (thread_projectDown lhs n hmn)
        (by simpa [hTop] using projectDown_thread rhs n hmn)
    · exact (K m).rel_trans
        (thread_projectDown rhs n hmn)
        (by simpa [hTop] using projectDown_thread lhs n hmn)
  · have hnm' : n ≤ m := by omega
    let y : (K m).Obj := projectToLevel m (embedFiniteStageToLimit n x)
    have hRebase :
        embedFiniteStageToLimit m y = embedFiniteStageToLimit n x := by
      simpa [y] using embedFiniteStageToLimit_rebase hnm' x
    simpa [y, hRebase] using
      kInfinityContinuous_hInfinityContinuous_restrict_apply m g y

/-- The completed global `K∞` reflection/reification pair also satisfies the
reverse section law on the continuous function space. -/
theorem kInfinityContinuous_hInfinityContinuous_apply
    (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj) :
    kInfinityContinuous (hInfinityContinuous g) = g := by
  apply ContinuousMap.ext
  intro x
  let f : ContinuousMap KInfinityCHPO KInfinityCHPO :=
    kInfinityContinuous (hInfinityContinuous g)
  let X : KInfinityCHPO.Obj → Prop := kInfinityCompactApproxPred x
  have hDir : KInfinityCHPO.Directed X :=
    kInfinityCompactApproxPred_directed x
  have hChosen :
      KInfinityCHPO.IsLeastUpperBound X (KInfinityCHPO.sup X hDir) :=
    KInfinityCHPO.sup_spec X hDir
  have hExact :
      KInfinityCHPO.IsLeastUpperBound X x :=
    kInfinityCompactApproxPred_isLub x
  have hEqv :
      KInfinityCHPO.Rel (KInfinityCHPO.sup X hDir) x ∧
        KInfinityCHPO.Rel x (KInfinityCHPO.sup X hDir) :=
    equivalent_of_isLeastUpperBound
      KInfinityCHPO.toHomotopyPartialOrder
      hChosen
      hExact
  have hLubF :
      KInfinityCHPO.IsLeastUpperBound (image f.toFun X) (f.toFun x) :=
    isLeastUpperBound_of_equiv
      KInfinityCHPO.toHomotopyPartialOrder
      (f.preserves_sup X hDir)
      (f.monotone' hEqv.1)
      (f.monotone' hEqv.2)
  have hLubG :
      KInfinityCHPO.IsLeastUpperBound (image g.toFun X) (g.toFun x) :=
    isLeastUpperBound_of_equiv
      KInfinityCHPO.toHomotopyPartialOrder
      (g.preserves_sup X hDir)
      (g.monotone' hEqv.1)
      (g.monotone' hEqv.2)
  have hImageEq :
      ∀ y : KInfinityCHPO.Obj, image f.toFun X y ↔ image g.toFun X y := by
    intro y
    constructor <;> intro hy
    · rcases hy with ⟨z, hz, rfl⟩
      rcases hz with ⟨n, a, ha, rfl⟩
      exact ⟨embedFiniteStageToLimit n a, ⟨n, a, ha, rfl⟩,
        (kInfinityContinuous_hInfinityContinuous_onStage n g a).symm⟩
    · rcases hy with ⟨z, hz, rfl⟩
      rcases hz with ⟨n, a, ha, rfl⟩
      exact ⟨embedFiniteStageToLimit n a, ⟨n, a, ha, rfl⟩,
        kInfinityContinuous_hInfinityContinuous_onStage n g a⟩
  have hLubG' :
      KInfinityCHPO.IsLeastUpperBound (image f.toFun X) (g.toFun x) :=
    (isLeastUpperBound_congr
      KInfinityCHPO.toHomotopyPartialOrder hImageEq).mpr hLubG
  have hOutEqv :
      KInfinityCHPO.Rel (f.toFun x) (g.toFun x) ∧
        KInfinityCHPO.Rel (g.toFun x) (f.toFun x) :=
    equivalent_of_isLeastUpperBound
      KInfinityCHPO.toHomotopyPartialOrder
      hLubF
      hLubG'
  apply Projective.Thread.ext
  intro n
  exact stage_antisymmetric n
    ((Projective.rel_iff.mp hOutEqv.1) n)
    ((Projective.rel_iff.mp hOutEqv.2) n)

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
  globalSection_restrict :
    ∀ (n : Nat) (g : (Exponential.chpo KInfinityCHPO KInfinityCHPO).Obj),
      restrictEndomapToStageContinuous (genericStageEmbedding n)
        (globalReflect (globalReify g)) =
          restrictEndomapToStageContinuous (genericStageEmbedding n) g
  globalSection :
    ContinuousMap.comp globalReflect globalReify =
      ContinuousMap.id (Exponential.chpo KInfinityCHPO KInfinityCHPO)
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
  globalSection_restrict := kInfinityContinuous_hInfinityContinuous_restrict
  globalSection := by
    ext g
    exact kInfinityContinuous_hInfinityContinuous_apply g
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

/-- The base object at the source boundary of a packed cell in the recursively
completed `K∞` tower. -/
def kInfinityTowerSourceObj :
    {n : Nat} → kInfinityTower.Cell n → KInfinityCHPO.Obj
  | 0, x => x.down
  | _ + 1, x => kInfinityTowerSourceObj (kInfinityTower.source x)

/-- The base object at the target boundary of a packed cell in the recursively
completed `K∞` tower. -/
def kInfinityTowerTargetObj :
    {n : Nat} → kInfinityTower.Cell n → KInfinityCHPO.Obj
  | 0, x => x.down
  | _ + 1, x => kInfinityTowerTargetObj (kInfinityTower.target x)

/-- Every packed cell in the recursively completed `K∞` tower of dimension `≥ 5`
already has equal 0-source and 0-target, because above dimension `5` the tower
is built by iterated identities. -/
theorem kInfinityTower_source_eq_target
    {n : Nat} (x : kInfinityTower.Cell (n + 5)) :
    kInfinityTowerSourceObj x = kInfinityTowerTargetObj x := by
  induction n with
  | zero =>
      rcases x with ⟨M, N, p, q, α, β, η, θ, ω, ξ, μ⟩
      exact p.down.down
  | succ n ih =>
      rcases x with ⟨x, y, hxy⟩
      change kInfinityTowerSourceObj x = kInfinityTowerTargetObj y
      have hxy' : x = y := hxy.down
      calc
        kInfinityTowerSourceObj x = kInfinityTowerTargetObj x := ih x
        _ = kInfinityTowerTargetObj y := congrArg kInfinityTowerTargetObj hxy'

/-- In the recursively completed all-dimensional `K∞` tower, no cell of
dimension `≥ 5` can have the chosen β-side point as its 0-source and the chosen
η-side point as its 0-target. Above dimension `5`, every higher cell is an
iterated identity between lower cells, so the explicit 5-cell separation forces
all higher boundary instances to be empty as well. -/
theorem example_4_2_no_recursive_higher_cell
    {n : Nat} {x : kInfinityTower.Cell (n + 5)}
    (hs : kInfinityTowerSourceObj x = interp1Beta)
    (ht : kInfinityTowerTargetObj x = interp1Eta) :
    False := by
  have hEq : interp1Beta = interp1Eta := by
    calc
      interp1Beta = kInfinityTowerSourceObj x := hs.symm
      _ = kInfinityTowerTargetObj x := kInfinityTower_source_eq_target x
      _ = interp1Eta := ht
  exact example_4_2 hEq

/-- Equivalently, the recursively completed all-dimensional `K∞` tower has no
packed higher cell of dimension `≥ 5` whose 0-source/0-target boundary is the
chosen β/η pair from Example 4.2. -/
theorem example_4_2_no_recursive_higher_cell_nonempty (n : Nat) :
    ¬ Nonempty
      {x : kInfinityTower.Cell (n + 5) //
        kInfinityTowerSourceObj x = interp1Beta ∧
          kInfinityTowerTargetObj x = interp1Eta} := by
  intro h
  rcases h with ⟨⟨x, hs, ht⟩⟩
  exact example_4_2_no_recursive_higher_cell hs ht

/-- Chosen-data packaging of the repository's current paper-facing closure
around Proposition 4.4 and Example 4.2. It combines the concrete non-trivial
homotopy λ-model witness with the distinguished β/η points and the entire
currently formalized separation suite between them. -/
structure Proposition44Example42Witness where
  model : NonTrivialHomotopyLambdaModel
  etaPoint : KInfinityCHPO.Obj
  betaPoint : KInfinityCHPO.Obj
  etaPoint_level0 : projectToLevel 0 etaPoint = some s1Left
  betaPoint_level0 : projectToLevel 0 betaPoint = some s1Right
  distinct : betaPoint ≠ etaPoint
  noPath : ¬ Nonempty (KInfinityPath betaPoint etaPoint)
  noPath2 :
    ∀ {p q : KInfinityPath betaPoint etaPoint},
      ¬ Nonempty (KInfinityPath2 p q)
  noPath3 :
    ∀ {p q : KInfinityPath betaPoint etaPoint}
      {α β : KInfinityPath2 p q},
      ¬ Nonempty (KInfinityPath3 α β)
  noPath4 :
    ∀ {p q : KInfinityPath betaPoint etaPoint}
      {α β : KInfinityPath2 p q} {η θ : KInfinityPath3 α β},
      ¬ Nonempty (KInfinityPath4 η θ)
  noPath5 :
    ∀ {p q : KInfinityPath betaPoint etaPoint}
      {α β : KInfinityPath2 p q} {η θ : KInfinityPath3 α β}
      {ω ξ : KInfinityPath4 η θ},
      ¬ Nonempty (KInfinityPath5 ω ξ)
  noRecursiveHigherCell :
    ∀ n : Nat,
      ¬ Nonempty
        {x : kInfinityTower.Cell (n + 5) //
          kInfinityTowerSourceObj x = betaPoint ∧
            kInfinityTowerTargetObj x = etaPoint}

/-- Proposition 4.4 together with the full currently formalized Example 4.2
separation suite. This is the repository's strongest honest Section 4 package:
the concrete `K∞` model is fully reflexive and non-trivial, and the chosen β/η
pair is separated through the explicit 1/2/3/4/5-cell hierarchy and the
recursively completed all-dimensional tower. -/
noncomputable def proposition_4_4_example_4_2 :
    Proposition44Example42Witness where
  model := proposition_4_4_model
  etaPoint := interp1Eta
  betaPoint := interp1Beta
  etaPoint_level0 := interp1Eta_level0
  betaPoint_level0 := interp1Beta_level0
  distinct := example_4_2
  noPath := example_4_2_not_connected
  noPath2 := by
    intro p q h
    rcases h with ⟨α⟩
    exact example_4_2_no_path2 α
  noPath3 := by
    intro p q α β h
    rcases h with ⟨η⟩
    exact example_4_2_no_path3 η
  noPath4 := by
    intro p q α β η θ h
    rcases h with ⟨ω⟩
    exact example_4_2_no_path4 ω
  noPath5 := by
    intro p q α β η θ ω ξ h
    rcases h with ⟨μ⟩
    exact example_4_2_no_path5 μ
  noRecursiveHigherCell := example_4_2_no_recursive_higher_cell_nonempty

end HigherLambdaModel.KInfinity
