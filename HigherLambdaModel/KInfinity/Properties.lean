import HigherLambdaModel.KInfinity.Construction

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
per-stage bounded-completeness data and coordinate projections, the witness now
contains a concrete compact finite approximation of each inverse-limit thread:
the canonical embedding of its level-zero coordinate. -/
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

/-- Proposition 4.1 in the repository's current chosen-data style: bounded
completeness of each stage, continuity of the coordinate projections, and a
concrete compact finite approximation of every point of `K∞`. -/
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

/-- Remark 4.3: the chosen application operation on `K∞`. -/
noncomputable def application
    (x y : KInfinityCHPO.Obj) :
    KInfinityCHPO.Obj :=
  kBase x y

/-- Remark 4.3 at the base coordinate. -/
theorem remark_4_3 (x y : KInfinityCHPO.Obj) :
    projectToLevel 0 (application x y) =
      ((projectToLevel 1 x).toFun (projectToLevel 0 y)) := by
  simpa [application] using proposition_4_3 x y

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
      simpa [x] using project_embedBase_self (x := some ⟨n - 1, false⟩)
    have hGroup : TypeNontrivial (sphereHomotopyGroup n ⟨n - 1, false⟩) := by
      rw [sphereHomotopyGroup, hEq, hpred']
      simpa using bool_typeNontrivial
    simpa [KInfinityKanComplex, piN, hx0] using hGroup
  · intro x hx
    rcases hx with ⟨a, ha⟩
    refine ⟨a.dim.succ, by omega, ?_⟩
    simpa [KInfinityKanComplex, piN, ha] using kInfinitySphereGroup_nontrivial_at_dim a

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
  simpa [interp1Eta] using project_embedBase_self (x := some s1Left)

@[simp] theorem interp1Beta_level0 :
    projectToLevel 0 interp1Beta = some s1Right := by
  simpa [interp1Beta] using project_embedBase_self (x := some s1Right)

/-- Example 4.2: the chosen β/η interpretations are distinct in `K∞`. -/
theorem example_4_2 : interp1Beta ≠ interp1Eta := by
  intro h
  have h0 := congrArg (projectToLevel 0) h
  have hPoint : s1Right = s1Left := by
    injection h0 with hPoint
  have hPole : true = false := by
    simpa [s1Left, s1Right] using congrArg SpherePoint.pole hPoint
  cases hPole

end HigherLambdaModel.KInfinity
