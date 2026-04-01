import HigherLambdaModel.KInfinity.NonTrivial

/-!
# The `K∞` Construction

This file specializes the generic c.h.p.o. constructions of Section 3 to the
tower used in Section 4 of Martínez-Rivillas and de Queiroz,
*The K∞ Homotopy λ-Model*.

As in the rest of the repository, the development is recorded in chosen-data
form: the tower `K₀, K₁, ...`, the initial h-projection pair, the recursive
projection pairs, and the associated strict projective system are all given by
explicit continuous maps.
-/

namespace HigherLambdaModel.KInfinity

open Classical
open HigherLambdaModel.Domain
open HigherLambdaModel.Lambda.HomotopyOrder

universe u

/-! ## Definition 4.5: the tower `K₀, K₁, ...` -/

/-- Definition 4.5: the Section 4 tower with `K₀ = N⁺` and
`Kₙ₊₁ = [Kₙ → Kₙ]`. -/
noncomputable def K : Nat → CompleteHomotopyPartialOrder
  | 0 => NPlus
  | n + 1 => Exponential.chpo (K n) (K n)

/-- The base object `K₀ = N⁺`. -/
noncomputable abbrev K0 : CompleteHomotopyPartialOrder := K 0

/-- Definition 4.5 at level zero. -/
@[simp] theorem K_zero : K 0 = NPlus := rfl

/-- Definition 4.5 at successor stages. -/
@[simp] theorem K_succ (n : Nat) :
    K (n + 1) = Exponential.chpo (K n) (K n) := rfl

/-- The distinguished bottom element `⊥ₙ` of `Kₙ`. -/
noncomputable abbrev bottomAt (n : Nat) : (K n).Obj := (K n).bottom

/-! ## Explicit h-projection pairs for c.h.p.o.'s -/

/-- A chosen h-projection pair between c.h.p.o.'s, specialized to the
order-theoretic setting used for the `Kₙ` tower. The inequality field records
the h-projection-pair section inequality pointwise in the codomain relation. -/
structure ProjectionPair
    (A : CompleteHomotopyPartialOrder)
    (B : CompleteHomotopyPartialOrder) where
  emb : ContinuousMap A B
  proj : ContinuousMap B A
  retract : ContinuousMap.comp proj emb = ContinuousMap.id A
  section_le : ∀ x : B.Obj, B.Rel (emb (proj x)) x
  emb_strict : emb A.bottom = B.bottom
  proj_strict : proj B.bottom = A.bottom

/-- The h-embedding carried by a Section 4 projection pair. -/
abbrev ProjectionPair.plus
    {A : CompleteHomotopyPartialOrder}
    {B : CompleteHomotopyPartialOrder}
    (p : ProjectionPair A B) :
    ContinuousMap A B :=
  p.emb

/-- The h-projection carried by a Section 4 projection pair. -/
abbrev ProjectionPair.minus
    {A : CompleteHomotopyPartialOrder}
    {B : CompleteHomotopyPartialOrder}
    (p : ProjectionPair A B) :
    ContinuousMap B A :=
  p.proj

/-! ## Definition 4.6: the initial pair `(f₀⁺, f₀⁻)` -/

/-- Definition 4.6(a): `f₀⁺(x)` is the constant map with value `x`. This
chooses the reflexive edge `x ⟶ x` for the paper's `x'`. -/
noncomputable def f0Plus : ContinuousMap (K 0) (K 1) :=
  curry (fstContinuous (K 0) (K 0))

/-- Definition 4.6(b): `f₀⁻(g) = g(⊥₀)`. -/
noncomputable def f0Minus : ContinuousMap (K 1) (K 0) :=
  evalContinuous (K 0) (K 0) bottom0

@[simp] theorem f0Plus_apply (x y : (K 0).Obj) :
    (f0Plus.toFun x).toFun y = x := rfl

@[simp] theorem f0Minus_apply (g : (K 1).Obj) :
    f0Minus.toFun g = g.toFun bottom0 := rfl

/-- Definition 4.6 packaged as a Section 4 projection pair. -/
noncomputable def initialPair : ProjectionPair (K 0) (K 1) where
  emb := f0Plus
  proj := f0Minus
  retract := by
    apply ContinuousMap.ext
    intro x
    rfl
  section_le := by
    intro g
    refine Exponential.rel_mk ?_
    intro y
    simpa [f0Plus, f0Minus] using g.monotone' ((K 0).bottom_le y)
  emb_strict := by
    apply ContinuousMap.ext
    intro y
    rfl
  proj_strict := by
    rfl

/-! ## Definition 4.7: recursive projection pairs -/

/-- The Section 4 action of the self-exponential functor on h-embeddings:
`h ↦ f⁺ ∘ h ∘ f⁻`. -/
noncomputable def mapPlus
    {A : CompleteHomotopyPartialOrder}
    {B : CompleteHomotopyPartialOrder}
    (p : ProjectionPair A B) :
    ContinuousMap (Exponential.chpo A A) (Exponential.chpo B B) :=
  ContinuousMap.comp (postcomposeContinuous p.emb) (precomposeContinuous p.proj)

/-- The Section 4 action of the self-exponential functor on h-projections:
`h ↦ f⁻ ∘ h ∘ f⁺`. -/
noncomputable def mapMinus
    {A : CompleteHomotopyPartialOrder}
    {B : CompleteHomotopyPartialOrder}
    (p : ProjectionPair A B) :
    ContinuousMap (Exponential.chpo B B) (Exponential.chpo A A) :=
  ContinuousMap.comp (postcomposeContinuous p.proj) (precomposeContinuous p.emb)

@[simp] theorem mapPlus_apply
    {A : CompleteHomotopyPartialOrder}
    {B : CompleteHomotopyPartialOrder}
    (p : ProjectionPair A B)
    (h : ContinuousMap A A)
    (x : B.Obj) :
    ((mapPlus p).toFun h).toFun x = p.emb.toFun (h.toFun (p.proj.toFun x)) := rfl

@[simp] theorem mapMinus_apply
    {A : CompleteHomotopyPartialOrder}
    {B : CompleteHomotopyPartialOrder}
    (p : ProjectionPair A B)
    (h : ContinuousMap B B)
    (x : A.Obj) :
    ((mapMinus p).toFun h).toFun x = p.proj.toFun (h.toFun (p.emb.toFun x)) := rfl

/-- Definition 4.7: the recursive action on projection pairs. -/
noncomputable def mapPair
    {A : CompleteHomotopyPartialOrder}
    {B : CompleteHomotopyPartialOrder}
    (p : ProjectionPair A B) :
    ProjectionPair (Exponential.chpo A A) (Exponential.chpo B B) where
  emb := mapPlus p
  proj := mapMinus p
  retract := by
    apply ContinuousMap.ext
    intro h
    apply ContinuousMap.ext
    intro x
    have h₁ :
        p.proj.toFun (p.emb.toFun x) = x := by
      simpa [ContinuousMap.comp] using congrArg (fun g => g.toFun x) p.retract
    have h₂ :
        p.proj.toFun (p.emb.toFun (h.toFun x)) = h.toFun x := by
      simpa [ContinuousMap.comp] using congrArg (fun g => g.toFun (h.toFun x)) p.retract
    calc
      (((mapMinus p).toFun ((mapPlus p).toFun h)).toFun x)
          = p.proj.toFun (p.emb.toFun (h.toFun (p.proj.toFun (p.emb.toFun x)))) := by
              rfl
      _ = p.proj.toFun (p.emb.toFun (h.toFun x)) := by rw [h₁]
      _ = h.toFun x := h₂
  section_le := by
    intro g
    refine Exponential.rel_mk ?_
    intro x
    have hSection :
        B.Rel
          (p.emb.toFun (p.proj.toFun (g.toFun (p.emb.toFun (p.proj.toFun x)))))
          (g.toFun (p.emb.toFun (p.proj.toFun x))) :=
      p.section_le (g.toFun (p.emb.toFun (p.proj.toFun x)))
    have hMonotone :
        B.Rel (g.toFun (p.emb.toFun (p.proj.toFun x))) (g.toFun x) :=
      g.monotone' (p.section_le x)
    exact B.rel_trans hSection hMonotone
  emb_strict := by
    apply ContinuousMap.ext
    intro x
    calc
      (((mapPlus p).toFun (Exponential.chpo A A).bottom).toFun x)
          = p.emb.toFun (((Exponential.chpo A A).bottom).toFun (p.proj.toFun x)) := by
              rfl
      _ = p.emb.toFun A.bottom := by
            rfl
      _ = B.bottom := by
            rw [p.emb_strict]
      _ = ((Exponential.chpo B B).bottom).toFun x := by
            rfl
  proj_strict := by
    apply ContinuousMap.ext
    intro x
    calc
      (((mapMinus p).toFun (Exponential.chpo B B).bottom).toFun x)
          = p.proj.toFun (((Exponential.chpo B B).bottom).toFun (p.emb.toFun x)) := by
              rfl
      _ = p.proj.toFun B.bottom := by
            rfl
      _ = A.bottom := by
            rw [p.proj_strict]
      _ = ((Exponential.chpo A A).bottom).toFun x := by
            rfl

/-- Definition 4.7: the projection pair from `Kₙ` to `Kₙ₊₁`. -/
noncomputable def pair : (n : Nat) → ProjectionPair (K n) (K (n + 1))
  | 0 => initialPair
  | n + 1 => by
      simpa [K] using mapPair (pair n)

/-- The recursive h-embeddings `fₙ⁺`. -/
noncomputable def fPlus (n : Nat) : ContinuousMap (K n) (K (n + 1)) :=
  (pair n).emb

/-- The recursive h-projections `fₙ⁻`. -/
noncomputable def fMinus (n : Nat) : ContinuousMap (K (n + 1)) (K n) :=
  (pair n).proj

@[simp] theorem fMinus_comp_fPlus (n : Nat) :
    ContinuousMap.comp (fMinus n) (fPlus n) = ContinuousMap.id (K n) :=
  (pair n).retract

theorem fPlus_fMinus_le (n : Nat) (x : (K (n + 1)).Obj) :
    (K (n + 1)).Rel (fPlus n (fMinus n x)) x :=
  (pair n).section_le x

@[simp] theorem fPlus_strict (n : Nat) :
    fPlus n ((K n).bottom) = (K (n + 1)).bottom :=
  (pair n).emb_strict

@[simp] theorem fMinus_strict_eq (n : Nat) :
    fMinus n ((K (n + 1)).bottom) = (K n).bottom :=
  (pair n).proj_strict

@[simp] theorem fPlus_zero_apply' (x y : (K 0).Obj) :
    ((fPlus 0).toFun x).toFun y = x := rfl

@[simp] theorem fMinus_zero_apply' (g : (K 1).Obj) :
    fMinus 0 g = g.toFun bottom0 := rfl

@[simp] theorem fPlus_succ_apply
    (n : Nat) (h : (K (n + 1)).Obj) (x : (K (n + 1)).Obj) :
    ((fPlus (n + 1)).toFun h).toFun x =
      (fPlus n).toFun (h.toFun ((fMinus n).toFun x)) := rfl

@[simp] theorem fMinus_succ_apply
    (n : Nat) (h : (K (n + 2)).Obj) (x : (K n).Obj) :
    ((fMinus (n + 1)).toFun h).toFun x =
      (fMinus n).toFun (h.toFun ((fPlus n).toFun x)) := rfl

/-! ## Remark 4.2: the inverse limit `K∞` -/

/-- The strict inverse system `(Kₙ, fₙ⁻)` of Remark 4.2. -/
noncomputable def system : Projective.System where
  obj := K
  map := fMinus
  strict := by
    intro n
    rw [fMinus_strict_eq]
    exact (K n).rel_refl ((K n).bottom)

/-- Remark 4.2: the c.h.p.o. inverse limit `K∞ = lim (Kₙ, fₙ⁻)`. -/
noncomputable abbrev KInfinityCHPO : CompleteHomotopyPartialOrder :=
  Projective.KInfinity system

/-- The underlying threads of the inverse limit. -/
abbrev Thread := Projective.Thread system

/-- The coordinate projection `f∞,ₙ(x) = xₙ`. -/
abbrev projectToLevel (n : Nat) (x : KInfinityCHPO.Obj) : (K n).Obj :=
  x.val n

/-- The `n`-th coordinate map from `K∞` to `Kₙ` is continuous. -/
noncomputable def projectContinuous (n : Nat) :
    ContinuousMap KInfinityCHPO (K n) where
  toFun := fun x => x.val n
  monotone' := by
    intro x y hxy
    exact (Projective.rel_iff.mp hxy) n
  preserves_sup := by
    intro X hX
    let Y : (K n).Obj → Prop := Projective.coordPred X n
    have hY : (K n).Directed Y := Projective.directed_coord hX n
    have hImage :
        image (fun x : KInfinityCHPO.Obj => x.val n) X = Y := by
      funext a
      apply propext
      constructor <;> intro ha <;> simpa [Y, Projective.coordPred] using ha
    simpa [KInfinityCHPO, Projective.limit, Y, hImage] using (K n).sup_spec Y hY

/-- The raw value of the projective-limit bottom thread. -/
@[simp] theorem project_bottom (n : Nat) :
    projectToLevel n (KInfinityCHPO.bottom) = (K n).bottom := rfl

/-! ## Levelwise Embeddings into the Limit -/

private def castLevel
    {n m : Nat}
    (h : n = m) :
    (K n).Obj → (K m).Obj := by
  subst h
  exact fun x => x

@[simp] private theorem castLevel_rfl
    {n : Nat} (x : (K n).Obj) :
    castLevel rfl x = x := rfl

/-- Repeated application of the h-embeddings `fₙ⁺`. -/
noncomputable def projectUp
    (n : Nat) (x : (K n).Obj) :
    (k : Nat) → (K (n + k)).Obj
  | 0 => by
      simpa using x
  | k + 1 => by
      simpa [Nat.add_assoc] using (fPlus (n + k)).toFun (projectUp n x k)

@[simp] theorem projectUp_zero
    (n : Nat) (x : (K n).Obj) :
    projectUp n x 0 = x := by
  rfl

@[simp] theorem projectUp_succ
    (n : Nat) (x : (K n).Obj) (k : Nat) :
    projectUp n x (k + 1) = (fPlus (n + k)).toFun (projectUp n x k) := by
  simpa [projectUp, Nat.add_assoc]

/-- Repeated application of the h-projections `fₙ⁻`. -/
noncomputable def projectDown
    (n : Nat) (x : (K n).Obj) :
    (m : Nat) → m ≤ n → (K m).Obj
  | m, hm =>
      if hmn : m = n then
        castLevel hmn.symm x
      else
        have hm' : m + 1 ≤ n := by omega
        (fMinus m).toFun (projectDown n x (m + 1) hm')
termination_by m hm => n - m
decreasing_by
  omega

@[simp] theorem projectDown_self
    (n : Nat) (x : (K n).Obj) :
    projectDown n x n (Nat.le_refl n) = x := by
  simp [projectDown]

theorem projectDown_step
    (n : Nat) (x : (K n).Obj)
    {m : Nat} (_hm : m < n) :
    projectDown n x m (by omega) =
      (fMinus m).toFun (projectDown n x (m + 1) (by omega)) := by
  have hmn : m ≠ n := by omega
  conv =>
    lhs
    unfold projectDown
  simp [hmn]

end HigherLambdaModel.KInfinity
