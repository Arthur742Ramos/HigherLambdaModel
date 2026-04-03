import HigherLambdaModel.Domain
import HigherLambdaModel.Simplicial

/-!
# Non-Triviality Infrastructure

This module formalizes the Section 4 non-triviality interface from
Martínez-Rivillas and de Queiroz, *The K∞ Homotopy λ-Model*.

The current repository develops the simplicial and c.h.p.o. layers separately,
but it does not yet internalize geometric realization or classical homotopy
groups. Following the repository's chosen-data style, we therefore package the
homotopy-group information of Definition 4.1 as explicit data attached to a Kan
complex. The order-theoretic part of Definition 4.3 is concrete: `NPlus` is
implemented as the flat c.h.p.o. on the sphere-summand carrier.
-/

namespace HigherLambdaModel.KInfinity

open Classical
open HigherLambdaModel.Lambda.TruncationCore
open HigherLambdaModel.Lambda.HomotopyOrder
open HigherLambdaModel.Domain

universe u v w

/-! ## Small Type-Level Helpers -/

/-- A type is infinite when it admits an injective encoding of `Nat`. -/
def TypeInfinite (α : Type u) : Prop :=
  ∃ f : Nat → α, Function.Injective f

/-- A type is non-trivial when it has two distinct points. -/
def TypeNontrivial (α : Type u) : Prop :=
  ∃ x y : α, x ≠ y

theorem nat_typeInfinite : TypeInfinite Nat := by
  refine ⟨fun n => n, ?_⟩
  intro m n hmn
  -- The identity embedding is injective: id m = id n unfolds to m = n.
  calc
    m = (fun k : Nat => k) m := by rfl
    _ = (fun k : Nat => k) n := hmn
    _ = n := by rfl

theorem bool_typeNontrivial : TypeNontrivial Bool := by
  exact ⟨false, true, by decide⟩

/-! ## Constant Kan Complexes -/

/-- The simplicial set with constant simplices and identity face/degeneracy
maps. This is a simple Kan-complex carrier used to attach the chosen
homotopy-group data of Section 4. -/
def constantSSet (α : Type u) : SSet where
  Simplex := fun _ => α
  face := fun _ _ x => x
  degen := fun _ _ x => x
  face_degen0_eq := by
    intro σ
    -- face₀ ∘ degen₀ = id because both are the identity on α.
    calc (fun _ _ (x : α) => x) 0 0 ((fun _ _ (x : α) => x) 0 0 σ)
        = (fun _ _ (x : α) => x) 0 0 σ := by rfl
      _ = σ := by rfl
  face_degen0_succ := by
    intro σ
    calc (fun _ _ (x : α) => x) 0 1 ((fun _ _ (x : α) => x) 0 0 σ)
        = (fun _ _ (x : α) => x) 0 0 σ := by rfl
      _ = σ := by rfl
  face_face := by
    intro n σ i j hij hj
    -- Both sides reduce to σ through the constant face map.
    calc (fun _ _ (x : α) => x) n i ((fun _ _ (x : α) => x) (n + 1) (j + 1) σ)
        = σ := by rfl
      _ = (fun _ _ (x : α) => x) n j ((fun _ _ (x : α) => x) (n + 1) i σ) := by rfl
  face_degen_lt := by
    intro n σ i j hij hj
    calc (fun _ _ (x : α) => x) (n + 1) i ((fun _ _ (x : α) => x) (n + 1) j σ)
        = σ := by rfl
      _ = (fun _ _ (x : α) => x) n (j - 1) ((fun _ _ (x : α) => x) n i σ) := by rfl
  face_degen_eq := by
    intro n σ i hi
    calc (fun _ _ (x : α) => x) (n + 1) i ((fun _ _ (x : α) => x) (n + 1) i σ)
        = (fun _ _ (x : α) => x) (n + 1) i σ := by rfl
      _ = σ := by rfl
  face_degen_succ := by
    intro n σ i hi
    calc (fun _ _ (x : α) => x) (n + 1) (i + 1) ((fun _ _ (x : α) => x) (n + 1) i σ)
        = (fun _ _ (x : α) => x) (n + 1) i σ := by rfl
      _ = σ := by rfl
  face_degen_gt := by
    intro n σ i j hji hi
    calc (fun _ _ (x : α) => x) (n + 1) i ((fun _ _ (x : α) => x) (n + 1) j σ)
        = σ := by rfl
      _ = (fun _ _ (x : α) => x) n j ((fun _ _ (x : α) => x) n (i - 1) σ) := by rfl
  degen_degen := by
    intro n σ i j hij hj
    calc (fun _ _ (x : α) => x) (n + 1) (j + 1) ((fun _ _ (x : α) => x) n i σ)
        = σ := by rfl
      _ = (fun _ _ (x : α) => x) (n + 1) i ((fun _ _ (x : α) => x) n j σ) := by rfl

private def constantHornPivot {n i : Nat} (_hi : i ≤ n + 1) : Nat :=
  if i = 0 then 1 else 0

private theorem constantHornPivot_ne
    {n i : Nat} (hi : i ≤ n + 1) :
    constantHornPivot hi ≠ i := by
  by_cases h : i = 0
  · subst h
    simp [constantHornPivot]
  · simp [constantHornPivot, h]
    intro h0
    exact h h0.symm

private theorem constantHornPivot_le
    {n i : Nat} (hi : i ≤ n + 1) :
    constantHornPivot hi ≤ n + 1 := by
  by_cases h : i = 0
  · subst h
    simp [constantHornPivot]
  · simp [constantHornPivot, h]

private theorem constantHorn_unique_index
    {i j : Nat} (hi : i ≤ 1) (hj : j ≤ 1) (hji : j ≠ i) :
    j = constantHornPivot hi := by
  by_cases h : i = 0
  · subst h
    have hj' : j = 0 ∨ j = 1 := by omega
    cases hj' with
    | inl hj0 =>
      exact False.elim (hji hj0)
    | inr hj1 =>
      simp [constantHornPivot, hj1]
  · have hi1 : i = 1 := by omega
    subst hi1
    have hj0 : j = 0 := by omega
    simp [constantHornPivot, h, hj0]

private theorem constantHornFacetEq
    {α : Type u} {n i : Nat}
    (Λ : Horn (constantSSet α) n i)
    {j k : Nat}
    (hj : j ≤ n + 1) (hk : k ≤ n + 1)
    (hji : j ≠ i) (hki : k ≠ i) :
    Λ.facet j hji = Λ.facet k hki := by
  cases n with
  | zero =>
    have hEq : j = k := by
      calc
        j = constantHornPivot Λ.missing_le := by
          exact constantHorn_unique_index Λ.missing_le hj hji
        _ = k := by
          exact (constantHorn_unique_index Λ.missing_le hk hki).symm
    subst hEq
    rfl
  | succ m =>
    by_cases hjk : j = k
    · subst hjk
      rfl
    · cases Nat.lt_or_gt_of_ne hjk with
      | inl hjkLt =>
        simpa [constantSSet] using (Λ.compatibility hj hk hji hki hjkLt).symm
      | inr hkjLt =>
        simpa [constantSSet] using Λ.compatibility hk hj hki hji hkjLt

/-- Every constant simplicial set is a Kan complex. -/
def constantKanComplex (α : Type u) : KanComplex where
  toSSet := constantSSet α
  fill := fun {n i} hi Λ =>
    Λ.facet (constantHornPivot hi) (constantHornPivot_ne hi)
  fill_spec := by
    intro n i hi Λ j hj hji
    exact constantHornFacetEq Λ
      (constantHornPivot_le hi) hj
      (constantHornPivot_ne hi) hji

/-! ## Definition 4.1 and Definition 4.2 -/

/-- Definition 4.1, in chosen-data form: a Kan complex equipped with explicit
models for `π₀(X)` and `πₙ(X,x)` together with the vertex predicate needed for
the local non-triviality clause of Definition 4.2. -/
structure HomotopyGroupKanComplex where
  carrier : KanComplex
  pi0 : Type v
  pi : Nat → carrier.toSSet.Simplex 0 → Type w
  component : carrier.toSSet.Simplex 0 → pi0
  hornVertex : carrier.toSSet.Simplex 0 → Prop

/-- The vertices of a chosen-data Kan complex. -/
abbrev Vertex (X : HomotopyGroupKanComplex) : Type _ :=
  X.carrier.toSSet.Simplex 0

/-- Definition 4.1: the chosen model of `π₀(X)`. -/
abbrev pi0 (X : HomotopyGroupKanComplex) : Type _ :=
  X.pi0

/-- Definition 4.1: the chosen model of `πₙ(X,x)` for `n > 0`. -/
abbrev piN (X : HomotopyGroupKanComplex) (n : Nat) (x : Vertex X) : Type _ :=
  X.pi n x

/-- Definition 4.2: a non-trivial Kan complex. -/
def IsNonTrivialKanComplex (X : HomotopyGroupKanComplex) : Prop :=
  TypeInfinite (pi0 X) ∧
    (∀ n : Nat, 1 ≤ n → ∃ x : Vertex X, TypeNontrivial (piN X n x)) ∧
      ∀ x : Vertex X, X.hornVertex x → ∃ n : Nat, 1 ≤ n ∧ TypeNontrivial (piN X n x)

/-! ## Example 4.1 -/

/-- A vertex of the chosen sphere-summand model of Example 4.1. The first
coordinate records the summand `Sⁿ`; the boolean distinguishes two marked
vertices inside that summand. -/
structure SpherePoint where
  dim : Nat
  pole : Bool
deriving DecidableEq

/-- The chosen homotopy group attached to a sphere summand. We record the
non-trivial group at dimension `dim + 1` by `Bool` and use `PUnit` elsewhere. -/
def sphereHomotopyGroup (n : Nat) (x : SpherePoint) : Type :=
  if n = x.dim.succ then Bool else PUnit

/-- A sphere-summand vertex is a horn vertex when it supports some non-trivial
higher homotopy group. This is the chosen-data form of belonging to a
non-degenerate horn for the Section 4 sphere model. -/
def SpherePoint.isHornVertex (x : SpherePoint) : Prop :=
  ∃ n : Nat, 1 ≤ n ∧ TypeNontrivial (sphereHomotopyGroup n x)

/-- Example 4.1: the chosen Section 4 model of `N = ⨿ₙ Sⁿ`. -/
def N : HomotopyGroupKanComplex where
  carrier := constantKanComplex SpherePoint
  pi0 := Nat
  pi := sphereHomotopyGroup
  component := fun x => x.dim
  hornVertex := SpherePoint.isHornVertex

private theorem sphereHomotopyGroup_nontrivial_at_dim (x : SpherePoint) :
    TypeNontrivial (sphereHomotopyGroup x.dim.succ x) := by
  simpa [sphereHomotopyGroup] using bool_typeNontrivial

private theorem spherePoint_isHornVertex (x : SpherePoint) :
    x.isHornVertex := by
  refine ⟨x.dim.succ, Nat.succ_le_succ (Nat.zero_le x.dim), ?_⟩
  exact sphereHomotopyGroup_nontrivial_at_dim x

/-- Example 4.1: the chosen sphere-summand model `N` is non-trivial. -/
theorem N_isNonTrivial : IsNonTrivialKanComplex N := by
  refine ⟨nat_typeInfinite, ?_, ?_⟩
  · intro n hn
    refine ⟨⟨n - 1, false⟩, ?_⟩
    have hpos : 0 < n := by omega
    have hpred : (n - 1).succ = n := by
      exact Nat.succ_pred_eq_of_pos hpos
    have hEq : n = (n - 1).succ := hpred.symm
    change TypeNontrivial (if n = (n - 1).succ then Bool else PUnit)
    rw [hEq]
    have hpred' : ((n - 1).succ - 1).succ = (n - 1).succ := by
      exact Nat.succ_pred_eq_of_pos (Nat.succ_pos (n - 1))
    rw [hpred']
    simpa using bool_typeNontrivial
  · intro x hx
    exact hx

/-! ## Definition 4.3: the flat c.h.p.o. `NPlus` -/

namespace Flat

/-- The flat order on `Option α`: `none` is bottom and distinct non-bottom
elements are incomparable. -/
def rel {α : Type u} : Option α → Option α → Prop
  | none, _ => True
  | some _, none => False
  | some a, some b => a = b

@[simp] theorem rel_none_left {α : Type u} (x : Option α) :
    rel none x := by
  cases x <;> simp [rel]

@[simp] theorem rel_some_none {α : Type u} (a : α) :
    ¬ rel (some a) none := by
  simp [rel]

@[simp] theorem rel_some_some {α : Type u} {a b : α} :
    rel (some a) (some b) ↔ a = b := by
  simp [rel]

@[simp] theorem rel_refl {α : Type u} (x : Option α) :
    rel x x := by
  cases x <;> simp [rel]

theorem rel_trans {α : Type u} {x y z : Option α} :
    rel x y → rel y z → rel x z := by
  cases x <;> cases y <;> cases z <;> simp [rel]
  intro hxy hyz
  exact hxy.trans hyz

/-- The flat homotopy partial order used for Definition 4.3. -/
def hpo (α : Type u) : HomotopyPartialOrder where
  Obj := Option α
  Hom := rel
  id := rel_refl
  comp := fun f g => rel_trans f g
  hom_contractible_or_empty := by
    intro x y
    by_cases h : rel x y
    · right
      exact ⟨h, fun h' => Subsingleton.elim _ _⟩
    · left
      exact h

@[simp] theorem hpo_rel_iff {α : Type u} {x y : Option α} :
    (hpo α).Rel x y ↔ rel x y := by
  constructor
  · intro h
    rcases h with ⟨h⟩
    exact h
  · intro h
    exact ⟨h⟩

theorem directed_unique_some
    {α : Type u}
    {X : Option α → Prop}
    (hX : (hpo α).Directed X)
    {a b : α}
    (ha : X (some a))
    (hb : X (some b)) :
    a = b := by
  rcases hX.2 ha hb with ⟨z, hz, haz, hbz⟩
  cases z with
  | none =>
    have : rel (some a) none := by
      simpa [hpo_rel_iff] using haz
    cases this
  | some c =>
    have hac : a = c := by simpa [hpo_rel_iff, rel] using haz
    have hbc : b = c := by simpa [hpo_rel_iff, rel] using hbz
    exact hac.trans hbc.symm

/-- The flat c.h.p.o. on `Option α`. -/
noncomputable def chpo (α : Type u) : CompleteHomotopyPartialOrder where
  toHomotopyPartialOrder := hpo α
  bottom := none
  bottom_le := by
    intro x
    exact ⟨rel_none_left x⟩
  sup := fun X hX =>
    if hSome : ∃ a : α, X (some a) then
      some (Classical.choose hSome)
    else
      none
  sup_spec := by
    intro X hX
    by_cases hSome : ∃ a : α, X (some a)
    · have ha : X (some (Classical.choose hSome)) := Classical.choose_spec hSome
      constructor
      · intro x hx
        cases x with
        | none =>
          have hrel :
              rel none
                (if hSome' : ∃ a : α, X (some a) then some (Classical.choose hSome') else none) := by
            simp [hSome, rel]
          exact ⟨hrel⟩
        | some b =>
          have hab : b = Classical.choose hSome := directed_unique_some hX hx ha
          have hrel :
              rel (some b)
                (if hSome' : ∃ a : α, X (some a) then some (Classical.choose hSome') else none) := by
            simp [hSome, rel, hab]
          exact ⟨hrel⟩
      · intro w hw
        simpa [hSome, hpo_rel_iff, rel] using hw ha
    · constructor
      · intro x hx
        cases x with
        | none =>
          have hrel :
              rel none
                (if hSome' : ∃ a : α, X (some a) then some (Classical.choose hSome') else none) := by
            simp [hSome, rel]
          exact ⟨hrel⟩
        | some a =>
          exact False.elim (hSome ⟨a, hx⟩)
      · intro w hw
        simpa [hSome, hpo_rel_iff, rel]

@[simp] theorem chpo_rel_iff {α : Type u} {x y : Option α} :
    (chpo α).Rel x y ↔ rel x y := by
  simpa [chpo] using (hpo_rel_iff (α := α) (x := x) (y := y))

/-- Every element of a flat c.h.p.o. is compact. -/
theorem isCompact
    {α : Type u}
    (x : (chpo α).Obj) :
    IsCompact (chpo α) x := by
  intro X hX hxSup
  by_cases hSome : ∃ a : α, X (some a)
  · have ha : X (some (Classical.choose hSome)) := Classical.choose_spec hSome
    cases x with
    | none =>
      rcases hX.1 with ⟨z, hz⟩
      exact ⟨z, hz, by simpa [chpo_rel_iff, rel]⟩
    | some b =>
      have hEq : b = Classical.choose hSome := by
        have hxSup' : rel (some b) ((chpo α).sup X hX) :=
          (chpo_rel_iff.mp hxSup)
        simpa [chpo, hSome, rel] using hxSup'
      refine ⟨some (Classical.choose hSome), ha, ?_⟩
      simpa [chpo_rel_iff, rel, hEq]
  · cases x with
    | none =>
      rcases hX.1 with ⟨z, hz⟩
      exact ⟨z, hz, by simpa [chpo_rel_iff, rel]⟩
    | some a =>
      have hxSup' : rel (some a) ((chpo α).sup X hX) :=
        (chpo_rel_iff.mp hxSup)
      have : False := by
        simpa [chpo, hSome, rel] using hxSup'
      exact False.elim this

/-- The flat c.h.p.o. is algebraic. -/
theorem algebraic (α : Type u) :
    Algebraic (chpo α) := by
  intro x
  constructor
  · refine ⟨⟨x, ?_⟩, ?_⟩
    exact ⟨isCompact x, (chpo α).rel_refl x⟩
    intro y z hy hz
    exact ⟨x, ⟨isCompact x, (chpo α).rel_refl x⟩, hy.2, hz.2⟩
  · constructor
    · intro y hy
      exact hy.2
    · intro w hw
      exact hw ⟨isCompact x, (chpo α).rel_refl x⟩

theorem unique_some_of_upperBound
    {α : Type u}
    {X : Option α → Prop}
    {w : Option α}
    (hw : (chpo α).IsUpperBound X w)
    {a b : α}
    (ha : X (some a))
    (hb : X (some b)) :
    a = b := by
  cases w with
  | none =>
    have : rel (some a) none := by
      simpa [chpo_rel_iff] using hw ha
    cases this
  | some c =>
    have hac : a = c := by simpa [chpo_rel_iff, rel] using hw ha
    have hbc : b = c := by simpa [chpo_rel_iff, rel] using hw hb
    exact hac.trans hbc.symm

/-- The flat c.h.p.o. is bounded complete. -/
theorem boundedComplete (α : Type u) :
    BoundedComplete (chpo α) := by
  intro X hUpper
  rcases hUpper with ⟨w, hw⟩
  by_cases hSome : ∃ a : α, X (some a)
  · let a := Classical.choose hSome
    have ha : X (some a) := Classical.choose_spec hSome
    refine ⟨some a, ?_⟩
    constructor
    · intro x hx
      cases x with
      | none =>
        simpa [chpo_rel_iff, rel]
      | some b =>
        have hEq : b = a := unique_some_of_upperBound hw hx ha
        simpa [chpo_rel_iff, rel, hEq]
    · intro u hu
      simpa [chpo_rel_iff, rel] using hu ha
  · refine ⟨none, ?_⟩
    constructor
    · intro x hx
      cases x with
      | none =>
        simpa [chpo_rel_iff, rel]
      | some a =>
        exact False.elim (hSome ⟨a, hx⟩)
    · intro u hu
      simpa [chpo_rel_iff, rel]

/-- The flat c.h.p.o. is a Homotopy Scott Domain. -/
noncomputable def scottDomain (α : Type u) : HomotopyScottDomain where
  carrier := chpo α
  algebraic := algebraic α
  boundedComplete := boundedComplete α

end Flat

/-- Definition 4.3: `N⁺ = N ∪ {⊥₀}` as a concrete c.h.p.o. The bottom element
is `none`; the sphere summand vertices are represented by `some x`. -/
noncomputable abbrev NPlus : CompleteHomotopyPartialOrder :=
  Flat.chpo SpherePoint

/-- The Scott-domain witness for `N⁺`, used as the base object `K₀`. -/
noncomputable abbrev NPlusScottDomain : HomotopyScottDomain :=
  Flat.scottDomain SpherePoint

/-- The distinguished bottom point `⊥₀` of Definition 4.3. -/
abbrev bottom0 : NPlus.Obj := none

/-! ## Definition 4.4 -/

/-- A chosen-data reflexivity witness for a c.h.p.o., matching the domain
equation content of Definition 4.4. -/
structure ReflexiveCHPO (K : CompleteHomotopyPartialOrder) where
  reify : ContinuousMap (Exponential.chpo K K) K
  reflect : ContinuousMap K (Exponential.chpo K K)
  retract : ContinuousMap.comp reify reflect = ContinuousMap.id K

/-- Definition 4.4: a non-trivial homotopy λ-model packages a non-trivial
Kan-complex witness together with a reflexive c.h.p.o. witness. -/
structure NonTrivialHomotopyLambdaModel where
  kan : HomotopyGroupKanComplex
  chpo : CompleteHomotopyPartialOrder
  nontrivial : IsNonTrivialKanComplex kan
  reflexive : ReflexiveCHPO chpo

end HigherLambdaModel.KInfinity
