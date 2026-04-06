import HigherLambdaModel.Domain.CHPO

/-!
# Scott Domains

This module formalizes Section 3.1 of Martínez-Rivillas and de Queiroz,
*The K∞ Homotopy λ-Model*:

- compact elements
- algebraic and bounded complete c.h.p.o.'s
- Homotopy Scott Domains
- the continuity criterion on algebraic c.h.p.o.'s
- preservation under products
- step functions for function-space Scott domains

The development builds on `HigherLambdaModel.Domain.CHPO`.
-/

namespace HigherLambdaModel.Domain

open Classical
open HigherLambdaModel.Lambda.TruncationCore
open HigherLambdaModel.Lambda.HomotopyOrder

universe u v w u' v'

/-! ## Definitions 3.11 and 3.12 -/

/-- Definition 3.11.1: a compact element of a c.h.p.o. -/
def IsCompact
    (K : CompleteHomotopyPartialOrder)
    (x : K.Obj) : Prop :=
  ∀ (X : K.Obj → Prop)
    (hX : K.Directed X),
      K.Rel x (K.sup X hX) →
        ∃ x₀ : K.Obj, X x₀ ∧ K.Rel x x₀

/-- The compact elements below `x`. -/
def compactBelow
    (K : CompleteHomotopyPartialOrder)
    (x : K.Obj) :
    K.Obj → Prop :=
  fun y => IsCompact K y ∧ K.Rel y x

/-- Definition 3.11.2: an algebraic c.h.p.o. -/
def Algebraic
    (K : CompleteHomotopyPartialOrder) : Prop :=
  ∀ x : K.Obj,
    K.Directed (compactBelow K x) ∧
      K.IsLeastUpperBound (compactBelow K x) x

/-- Definition 3.11.3: bounded completeness. -/
def BoundedComplete
    (K : CompleteHomotopyPartialOrder) : Prop :=
  ∀ X : K.Obj → Prop,
    (∃ w : K.Obj, K.IsUpperBound X w) →
      ∃ z : K.Obj, K.IsLeastUpperBound X z

/-- Definition 3.12: a Homotopy Scott Domain is a bounded complete algebraic
c.h.p.o. -/
structure HomotopyScottDomain where
  carrier : CompleteHomotopyPartialOrder
  algebraic : Algebraic carrier
  boundedComplete : BoundedComplete carrier

instance : Coe HomotopyScottDomain CompleteHomotopyPartialOrder where
  coe K := K.carrier

/-- A raw function is continuous when it is represented by a `ContinuousMap`. -/
def IsContinuous
    (K : CompleteHomotopyPartialOrder)
    (L : CompleteHomotopyPartialOrder)
    (f : K.Obj → L.Obj) : Prop :=
  ∃ g : ContinuousMap K L, g.toFun = f

/-- The compact-approximation predicate of Proposition 3.12. -/
def CompactApproximation
    (K : CompleteHomotopyPartialOrder)
    (L : CompleteHomotopyPartialOrder)
    (f : K.Obj → L.Obj) : Prop :=
  ∀ x : K.Obj,
    L.IsLeastUpperBound (image f (compactBelow K x)) (f x)

/-! ## Bottom Compactness -/

/-- The bottom element of any c.h.p.o. is compact. -/
theorem bottom_isCompact (K : CompleteHomotopyPartialOrder) : IsCompact K K.bottom := by
  intro X hX _; rcases hX.1 with ⟨x, hx⟩; exact ⟨x, hx, K.bottom_le x⟩

/-- The image of a compact element under a section of a retraction is compact. -/
theorem compact_of_retraction
    {K L : CompleteHomotopyPartialOrder}
    (e : ContinuousMap K L) (r : ContinuousMap L K)
    (hret : ∀ x : K.Obj, K.Rel (r.toFun (e.toFun x)) x ∧ K.Rel x (r.toFun (e.toFun x)))
    (hsec : ∀ y : L.Obj, L.Rel (e.toFun (r.toFun y)) y)
    {x : K.Obj} (hx : IsCompact K x) : IsCompact L (e.toFun x) := by
  intro Y hY heSup
  have hZ : K.Directed (image r.toFun Y) := r.directed_image hY
  have hrSup : K.Rel (r.toFun (L.sup Y hY)) (K.sup (image r.toFun Y) hZ) := by
    refine (r.preserves_sup Y hY).2 ?_
    intro a ha
    rcases ha with ⟨y, hy, rfl⟩
    exact (K.sup_spec _ hZ).1 ⟨y, hy, rfl⟩
  have hxSupZ : K.Rel x (K.sup (image r.toFun Y) hZ) := by
    exact K.rel_trans (hret x).2 (K.rel_trans (r.monotone' heSup) hrSup)
  rcases hx _ hZ hxSupZ with ⟨z, ⟨y, hy, rfl⟩, hxz⟩
  exact ⟨y, hy, L.rel_trans (e.monotone' hxz) (hsec y)⟩

/-- Compactness below is monotone in the ambient element. -/
theorem compactBelow_mono {K : CompleteHomotopyPartialOrder} {x y : K.Obj}
    (hxy : K.Rel x y) {z : K.Obj} (hz : compactBelow K x z) : compactBelow K y z :=
  ⟨hz.1, K.rel_trans hz.2 hxy⟩

/-- The bottom element is compact-below every element. -/
theorem bottom_compactBelow (K : CompleteHomotopyPartialOrder) (x : K.Obj) :
    compactBelow K x K.bottom := ⟨bottom_isCompact K, K.bottom_le x⟩

/-- The empty predicate has bottom as least upper bound. -/
theorem empty_isLeastUpperBound
    (K : CompleteHomotopyPartialOrder) :
    K.IsLeastUpperBound (fun _ : K.Obj => False) K.bottom := by
  constructor
  · intro x hx
    exact False.elim hx
  · intro w _hw
    exact K.bottom_le w

private def pairPred {K : CompleteHomotopyPartialOrder} (x y : K.Obj) : K.Obj → Prop :=
  fun z => z = x ∨ z = y

/-! ## Compactness Closure Lemmas -/

/-- A least upper bound of two compact elements is compact. This is the binary
finite-supremum closure step needed before finite-step bases can be assembled
from compact step functions. -/
theorem compact_of_pair_isLeastUpperBound
    {K : CompleteHomotopyPartialOrder}
    {x y z : K.Obj}
    (hx : IsCompact K x)
    (hy : IsCompact K y)
    (hz : K.IsLeastUpperBound (pairPred x y) z) :
    IsCompact K z := by
  intro X hX hzSup
  have hxSup : K.Rel x (K.sup X hX) := by
    exact K.rel_trans (hz.1 (Or.inl rfl)) hzSup
  have hySup : K.Rel y (K.sup X hX) := by
    exact K.rel_trans (hz.1 (Or.inr rfl)) hzSup
  rcases hx X hX hxSup with ⟨x₀, hx₀, hxx₀⟩
  rcases hy X hX hySup with ⟨y₀, hy₀, hyy₀⟩
  rcases hX.2 (x := x₀) (y := y₀) hx₀ hy₀ with ⟨w, hw, hx₀w, hy₀w⟩
  refine ⟨w, hw, hz.2 ?_⟩
  intro u hu
  rcases hu with rfl | rfl
  · exact K.rel_trans hxx₀ hx₀w
  · exact K.rel_trans hyy₀ hy₀w

/-- In a bounded-complete c.h.p.o., any two compact elements admit a chosen
compact binary least upper bound whenever they admit a common upper bound. -/
theorem exists_pair_compact_isLeastUpperBound
    {K : CompleteHomotopyPartialOrder}
    (hK : BoundedComplete K)
    {x y : K.Obj}
    (hx : IsCompact K x)
    (hy : IsCompact K y)
    (hUpper : ∃ w : K.Obj, K.IsUpperBound (pairPred x y) w) :
    ∃ z : K.Obj, K.IsLeastUpperBound (pairPred x y) z ∧ IsCompact K z := by
  rcases hK (pairPred x y) hUpper with ⟨z, hz⟩
  exact ⟨z, hz, compact_of_pair_isLeastUpperBound hx hy hz⟩

/-- In a bounded-complete c.h.p.o., every finite upper-bounded family of compact
elements admits a chosen compact least upper bound. This is the finite closure
property needed to move from single compact step functions toward finite-step
bases. -/
theorem exists_list_compact_isLeastUpperBound
    {K : CompleteHomotopyPartialOrder}
    (hK : BoundedComplete K) :
    ∀ xs : List K.Obj,
      (∀ x : K.Obj, x ∈ xs → IsCompact K x) →
      (∃ w : K.Obj, K.IsUpperBound (fun y => y ∈ xs) w) →
      ∃ z : K.Obj, K.IsLeastUpperBound (fun y => y ∈ xs) z ∧ IsCompact K z
  | [], _hcompact, _hUpper =>
      ⟨K.bottom,
        by
          constructor
          · intro y hy
            cases hy
          · intro w _hw
            exact K.bottom_le w,
        bottom_isCompact K⟩
  | x :: xs, hcompact, hUpper => by
      have hx : IsCompact K x := hcompact x (by simp)
      have hcompactTail : ∀ y : K.Obj, y ∈ xs → IsCompact K y := by
        intro y hy
        exact hcompact y (by simp [hy])
      have hUpperTail : ∃ w : K.Obj, K.IsUpperBound (fun y => y ∈ xs) w := by
        rcases hUpper with ⟨w, hw⟩
        exact ⟨w, fun y hy => hw (by simp [hy])⟩
      rcases exists_list_compact_isLeastUpperBound hK xs hcompactTail hUpperTail with
        ⟨z, hz, hzCompact⟩
      have hUpperPair : ∃ w : K.Obj, K.IsUpperBound (pairPred x z) w := by
        rcases hUpper with ⟨w, hw⟩
        refine ⟨w, ?_⟩
        intro y hy
        rcases hy with rfl | rfl
        · exact hw (by simp)
        · exact hz.2 (by
            intro t ht
            exact hw (by simp [ht]))
      rcases exists_pair_compact_isLeastUpperBound hK hx hzCompact hUpperPair with
        ⟨u, hu, huCompact⟩
      refine ⟨u, ?_, huCompact⟩
      constructor
      · intro y hy
        have hy' : y = x ∨ y ∈ xs := by
          simpa using hy
        rcases hy' with rfl | hy
        · exact hu.1 (Or.inl rfl)
        · exact K.rel_trans (hz.1 hy) (hu.1 (Or.inr rfl))
      · intro w hw
        have hzw : K.Rel z w := hz.2 (by
          intro y hy
          exact hw (by simp [hy]))
        exact hu.2 (by
          intro y hy
          rcases hy with rfl | rfl
          · exact hw (by simp)
          · exact hzw)

/-- In a bounded-complete c.h.p.o., every finite family of compact-below
approximants of `x` admits a chosen compact-below least upper bound. This is
the finite assembly step needed to turn compact pointwise data into finite
approximants that still remain below the target element. -/
theorem exists_list_compactBelow_isLeastUpperBound
    {K : CompleteHomotopyPartialOrder}
    (hK : BoundedComplete K)
    {x : K.Obj}
    (xs : List K.Obj)
    (hcompactBelow : ∀ y : K.Obj, y ∈ xs → compactBelow K x y) :
    ∃ z : K.Obj, compactBelow K x z ∧ K.IsLeastUpperBound (fun y => y ∈ xs) z := by
  have hcompact : ∀ y : K.Obj, y ∈ xs → IsCompact K y := by
    intro y hy
    exact (hcompactBelow y hy).1
  have hUpper : ∃ w : K.Obj, K.IsUpperBound (fun y => y ∈ xs) w := by
    refine ⟨x, ?_⟩
    intro y hy
    exact (hcompactBelow y hy).2
  rcases exists_list_compact_isLeastUpperBound hK xs hcompact hUpper with
    ⟨z, hz, hzCompact⟩
  refine ⟨z, ⟨hzCompact, hz.2 ?_⟩, hz⟩
  intro y hy
  exact (hcompactBelow y hy).2

/-! ## Helper Lemmas -/

/-- Directedness is invariant under pointwise equivalent predicates. -/
theorem directed_congr
    (K : HomotopyPartialOrder)
    {P Q : K.Obj → Prop}
    (hPQ : ∀ x : K.Obj, P x ↔ Q x) :
    K.Directed P ↔ K.Directed Q := by
  constructor
  · intro hP
    rcases hP with ⟨⟨x, hx⟩, hdir⟩
    refine ⟨⟨x, (hPQ x).mp hx⟩, ?_⟩
    intro x y hx hy
    rcases hdir ((hPQ x).mpr hx) ((hPQ y).mpr hy) with ⟨z, hz, hxz, hyz⟩
    exact ⟨z, (hPQ z).mp hz, hxz, hyz⟩
  · intro hQ
    rcases hQ with ⟨⟨x, hx⟩, hdir⟩
    refine ⟨⟨x, (hPQ x).mpr hx⟩, ?_⟩
    intro x y hx hy
    rcases hdir ((hPQ x).mp hx) ((hPQ y).mp hy) with ⟨z, hz, hxz, hyz⟩
    exact ⟨z, (hPQ z).mpr hz, hxz, hyz⟩

/-- Least-upper-bound witnesses are invariant under pointwise equivalent
predicates. -/
theorem isLeastUpperBound_congr
    (K : HomotopyPartialOrder)
    {P Q : K.Obj → Prop} {x : K.Obj}
    (hPQ : ∀ y : K.Obj, P y ↔ Q y) :
    K.IsLeastUpperBound P x ↔ K.IsLeastUpperBound Q x := by
  constructor
  · intro hx
    constructor
    · intro y hy
      exact hx.1 ((hPQ y).mpr hy)
    · intro z hz
      exact hx.2 (by
        intro y hy
        exact hz ((hPQ y).mp hy))
  · intro hx
    constructor
    · intro y hy
      exact hx.1 ((hPQ y).mp hy)
    · intro z hz
      exact hx.2 (by
        intro y hy
        exact hz ((hPQ y).mpr hy))

/-- Chosen suprema for extensionally equal directed predicates are equivalent
in the ambient h.p.o. relation. -/
theorem sup_equiv_of_pred_equiv
    (K : CompleteHomotopyPartialOrder)
    {P Q : K.Obj → Prop}
    (hPQ : ∀ x : K.Obj, P x ↔ Q x)
    (hP : K.Directed P)
    (hQ : K.Directed Q) :
    K.Rel (K.sup P hP) (K.sup Q hQ) ∧
      K.Rel (K.sup Q hQ) (K.sup P hP) := by
  exact equivalent_of_isLeastUpperBound
    K.toHomotopyPartialOrder
    (K.sup_spec P hP)
    ((isLeastUpperBound_congr K.toHomotopyPartialOrder hPQ).mpr (K.sup_spec Q hQ))

/-- Compact elements are preserved by equivalence in the h.p.o. relation. -/
theorem compact_of_equiv
    {K : CompleteHomotopyPartialOrder}
    {x y : K.Obj}
    (hx : IsCompact K x)
    (hxy : K.Rel x y)
    (hyx : K.Rel y x) :
    IsCompact K y := by
  intro X hX hySup
  rcases hx X hX (K.rel_trans hxy hySup) with ⟨z, hz, hxz⟩
  exact ⟨z, hz, K.rel_trans hyx hxz⟩

/-- Monotonicity extracted from a compact approximation witness. -/
theorem compactApproximation_monotone
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (f : K.Obj → L.Obj)
    (hf : CompactApproximation K L f) :
    ∀ {x y : K.Obj}, K.Rel x y → L.Rel (f x) (f y) := by
  intro x y hxy
  refine (hf x).2 ?_
  intro z hz
  rcases hz with ⟨e, ⟨heCompact, hex⟩, rfl⟩
  exact (hf y).1 ⟨e, ⟨heCompact, K.rel_trans hex hxy⟩, rfl⟩

/-! ## Proposition 3.12 -/

/-- The forward direction of Proposition 3.12. -/
theorem ContinuousMap.compactApproximation
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (hK : Algebraic K)
    (f : ContinuousMap K L) :
    CompactApproximation K L f.toFun := by
  intro x
  let X : K.Obj → Prop := compactBelow K x
  have hDir : K.Directed X := (hK x).1
  have hChosen : K.IsLeastUpperBound X (K.sup X hDir) := K.sup_spec X hDir
  have hExact : K.IsLeastUpperBound X x := (hK x).2
  have hEqv :
      K.Rel (K.sup X hDir) x ∧ K.Rel x (K.sup X hDir) :=
    equivalent_of_isLeastUpperBound K.toHomotopyPartialOrder hChosen hExact
  exact isLeastUpperBound_of_equiv
    L.toHomotopyPartialOrder
    (f.preserves_sup X hDir)
    (f.monotone' hEqv.1)
    (f.monotone' hEqv.2)

/-- The reverse direction of Proposition 3.12. -/
def continuousOfCompactApproximation
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (f : K.Obj → L.Obj)
    (hf : CompactApproximation K L f) :
    ContinuousMap K L where
  toFun := f
  monotone' := by
    intro x y hxy
    exact compactApproximation_monotone f hf hxy
  preserves_sup := by
    intro X hX
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact compactApproximation_monotone f hf ((K.sup_spec X hX).1 hx)
    · intro w hw
      refine (hf (K.sup X hX)).2 ?_
      intro a ha
      rcases ha with ⟨e, ⟨heCompact, heSup⟩, rfl⟩
      rcases heCompact X hX heSup with ⟨x, hx, hex⟩
      exact L.rel_trans
        (compactApproximation_monotone f hf hex)
        (hw ⟨x, hx, rfl⟩)

/-- Proposition 3.12. -/
theorem continuous_iff_compactApproximation
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (hK : Algebraic K)
    (f : K.Obj → L.Obj) :
    IsContinuous K L f ↔ CompactApproximation K L f := by
  constructor
  · intro hf
    rcases hf with ⟨g, rfl⟩
    exact ContinuousMap.compactApproximation (hK := hK) g
  · intro hf
    exact ⟨continuousOfCompactApproximation f hf, rfl⟩

/-! ## Proposition 3.13 -/

/-- The predicate `X × {y}` used in Proposition 3.13.1. -/
def freezeRight
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (X : K.Obj → Prop)
    (y : L.Obj) :
    (Product.chpo K L).Obj → Prop :=
  fun p => X p.1 ∧ p.2 = y

/-- The predicate `{x} × Y` used in Proposition 3.13.1. -/
def freezeLeft
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (x : K.Obj)
    (Y : L.Obj → Prop) :
    (Product.chpo K L).Obj → Prop :=
  fun p => p.1 = x ∧ Y p.2

/-- `X × {y}` is directed when `X` is directed. -/
theorem directed_freezeRight
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {X : K.Obj → Prop}
    (hX : K.Directed X)
    (y : L.Obj) :
    (Product.chpo K L).Directed (freezeRight X y) := by
  rcases hX with ⟨⟨x, hx⟩, hdir⟩
  refine ⟨⟨(x, y), ⟨hx, rfl⟩⟩, ?_⟩
  intro a b ha hb
  rcases ha with ⟨ha₁, ha₂⟩
  rcases hb with ⟨hb₁, hb₂⟩
  rcases hdir ha₁ hb₁ with ⟨c, hc, hac, hbc⟩
  exact ⟨(c, y), ⟨hc, rfl⟩,
    Product.rel_mk hac (ha₂ ▸ L.rel_refl y),
    Product.rel_mk hbc (hb₂ ▸ L.rel_refl y)⟩

/-- `{x} × Y` is directed when `Y` is directed. -/
theorem directed_freezeLeft
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (x : K.Obj)
    {Y : L.Obj → Prop}
    (hY : L.Directed Y) :
    (Product.chpo K L).Directed (freezeLeft x Y) := by
  rcases hY with ⟨⟨y, hy⟩, hdir⟩
  refine ⟨⟨(x, y), ⟨rfl, hy⟩⟩, ?_⟩
  intro a b ha hb
  rcases ha with ⟨ha₁, ha₂⟩
  rcases hb with ⟨hb₁, hb₂⟩
  rcases hdir ha₂ hb₂ with ⟨c, hc, hac, hbc⟩
  exact ⟨(x, c), ⟨rfl, hc⟩,
    Product.rel_mk (ha₁ ▸ K.rel_refl x) hac,
    Product.rel_mk (hb₁ ▸ K.rel_refl x) hbc⟩

/-- Proposition 3.13.1: compactness is coordinatewise on products. -/
theorem compact_prod_iff
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {x : K.Obj} {y : L.Obj} :
    IsCompact (Product.chpo K L) (x, y) ↔
      IsCompact K x ∧ IsCompact L y := by
  constructor
  · intro hxy
    constructor
    · intro X hX hxSup
      let P : (Product.chpo K L).Obj → Prop := freezeRight X y
      have hP : (Product.chpo K L).Directed P := directed_freezeRight hX y
      have hPred :
          ∀ z : K.Obj, X z ↔ Product.fstPred P z := by
        intro z
        constructor
        · intro hz
          exact ⟨y, ⟨hz, rfl⟩⟩
        · intro hz
          rcases hz with ⟨y', hy'⟩
          exact hy'.1
      have hSupFst :
          K.Rel (K.sup X hX)
            (K.sup (Product.fstPred P) (Product.directed_fst hP)) :=
        (sup_equiv_of_pred_equiv K hPred hX (Product.directed_fst hP)).1
      have hxySup :
          (Product.chpo K L).Rel (x, y) ((Product.chpo K L).sup P hP) := by
        refine Product.rel_mk ?_ ?_
        · exact K.rel_trans hxSup hSupFst
        · rcases hX.1 with ⟨x₀, hx₀⟩
          exact ((L.sup_spec (Product.sndPred P) (Product.directed_snd hP)).1
            ⟨x₀, ⟨hx₀, rfl⟩⟩)
      rcases hxy P hP hxySup with ⟨p, hp, hxp⟩
      exact ⟨p.1, hp.1, (Product.rel_iff.mp hxp).1⟩
    · intro Y hY hySup
      let P : (Product.chpo K L).Obj → Prop := freezeLeft x Y
      have hP : (Product.chpo K L).Directed P := directed_freezeLeft x hY
      have hPred :
          ∀ z : L.Obj, Y z ↔ Product.sndPred P z := by
        intro z
        constructor
        · intro hz
          exact ⟨x, ⟨rfl, hz⟩⟩
        · intro hz
          rcases hz with ⟨x', hx'⟩
          exact hx'.2
      have hSupSnd :
          L.Rel (L.sup Y hY)
            (L.sup (Product.sndPred P) (Product.directed_snd hP)) :=
        (sup_equiv_of_pred_equiv L hPred hY (Product.directed_snd hP)).1
      have hxySup :
          (Product.chpo K L).Rel (x, y) ((Product.chpo K L).sup P hP) := by
        refine Product.rel_mk ?_ ?_
        · rcases hY.1 with ⟨y₀, hy₀⟩
          exact ((K.sup_spec (Product.fstPred P) (Product.directed_fst hP)).1
            ⟨y₀, ⟨rfl, hy₀⟩⟩)
        · exact L.rel_trans hySup hSupSnd
      rcases hxy P hP hxySup with ⟨p, hp, hxp⟩
      exact ⟨p.2, hp.2, (Product.rel_iff.mp hxp).2⟩
  · rintro ⟨hx, hy⟩
    intro X hX hxySup
    have hxSup : K.Rel x (K.sup (Product.fstPred X) (Product.directed_fst hX)) :=
      (Product.rel_iff.mp hxySup).1
    have hySup : L.Rel y (L.sup (Product.sndPred X) (Product.directed_snd hX)) :=
      (Product.rel_iff.mp hxySup).2
    rcases hx (Product.fstPred X) (Product.directed_fst hX) hxSup with ⟨x₀, hx₀, hxx₀⟩
    rcases hy (Product.sndPred X) (Product.directed_snd hX) hySup with ⟨y₀, hy₀, hyy₀⟩
    rcases hx₀ with ⟨px, hpx⟩
    rcases hy₀ with ⟨py, hpy⟩
    rcases hX.2 hpx hpy with ⟨z, hz, hpz, hqz⟩
    refine ⟨z, hz, Product.rel_mk ?_ ?_⟩
    · exact K.rel_trans hxx₀ ((Product.rel_iff.mp hpz).1)
    · exact L.rel_trans hyy₀ ((Product.rel_iff.mp hqz).2)

/-- The compact-below predicate on a product is coordinatewise. -/
theorem compactBelow_prod_iff
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {p q : (Product.chpo K L).Obj} :
    compactBelow (Product.chpo K L) p q ↔
      compactBelow K p.1 q.1 ∧ compactBelow L p.2 q.2 := by
  constructor
  · intro hq
    rcases hq with ⟨hqCompact, hqp⟩
    exact ⟨⟨(compact_prod_iff.mp hqCompact).1, (Product.rel_iff.mp hqp).1⟩,
      ⟨(compact_prod_iff.mp hqCompact).2, (Product.rel_iff.mp hqp).2⟩⟩
  · intro hq
    exact ⟨(compact_prod_iff.mpr ⟨hq.1.1, hq.2.1⟩), Product.rel_mk hq.1.2 hq.2.2⟩

/-- Proposition 3.13.2: products of algebraic c.h.p.o.'s are algebraic. -/
theorem algebraic_prod
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (hK : Algebraic K)
    (hL : Algebraic L) :
    Algebraic (Product.chpo K L) := by
  intro p
  let Q : (Product.chpo K L).Obj → Prop :=
    fun q => compactBelow K p.1 q.1 ∧ compactBelow L p.2 q.2
  have hEquiv :
      ∀ q : (Product.chpo K L).Obj,
        compactBelow (Product.chpo K L) p q ↔ Q q := by
    intro q
    exact compactBelow_prod_iff
  have hDirQ : (Product.chpo K L).Directed Q := by
    rcases (hK p.1).1 with ⟨⟨a, ha⟩, hdirK⟩
    rcases (hL p.2).1 with ⟨⟨b, hb⟩, hdirL⟩
    refine ⟨⟨(a, b), ⟨ha, hb⟩⟩, ?_⟩
    intro q r hq hr
    rcases hdirK hq.1 hr.1 with ⟨a', ha', hqa, hra⟩
    rcases hdirL hq.2 hr.2 with ⟨b', hb', hqb, hrb⟩
    exact ⟨(a', b'), ⟨ha', hb'⟩,
      Product.rel_mk hqa hqb,
      Product.rel_mk hra hrb⟩
  have hLubQ : (Product.chpo K L).IsLeastUpperBound Q p := by
    constructor
    · intro q hq
      exact Product.rel_mk hq.1.2 hq.2.2
    · intro w hw
      rcases (hK p.1).1.1 with ⟨a₀, ha₀⟩
      rcases (hL p.2).1.1 with ⟨b₀, hb₀⟩
      have hwK : K.IsUpperBound (compactBelow K p.1) w.1 := by
        intro a ha
        exact (Product.rel_iff.mp (hw (x := (a, b₀)) ⟨ha, hb₀⟩)).1
      have hwL : L.IsUpperBound (compactBelow L p.2) w.2 := by
        intro b hb
        exact (Product.rel_iff.mp (hw (x := (a₀, b)) ⟨ha₀, hb⟩)).2
      exact Product.rel_mk ((hK p.1).2.2 hwK) ((hL p.2).2.2 hwL)
  exact ⟨(directed_congr (Product.chpo K L).toHomotopyPartialOrder hEquiv).mpr hDirQ,
    (isLeastUpperBound_congr (Product.chpo K L).toHomotopyPartialOrder hEquiv).mpr hLubQ⟩

/-- Proposition 3.13.3: products of bounded complete c.h.p.o.'s are bounded
complete. -/
theorem boundedComplete_prod
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (hK : BoundedComplete K)
    (hL : BoundedComplete L) :
    BoundedComplete (Product.chpo K L) := by
  intro X hUpper
  rcases hUpper with ⟨w, hw⟩
  have hUpperK : ∃ z : K.Obj, K.IsUpperBound (Product.fstPred X) z := by
    refine ⟨w.1, ?_⟩
    intro x hx
    rcases hx with ⟨y, hxy⟩
    exact (Product.rel_iff.mp (hw hxy)).1
  have hUpperL : ∃ z : L.Obj, L.IsUpperBound (Product.sndPred X) z := by
    refine ⟨w.2, ?_⟩
    intro y hy
    rcases hy with ⟨x, hxy⟩
    exact (Product.rel_iff.mp (hw hxy)).2
  rcases hK (Product.fstPred X) hUpperK with ⟨xSup, hxSup⟩
  rcases hL (Product.sndPred X) hUpperL with ⟨ySup, hySup⟩
  refine ⟨(xSup, ySup), ?_⟩
  constructor
  · intro q hq
    exact Product.rel_mk
      (hxSup.1 ⟨q.2, hq⟩)
      (hySup.1 ⟨q.1, hq⟩)
  · intro w' hw'
    refine Product.rel_mk ?_ ?_
    · refine hxSup.2 ?_
      intro x hx
      rcases hx with ⟨y, hxy⟩
      exact (Product.rel_iff.mp (hw' hxy)).1
    · refine hySup.2 ?_
      intro y hy
      rcases hy with ⟨x, hxy⟩
      exact (Product.rel_iff.mp (hw' hxy)).2

/-- Products preserve Homotopy Scott Domains. -/
def HomotopyScottDomain.prod
    (K : HomotopyScottDomain)
    (L : HomotopyScottDomain) :
    HomotopyScottDomain where
  carrier := Product.chpo K L
  algebraic := algebraic_prod K.algebraic L.algebraic
  boundedComplete := boundedComplete_prod K.boundedComplete L.boundedComplete

/-! ## Step Functions -/

/-- A step function with compact source element, as used in Proposition 3.14. -/
noncomputable def stepFunction
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (a : K.Obj)
    (ha : IsCompact K a)
    (b : L.Obj) :
    ContinuousMap K L where
  toFun := fun x => if K.Rel a x then b else L.bottom
  monotone' := by
    intro x y hxy
    by_cases hax : K.Rel a x
    · have hay : K.Rel a y := K.rel_trans hax hxy
      simp [hax, hay]
      exact L.rel_refl b
    · by_cases hay : K.Rel a y
      · simp [hax, hay]
        exact L.bottom_le b
      · simp [hax, hay]
        exact L.rel_refl L.bottom
  preserves_sup := by
    intro X hX
    let s : K.Obj → L.Obj := fun x => if K.Rel a x then b else L.bottom
    by_cases hSup : K.Rel a (K.sup X hX)
    · rcases ha X hX hSup with ⟨x₀, hx₀, hax₀⟩
      constructor
      · intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        by_cases hax : K.Rel a x
        · simp [hax, hSup]
          exact L.rel_refl b
        · simp [hax, hSup]
          exact L.bottom_le b
      · intro w hw
        simpa [hax₀, hSup] using hw ⟨x₀, hx₀, by simp [hax₀]⟩
    · constructor
      · intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        have hxSup : K.Rel x (K.sup X hX) := (K.sup_spec X hX).1 hx
        have hNot : ¬ K.Rel a x := by
          intro hax
          exact hSup (K.rel_trans hax hxSup)
        simp [hNot, hSup]
        exact L.rel_refl L.bottom
      · intro w hw
        simpa [hSup] using L.bottom_le w

/-- The value of a step function at its compact threshold is `b`. -/
@[simp] theorem stepFunction_at
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (a : K.Obj) (ha : IsCompact K a) (b : L.Obj) :
    stepFunction a ha b a = b := by
  simp [stepFunction, K.rel_refl a]

/-- A step function below `f(a)` lies below `f` pointwise. -/
theorem stepFunction_below
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (a : K.Obj)
    (ha : IsCompact K a)
    (b : L.Obj)
    (f : ContinuousMap K L)
    (hba : L.Rel b (f.toFun a)) :
    (Exponential.chpo K L).Rel (stepFunction a ha b) f := by
  refine Exponential.rel_mk ?_
  intro x
  by_cases hax : K.Rel a x
  · simpa [stepFunction, hax] using L.rel_trans hba (f.monotone' hax)
  · simpa [stepFunction, hax] using L.bottom_le (f.toFun x)

/-- Step functions with compact source and target are compact in the exponential
c.h.p.o. This is the basic compactness ingredient of Proposition 3.14. -/
theorem stepFunction_compact
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (a : K.Obj)
    (ha : IsCompact K a)
    (b : L.Obj)
    (hb : IsCompact L b) :
    IsCompact (Exponential.chpo K L) (stepFunction a ha b) := by
  intro F hF hStep
  have hbSup :
      L.Rel b (((Exponential.chpo K L).sup F hF).toFun a) := by
    have hAtA : L.Rel (stepFunction a ha b a) (((Exponential.chpo K L).sup F hF).toFun a) :=
      (Exponential.rel_iff.mp hStep) a
    simpa [stepFunction_at] using hAtA
  rcases hb (Exponential.evalPred F a) (Exponential.directed_eval hF a) hbSup with
    ⟨c, hc, hbc⟩
  rcases hc with ⟨f, hf, hfa⟩
  refine ⟨f, hf, Exponential.rel_mk ?_⟩
  intro x
  by_cases hax : K.Rel a x
  · have hmon : L.Rel (f.toFun a) (f.toFun x) := f.monotone' hax
    have hbfa : L.Rel b (f.toFun a) := by simpa [hfa] using hbc
    simpa [stepFunction, hax] using L.rel_trans hbfa hmon
  · simpa [stepFunction, hax] using L.bottom_le (f.toFun x)

/-! ## Bounded Completeness of Function Spaces -/

/-- Pointwise bounded suprema of an upper-bounded family of continuous maps. -/
noncomputable def boundedSupMap
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (hL : BoundedComplete L)
    (F : ContinuousMap K L → Prop)
    (u : ContinuousMap K L)
    (hu : (Exponential.chpo K L).IsUpperBound F u) :
    ContinuousMap K L where
  toFun := fun x =>
    Classical.choose <|
      hL (Exponential.evalPred F x) ⟨u.toFun x, by
        intro a ha
        rcases ha with ⟨f, hf, rfl⟩
        exact (Exponential.rel_iff.mp (hu hf)) x⟩
  monotone' := by
    intro x y hxy
    let gx : L.Obj :=
      Classical.choose <|
        hL (Exponential.evalPred F x) ⟨u.toFun x, by
          intro a ha
          rcases ha with ⟨f, hf, rfl⟩
          exact (Exponential.rel_iff.mp (hu hf)) x⟩
    let gy : L.Obj :=
      Classical.choose <|
        hL (Exponential.evalPred F y) ⟨u.toFun y, by
          intro a ha
          rcases ha with ⟨f, hf, rfl⟩
          exact (Exponential.rel_iff.mp (hu hf)) y⟩
    have hSpecX :
        L.IsLeastUpperBound (Exponential.evalPred F x) gx :=
      Classical.choose_spec <|
        hL (Exponential.evalPred F x) ⟨u.toFun x, by
          intro a ha
          rcases ha with ⟨f, hf, rfl⟩
          exact (Exponential.rel_iff.mp (hu hf)) x⟩
    have hSpecY :
        L.IsLeastUpperBound (Exponential.evalPred F y) gy :=
      Classical.choose_spec <|
        hL (Exponential.evalPred F y) ⟨u.toFun y, by
          intro a ha
          rcases ha with ⟨f, hf, rfl⟩
          exact (Exponential.rel_iff.mp (hu hf)) y⟩
    refine hSpecX.2 ?_
    intro a ha
    rcases ha with ⟨f, hf, rfl⟩
    exact L.rel_trans
      (f.monotone' hxy)
      (hSpecY.1 ⟨f, hf, rfl⟩)
  preserves_sup := by
    intro X hX
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      let gx : L.Obj :=
        Classical.choose <|
          hL (Exponential.evalPred F x) ⟨u.toFun x, by
            intro a ha
            rcases ha with ⟨f, hf, rfl⟩
            exact (Exponential.rel_iff.mp (hu hf)) x⟩
      let gSup : L.Obj :=
        Classical.choose <|
          hL (Exponential.evalPred F (K.sup X hX)) ⟨u.toFun (K.sup X hX), by
            intro a ha
            rcases ha with ⟨f, hf, rfl⟩
            exact (Exponential.rel_iff.mp (hu hf)) (K.sup X hX)⟩
      have hSpecX :
          L.IsLeastUpperBound (Exponential.evalPred F x) gx :=
        Classical.choose_spec <|
          hL (Exponential.evalPred F x) ⟨u.toFun x, by
            intro a ha
            rcases ha with ⟨f, hf, rfl⟩
            exact (Exponential.rel_iff.mp (hu hf)) x⟩
      have hSpecSup :
          L.IsLeastUpperBound (Exponential.evalPred F (K.sup X hX)) gSup :=
        Classical.choose_spec <|
          hL (Exponential.evalPred F (K.sup X hX)) ⟨u.toFun (K.sup X hX), by
            intro a ha
            rcases ha with ⟨f, hf, rfl⟩
            exact (Exponential.rel_iff.mp (hu hf)) (K.sup X hX)⟩
      exact hSpecX.2 <| by
        intro a ha
        rcases ha with ⟨f, hf, rfl⟩
        exact L.rel_trans
          ((f.preserves_sup X hX).1 ⟨x, hx, rfl⟩)
          (hSpecSup.1 ⟨f, hf, rfl⟩)
    · intro w hw
      let gSup : L.Obj :=
        Classical.choose <|
          hL (Exponential.evalPred F (K.sup X hX)) ⟨u.toFun (K.sup X hX), by
            intro a ha
            rcases ha with ⟨f, hf, rfl⟩
            exact (Exponential.rel_iff.mp (hu hf)) (K.sup X hX)⟩
      have hSpecSup :
          L.IsLeastUpperBound (Exponential.evalPred F (K.sup X hX)) gSup :=
        Classical.choose_spec <|
          hL (Exponential.evalPred F (K.sup X hX)) ⟨u.toFun (K.sup X hX), by
            intro a ha
            rcases ha with ⟨f, hf, rfl⟩
            exact (Exponential.rel_iff.mp (hu hf)) (K.sup X hX)⟩
      refine hSpecSup.2 ?_
      intro a ha
      rcases ha with ⟨f, hf, rfl⟩
      refine (f.preserves_sup X hX).2 ?_
      intro b hb
      rcases hb with ⟨x, hx, rfl⟩
      let gx : L.Obj :=
        Classical.choose <|
          hL (Exponential.evalPred F x) ⟨u.toFun x, by
            intro c hc
            rcases hc with ⟨f', hf', rfl⟩
            exact (Exponential.rel_iff.mp (hu hf')) x⟩
      have hSpecX :
          L.IsLeastUpperBound (Exponential.evalPred F x) gx :=
        Classical.choose_spec <|
          hL (Exponential.evalPred F x) ⟨u.toFun x, by
            intro c hc
            rcases hc with ⟨f', hf', rfl⟩
            exact (Exponential.rel_iff.mp (hu hf')) x⟩
      exact L.rel_trans
        (hSpecX.1 ⟨f, hf, rfl⟩)
        (hw ⟨x, hx, rfl⟩)

/-- The pointwise bounded supremum is the least upper bound in the exponential
c.h.p.o. -/
theorem boundedSupMap_spec
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (hL : BoundedComplete L)
    (F : ContinuousMap K L → Prop)
    (u : ContinuousMap K L)
    (hu : (Exponential.chpo K L).IsUpperBound F u) :
    (Exponential.chpo K L).IsLeastUpperBound F (boundedSupMap hL F u hu) := by
  constructor
  · intro f hf
    refine Exponential.rel_mk ?_
    intro x
    let gx : L.Obj :=
      Classical.choose <|
        hL (Exponential.evalPred F x) ⟨u.toFun x, by
          intro a ha
          rcases ha with ⟨f', hf', rfl⟩
          exact (Exponential.rel_iff.mp (hu hf')) x⟩
    have hSpecX :
        L.IsLeastUpperBound (Exponential.evalPred F x) gx :=
      Classical.choose_spec <|
        hL (Exponential.evalPred F x) ⟨u.toFun x, by
          intro a ha
          rcases ha with ⟨f', hf', rfl⟩
          exact (Exponential.rel_iff.mp (hu hf')) x⟩
    exact hSpecX.1 ⟨f, hf, rfl⟩
  · intro w hw
    refine Exponential.rel_mk ?_
    intro x
    let gx : L.Obj :=
      Classical.choose <|
        hL (Exponential.evalPred F x) ⟨u.toFun x, by
          intro a ha
          rcases ha with ⟨f, hf, rfl⟩
          exact (Exponential.rel_iff.mp (hu hf)) x⟩
    have hSpecX :
        L.IsLeastUpperBound (Exponential.evalPred F x) gx :=
      Classical.choose_spec <|
        hL (Exponential.evalPred F x) ⟨u.toFun x, by
          intro a ha
          rcases ha with ⟨f, hf, rfl⟩
          exact (Exponential.rel_iff.mp (hu hf)) x⟩
    exact hSpecX.2 (by
      intro a ha
      rcases ha with ⟨f, hf, rfl⟩
      exact (Exponential.rel_iff.mp (hw hf)) x)

/-- The exponential c.h.p.o. inherits bounded completeness from the codomain.
This is the bounded-complete half of Proposition 3.14. -/
theorem boundedComplete_exponential
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (hL : BoundedComplete L) :
    BoundedComplete (Exponential.chpo K L) := by
  intro F hUpper
  rcases hUpper with ⟨u, hu⟩
  exact ⟨boundedSupMap hL F u hu, boundedSupMap_spec hL F u hu⟩

/-- A chosen compact step-function datum below a target continuous map. The
source threshold is compact, and the target value is compact-below the actual
value of the target map at that source point. -/
structure StepApproxDatum
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (f : ContinuousMap K L) where
  source : K.Obj
  sourceCompact : IsCompact K source
  target : L.Obj
  targetCompactBelow : compactBelow L (f.toFun source) target

namespace StepApproxDatum

/-- The step function carried by a compact step-approximation datum. -/
noncomputable def toMap
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {f : ContinuousMap K L}
    (d : StepApproxDatum f) :
    ContinuousMap K L :=
  stepFunction d.source d.sourceCompact d.target

/-- Every chosen step-approximation datum yields a compact-below approximant of
the target map in the exponential c.h.p.o. -/
theorem toMap_compactBelow
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {f : ContinuousMap K L}
    (d : StepApproxDatum f) :
    compactBelow (Exponential.chpo K L) f d.toMap := by
  refine ⟨stepFunction_compact d.source d.sourceCompact d.target d.targetCompactBelow.1, ?_⟩
  exact stepFunction_below d.source d.sourceCompact d.target f d.targetCompactBelow.2

end StepApproxDatum

/-- A finite family of compact step-approximation data below a continuous map
admits a chosen compact-below least upper bound in the exponential c.h.p.o. -/
theorem exists_listStepApproxDatum_compactBelow_isLeastUpperBound
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (hL : BoundedComplete L)
    (f : ContinuousMap K L)
    (steps : List (StepApproxDatum f)) :
    ∃ h : ContinuousMap K L,
      compactBelow (Exponential.chpo K L) f h ∧
      (Exponential.chpo K L).IsLeastUpperBound
        (fun g => g ∈ steps.map StepApproxDatum.toMap) h := by
  let maps := steps.map StepApproxDatum.toMap
  have hcompactBelow :
      ∀ g : ContinuousMap K L, g ∈ maps → compactBelow (Exponential.chpo K L) f g := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨d, hd, rfl⟩
    exact d.toMap_compactBelow
  simpa [maps] using
    (exists_list_compactBelow_isLeastUpperBound
      (K := Exponential.chpo K L)
      (hK := boundedComplete_exponential hL)
      (x := f)
      maps
      hcompactBelow)

/-- A chosen finite-step approximant assembled from a finite family of compact
step-approximation data below a target map. -/
noncomputable def assembleStepApproximants
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (hL : BoundedComplete L)
    (f : ContinuousMap K L)
    (steps : List (StepApproxDatum f)) :
    ContinuousMap K L :=
  Classical.choose (exists_listStepApproxDatum_compactBelow_isLeastUpperBound hL f steps)

/-- The chosen finite-step approximant remains compact-below the target map. -/
theorem assembleStepApproximants_compactBelow
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (hL : BoundedComplete L)
    (f : ContinuousMap K L)
    (steps : List (StepApproxDatum f)) :
    compactBelow (Exponential.chpo K L) f (assembleStepApproximants hL f steps) :=
  (Classical.choose_spec (exists_listStepApproxDatum_compactBelow_isLeastUpperBound hL f steps)).1

/-- The chosen finite-step approximant is the least upper bound of the finite
step maps from which it is assembled. -/
theorem assembleStepApproximants_isLeastUpperBound
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (hL : BoundedComplete L)
    (f : ContinuousMap K L)
    (steps : List (StepApproxDatum f)) :
    (Exponential.chpo K L).IsLeastUpperBound
      (fun g => g ∈ steps.map StepApproxDatum.toMap)
      (assembleStepApproximants hL f steps) :=
  (Classical.choose_spec (exists_listStepApproxDatum_compactBelow_isLeastUpperBound hL f steps)).2

/-- Enlarging the finite family of step data can only enlarge the chosen
assembled finite-step approximant. -/
theorem assembleStepApproximants_mono
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (hL : BoundedComplete L)
    (f : ContinuousMap K L)
    {steps₁ steps₂ : List (StepApproxDatum f)}
    (hsubset : ∀ d : StepApproxDatum f, d ∈ steps₁ → d ∈ steps₂) :
    (Exponential.chpo K L).Rel
      (assembleStepApproximants hL f steps₁)
      (assembleStepApproximants hL f steps₂) := by
  have hUpper₂ :
      (Exponential.chpo K L).IsUpperBound
        (fun g => g ∈ steps₂.map StepApproxDatum.toMap)
        (assembleStepApproximants hL f steps₂) :=
    (assembleStepApproximants_isLeastUpperBound hL f steps₂).1
  have hUpper₁ :
      (Exponential.chpo K L).IsUpperBound
        (fun g => g ∈ steps₁.map StepApproxDatum.toMap)
        (assembleStepApproximants hL f steps₂) := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨d, hd, rfl⟩
    exact hUpper₂ (by
      exact List.mem_map.mpr ⟨d, hsubset d hd, rfl⟩)
  exact (assembleStepApproximants_isLeastUpperBound hL f steps₁).2 hUpper₁

/-! ## A Chosen Finite-Step Basis Interface -/

/-- A chosen algebraic basis of compact approximants for a continuous map in a
function space, capturing the step-function content of Proposition 3.14. -/
structure FiniteStepBasis
    (K : HomotopyScottDomain)
    (L : HomotopyScottDomain)
    (f : ContinuousMap K L) where
  basis : ContinuousMap K L → Prop
  basis_iff :
    ∀ g : ContinuousMap K L,
      basis g ↔ compactBelow (Exponential.chpo K L) f g
  directed : (Exponential.chpo K L).Directed basis
  exact : (Exponential.chpo K L).IsLeastUpperBound basis f

/-- Proposition 3.14, packaged in chosen-data form: once every continuous map
admits a directed finite-step basis of compact approximants, the exponential of
Scott domains is again a Scott domain. -/
def exponentialScottDomainOfFiniteStepBasis
    (K : HomotopyScottDomain)
    (L : HomotopyScottDomain)
    (hBasis : ∀ f : ContinuousMap K L, Nonempty (FiniteStepBasis K L f)) :
    HomotopyScottDomain where
  carrier := Exponential.chpo K L
  algebraic := by
    intro f
    rcases hBasis f with ⟨B⟩
    refine ⟨(directed_congr (Exponential.chpo K L).toHomotopyPartialOrder B.basis_iff).mp B.directed, ?_⟩
    exact (isLeastUpperBound_congr (Exponential.chpo K L).toHomotopyPartialOrder B.basis_iff).mp B.exact
  boundedComplete := boundedComplete_exponential L.boundedComplete

/-- Proposition 3.14 specialized to self-exponentials `Kn+1 = [Kn → Kn]`. -/
def selfExponentialScottDomainOfFiniteStepBasis
    (K : HomotopyScottDomain)
    (hBasis : ∀ f : ContinuousMap K K, Nonempty (FiniteStepBasis K K f)) :
    HomotopyScottDomain :=
  exponentialScottDomainOfFiniteStepBasis K K hBasis

/-! ## Step Function Properties -/

/-- A step function with bottom source yields the constant map. -/
theorem stepFunction_bottom_source
    {K L : CompleteHomotopyPartialOrder} (ha : IsCompact K K.bottom) (b : L.Obj) :
    (Exponential.chpo K L).Rel (stepFunction K.bottom ha b) (ContinuousMap.const K L b) := by
  refine Exponential.rel_mk ?_
  intro x; simp only [stepFunction, K.bottom_le x, ite_true]; exact L.rel_refl b

/-- The bottom continuous map is a step function with bottom arguments. -/
theorem bottom_map_is_step
    {K L : CompleteHomotopyPartialOrder} (ha : IsCompact K K.bottom) :
    (Exponential.chpo K L).Rel (stepFunction K.bottom ha L.bottom) (Exponential.chpo K L).bottom := by
  refine Exponential.rel_mk ?_
  intro x; simp only [stepFunction, K.bottom_le x, ite_true]; exact L.rel_refl L.bottom

/-- The bottom continuous map is compact in the exponential c.h.p.o. -/
theorem bottom_map_compact (K L : CompleteHomotopyPartialOrder) :
    IsCompact (Exponential.chpo K L) (Exponential.chpo K L).bottom :=
  bottom_isCompact (Exponential.chpo K L)

/-- The exponential bottom map is compact-below every continuous map. -/
theorem bottom_map_compactBelow {K L : CompleteHomotopyPartialOrder} (f : ContinuousMap K L) :
    compactBelow (Exponential.chpo K L) f (Exponential.chpo K L).bottom :=
  bottom_compactBelow (Exponential.chpo K L) f

end HigherLambdaModel.Domain
