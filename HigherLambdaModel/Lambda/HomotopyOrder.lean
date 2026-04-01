/-
# Homotopy Partial Orders and CHP O

This module formalizes the domain-theoretic layer used in Definitions 2.3-2.6
of "The Theory of an Arbitrary Higher λ-Model" (arXiv:2111.07092):

- homotopy partial orders (h.p.o.)
- directed predicates
- complete homotopy partial orders (c.h.p.o.)
- continuous maps
- the `CHPO` morphism interface

The paper phrases these notions through ambient ∞-categorical semantics. Here
we package the order-theoretic content constructively as explicit data and
proofs, so later semantic constructions can refer to chosen bottoms and
suprema without appealing to choice.
-/

import HigherLambdaModel.Lambda.TruncationCore

namespace HigherLambdaModel.Lambda.HomotopyOrder

open HigherLambdaModel.Lambda.TruncationCore

universe u v w

/-! ## Predicate Images -/

/-- The image of a predicate under a function. -/
def image {α : Sort u} {β : Sort v} (f : α → β) (X : α → Prop) : β → Prop :=
  fun y => ∃ x, X x ∧ f x = y

theorem image_id {α : Sort u} (X : α → Prop) :
    image (fun x => x) X = X := by
  funext x
  apply propext
  constructor
  · intro hx
    rcases hx with ⟨x', hx', hEq⟩
    simpa [hEq] using hx'
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem image_comp {α : Sort u} {β : Sort v} {γ : Sort w}
    (g : β → γ) (f : α → β) (X : α → Prop) :
    image g (image f X) = image (fun x => g (f x)) X := by
  funext z
  apply propext
  constructor
  · intro hz
    rcases hz with ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  · intro hz
    rcases hz with ⟨x, hx, rfl⟩
    exact ⟨f x, ⟨x, hx, rfl⟩, rfl⟩

/-! ## Homotopy Partial Orders (Definition 2.3) -/

/-- A homotopy partial order consists of hom-spaces that are either empty or
contractible. The induced relation `Rel x y` records mere inhabitation of the
corresponding hom-space. -/
structure HomotopyPartialOrder where
  Obj : Type u
  Hom : Obj → Obj → Sort v
  id : ∀ x : Obj, Hom x x
  comp : ∀ {x y z : Obj}, Hom x y → Hom y z → Hom x z
  hom_contractible_or_empty :
    ∀ x y : Obj, (Hom x y → False) ∨ IsContractible (Hom x y)

namespace HomotopyPartialOrder

/-- The induced preorder-like relation of an h.p.o. -/
def Rel (K : HomotopyPartialOrder) (x y : K.Obj) : Prop :=
  Nonempty (K.Hom x y)

/-- Reflexivity of the induced h.p.o. relation. -/
theorem rel_refl (K : HomotopyPartialOrder) (x : K.Obj) : Rel K x x :=
  ⟨K.id x⟩

/-- Transitivity of the induced h.p.o. relation. -/
theorem rel_trans
    (K : HomotopyPartialOrder)
    {x y z : K.Obj} :
    Rel K x y → Rel K y z → Rel K x z := by
  intro hxy hyz
  rcases hxy with ⟨f⟩
  rcases hyz with ⟨g⟩
  exact ⟨K.comp f g⟩

/-- A predicate is directed when it is inhabited and every pair of points has a
common upper bound inside the same predicate. -/
def Directed (K : HomotopyPartialOrder) (X : K.Obj → Prop) : Prop :=
  (∃ x, X x) ∧
    ∀ {x y : K.Obj}, X x → X y →
      ∃ z, X z ∧ Rel K x z ∧ Rel K y z

/-- An upper bound of a predicate with respect to the induced h.p.o. relation. -/
def IsUpperBound (K : HomotopyPartialOrder) (X : K.Obj → Prop) (z : K.Obj) : Prop :=
  ∀ ⦃x : K.Obj⦄, X x → Rel K x z

/-- A least upper bound of a predicate with respect to the induced h.p.o.
relation. -/
def IsLeastUpperBound (K : HomotopyPartialOrder) (X : K.Obj → Prop) (z : K.Obj) : Prop :=
  IsUpperBound K X z ∧
    ∀ ⦃w : K.Obj⦄, IsUpperBound K X w → Rel K z w

end HomotopyPartialOrder

/-! ## Complete Homotopy Partial Orders (Definition 2.4) -/

/-- A complete homotopy partial order is an h.p.o. equipped with an initial
object and a chosen supremum for every directed predicate. -/
structure CompleteHomotopyPartialOrder extends HomotopyPartialOrder where
  bottom : Obj
  bottom_le :
    ∀ x : Obj, HomotopyPartialOrder.Rel toHomotopyPartialOrder bottom x
  sup :
    (X : Obj → Prop) →
      HomotopyPartialOrder.Directed toHomotopyPartialOrder X →
        Obj
  sup_spec :
    ∀ (X : Obj → Prop)
      (hX : HomotopyPartialOrder.Directed toHomotopyPartialOrder X),
      HomotopyPartialOrder.IsLeastUpperBound
        toHomotopyPartialOrder X (sup X hX)

namespace CompleteHomotopyPartialOrder

/-- The chosen supremum of a directed predicate is indeed an upper bound. -/
theorem sup_isUpperBound
    (K : CompleteHomotopyPartialOrder)
    (X : K.Obj → Prop)
    (hX : HomotopyPartialOrder.Directed K.toHomotopyPartialOrder X) :
    HomotopyPartialOrder.IsUpperBound
      K.toHomotopyPartialOrder X (K.sup X hX) :=
  (K.sup_spec X hX).1

/-- The chosen supremum is least among upper bounds. -/
theorem sup_isLeast
    (K : CompleteHomotopyPartialOrder)
    (X : K.Obj → Prop)
    (hX : HomotopyPartialOrder.Directed K.toHomotopyPartialOrder X)
    {w : K.Obj}
    (hw : HomotopyPartialOrder.IsUpperBound K.toHomotopyPartialOrder X w) :
    HomotopyPartialOrder.Rel K.toHomotopyPartialOrder (K.sup X hX) w :=
  (K.sup_spec X hX).2 hw

end CompleteHomotopyPartialOrder

/-! ## Continuous Maps (Definition 2.5) -/

/-- A continuous map between c.h.p.o.'s is monotone and sends the chosen
supremum of each directed predicate to a least upper bound of the image
predicate. -/
structure ContinuousMap
    (K : CompleteHomotopyPartialOrder)
    (L : CompleteHomotopyPartialOrder) where
  toFun : K.Obj → L.Obj
  monotone' :
    ∀ {x y : K.Obj},
      HomotopyPartialOrder.Rel K.toHomotopyPartialOrder x y →
        HomotopyPartialOrder.Rel L.toHomotopyPartialOrder (toFun x) (toFun y)
  preserves_sup :
    ∀ (X : K.Obj → Prop)
      (hX : HomotopyPartialOrder.Directed K.toHomotopyPartialOrder X),
      HomotopyPartialOrder.IsLeastUpperBound
        L.toHomotopyPartialOrder (image toFun X) (toFun (K.sup X hX))

namespace ContinuousMap

instance
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder} :
    CoeFun (ContinuousMap K L) (fun _ => K.Obj → L.Obj) where
  coe f := f.toFun

/-- The image of a directed predicate under a continuous map is directed. -/
theorem directed_image
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (f : ContinuousMap K L)
    {X : K.Obj → Prop}
    (hX : HomotopyPartialOrder.Directed K.toHomotopyPartialOrder X) :
    HomotopyPartialOrder.Directed L.toHomotopyPartialOrder (image f X) := by
  rcases hX with ⟨⟨x, hx⟩, hdir⟩
  refine ⟨⟨f x, ⟨x, hx, rfl⟩⟩, ?_⟩
  intro a b ha hb
  rcases ha with ⟨x, hx, rfl⟩
  rcases hb with ⟨y, hy, rfl⟩
  rcases hdir hx hy with ⟨z, hz, hxz, hyz⟩
  exact ⟨f z, ⟨z, hz, rfl⟩, f.monotone' hxz, f.monotone' hyz⟩

/-- The identity map is continuous. -/
def id (K : CompleteHomotopyPartialOrder) : ContinuousMap K K where
  toFun := fun x => x
  monotone' := by
    intro x y hxy
    exact hxy
  preserves_sup := by
    intro X hX
    simpa [image_id] using K.sup_spec X hX

/-- Composition of continuous maps is continuous. -/
def comp
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    (g : ContinuousMap L M)
    (f : ContinuousMap K L) :
    ContinuousMap K M where
  toFun := fun x => g (f x)
  monotone' := by
    intro x y hxy
    exact g.monotone' (f.monotone' hxy)
  preserves_sup := by
    intro X hX
    have hImage :
        HomotopyPartialOrder.Directed L.toHomotopyPartialOrder (image f X) :=
      directed_image f hX
    have hChosen :
        HomotopyPartialOrder.IsLeastUpperBound
          M.toHomotopyPartialOrder
          (image g (image f X))
          (g (L.sup (image f X) hImage)) :=
      g.preserves_sup (image f X) hImage
    have hhf_to_supL :
        HomotopyPartialOrder.Rel
          L.toHomotopyPartialOrder
          (f (K.sup X hX))
          (L.sup (image f X) hImage) :=
      (f.preserves_sup X hX).2
        ((L.sup_spec (image f X) hImage).1)
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact g.monotone' ((f.preserves_sup X hX).1 ⟨x, hx, rfl⟩)
    · intro w hw
      have hw' :
          HomotopyPartialOrder.IsUpperBound
            M.toHomotopyPartialOrder
            (image g (image f X))
            w := by
        intro z hz
        rcases hz with ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        exact hw ⟨x, hx, rfl⟩
      have hToChosen :
          HomotopyPartialOrder.Rel
            M.toHomotopyPartialOrder
            (g (f (K.sup X hX)))
            (g (L.sup (image f X) hImage)) :=
        g.monotone' hhf_to_supL
      have hChosenToW :
          HomotopyPartialOrder.Rel
            M.toHomotopyPartialOrder
            (g (L.sup (image f X) hImage))
            w :=
        hChosen.2 hw'
      exact HomotopyPartialOrder.rel_trans
        M.toHomotopyPartialOrder hToChosen hChosenToW

end ContinuousMap

/-! ## CHP O (Definition 2.6) -/

namespace CHPO

/-- Objects of `CHPO`. -/
abbrev Obj := CompleteHomotopyPartialOrder

/-- Morphisms in `CHPO` are continuous maps. -/
abbrev Hom (K L : Obj) := ContinuousMap K L

/-- Identity morphism in `CHPO`. -/
def id (K : Obj) : Hom K K :=
  ContinuousMap.id K

/-- Composition of morphisms in `CHPO`. -/
def comp {K L M : Obj} (g : Hom L M) (f : Hom K L) : Hom K M :=
  ContinuousMap.comp g f

end CHPO

end HigherLambdaModel.Lambda.HomotopyOrder
