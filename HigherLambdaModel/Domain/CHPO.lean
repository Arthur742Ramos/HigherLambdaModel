import HigherLambdaModel.Lambda.HomotopyOrder

/-!
# CHPO Constructions

This module formalizes the Section 3 order-theoretic constructions from
Martínez-Rivillas and de Queiroz, *The K∞ Homotopy λ-Model*:

- products of h.p.o.'s and c.h.p.o.'s
- function spaces of continuous maps with the pointwise order
- continuity of evaluation, abstraction, and composition
- projective systems and their inverse limits

The implementation stays close to the repository's chosen-data presentation:
suprema, bottoms, and continuity witnesses are all explicit structure fields.
-/

namespace HigherLambdaModel.Domain

open Classical
open HigherLambdaModel.Lambda.TruncationCore
open HigherLambdaModel.Lambda.HomotopyOrder

universe u v w u' v' w'

/-! ## Basic Helper Lemmas -/

/-- Contractible types are closed under binary products. -/
theorem isContractible_prod
    {α : Sort u} {β : Sort v}
    (hα : IsContractible α) (hβ : IsContractible β) :
    IsContractible (α ×' β) := by
  rcases hα with ⟨a, ha⟩
  rcases hβ with ⟨b, hb⟩
  refine ⟨⟨a, b⟩, ?_⟩
  intro x
  cases x with
  | mk x y =>
    cases ha x
    cases hb y
    rfl

/-- If a hom-space is inhabited, then the h.p.o. axiom supplies its
contractibility witness. -/
theorem hom_contractible_of_rel
    (K : HomotopyPartialOrder)
    {x y : K.Obj}
    (hxy : K.Rel x y) :
    IsContractible (K.Hom x y) := by
  rcases hxy with ⟨f⟩
  rcases K.hom_contractible_or_empty x y with hEmpty | hContr
  · exact False.elim (hEmpty f)
  · exact hContr

/-- Two least upper bounds of the same predicate are equivalent in the induced
homotopy order. -/
theorem equivalent_of_isLeastUpperBound
    (K : HomotopyPartialOrder)
    {X : K.Obj → Prop} {x y : K.Obj}
    (hx : K.IsLeastUpperBound X x)
    (hy : K.IsLeastUpperBound X y) :
    K.Rel x y ∧ K.Rel y x := by
  exact ⟨hx.2 hy.1, hy.2 hx.1⟩

/-- Transport a least-upper-bound witness across an equivalence in the
underlying h.p.o. -/
theorem isLeastUpperBound_of_equiv
    (K : HomotopyPartialOrder)
    {X : K.Obj → Prop} {x y : K.Obj}
    (hx : K.IsLeastUpperBound X x)
    (hxy : K.Rel x y)
    (hyx : K.Rel y x) :
    K.IsLeastUpperBound X y := by
  constructor
  · intro z hz
    exact K.rel_trans (hx.1 hz) hxy
  · intro z hz
    exact K.rel_trans hyx (hx.2 hz)

/-- Extensionality for continuous maps. The proof fields are propositions, so
equality is determined by the underlying function. -/
@[ext] theorem ContinuousMap.ext
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {f g : ContinuousMap K L}
    (h : ∀ x, f x = g x) :
    f = g := by
  cases f
  cases g
  simp [ContinuousMap.mk.injEq]
  exact funext h

/-! ## Products (Propositions 3.2 and 3.3) -/

namespace Product

/-- Proposition 3.2: the product of two h.p.o.'s is an h.p.o. -/
def hpo (K : HomotopyPartialOrder) (L : HomotopyPartialOrder) :
    HomotopyPartialOrder where
  Obj := K.Obj × L.Obj
  Hom := fun x y => K.Hom x.1 y.1 ×' L.Hom x.2 y.2
  id := fun x => ⟨K.id x.1, L.id x.2⟩
  comp := fun f g => ⟨K.comp f.1 g.1, L.comp f.2 g.2⟩
  hom_contractible_or_empty := by
    intro x y
    rcases K.hom_contractible_or_empty x.1 y.1 with hKEmpty | hKContr
    · left
      intro h
      exact hKEmpty h.1
    · rcases L.hom_contractible_or_empty x.2 y.2 with hLEmpty | hLContr
      · left
        intro h
        exact hLEmpty h.2
      · right
        exact isContractible_prod hKContr hLContr

/-- Pointwise introduction into the product relation. -/
theorem rel_mk
    {K : HomotopyPartialOrder} {L : HomotopyPartialOrder}
    {x y : (hpo K L).Obj}
    (h₁ : K.Rel x.1 y.1) (h₂ : L.Rel x.2 y.2) :
    (hpo K L).Rel x y := by
  rcases h₁ with ⟨f⟩
  rcases h₂ with ⟨g⟩
  exact ⟨⟨f, g⟩⟩

/-- The product relation is coordinatewise. -/
theorem rel_iff
    {K : HomotopyPartialOrder} {L : HomotopyPartialOrder}
    {x y : (hpo K L).Obj} :
    (hpo K L).Rel x y ↔ K.Rel x.1 y.1 ∧ L.Rel x.2 y.2 := by
  constructor
  · intro h
    rcases h with ⟨f, g⟩
    exact ⟨⟨f⟩, ⟨g⟩⟩
  · intro h
    exact rel_mk h.1 h.2

/-- First projection of a predicate on a product object type. -/
def fstPred
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (X : (K.Obj × L.Obj) → Prop) :
    K.Obj → Prop :=
  fun x => ∃ y, X (x, y)

/-- Second projection of a predicate on a product object type. -/
def sndPred
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (X : (K.Obj × L.Obj) → Prop) :
    L.Obj → Prop :=
  fun y => ∃ x, X (x, y)

/-- The image of a predicate under the first projection is the first projected
predicate. -/
theorem image_fstPred
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (X : (K.Obj × L.Obj) → Prop) :
    image (fun p : K.Obj × L.Obj => p.fst) X = fstPred X := by
  funext x
  apply propext
  constructor
  · intro hx
    rcases hx with ⟨p, hp, hpEq⟩
    rcases p with ⟨a, b⟩
    simp at hpEq
    subst hpEq
    exact ⟨b, hp⟩
  · intro hx
    rcases hx with ⟨y, hxy⟩
    exact ⟨(x, y), hxy, rfl⟩

/-- The image of a predicate under the second projection is the second
projected predicate. -/
theorem image_sndPred
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (X : (K.Obj × L.Obj) → Prop) :
    image (fun p : K.Obj × L.Obj => p.snd) X = sndPred X := by
  funext y
  apply propext
  constructor
  · intro hy
    rcases hy with ⟨p, hp, hpEq⟩
    rcases p with ⟨a, b⟩
    simp at hpEq
    subst hpEq
    exact ⟨a, hp⟩
  · intro hy
    rcases hy with ⟨x, hxy⟩
    exact ⟨(x, y), hxy, rfl⟩

/-- Directed predicates on products project to directed predicates on the first
factor. -/
theorem directed_fst
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {X : (K.Obj × L.Obj) → Prop}
    (hX : (hpo K.toHomotopyPartialOrder L.toHomotopyPartialOrder).Directed X) :
    K.Directed (fstPred X) := by
  rcases hX with ⟨⟨x, hx⟩, hdir⟩
  refine ⟨⟨x.1, x.2, hx⟩, ?_⟩
  intro a b ha hb
  rcases ha with ⟨a₂, ha⟩
  rcases hb with ⟨b₂, hb⟩
  rcases hdir ha hb with ⟨c, hc, hac, hbc⟩
  exact ⟨c.1, ⟨c.2, hc⟩, (rel_iff.mp hac).1, (rel_iff.mp hbc).1⟩

/-- Directed predicates on products project to directed predicates on the
second factor. -/
theorem directed_snd
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {X : (K.Obj × L.Obj) → Prop}
    (hX : (hpo K.toHomotopyPartialOrder L.toHomotopyPartialOrder).Directed X) :
    L.Directed (sndPred X) := by
  rcases hX with ⟨⟨x, hx⟩, hdir⟩
  refine ⟨⟨x.2, x.1, hx⟩, ?_⟩
  intro a b ha hb
  rcases ha with ⟨a₁, ha⟩
  rcases hb with ⟨b₁, hb⟩
  rcases hdir ha hb with ⟨c, hc, hac, hbc⟩
  exact ⟨c.2, ⟨c.1, hc⟩, (rel_iff.mp hac).2, (rel_iff.mp hbc).2⟩

/-- Proposition 3.3: the product of two c.h.p.o.'s is a c.h.p.o. -/
def chpo (K : CompleteHomotopyPartialOrder) (L : CompleteHomotopyPartialOrder) :
    CompleteHomotopyPartialOrder where
  toHomotopyPartialOrder := hpo K.toHomotopyPartialOrder L.toHomotopyPartialOrder
  bottom := (K.bottom, L.bottom)
  bottom_le := by
    intro x
    exact rel_mk (K.bottom_le x.1) (L.bottom_le x.2)
  sup := fun X hX =>
    (K.sup (fstPred X) (directed_fst hX), L.sup (sndPred X) (directed_snd hX))
  sup_spec := by
    intro X hX
    constructor
    · intro x hx
      refine rel_mk ?_ ?_
      · exact (K.sup_spec (fstPred X) (directed_fst hX)).1 ⟨x.2, hx⟩
      · exact (L.sup_spec (sndPred X) (directed_snd hX)).1 ⟨x.1, hx⟩
    · intro w hw
      refine rel_mk ?_ ?_
      · refine (K.sup_spec (fstPred X) (directed_fst hX)).2 ?_
        intro x hx
        rcases hx with ⟨y, hxy⟩
        exact (rel_iff.mp (hw hxy)).1
      · refine (L.sup_spec (sndPred X) (directed_snd hX)).2 ?_
        intro y hy
        rcases hy with ⟨x, hxy⟩
        exact (rel_iff.mp (hw hxy)).2

end Product

/-! ## Basic Continuous Maps into and out of Products -/

/-- The constant map into a c.h.p.o. is continuous. -/
def ContinuousMap.const
    (K : CompleteHomotopyPartialOrder)
    (L : CompleteHomotopyPartialOrder)
    (y : L.Obj) :
    ContinuousMap K L where
  toFun := fun _ => y
  monotone' := by
    intro x x' hxx'
    exact L.rel_refl y
  preserves_sup := by
    intro X hX
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, hEq⟩
      simpa [hEq] using L.rel_refl y
    · intro w hw
      rcases hX.1 with ⟨x, hx⟩
      exact hw ⟨x, hx, rfl⟩

/-- The first projection on a product c.h.p.o. is continuous. -/
def fstContinuous
    (K : CompleteHomotopyPartialOrder)
    (L : CompleteHomotopyPartialOrder) :
    ContinuousMap (Product.chpo K L) K where
  toFun := fun x => x.1
  monotone' := by
    intro x y hxy
    exact (Product.rel_iff.mp hxy).1
  preserves_sup := by
    intro X hX
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact (K.sup_spec (Product.fstPred X) (Product.directed_fst hX)).1 ⟨x.2, hx⟩
    · intro w hw
      refine (K.sup_spec (Product.fstPred X) (Product.directed_fst hX)).2 ?_
      intro z hz
      rcases hz with ⟨y, hzy⟩
      exact hw ⟨(z, y), hzy, rfl⟩

/-- The second projection on a product c.h.p.o. is continuous. -/
def sndContinuous
    (K : CompleteHomotopyPartialOrder)
    (L : CompleteHomotopyPartialOrder) :
    ContinuousMap (Product.chpo K L) L where
  toFun := fun x => x.2
  monotone' := by
    intro x y hxy
    exact (Product.rel_iff.mp hxy).2
  preserves_sup := by
    intro X hX
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact (L.sup_spec (Product.sndPred X) (Product.directed_snd hX)).1 ⟨x.1, hx⟩
    · intro w hw
      refine (L.sup_spec (Product.sndPred X) (Product.directed_snd hX)).2 ?_
      intro z hz
      rcases hz with ⟨x, hxz⟩
      exact hw ⟨(x, z), hxz, rfl⟩

/-- Pairing of continuous maps into a product is continuous. -/
def ContinuousMap.pair
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    (f : ContinuousMap K L)
    (g : ContinuousMap K M) :
    ContinuousMap K (Product.chpo L M) where
  toFun := fun x => (f x, g x)
  monotone' := by
    intro x y hxy
    exact Product.rel_mk (f.monotone' hxy) (g.monotone' hxy)
  preserves_sup := by
    intro X hX
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact Product.rel_mk
        ((f.preserves_sup X hX).1 ⟨x, hx, rfl⟩)
        ((g.preserves_sup X hX).1 ⟨x, hx, rfl⟩)
    · intro w hw
      refine Product.rel_mk ?_ ?_
      · refine (f.preserves_sup X hX).2 ?_
        intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        exact (Product.rel_iff.mp (hw ⟨x, hx, rfl⟩)).1
      · refine (g.preserves_sup X hX).2 ?_
        intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        exact (Product.rel_iff.mp (hw ⟨x, hx, rfl⟩)).2

/-! ## Directed Suprema of Continuous Maps (Lemma 3.1) -/

namespace Exponential

/-- The h.p.o. relation on continuous maps is the pointwise relation. The
hom-space itself keeps the pointwise higher-simplex data. -/
def hpo
    (K : CompleteHomotopyPartialOrder)
    (L : CompleteHomotopyPartialOrder) :
    HomotopyPartialOrder where
  Obj := ContinuousMap K L
  Hom := fun f g => ∀ x : K.Obj, L.Hom (f x) (g x)
  id := fun f x => L.id (f x)
  comp := fun α β x => L.comp (α x) (β x)
  hom_contractible_or_empty := by
    intro f g
    by_cases hfg : Nonempty (∀ x : K.Obj, L.Hom (f x) (g x))
    · right
      let center : ∀ x : K.Obj, L.Hom (f x) (g x) := Classical.choice hfg
      refine ⟨center, ?_⟩
      intro h
      funext x
      exact contractible_is_prop
        (hom_contractible_of_rel L.toHomotopyPartialOrder ⟨center x⟩)
        (center x) (h x)
    · left
      intro h
      exact hfg ⟨h⟩

/-- Pointwise introduction into the exponential relation. -/
theorem rel_mk
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {f g : ContinuousMap K L}
    (hfg : ∀ x : K.Obj, L.Rel (f x) (g x)) :
    (hpo K L).Rel f g := by
  refine ⟨fun x => Classical.choice (hfg x)⟩

/-- The exponential relation is pointwise. -/
theorem rel_iff
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {f g : ContinuousMap K L} :
    (hpo K L).Rel f g ↔ ∀ x : K.Obj, L.Rel (f x) (g x) := by
  constructor
  · intro h x
    rcases h with ⟨h⟩
    exact ⟨h x⟩
  · intro h
    exact rel_mk h

/-- The pointwise image of a predicate of continuous maps at a fixed point. -/
def evalPred
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (F : ContinuousMap K L → Prop)
    (x : K.Obj) :
    L.Obj → Prop :=
  image (fun f : ContinuousMap K L => f x) F

/-- A directed family of continuous maps is directed pointwise. -/
theorem directed_eval
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {F : ContinuousMap K L → Prop}
    (hF : (hpo K L).Directed F)
    (x : K.Obj) :
    L.Directed (evalPred F x) := by
  rcases hF with ⟨⟨f, hf⟩, hdir⟩
  refine ⟨⟨f.toFun x, ⟨f, hf, rfl⟩⟩, ?_⟩
  intro a b ha hb
  rcases ha with ⟨f, hf, rfl⟩
  rcases hb with ⟨g, hg, rfl⟩
  rcases hdir hf hg with ⟨h, hh, hfh, hgh⟩
  exact ⟨h.toFun x, ⟨h, hh, rfl⟩, (rel_iff.mp hfh) x, (rel_iff.mp hgh) x⟩

/-- Lemma 3.1: the pointwise supremum of a directed family of continuous maps
is again continuous. -/
def directedSupMap
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    (F : ContinuousMap K L → Prop)
    (hF : (hpo K L).Directed F) :
    ContinuousMap K L where
  toFun := fun x => L.sup (evalPred F x) (directed_eval hF x)
  monotone' := by
    intro x y hxy
    refine (L.sup_spec (evalPred F x) (directed_eval hF x)).2 ?_
    intro z hz
    rcases hz with ⟨f, hf, rfl⟩
    exact L.rel_trans
      (f.monotone' hxy)
      ((L.sup_spec (evalPred F y) (directed_eval hF y)).1 ⟨f, hf, rfl⟩)
  preserves_sup := by
    intro X hX
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      refine (L.sup_spec (evalPred F x) (directed_eval hF x)).2 ?_
      intro a ha
      rcases ha with ⟨f, hf, rfl⟩
      exact L.rel_trans
        ((f.preserves_sup X hX).1 ⟨x, hx, rfl⟩)
        ((L.sup_spec (evalPred F (K.sup X hX))
          (directed_eval hF (K.sup X hX))).1 ⟨f, hf, rfl⟩)
    · intro w hw
      have hEvalSup :
          L.IsUpperBound
            (evalPred F (K.sup X hX))
            w := by
        intro a ha
        rcases ha with ⟨f, hf, rfl⟩
        refine (f.preserves_sup X hX).2 ?_
        intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        exact L.rel_trans
          ((L.sup_spec (evalPred F x) (directed_eval hF x)).1 ⟨f, hf, rfl⟩)
          (hw ⟨x, hx, rfl⟩)
      exact (L.sup_spec
        (evalPred F (K.sup X hX))
        (directed_eval hF (K.sup X hX))).2 hEvalSup

/-- Proposition 3.5 and Definition 3.8: the continuous maps `[K → L]` form a
c.h.p.o. under the pointwise order. -/
def chpo
    (K : CompleteHomotopyPartialOrder)
    (L : CompleteHomotopyPartialOrder) :
    CompleteHomotopyPartialOrder where
  toHomotopyPartialOrder := hpo K L
  bottom := ContinuousMap.const K L L.bottom
  bottom_le := by
    intro f
    refine rel_mk ?_
    intro x
    exact L.bottom_le (f.toFun x)
  sup := fun F hF => directedSupMap F hF
  sup_spec := by
    intro F hF
    constructor
    · intro f hf
      refine rel_mk ?_
      intro x
      exact (L.sup_spec (evalPred F x) (directed_eval hF x)).1 ⟨f, hf, rfl⟩
    · intro w hw
      refine rel_mk ?_
      intro x
      refine (L.sup_spec (evalPred F x) (directed_eval hF x)).2 ?_
      intro y hy
      rcases hy with ⟨f, hf, rfl⟩
      exact (rel_iff.mp (hw hf)) x

end Exponential

/-! ## Evaluation Maps -/

/-- Evaluation at a fixed point is continuous. This is the one-variable part of
Proposition 3.6. -/
def evalContinuous
    (K : CompleteHomotopyPartialOrder)
    (L : CompleteHomotopyPartialOrder)
    (x : K.Obj) :
    ContinuousMap (Exponential.chpo K L) L where
  toFun := fun f => f.toFun x
  monotone' := by
    intro f g hfg
    exact (Exponential.rel_iff.mp hfg) x
  preserves_sup := by
    intro F hF
    simpa [Exponential.chpo, Exponential.directedSupMap, Exponential.evalPred] using
      L.sup_spec (Exponential.evalPred F x) (Exponential.directed_eval hF x)

/-! ## Separate and Joint Continuity (Lemma 3.2) -/

/-- The slice in the first variable of a jointly continuous map. -/
def ContinuousMap.sliceLeft
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    (f : ContinuousMap (Product.chpo K L) M)
    (y : L.Obj) :
    ContinuousMap K M :=
  ContinuousMap.comp f
    (ContinuousMap.pair (ContinuousMap.id K) (ContinuousMap.const K L y))

/-- The slice in the second variable of a jointly continuous map. -/
def ContinuousMap.sliceRight
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    (f : ContinuousMap (Product.chpo K L) M)
    (x : K.Obj) :
    ContinuousMap L M :=
  ContinuousMap.comp f
    (ContinuousMap.pair (ContinuousMap.const L K x) (ContinuousMap.id L))

/-- Evaluation of the left slice is definitional. -/
@[simp] theorem ContinuousMap.sliceLeft_apply
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    (f : ContinuousMap (Product.chpo K L) M)
    (y : L.Obj) (x : K.Obj) :
    ContinuousMap.sliceLeft f y x = f.toFun (x, y) :=
  rfl

/-- Evaluation of the right slice is definitional. -/
@[simp] theorem ContinuousMap.sliceRight_apply
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    (f : ContinuousMap (Product.chpo K L) M)
    (x : K.Obj) (y : L.Obj) :
    ContinuousMap.sliceRight f x y = f.toFun (x, y) :=
  rfl

/-- Chosen witnesses for separate continuity in the two arguments. -/
structure SeparateContinuousWitness
    (K : CompleteHomotopyPartialOrder)
    (L : CompleteHomotopyPartialOrder)
    (M : CompleteHomotopyPartialOrder)
    (f : K.Obj × L.Obj → M.Obj) where
  left : ∀ _ : L.Obj, ContinuousMap K M
  right : ∀ _ : K.Obj, ContinuousMap L M
  left_apply : ∀ y x, left y x = f (x, y)
  right_apply : ∀ x y, right x y = f (x, y)

/-- Joint continuity, recorded as the existence of a continuous map with the
prescribed underlying function. -/
def JointlyContinuous
    (K : CompleteHomotopyPartialOrder)
    (L : CompleteHomotopyPartialOrder)
    (M : CompleteHomotopyPartialOrder)
    (f : K.Obj × L.Obj → M.Obj) : Prop :=
  ∃ g : ContinuousMap (Product.chpo K L) M, ∀ p : K.Obj × L.Obj, g.toFun p = f p

namespace SeparateContinuousWitness

/-- A separately continuous function is monotone in the joint product order. -/
theorem monotone
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    {f : K.Obj × L.Obj → M.Obj}
    (hf : SeparateContinuousWitness K L M f)
    {x y : K.Obj × L.Obj}
    (hxy : (Product.chpo K L).Rel x y) :
    M.Rel (f x) (f y) := by
  have hx : K.Rel x.1 y.1 := (Product.rel_iff.mp hxy).1
  have hy : L.Rel x.2 y.2 := (Product.rel_iff.mp hxy).2
  have hRight :
      M.Rel ((hf.right x.1).toFun x.2) ((hf.right x.1).toFun y.2) :=
    (hf.right x.1).monotone' hy
  have hLeft :
      M.Rel ((hf.left y.2).toFun x.1) ((hf.left y.2).toFun y.1) :=
    (hf.left y.2).monotone' hx
  have h₁ : M.Rel (f x) (f (x.1, y.2)) := by
    simpa [hf.right_apply] using hRight
  have h₂ : M.Rel (f (x.1, y.2)) (f y) := by
    simpa [hf.left_apply] using hLeft
  exact M.rel_trans h₁ h₂

/-- Every jointly continuous function yields chosen separate-continuity
witnesses. This is the forward implication of Lemma 3.2. -/
def ofJoint
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    (f : ContinuousMap (Product.chpo K L) M) :
    SeparateContinuousWitness K L M f.toFun where
  left := fun y => ContinuousMap.sliceLeft f y
  right := fun x => ContinuousMap.sliceRight f x
  left_apply := by
    intro y x
    rfl
  right_apply := by
    intro x y
    rfl

/-- The reverse implication of Lemma 3.2: separate continuity implies joint
continuity. -/
def joint
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    {f : K.Obj × L.Obj → M.Obj}
    (hf : SeparateContinuousWitness K L M f) :
    ContinuousMap (Product.chpo K L) M where
  toFun := f
  monotone' := by
    intro x y hxy
    exact hf.monotone hxy
  preserves_sup := by
    intro X hX
    let X₀ : K.Obj → Prop := Product.fstPred X
    let X₁ : L.Obj → Prop := Product.sndPred X
    let s₀ : K.Obj := K.sup X₀ (Product.directed_fst hX)
    let s₁ : L.Obj := L.sup X₁ (Product.directed_snd hX)
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact hf.monotone <|
        Product.rel_mk
          ((K.sup_spec X₀ (Product.directed_fst hX)).1 ⟨x.2, hx⟩)
          ((L.sup_spec X₁ (Product.directed_snd hX)).1 ⟨x.1, hx⟩)
    · intro w hw
      have hPairUpper :
          ∀ {x : K.Obj} {y : L.Obj}, X₀ x → X₁ y → M.Rel (f (x, y)) w := by
        intro x y hx hy
        rcases hx with ⟨yx, hxyx⟩
        rcases hy with ⟨xx, hxxy⟩
        rcases hX.2 hxyx hxxy with ⟨z, hz, h₁, h₂⟩
        have hxz : K.Rel x z.1 := (Product.rel_iff.mp h₁).1
        have hyz : L.Rel y z.2 := (Product.rel_iff.mp h₂).2
        have hxy_z : (Product.chpo K L).Rel (x, y) z :=
          Product.rel_mk hxz hyz
        exact M.rel_trans (hf.monotone hxy_z) (hw ⟨z, hz, rfl⟩)
      have hLeftUpper :
          M.IsUpperBound (image (hf.left s₁) X₀) w := by
        intro a ha
        rcases ha with ⟨x, hx, rfl⟩
        have hRightUpper :
            M.IsUpperBound (image (hf.right x) X₁) w := by
          intro b hb
          rcases hb with ⟨y, hy, rfl⟩
          simpa [hf.right_apply] using hPairUpper hx hy
        have hSlice :
            M.Rel ((hf.right x).toFun s₁) w :=
          ((hf.right x).preserves_sup X₁ (Product.directed_snd hX)).2 hRightUpper
        have hSlice' : M.Rel (f (x, s₁)) w := by
          simpa [hf.right_apply] using hSlice
        simpa [hf.left_apply] using hSlice'
      have hFinal :
          M.Rel ((hf.left s₁).toFun s₀) w :=
        ((hf.left s₁).preserves_sup X₀ (Product.directed_fst hX)).2 hLeftUpper
      simpa [hf.left_apply] using hFinal

end SeparateContinuousWitness

/-- Lemma 3.2: joint continuity is equivalent to separate continuity. -/
theorem jointlyContinuous_iff_separatelyContinuous
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    {f : K.Obj × L.Obj → M.Obj} :
    JointlyContinuous K L M f ↔
      Nonempty (SeparateContinuousWitness K L M f) := by
  constructor
  · intro hf
    rcases hf with ⟨g, hg⟩
    refine ⟨{
      left := fun y => ContinuousMap.sliceLeft g y
      right := fun x => ContinuousMap.sliceRight g x
      left_apply := ?_
      right_apply := ?_
    }⟩
    · intro y x
      rw [ContinuousMap.sliceLeft_apply, hg]
    · intro x y
      rw [ContinuousMap.sliceRight_apply, hg]
  · intro hf
    rcases hf with ⟨hf⟩
    exact ⟨hf.joint, by intro p; rfl⟩

/-! ## Application and Abstraction (Propositions 3.6-3.8) -/

/-- Proposition 3.6: application is continuous. -/
def applicationContinuous
    (K : CompleteHomotopyPartialOrder)
    (L : CompleteHomotopyPartialOrder) :
    ContinuousMap (Product.chpo (Exponential.chpo K L) K) L := by
  let h :
      SeparateContinuousWitness
        (Exponential.chpo K L) K L
        (fun p => p.1.toFun p.2) :=
    { left := fun x => evalContinuous K L x
      right := fun f => f
      left_apply := by
        intro x f
        rfl
      right_apply := by
        intro f x
        rfl }
  exact h.joint

/-- Currying a continuous map. This is Proposition 3.7(1). -/
def curry
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    (f : ContinuousMap (Product.chpo K L) M) :
    ContinuousMap K (Exponential.chpo L M) where
  toFun := fun x => ContinuousMap.sliceRight f x
  monotone' := by
    intro x y hxy
    refine Exponential.rel_mk ?_
    intro z
    exact f.monotone' <|
      show (Product.chpo K L).Rel (x, z) (y, z) from
        Product.rel_mk hxy (L.rel_refl z)
  preserves_sup := by
    intro X hX
    constructor
    · intro g hg
      rcases hg with ⟨x, hx, rfl⟩
      refine Exponential.rel_mk ?_
      intro y
      exact f.monotone' <|
        show (Product.chpo K L).Rel (x, y) (K.sup X hX, y) from
          Product.rel_mk
            ((K.sup_spec X hX).1 hx)
            (L.rel_refl y)
    · intro w hw
      refine Exponential.rel_mk ?_
      intro y
      have hUpper :
          M.IsUpperBound (image (ContinuousMap.sliceLeft f y) X) (w.toFun y) := by
        intro a ha
        rcases ha with ⟨x, hx, rfl⟩
        exact (Exponential.rel_iff.mp (hw ⟨x, hx, rfl⟩)) y
      exact ((ContinuousMap.sliceLeft f y).preserves_sup X hX).2 hUpper

/-- Uncurrying a continuous map. -/
def uncurry
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    (g : ContinuousMap K (Exponential.chpo L M)) :
    ContinuousMap (Product.chpo K L) M := by
  let h :
      SeparateContinuousWitness
        K L M
        (fun p => (g.toFun p.1).toFun p.2) :=
    { left := fun y => ContinuousMap.comp (evalContinuous L M y) g
      right := fun x => g.toFun x
      left_apply := by
        intro y x
        rfl
      right_apply := by
        intro x y
        rfl }
  exact h.joint

/-- Evaluation of `uncurry`. -/
@[simp] theorem uncurry_apply
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    (g : ContinuousMap K (Exponential.chpo L M))
    (x : K.Obj) (y : L.Obj) :
    uncurry g (x, y) = (g.toFun x).toFun y :=
  rfl

/-- Proposition 3.7(2): abstraction is continuous as a morphism between
function spaces. -/
def curryContinuous
    (K : CompleteHomotopyPartialOrder)
    (L : CompleteHomotopyPartialOrder)
    (M : CompleteHomotopyPartialOrder) :
    ContinuousMap
      (Exponential.chpo (Product.chpo K L) M)
      (Exponential.chpo K (Exponential.chpo L M)) where
  toFun := fun f => curry f
  monotone' := by
    intro f g hfg
    refine Exponential.rel_mk ?_
    intro x
    refine Exponential.rel_mk ?_
    intro y
    exact show M.Rel (((curry f).toFun x).toFun y) (((curry g).toFun x).toFun y) from
      (Exponential.rel_iff.mp hfg) (x, y)
  preserves_sup := by
    intro F hF
    constructor
    · intro g hg
      rcases hg with ⟨f, hf, rfl⟩
      refine Exponential.rel_mk ?_
      intro x
      refine Exponential.rel_mk ?_
      intro y
      exact show
          M.Rel ((((fun f => curry f) f).toFun x).toFun y)
            (((curry ((Exponential.chpo (Product.chpo K L) M).sup F hF)).toFun x).toFun y) from
        (M.sup_spec
          (Exponential.evalPred F (x, y))
          (Exponential.directed_eval hF (x, y))).1 ⟨f, hf, rfl⟩
    · intro w hw
      refine Exponential.rel_mk ?_
      intro x
      refine Exponential.rel_mk ?_
      intro y
      refine show
          M.Rel (((curry ((Exponential.chpo (Product.chpo K L) M).sup F hF)).toFun x).toFun y)
            ((w.toFun x).toFun y) from
        (M.sup_spec
          (Exponential.evalPred F (x, y))
          (Exponential.directed_eval hF (x, y))).2 ?_
      intro z hz
      rcases hz with ⟨f, hf, rfl⟩
      exact (Exponential.rel_iff.mp ((Exponential.rel_iff.mp (hw ⟨f, hf, rfl⟩)) x)) y

/-- `uncurry` is inverse to `curry`. -/
@[simp] theorem uncurry_curry
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    (f : ContinuousMap (Product.chpo K L) M) :
    uncurry (curry f) = f := by
  ext p
  cases p with
  | mk x y =>
    change (((curry f).toFun x).toFun y) = f.toFun (x, y)
    rfl

/-- `curry` is inverse to `uncurry`. -/
@[simp] theorem curry_uncurry
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    (g : ContinuousMap K (Exponential.chpo L M)) :
    curry (uncurry g) = g := by
  ext x
  apply ContinuousMap.ext
  intro y
  change (uncurry g).toFun (x, y) = (g.toFun x).toFun y
  exact uncurry_apply g x y

/-- A terminal c.h.p.o., used in Proposition 3.8. -/
def terminalCHPO : CompleteHomotopyPartialOrder where
  Obj := PUnit
  Hom := fun _ _ => PUnit
  id := fun _ => PUnit.unit
  comp := fun _ _ => PUnit.unit
  hom_contractible_or_empty := by
    intro x y
    right
    refine ⟨PUnit.unit, ?_⟩
    intro z
    cases z
    rfl
  bottom := PUnit.unit
  bottom_le := by
    intro x
    exact ⟨PUnit.unit⟩
  sup := fun X hX => PUnit.unit
  sup_spec := by
    intro X hX
    constructor
    · intro x hx
      exact ⟨PUnit.unit⟩
    · intro w hw
      exact ⟨PUnit.unit⟩

/-- Proposition 3.8 packaged as explicit cartesian closed structure for the
ordinary category of c.h.p.o.'s and continuous maps. -/
structure CartesianClosedData where
  terminal : CompleteHomotopyPartialOrder
  exponential : CompleteHomotopyPartialOrder → CompleteHomotopyPartialOrder → CompleteHomotopyPartialOrder
  eval :
    ∀ K L : CompleteHomotopyPartialOrder,
      ContinuousMap (Product.chpo (exponential K L) K) L
  curry :
    ∀ {K L M : CompleteHomotopyPartialOrder},
      ContinuousMap (Product.chpo M K) L →
        ContinuousMap M (exponential K L)
  uncurry :
    ∀ {K L M : CompleteHomotopyPartialOrder},
      ContinuousMap M (exponential K L) →
        ContinuousMap (Product.chpo M K) L
  uncurry_curry :
    ∀ {K L M : CompleteHomotopyPartialOrder}
      (f : ContinuousMap (Product.chpo M K) L),
      uncurry (curry f) = f
  curry_uncurry :
    ∀ {K L M : CompleteHomotopyPartialOrder}
      (g : ContinuousMap M (exponential K L)),
      curry (uncurry g) = g

/-- Proposition 3.8: `CHPO` is cartesian closed. -/
def cartesianClosed : CartesianClosedData where
  terminal := terminalCHPO
  exponential := Exponential.chpo
  eval := applicationContinuous
  curry := fun {_ _ _} f => curry f
  uncurry := fun {_ _ _} g => uncurry g
  uncurry_curry := by
    intro K L M f
    exact uncurry_curry f
  curry_uncurry := by
    intro K L M g
    exact curry_uncurry g

/-! ## CHPO as a 0-∞-Category (Proposition 3.11) -/

/-- Postcomposition is continuous in the right argument, as required by
Proposition 3.11. -/
def postcomposeContinuous
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    (g : ContinuousMap L M) :
    ContinuousMap (Exponential.chpo K L) (Exponential.chpo K M) where
  toFun := fun f => ContinuousMap.comp g f
  monotone' := by
    intro f h hfh
    refine Exponential.rel_mk ?_
    intro x
    exact g.monotone' ((Exponential.rel_iff.mp hfh) x)
  preserves_sup := by
    intro F hF
    constructor
    · intro h hh
      rcases hh with ⟨f, hf, rfl⟩
      refine Exponential.rel_mk ?_
      intro x
      exact g.monotone'
        ((Exponential.rel_iff.mp
          (((Exponential.chpo K L).sup_spec F hF).1 hf)) x)
    · intro w hw
      refine Exponential.rel_mk ?_
      intro x
      have hUpper :
          M.IsUpperBound (image g (Exponential.evalPred F x)) (w.toFun x) := by
        intro a ha
        rcases ha with ⟨b, hb, rfl⟩
        rcases hb with ⟨f, hf, rfl⟩
        exact (Exponential.rel_iff.mp (hw ⟨f, hf, rfl⟩)) x
      exact (g.preserves_sup (Exponential.evalPred F x) (Exponential.directed_eval hF x)).2 hUpper

/-- Precomposition is continuous in the left argument, as required by
Proposition 3.11. -/
def precomposeContinuous
    {K : CompleteHomotopyPartialOrder}
    {L : CompleteHomotopyPartialOrder}
    {M : CompleteHomotopyPartialOrder}
    (f : ContinuousMap K L) :
    ContinuousMap (Exponential.chpo L M) (Exponential.chpo K M) where
  toFun := fun g => ContinuousMap.comp g f
  monotone' := by
    intro g h hgh
    refine Exponential.rel_mk ?_
    intro x
    exact (Exponential.rel_iff.mp hgh) (f.toFun x)
  preserves_sup := by
    intro F hF
    constructor
    · intro h hh
      rcases hh with ⟨g, hg, rfl⟩
      refine Exponential.rel_mk ?_
      intro x
      exact (Exponential.rel_iff.mp
        (((Exponential.chpo L M).sup_spec F hF).1 hg)) (f.toFun x)
    · intro w hw
      refine Exponential.rel_mk ?_
      intro x
      refine (M.sup_spec
        (Exponential.evalPred F (f.toFun x))
        (Exponential.directed_eval hF (f.toFun x))).2 ?_
      intro y hy
      rcases hy with ⟨g, hg, rfl⟩
      exact (Exponential.rel_iff.mp (hw ⟨g, hg, rfl⟩)) x

/-- A lightweight chosen-data presentation of Proposition 3.11. -/
structure ZeroInfinityPresentation where
  homObject : CompleteHomotopyPartialOrder → CompleteHomotopyPartialOrder → CompleteHomotopyPartialOrder
  id : ∀ K : CompleteHomotopyPartialOrder, ContinuousMap K K
  comp :
    ∀ {K L M : CompleteHomotopyPartialOrder},
      ContinuousMap L M → ContinuousMap K L → ContinuousMap K M
  assoc :
    ∀ {K L M N : CompleteHomotopyPartialOrder}
      (h : ContinuousMap M N) (g : ContinuousMap L M) (f : ContinuousMap K L),
      comp h (comp g f) = comp (comp h g) f
  id_left :
    ∀ {K L : CompleteHomotopyPartialOrder} (f : ContinuousMap K L),
      comp (id L) f = f
  id_right :
    ∀ {K L : CompleteHomotopyPartialOrder} (f : ContinuousMap K L),
      comp f (id K) = f
  postcompose :
    ∀ {K L M : CompleteHomotopyPartialOrder},
      ContinuousMap L M →
        ContinuousMap (homObject K L) (homObject K M)
  precompose :
    ∀ {K L M : CompleteHomotopyPartialOrder},
      ContinuousMap K L →
        ContinuousMap (homObject L M) (homObject K M)
  bottom_absorb :
    ∀ {K L M : CompleteHomotopyPartialOrder}
      (f : ContinuousMap K L),
      comp (ContinuousMap.const L M M.bottom) f = ContinuousMap.const K M M.bottom

/-- Proposition 3.11: `CHPO` is a `0-∞`-category in the order-theoretic sense
formalized in this repository. -/
def zeroInfinityPresentation : ZeroInfinityPresentation where
  homObject := Exponential.chpo
  id := ContinuousMap.id
  comp := fun {_ _ _} g f => ContinuousMap.comp g f
  assoc := by
    intro K L M N h g f
    ext x
    rfl
  id_left := by
    intro K L f
    ext x
    rfl
  id_right := by
    intro K L f
    ext x
    rfl
  postcompose := fun {_ _ _} g => postcomposeContinuous g
  precompose := fun {_ _ _} f => precomposeContinuous f
  bottom_absorb := by
    intro K L M f
    ext x
    rfl

/-! ## Projective Systems and `K∞` (Definition 3.10 and Remark 3.7) -/

namespace Projective

/-- Definition 3.10, made explicit in the chosen-data style of the repository.

The extra field `strict` is the bottom-compatibility witness needed to build the
chosen bottom element of the inverse limit as a c.h.p.o. -/
structure System where
  obj : Nat → CompleteHomotopyPartialOrder
  map : ∀ n : Nat, ContinuousMap (obj (n + 1)) (obj n)
  strict : ∀ n : Nat, (obj n).Rel ((map n).toFun (obj (n + 1)).bottom) (obj n).bottom

/-- An element of the projective limit consists of a coherent thread of
elements, with coherence recorded up to the ambient h.p.o. equivalence. -/
structure Thread (S : System) where
  val : ∀ n : Nat, (S.obj n).Obj
  toPrev : ∀ n : Nat, (S.obj n).Rel ((S.map n).toFun (val (n + 1))) (val n)
  fromPrev : ∀ n : Nat, (S.obj n).Rel (val n) ((S.map n).toFun (val (n + 1)))

/-- The inverse-limit h.p.o. is ordered pointwise. -/
def hpo (S : System) : HomotopyPartialOrder where
  Obj := Thread S
  Hom := fun x y => ∀ n : Nat, (S.obj n).Hom (x.val n) (y.val n)
  id := fun x n => (S.obj n).id (x.val n)
  comp := fun α β n => (S.obj n).comp (α n) (β n)
  hom_contractible_or_empty := by
    intro x y
    by_cases hxy : Nonempty (∀ n : Nat, (S.obj n).Hom (x.val n) (y.val n))
    · right
      let center : ∀ n : Nat, (S.obj n).Hom (x.val n) (y.val n) := Classical.choice hxy
      refine ⟨center, ?_⟩
      intro h
      funext n
      exact contractible_is_prop
        (hom_contractible_of_rel (S.obj n).toHomotopyPartialOrder ⟨center n⟩)
        (center n) (h n)
    · left
      intro h
      exact hxy ⟨h⟩

/-- Pointwise introduction into the inverse-limit relation. -/
theorem rel_mk
    {S : System}
    {x y : Thread S}
    (hxy : ∀ n : Nat, (S.obj n).Rel (x.val n) (y.val n)) :
    (hpo S).Rel x y := by
  exact ⟨fun n => Classical.choice (hxy n)⟩

/-- The inverse-limit relation is pointwise. -/
theorem rel_iff
    {S : System}
    {x y : Thread S} :
    (hpo S).Rel x y ↔ ∀ n : Nat, (S.obj n).Rel (x.val n) (y.val n) := by
  constructor
  · intro h n
    rcases h with ⟨h⟩
    exact ⟨h n⟩
  · intro h
    exact rel_mk h

/-- The `n`-th coordinate predicate of a predicate on inverse-limit threads. -/
def coordPred
    {S : System}
    (X : Thread S → Prop)
    (n : Nat) :
    (S.obj n).Obj → Prop :=
  fun a => ∃ x : Thread S, X x ∧ x.val n = a

/-- Directed predicates in the inverse limit are directed in each coordinate. -/
theorem directed_coord
    {S : System}
    {X : Thread S → Prop}
    (hX : (hpo S).Directed X)
    (n : Nat) :
    (S.obj n).Directed (coordPred X n) := by
  rcases hX with ⟨⟨x, hx⟩, hdir⟩
  refine ⟨⟨x.val n, ⟨x, hx, rfl⟩⟩, ?_⟩
  intro a b ha hb
  rcases ha with ⟨x, hx, rfl⟩
  rcases hb with ⟨y, hy, rfl⟩
  rcases hdir hx hy with ⟨z, hz, hxz, hyz⟩
  exact ⟨z.val n, ⟨z, hz, rfl⟩, (rel_iff.mp hxz) n, (rel_iff.mp hyz) n⟩

/-- Definition 3.10 / Remark 3.7: the inverse limit `K∞` of a strict
projective system, equipped with its pointwise c.h.p.o. structure. -/
def limit (S : System) : CompleteHomotopyPartialOrder where
  toHomotopyPartialOrder := hpo S
  bottom :=
    { val := fun n => (S.obj n).bottom
      toPrev := fun n => S.strict n
      fromPrev := fun n => (S.obj n).bottom_le ((S.map n).toFun (S.obj (n + 1)).bottom) }
  bottom_le := by
    intro x
    exact rel_mk (fun n => (S.obj n).bottom_le (x.val n))
  sup := fun X hX =>
    { val := fun n => (S.obj n).sup (coordPred X n) (directed_coord hX n)
      toPrev := by
        intro n
        let Yₙ : (S.obj n).Obj → Prop := coordPred X n
        let Yₙ₁ : (S.obj (n + 1)).Obj → Prop := coordPred X (n + 1)
        have hImageLub :
            (S.obj n).IsLeastUpperBound
              (image (S.map n) Yₙ₁)
              ((S.map n).toFun ((S.obj (n + 1)).sup Yₙ₁ (directed_coord hX (n + 1)))) :=
          (S.map n).preserves_sup Yₙ₁ (directed_coord hX (n + 1))
        have hCoordLub :
            (S.obj n).IsLeastUpperBound
              Yₙ
              ((S.map n).toFun ((S.obj (n + 1)).sup Yₙ₁ (directed_coord hX (n + 1)))) := by
          constructor
          · intro a ha
            rcases ha with ⟨x, hx, rfl⟩
            exact (S.obj n).rel_trans
              (x.fromPrev n)
              (hImageLub.1 ⟨x.val (n + 1), ⟨x, hx, rfl⟩, rfl⟩)
          · intro w hw
            refine hImageLub.2 ?_
            intro a ha
            rcases ha with ⟨b, hb, rfl⟩
            rcases hb with ⟨x, hx, rfl⟩
            exact (S.obj n).rel_trans (x.toPrev n) (hw ⟨x, hx, rfl⟩)
        exact (equivalent_of_isLeastUpperBound
          (S.obj n).toHomotopyPartialOrder
          hCoordLub
          ((S.obj n).sup_spec Yₙ (directed_coord hX n))).1
      fromPrev := by
        intro n
        let Yₙ : (S.obj n).Obj → Prop := coordPred X n
        let Yₙ₁ : (S.obj (n + 1)).Obj → Prop := coordPred X (n + 1)
        have hImageLub :
            (S.obj n).IsLeastUpperBound
              (image (S.map n) Yₙ₁)
              ((S.map n).toFun ((S.obj (n + 1)).sup Yₙ₁ (directed_coord hX (n + 1)))) :=
          (S.map n).preserves_sup Yₙ₁ (directed_coord hX (n + 1))
        have hCoordLub :
            (S.obj n).IsLeastUpperBound
              Yₙ
              ((S.map n).toFun ((S.obj (n + 1)).sup Yₙ₁ (directed_coord hX (n + 1)))) := by
          constructor
          · intro a ha
            rcases ha with ⟨x, hx, rfl⟩
            exact (S.obj n).rel_trans
              (x.fromPrev n)
              (hImageLub.1 ⟨x.val (n + 1), ⟨x, hx, rfl⟩, rfl⟩)
          · intro w hw
            refine hImageLub.2 ?_
            intro a ha
            rcases ha with ⟨b, hb, rfl⟩
            rcases hb with ⟨x, hx, rfl⟩
            exact (S.obj n).rel_trans (x.toPrev n) (hw ⟨x, hx, rfl⟩)
        exact (equivalent_of_isLeastUpperBound
          (S.obj n).toHomotopyPartialOrder
          hCoordLub
          ((S.obj n).sup_spec Yₙ (directed_coord hX n))).2
    }
  sup_spec := by
    intro X hX
    constructor
    · intro x hx
      exact rel_mk (fun n =>
        ((S.obj n).sup_spec (coordPred X n) (directed_coord hX n)).1 ⟨x, hx, rfl⟩)
    · intro w hw
      exact rel_mk (fun n =>
        ((S.obj n).sup_spec (coordPred X n) (directed_coord hX n)).2 <|
          by
            intro a ha
            rcases ha with ⟨x, hx, rfl⟩
            exact (rel_iff.mp (hw hx)) n)

/-- Definition 3.10 packaged with the standard notation `K∞`. -/
abbrev KInfinity (S : System) : CompleteHomotopyPartialOrder :=
  limit S

end Projective

/-! ## ω-Diagrams and Colimits (Corollary 3.1) -/

/-- An ordinary `ω`-diagram in the category of c.h.p.o.'s. -/
structure OmegaDiagram where
  obj : Nat → CompleteHomotopyPartialOrder
  map : ∀ n : Nat, ContinuousMap (obj n) (obj (n + 1))

/-- A cocone over an `ω`-diagram in the ordinary category of c.h.p.o.'s with a
fixed apex. -/
structure OmegaCocone (D : OmegaDiagram) (A : CompleteHomotopyPartialOrder) where
  leg : ∀ n : Nat, ContinuousMap (D.obj n) A
  comm : ∀ n : Nat, ContinuousMap.comp (leg (n + 1)) (D.map n) = leg n

/-- A chosen colimit presentation for an `ω`-diagram. -/
structure OmegaColimit (D : OmegaDiagram) where
  apex : CompleteHomotopyPartialOrder
  cocone : OmegaCocone D apex
  desc :
    ∀ {A : CompleteHomotopyPartialOrder},
      OmegaCocone D A → ContinuousMap apex A
  fac :
    ∀ {A : CompleteHomotopyPartialOrder} (c : OmegaCocone D A) (n : Nat),
      ContinuousMap.comp (desc c) (cocone.leg n) = c.leg n
  uniq :
    ∀ {A : CompleteHomotopyPartialOrder} (c : OmegaCocone D A)
      (m : ContinuousMap apex A),
      (∀ n : Nat, ContinuousMap.comp m (cocone.leg n) = c.leg n) →
        m = desc c

end HigherLambdaModel.Domain
