import HigherLambdaModel.Simplicial.InfinityCategory

/-!
# Joins, Limits, and the Homotopy Domain Equation

This module packages Definitions 2.15-2.26 and Theorem 2.3 from
Martínez-Rivillas and de Queiroz, *The K∞ Homotopy λ-Model*.

The categorical infrastructure is recorded as explicit chosen data. This keeps
the later semantic interface usable without rederiving the surrounding
∞-categorical metatheory inside the present repository.
-/

universe u v w

abbrev Vertex (X : SSet) := Obj X

/-- A lightweight contractibility predicate on types. -/
def TypeContractible (α : Sort u) : Prop :=
  ∃ center : α, ∀ x : α, center = x

/-- A chosen model of the join `K ⋆ L` of simplicial sets (Definition 2.15). -/
structure Join (K L : SSet) where
  toSSet : SSet
  inl : SSetHom K toSSet
  inr : SSetHom L toSSet
  mixed : ∀ {i j : Nat}, K.Simplex i → L.Simplex j → toSSet.Simplex (i + 1 + j)

/-- A cone on a diagram `p : K → X`. -/
structure Cone (K : SSet) (X : InfinityCategory) (p : SSetHom K X.toSSet) where
  apex : Vertex X.toSSet
  leg : ∀ x : Vertex K, Morphism X.toSSet (p.app 0 x) apex

/-- A cocone on a diagram `p : K → X`. -/
structure Cocone (K : SSet) (X : InfinityCategory) (p : SSetHom K X.toSSet) where
  apex : Vertex X.toSSet
  leg : ∀ x : Vertex K, Morphism X.toSSet apex (p.app 0 x)

/-- A final object in an ∞-category, recorded through chosen morphism-space
models that are contractible (Definition 2.17). -/
structure FinalObject (X : InfinityCategory) where
  obj : Vertex X.toSSet
  homSpace : ∀ x : Vertex X.toSSet, MorphismSpace X x obj
  contractible :
    ∀ x : Vertex X.toSSet, ∀ n : Nat,
      TypeContractible ((homSpace x).carrier.toSSet.Simplex n)

/-- A limit object for a diagram `p`, packaged as a chosen cone together with a
universal-property predicate (Definition 2.18). -/
structure Limit (K : SSet) (X : InfinityCategory) (p : SSetHom K X.toSSet) where
  cone : Cone K X p
  isUniversal : Prop

/-- A colimit object for a diagram `p`, packaged as a chosen cocone together
with a universal-property predicate (Definition 2.18). -/
structure Colimit (K : SSet) (X : InfinityCategory) (p : SSetHom K X.toSSet) where
  cocone : Cocone K X p
  isUniversal : Prop

/-- An `ω`-diagram in an ∞-category (Definition 2.20). -/
structure OmegaDiagram (X : InfinityCategory) where
  obj : Nat → Vertex X.toSSet
  map : ∀ n : Nat, Morphism X.toSSet (obj n) (obj (n + 1))

/-- An `ωᵒᵖ`-diagram in an ∞-category. -/
structure OmegaOpDiagram (X : InfinityCategory) where
  obj : Nat → Vertex X.toSSet
  map : ∀ n : Nat, Morphism X.toSSet (obj (n + 1)) (obj n)

/-- A chosen colimit of an `ω`-diagram. -/
structure OmegaColimit {X : InfinityCategory} (D : OmegaDiagram X) where
  apex : Vertex X.toSSet
  leg : ∀ n : Nat, Morphism X.toSSet (D.obj n) apex
  isUniversal : Prop

/-- A chosen limit of an `ωᵒᵖ`-diagram. -/
structure OmegaLimit {X : InfinityCategory} (D : OmegaOpDiagram X) where
  apex : Vertex X.toSSet
  leg : ∀ n : Nat, Morphism X.toSSet apex (D.obj n)
  isUniversal : Prop

/-- An ∞-category is `ω`-complete when every `ωᵒᵖ`-diagram admits a limit
(Definition 2.20). -/
def OmegaComplete (X : InfinityCategory) : Prop :=
  ∀ D : OmegaOpDiagram X, Nonempty (OmegaLimit D)

/-- An ∞-category is `ω`-cocomplete when every `ω`-diagram admits a colimit
(Definition 2.20). -/
def OmegaCocomplete (X : InfinityCategory) : Prop :=
  ∀ D : OmegaDiagram X, Nonempty (OmegaColimit D)

/-- Applying an ∞-functor to an `ω`-diagram. -/
def OmegaDiagram.mapFunctor {X Y : InfinityCategory}
    (D : OmegaDiagram X) (F : CatFunctor X Y) : OmegaDiagram Y where
  obj := fun n => CatFunctor.onObj F (D.obj n)
  map := fun n => CatFunctor.onMorphism F (D.map n)

/-- An `ω`-continuous endofunctor preserves chosen colimits of `ω`-diagrams
(Definition 2.20). -/
structure OmegaContinuous {X : InfinityCategory} (F : CatFunctor X X) where
  preservesColimit :
    ∀ D : OmegaDiagram X,
      OmegaColimit D → OmegaColimit (OmegaDiagram.mapFunctor D F)

/-- The data appearing in Theorem 2.3: a starting object, a seed edge, a chosen
`ω`-diagram of iterates, its colimit, and the resulting fixed-point equivalence. -/
structure FixedPointWitness {X : InfinityCategory} (F : CatFunctor X X) where
  base : Vertex X.toSSet
  seed : Morphism X.toSSet base (CatFunctor.onObj F base)
  chain : OmegaDiagram X
  colimit : OmegaColimit chain
  shiftedColimit : OmegaColimit (OmegaDiagram.mapFunctor chain F)
  shiftEquiv : EquivalentVertices X.toSSet colimit.apex shiftedColimit.apex
  shiftedApex : shiftedColimit.apex = CatFunctor.onObj F colimit.apex

/-- The fixed-point equivalence carried by a fixed-point witness. The witness
stores the comparison with the colimit of the shifted chain, and the target
fixed point is derived by identifying that colimit with `F` applied to the
original colimit apex. -/
def FixedPointWitness.fixed {X : InfinityCategory} {F : CatFunctor X X}
    (w : FixedPointWitness F) :
    EquivalentVertices X.toSSet w.colimit.apex (CatFunctor.onObj F w.colimit.apex) :=
  w.shiftedApex ▸ w.shiftEquiv

/-- The fixed-point theorem of Definition/Theorem 2.3, packaged as extraction
of the chosen fixed-point equivalence from explicit witness data. -/
def fixedPointTheorem {X : InfinityCategory} (F : CatFunctor X X)
    (_hF : OmegaContinuous F) (w : FixedPointWitness F) :
    EquivalentVertices X.toSSet w.colimit.apex (CatFunctor.onObj F w.colimit.apex) :=
  w.fixed

/-- Directed predicates for the homotopy-order layer. -/
def Directed {α : Type u} (le : α → α → Prop) (P : α → Prop) : Prop :=
  (∃ x, P x) ∧
    ∀ {x y : α}, P x → P y → ∃ z, P z ∧ le x z ∧ le y z

/-- Upper bounds relative to a chosen homotopy order. -/
def IsUpperBound {α : Type u} (le : α → α → Prop) (P : α → Prop) (z : α) : Prop :=
  ∀ {x : α}, P x → le x z

/-- Least upper bounds relative to a chosen homotopy order. -/
def IsLeastUpperBound {α : Type u}
    (le : α → α → Prop) (P : α → Prop) (z : α) : Prop :=
  IsUpperBound le P z ∧
    ∀ {w : α}, IsUpperBound le P w → le z w

/-- A Kan complex whose vertices carry a complete homotopy order. This packages
the c.h.p.o. structure required in Definition 2.21. -/
structure CompleteHomotopySpace where
  carrier : KanComplex
  le : Vertex carrier.toSSet → Vertex carrier.toSSet → Prop
  refl : ∀ x : Vertex carrier.toSSet, le x x
  trans : ∀ {x y z : Vertex carrier.toSSet}, le x y → le y z → le x z
  bottom : Vertex carrier.toSSet
  bottom_le : ∀ x : Vertex carrier.toSSet, le bottom x
  sup :
    (P : Vertex carrier.toSSet → Prop) →
      Directed le P →
        Vertex carrier.toSSet
  sup_spec :
    ∀ (P : Vertex carrier.toSSet → Prop) (hP : Directed le P),
      IsLeastUpperBound le P (sup P hP)

/-- Composition preserves directed suprema when composing on either side. The
image predicates are spelled out directly to avoid introducing extra chosen
suprema beyond the homotopy-order data already carried by the hom-spaces. -/
def CompositionContinuous
    (Obj : Type u)
    (Hom : Obj → Obj → CompleteHomotopySpace)
    (comp :
      ∀ {A B C : Obj},
        Vertex ((Hom A B).carrier.toSSet) →
          Vertex ((Hom B C).carrier.toSSet) →
            Vertex ((Hom A C).carrier.toSSet)) : Prop :=
  (∀ {A B C : Obj}
    (g : Vertex ((Hom B C).carrier.toSSet))
    (F : Vertex ((Hom A B).carrier.toSSet) → Prop)
    (hF : Directed (Hom A B).le F),
      IsLeastUpperBound (Hom A C).le
        (fun h => ∃ f, F f ∧ comp f g = h)
        (comp ((Hom A B).sup F hF) g))
    ∧
  ∀ {A B C : Obj}
    (f : Vertex ((Hom A B).carrier.toSSet))
    (G : Vertex ((Hom B C).carrier.toSSet) → Prop)
    (hG : Directed (Hom B C).le G),
      IsLeastUpperBound (Hom A C).le
        (fun h => ∃ g, G g ∧ comp f g = h)
        (comp f ((Hom B C).sup G hG))

/-- A `0`-∞-category in the sense of Definition 2.21. The continuity of
composition is recorded as an explicit predicate field on the chosen operation. -/
structure ZeroInfinityCategory where
  Obj : Type u
  Hom : Obj → Obj → CompleteHomotopySpace
  id : ∀ A : Obj, Vertex ((Hom A A).carrier.toSSet)
  comp :
    ∀ {A B C : Obj},
      Vertex ((Hom A B).carrier.toSSet) →
        Vertex ((Hom B C).carrier.toSSet) →
          Vertex ((Hom A C).carrier.toSSet)
  assoc :
    ∀ {A B C D : Obj}
      (f : Vertex ((Hom A B).carrier.toSSet))
      (g : Vertex ((Hom B C).carrier.toSSet))
      (h : Vertex ((Hom C D).carrier.toSSet)),
      comp (comp f g) h = comp f (comp g h)
  id_left :
    ∀ {A B : Obj} (f : Vertex ((Hom A B).carrier.toSSet)),
      comp (id A) f = f
  id_right :
    ∀ {A B : Obj} (f : Vertex ((Hom A B).carrier.toSSet)),
      comp f (id B) = f
  comp_monotone_left :
    ∀ {A B C : Obj} {f f' : Vertex ((Hom A B).carrier.toSSet)}
      (g : Vertex ((Hom B C).carrier.toSSet)),
      (Hom A B).le f f' →
        (Hom A C).le (comp f g) (comp f' g)
  comp_monotone_right :
    ∀ {A B C : Obj} (f : Vertex ((Hom A B).carrier.toSSet))
      {g g' : Vertex ((Hom B C).carrier.toSSet)},
      (Hom B C).le g g' →
        (Hom A C).le (comp f g) (comp f g')
  comp_continuous : CompositionContinuous Obj Hom comp
  bottom_absorb :
    ∀ {A B C : Obj} (f : Vertex ((Hom A B).carrier.toSSet)),
      comp f (Hom B C).bottom = (Hom A C).bottom

/-- The carrier type of 0-cells in a hom-space. -/
abbrev HomObj (K : ZeroInfinityCategory) (A B : K.Obj) :=
  Vertex ((K.Hom A B).carrier.toSSet)

/-- An h-projection pair in a `0`-∞-category (Definition 2.22). -/
structure HProjectionPair (K : ZeroInfinityCategory) (A B : K.Obj) where
  emb : HomObj K A B
  proj : HomObj K B A
  retract : K.comp emb proj = K.id A
  section_le : (K.Hom B B).le (K.comp proj emb) (K.id B)

/-- The h-embedding carried by an h-projection pair. -/
abbrev HEmbedding (K : ZeroInfinityCategory) (A B : K.Obj) :=
  HomObj K A B

/-- The h-projection carried by an h-projection pair. -/
abbrev HProjection (K : ZeroInfinityCategory) (A B : K.Obj) :=
  HomObj K B A

/-- Identity h-projection pair. -/
def HProjectionPair.id (K : ZeroInfinityCategory) (A : K.Obj) :
    HProjectionPair K A A where
  emb := K.id A
  proj := K.id A
  retract := by rw [K.id_left]
  section_le := by
    simpa [K.id_left] using (K.Hom A A).refl (K.id A)

/-- Composition of h-projection pairs, giving the morphisms of
Definition 2.23. -/
def HProjectionPair.comp (K : ZeroInfinityCategory)
    {A B C : K.Obj}
    (f : HProjectionPair K A B)
    (g : HProjectionPair K B C) :
    HProjectionPair K A C where
  emb := K.comp f.emb g.emb
  proj := K.comp g.proj f.proj
  retract := by
    calc
      K.comp (K.comp f.emb g.emb) (K.comp g.proj f.proj)
          = K.comp f.emb (K.comp g.emb (K.comp g.proj f.proj)) := by
              rw [K.assoc]
      _ = K.comp f.emb (K.comp (K.comp g.emb g.proj) f.proj) := by
            have hAssoc := K.assoc g.emb g.proj f.proj
            exact congrArg (fun t => K.comp f.emb t) hAssoc.symm
      _ = K.comp f.emb (K.comp (K.id B) f.proj) := by
            rw [g.retract]
      _ = K.comp f.emb f.proj := by
            rw [K.id_left]
      _ = K.id A := f.retract
  section_le := by
    have h₁ :
        (K.Hom B B).le (K.comp f.proj f.emb) (K.id B) :=
      f.section_le
    have h₂ :
        (K.Hom B C).le
          (K.comp (K.comp f.proj f.emb) g.emb)
          (K.comp (K.id B) g.emb) :=
      K.comp_monotone_left g.emb h₁
    have h₃ :
        (K.Hom C C).le
          (K.comp g.proj (K.comp (K.comp f.proj f.emb) g.emb))
          (K.comp g.proj (K.comp (K.id B) g.emb)) :=
      K.comp_monotone_right g.proj h₂
    have h₄ :
        (K.Hom C C).le
          (K.comp g.proj (K.comp (K.id B) g.emb))
          (K.comp g.proj g.emb) := by
      rw [K.id_left]
      exact (K.Hom C C).refl (K.comp g.proj g.emb)
    have h₅ :
        (K.Hom C C).le (K.comp g.proj g.emb) (K.id C) :=
      g.section_le
    have hStart :
        K.comp (K.comp g.proj f.proj) (K.comp f.emb g.emb) =
          K.comp g.proj (K.comp (K.comp f.proj f.emb) g.emb) := by
      calc
        K.comp (K.comp g.proj f.proj) (K.comp f.emb g.emb)
            = K.comp g.proj (K.comp f.proj (K.comp f.emb g.emb)) := by
                rw [K.assoc]
        _ = K.comp g.proj (K.comp (K.comp f.proj f.emb) g.emb) := by
              have hAssoc := K.assoc f.proj f.emb g.emb
              exact congrArg (fun t => K.comp g.proj t) hAssoc.symm
    rw [hStart]
    exact (K.Hom C C).trans h₃ ((K.Hom C C).trans h₄ h₅)

/-- The `0`-∞-category of h-projection pairs from Definition 2.23, recorded as
objects together with the chosen identity and composition operations. -/
structure HProjectionPairCategory (K : ZeroInfinityCategory) where
  id : ∀ A : K.Obj, HProjectionPair K A A
  comp :
    ∀ {A B C : K.Obj},
      HProjectionPair K A B →
        HProjectionPair K B C →
          HProjectionPair K A C

/-- The canonical h-projection-pair category of a `0`-∞-category. -/
def hProjectionPairCategory (K : ZeroInfinityCategory) : HProjectionPairCategory K where
  id := fun A => HProjectionPair.id K A
  comp := fun {_ _ _} f g => HProjectionPair.comp K f g

/-- A contravariant/covariant bifunctor `Kᵒᵖ × K → K` as in Definition 2.24. -/
structure Bifunctor (K : ZeroInfinityCategory) where
  onObj : K.Obj → K.Obj → K.Obj
  onMor :
    ∀ {A B C D : K.Obj},
      HomObj K B A →
        HomObj K C D →
          HomObj K (onObj A C) (onObj B D)
  map_id :
    ∀ A C : K.Obj,
      onMor (K.id A) (K.id C) = K.id (onObj A C)
  map_comp :
    ∀ {A B C D E F : K.Obj}
      (f₁ : HomObj K B A) (f₂ : HomObj K C B)
      (g₁ : HomObj K D E) (g₂ : HomObj K E F),
      onMor (K.comp f₂ f₁) (K.comp g₁ g₂) =
        K.comp (onMor f₁ g₁) (onMor f₂ g₂)

/-- Local monotonicity of a bifunctor (Definition 2.25). -/
def LocallyMonotonic (K : ZeroInfinityCategory) (F : Bifunctor K) : Prop :=
  ∀ {A B C D : K.Obj}
    {f f' : HomObj K B A} {g g' : HomObj K C D},
    (K.Hom B A).le f f' →
      (K.Hom C D).le g g' →
        (K.Hom (F.onObj A C) (F.onObj B D)).le
          (F.onMor f g) (F.onMor f' g')

/-- Local continuity of a bifunctor (Definition 2.26). The order-theoretic
content is recorded as a proposition on chosen directed suprema. -/
def BifunctorPreservesDirectedSups (K : ZeroInfinityCategory) (F : Bifunctor K) : Prop :=
  (∀ {A B C D : K.Obj}
    (f : HomObj K B A)
    (G : HomObj K C D → Prop)
    (hG : Directed (K.Hom C D).le G),
      IsLeastUpperBound (K.Hom (F.onObj A C) (F.onObj B D)).le
        (fun h => ∃ g, G g ∧ F.onMor f g = h)
        (F.onMor f ((K.Hom C D).sup G hG)))
    ∧
  ∀ {A B C D : K.Obj}
    (g : HomObj K C D)
    (H : HomObj K B A → Prop)
    (hH : Directed (K.Hom B A).le H),
      IsLeastUpperBound (K.Hom (F.onObj A C) (F.onObj B D)).le
        (fun h => ∃ f, H f ∧ F.onMor f g = h)
        (F.onMor ((K.Hom B A).sup H hH) g)

structure LocallyContinuous (K : ZeroInfinityCategory) (F : Bifunctor K) where
  monotone : LocallyMonotonic K F
  preservesDirectedSups : BifunctorPreservesDirectedSups K F

/-- Equivalence of objects in a `0`-∞-category, used to express the homotopy
domain equation. -/
structure ObjectEquivalence (K : ZeroInfinityCategory) (A B : K.Obj) where
  forward : HomObj K A B
  backward : HomObj K B A
  left_inv : K.comp forward backward = K.id A
  right_inv : K.comp backward forward = K.id B

/-- A cartesian closed `0`-∞-category with chosen final object and exponential,
enough to state the homotopy domain equation from Remark 2.7. -/
structure CartesianClosedZeroInfinityCategory extends ZeroInfinityCategory where
  final : Obj
  exponential : Obj → Obj → Obj

/-- The homotopy domain equation `K ≃ [K ⇒ K]`. -/
structure HomotopyDomainEquation (K : CartesianClosedZeroInfinityCategory) where
  object : K.Obj
  equivalence :
    ObjectEquivalence K.toZeroInfinityCategory object (K.exponential object object)
