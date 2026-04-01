/-!
# ∞-Categories and Kan Complexes

This module packages Definitions 2.7-2.14 of
Martínez-Rivillas and de Queiroz, *The K∞ Homotopy λ-Model*.

It is intentionally self-contained at the module level, so later files can
import a stable API without depending on hidden namespace details.
-/

universe u v

/-- A simplicial set, repeated here as the ambient carrier for the
∞-categorical layer of Section 2. -/
structure SSet where
  Simplex : Nat → Type u
  face : (n : Nat) → Nat → Simplex (n + 1) → Simplex n
  degen : (n : Nat) → Nat → Simplex n → Simplex (n + 1)
  face_degen0_eq : ∀ (σ : Simplex 0),
      face 0 0 (degen 0 0 σ) = σ
  face_degen0_succ : ∀ (σ : Simplex 0),
      face 0 1 (degen 0 0 σ) = σ
  face_face : ∀ (n : Nat) (σ : Simplex (n + 2)) {i j : Nat},
      i ≤ j → j ≤ n + 1 →
      face n i (face (n + 1) (j + 1) σ) = face n j (face (n + 1) i σ)
  face_degen_lt : ∀ (n : Nat) (σ : Simplex (n + 1)) {i j : Nat},
      i < j → j ≤ n + 1 →
      face (n + 1) i (degen (n + 1) j σ) =
        degen n (j - 1) (face n i σ)
  face_degen_eq : ∀ (n : Nat) (σ : Simplex (n + 1)) {i : Nat},
      i ≤ n + 1 →
      face (n + 1) i (degen (n + 1) i σ) = σ
  face_degen_succ : ∀ (n : Nat) (σ : Simplex (n + 1)) {i : Nat},
      i ≤ n + 1 →
      face (n + 1) (i + 1) (degen (n + 1) i σ) = σ
  face_degen_gt : ∀ (n : Nat) (σ : Simplex (n + 1)) {i j : Nat},
      j + 1 < i → i ≤ n + 2 →
      face (n + 1) i (degen (n + 1) j σ) =
        degen n j (face n (i - 1) σ)
  degen_degen : ∀ (n : Nat) (σ : Simplex n) {i j : Nat},
      i ≤ j → j ≤ n →
      degen (n + 1) (j + 1) (degen n i σ) =
        degen (n + 1) i (degen n j σ)

abbrev Obj (X : SSet) : Type u := X.Simplex 0

/-- Simplicial morphisms, used as functors of simplicial sets. -/
structure SSetHom (X Y : SSet) where
  app : ∀ n, X.Simplex n → Y.Simplex n
  natural_face : ∀ (n i : Nat) (σ : X.Simplex (n + 1)),
      app n (X.face n i σ) = Y.face n i (app (n + 1) σ)
  natural_degen : ∀ (n i : Nat) (σ : X.Simplex n),
      app (n + 1) (X.degen n i σ) = Y.degen n i (app n σ)

namespace SSetHom

instance {X Y : SSet} : CoeFun (SSetHom X Y) (fun _ => ∀ n, X.Simplex n → Y.Simplex n) where
  coe f := f.app

def id (X : SSet) : SSetHom X X where
  app := fun _ σ => σ
  natural_face := by
    intro n i σ
    rfl
  natural_degen := by
    intro n i σ
    rfl

def comp {X Y Z : SSet} (g : SSetHom Y Z) (f : SSetHom X Y) : SSetHom X Z where
  app := fun n σ => g.app n (f.app n σ)
  natural_face := by
    intro n i σ
    rw [f.natural_face, g.natural_face]
  natural_degen := by
    intro n i σ
    rw [f.natural_degen, g.natural_degen]

end SSetHom

/-- Compatible horn data for an `(n + 1)`-simplex with one face removed. -/
structure Horn (X : SSet) (n missing : Nat) where
  missing_le : missing ≤ n + 1
  facet : ∀ (i : Nat), i ≠ missing → X.Simplex n
  compatibility :
    match n with
    | 0 => True
    | m + 1 =>
        ∀ {i j : Nat} (_hi : i ≤ m + 2) (_hj : j ≤ m + 2)
          (hmi : i ≠ missing) (hmj : j ≠ missing), i < j →
          X.face m i (facet j hmj) =
            X.face m (j - 1) (facet i hmi)

/-- Compatible boundary data for an `(n + 1)`-simplex. -/
structure Boundary (X : SSet) (n : Nat) where
  facet : ∀ (i : Nat), i ≤ n + 1 → X.Simplex n
  compatibility :
    match n with
    | 0 => True
    | m + 1 =>
        ∀ {i j : Nat} (hi : i ≤ m + 2) (hj : j ≤ m + 2), i < j →
          X.face m i (facet j hj) =
            X.face m (j - 1) (facet i hi)

/-- An ∞-category is a simplicial set with fillers for every inner horn
(Definition 2.7). -/
structure InfinityCategory where
  toSSet : SSet
  fill :
    ∀ {n i : Nat},
      0 < i → i < n + 1 →
        Horn toSSet n i → toSSet.Simplex (n + 1)
  fill_spec :
    ∀ {n i : Nat} (hi0 : 0 < i) (hin : i < n + 1)
      (Λ : Horn toSSet n i) (j : Nat) (_hj : j ≤ n + 1)
      (hji : j ≠ i),
      toSSet.face n j (fill hi0 hin Λ) = Λ.facet j hji

/-- A Kan complex is a simplicial set with fillers for all horns
(Definition 2.8). -/
structure KanComplex where
  toSSet : SSet
  fill :
    ∀ {n i : Nat},
      i ≤ n + 1 →
        Horn toSSet n i → toSSet.Simplex (n + 1)
  fill_spec :
    ∀ {n i : Nat} (hi : i ≤ n + 1)
      (Λ : Horn toSSet n i) (j : Nat) (_hj : j ≤ n + 1)
      (hji : j ≠ i),
      toSSet.face n j (fill hi Λ) = Λ.facet j hji

/-- Every Kan complex determines an ∞-category by restriction to inner horns. -/
def KanComplex.toInfinityCategory (K : KanComplex) : InfinityCategory where
  toSSet := K.toSSet
  fill := fun {_n _i} hi0 hin Λ => K.fill (i := _i) (Nat.le_of_lt hin) Λ
  fill_spec := by
    intro n i hi0 hin Λ j hj hji
    exact K.fill_spec (i := i) (Nat.le_of_lt hin) Λ j hj hji

/-- A boundary square against `p : X → S`, internalizing Definition 2.10. -/
structure BoundarySquare {X S : SSet} (p : SSetHom X S) (n : Nat) where
  boundary : Boundary X n
  simplex : S.Simplex (n + 1)
  comm :
    ∀ (i : Nat) (hi : i ≤ n + 1),
      p.app n (boundary.facet i hi) = S.face n i simplex

/-- A trivial fibration is a simplicial morphism with the right lifting
property against every boundary inclusion `∂Δ[n] ↪ Δ[n]`
(Definition 2.10). -/
structure TrivialFibration {X S : SSet} (p : SSetHom X S) where
  lift : ∀ {n : Nat}, BoundarySquare p n → X.Simplex (n + 1)
  lift_boundary :
    ∀ {n : Nat} (sq : BoundarySquare p n) (i : Nat) (hi : i ≤ n + 1),
      X.face n i (lift sq) = sq.boundary.facet i hi
  lift_comm :
    ∀ {n : Nat} (sq : BoundarySquare p n),
      p.app (n + 1) (lift sq) = sq.simplex

/-- A 1-simplex with chosen source and target. -/
structure Morphism (X : SSet) (x y : Obj X) where
  simplex : X.Simplex 1
  source : X.face 0 1 simplex = x
  target : X.face 0 0 simplex = y

/-- Identity 1-simplex as a degenerate edge. -/
def Morphism.id (X : SSet) (x : Obj X) : Morphism X x x where
  simplex := X.degen 0 0 x
  source := X.face_degen0_succ x
  target := X.face_degen0_eq x

/-- A 2-simplex with prescribed boundary 1-simplices. -/
structure Triangle (X : SSet) {x y z : Obj X}
    (f : Morphism X x y) (h : Morphism X x z) (g : Morphism X y z) where
  simplex : X.Simplex 2
  face0 : X.face 1 0 simplex = g.simplex
  face1 : X.face 1 1 simplex = h.simplex
  face2 : X.face 1 2 simplex = f.simplex

/-- Invertible 1-morphisms, matching Definition 2.12. -/
structure Invertible (X : SSet) {x y : Obj X} (f : Morphism X x y) where
  inverse : Morphism X y x
  leftWitness : Triangle X f (Morphism.id X x) inverse
  rightWitness : Triangle X inverse (Morphism.id X y) f

/-- Equivalent vertices in an ∞-category. -/
structure EquivalentVertices (X : SSet) (x y : Obj X) where
  hom : Morphism X x y
  invertible : Invertible X hom

/-- A chosen Kan-complex model of the morphism space `X(x,y)` from
Definition 2.11. -/
structure MorphismSpace (X : InfinityCategory) (x y : Obj X.toSSet) where
  carrier : KanComplex
  realize : Obj carrier.toSSet → Morphism X.toSSet x y

/-- Functors of ∞-categories are simplicial morphisms. -/
abbrev CatFunctor (X Y : InfinityCategory) : Type _ :=
  SSetHom X.toSSet Y.toSSet

/-- Action of an ∞-functor on vertices. -/
def CatFunctor.onObj {X Y : InfinityCategory} (F : CatFunctor X Y) :
    Obj X.toSSet → Obj Y.toSSet :=
  fun x => F.app 0 x

/-- Action of an ∞-functor on 1-morphisms. -/
def CatFunctor.onMorphism {X Y : InfinityCategory} (F : CatFunctor X Y)
    {x y : Obj X.toSSet} (f : Morphism X.toSSet x y) :
    Morphism Y.toSSet (CatFunctor.onObj F x) (CatFunctor.onObj F y) where
  simplex := F.app 1 f.simplex
  source := by
    calc
      Y.toSSet.face 0 1 (F.app 1 f.simplex)
          = F.app 0 (X.toSSet.face 0 1 f.simplex) := (F.natural_face 0 1 f.simplex).symm
      _ = F.app 0 x := by rw [f.source]
  target := by
    calc
      Y.toSSet.face 0 0 (F.app 1 f.simplex)
          = F.app 0 (X.toSSet.face 0 0 f.simplex) := (F.natural_face 0 0 f.simplex).symm
      _ = F.app 0 y := by rw [f.target]

/-- A chosen cylinder object over `X`, representing a model of `X × Δ[1]`. -/
structure Cylinder (X : SSet) where
  carrier : SSet
  left : SSetHom X carrier
  right : SSetHom X carrier

/-- Natural transformations between simplicial functors into an ∞-category
(Definition 2.13). -/
structure NaturalTransformation {X : SSet} {Y : InfinityCategory}
    (F G : SSetHom X Y.toSSet) where
  cylinder : Cylinder X
  homotopy : SSetHom cylinder.carrier Y.toSSet
  atLeft :
    ∀ x : Obj X, homotopy.app 0 (cylinder.left.app 0 x) = F.app 0 x
  atRight :
    ∀ x : Obj X, homotopy.app 0 (cylinder.right.app 0 x) = G.app 0 x
  component :
    ∀ x : Obj X, Morphism Y.toSSet (F.app 0 x) (G.app 0 x)

/-- Natural equivalences are natural transformations with pointwise
invertible components. -/
structure NaturalEquivalence {X : SSet} {Y : InfinityCategory}
    (F G : SSetHom X Y.toSSet) where
  toNaturalTransformation : NaturalTransformation F G
  invertibleComponent :
    ∀ x : Obj X, Invertible Y.toSSet (toNaturalTransformation.component x)

/-- Categorical equivalence of ∞-categories (Definition 2.14). -/
structure CategoricalEquivalence {X Y : InfinityCategory} (F : CatFunctor X Y) where
  inverse : CatFunctor Y X
  unit :
    NaturalEquivalence
      (Y := X)
      (SSetHom.comp inverse F)
      (SSetHom.id X.toSSet)
  counit :
    NaturalEquivalence
      (Y := Y)
      (SSetHom.comp F inverse)
      (SSetHom.id Y.toSSet)

/-- For Kan complexes, categorical equivalence is the homotopy equivalence of
Remark 2.4. -/
structure HomotopyEquivalence {K L : KanComplex} (F : SSetHom K.toSSet L.toSSet) where
  inverse : SSetHom L.toSSet K.toSSet
  unit :
    NaturalEquivalence
      (Y := K.toInfinityCategory)
      (SSetHom.comp inverse F)
      (SSetHom.id K.toSSet)
  counit :
    NaturalEquivalence
      (Y := L.toInfinityCategory)
      (SSetHom.comp F inverse)
      (SSetHom.id L.toSSet)
