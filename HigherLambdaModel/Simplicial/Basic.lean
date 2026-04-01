/-!
# Simplicial Foundations

This module formalizes the simplicial-set layer from Section 2.1 of
Martínez-Rivillas and de Queiroz, *The K∞ Homotopy λ-Model*.

The development is intentionally independent from the older simplicial
definitions in `HigherLambdaModel.Lambda.ExtensionalKan`.
-/

namespace _root_.HigherLambdaModel.Simplicial

universe u v

/-! ## Elementary Type Equivalences -/

/-- A lightweight equivalence of types. The repository currently does not
depend on a bundled equivalence type from an external library, so Section 2
uses this local notion whenever a definitional bijection is part of the data. -/
structure TypeEquiv (α : Type u) (β : Type v) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a : α, invFun (toFun a) = a
  right_inv : ∀ b : β, toFun (invFun b) = b

/-! ## Simplicial Indexing Category -/

/-- `DeltaHom m n` is an order-preserving map `[m] → [n]` between finite
ordinals. This is the morphism type of the simplicial indexing category `Δ`
from Definition 2.1. -/
structure DeltaHom (m n : Nat) where
  toFun : Fin (m + 1) → Fin (n + 1)
  monotone' : ∀ ⦃a b : Fin (m + 1)⦄, a ≤ b → toFun a ≤ toFun b

namespace DeltaHom

instance {m n : Nat} : CoeFun (DeltaHom m n) (fun _ => Fin (m + 1) → Fin (n + 1)) where
  coe f := f.toFun

@[ext]
theorem ext {m n : Nat} {f g : DeltaHom m n}
    (h : ∀ a, f a = g a) : f = g := by
  cases f with
  | mk f hf =>
    cases g with
    | mk g hg =>
      simp only at h
      have hfg : f = g := funext h
      subst hfg
      simp

/-- Identity simplicial operator. -/
def id (n : Nat) : DeltaHom n n where
  toFun := fun a => a
  monotone' := by
    intro a b hab
    exact hab

/-- Composition of simplicial operators. -/
def comp {ℓ m n : Nat} (g : DeltaHom m n) (f : DeltaHom ℓ m) : DeltaHom ℓ n where
  toFun := fun a => g (f a)
  monotone' := by
    intro a b hab
    exact g.monotone' (f.monotone' hab)

@[simp]
theorem id_apply {n : Nat} (a : Fin (n + 1)) :
    id n a = a :=
  rfl

@[simp]
theorem comp_apply {ℓ m n : Nat} (g : DeltaHom m n) (f : DeltaHom ℓ m) (a : Fin (ℓ + 1)) :
    comp g f a = g (f a) :=
  rfl

@[simp]
theorem id_comp {m n : Nat} (f : DeltaHom m n) :
    comp (id n) f = f := by
  ext a
  rfl

@[simp]
theorem comp_id {m n : Nat} (f : DeltaHom m n) :
    comp f (id m) = f := by
  ext a
  rfl

theorem comp_assoc {k ℓ m n : Nat}
    (h : DeltaHom m n) (g : DeltaHom ℓ m) (f : DeltaHom k ℓ) :
    comp h (comp g f) = comp (comp h g) f := by
  ext a
  rfl

end DeltaHom

/-! ## Simplicial Sets and Simplicial Morphisms -/

/-- A simplicial set given by face and degeneracy maps satisfying the standard
simplicial identities of Remark 2.2 and Definition 2.2. Indices are modeled by
natural numbers, and the laws are required exactly in the in-range cases. -/
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

namespace SSet

/-- Vertices of a simplicial set. -/
abbrev Obj (X : SSet) : Type u := X.Simplex 0

/-- A simplicial morphism is a natural transformation of simplicial sets
(Definition 2.2). -/
structure Hom (X Y : SSet) where
  app : ∀ n, X.Simplex n → Y.Simplex n
  natural_face : ∀ (n i : Nat) (σ : X.Simplex (n + 1)),
      app n (X.face n i σ) = Y.face n i (app (n + 1) σ)
  natural_degen : ∀ (n i : Nat) (σ : X.Simplex n),
      app (n + 1) (X.degen n i σ) = Y.degen n i (app n σ)

namespace Hom

instance {X Y : SSet} : CoeFun (Hom X Y) (fun _ => ∀ n, X.Simplex n → Y.Simplex n) where
  coe f := f.app

@[ext]
theorem ext {X Y : SSet} {f g : Hom X Y}
    (h : ∀ n σ, f.app n σ = g.app n σ) : f = g := by
  cases f with
  | mk f hf hd =>
    cases g with
    | mk g gf gd =>
      simp only at h
      have hfg : f = g := funext (fun n => funext (h n))
      subst hfg
      simp

/-- Identity simplicial morphism. -/
def id (X : SSet) : Hom X X where
  app := fun _ σ => σ
  natural_face := by
    intro n i σ
    rfl
  natural_degen := by
    intro n i σ
    rfl

/-- Composition of simplicial morphisms. -/
def comp {X Y Z : SSet} (g : Hom Y Z) (f : Hom X Y) : Hom X Z where
  app := fun n σ => g.app n (f.app n σ)
  natural_face := by
    intro n i σ
    rw [f.natural_face, g.natural_face]
  natural_degen := by
    intro n i σ
    rw [f.natural_degen, g.natural_degen]

@[simp]
theorem id_app {X : SSet} (n : Nat) (σ : X.Simplex n) :
    id X n σ = σ :=
  rfl

@[simp]
theorem comp_app {X Y Z : SSet} (g : Hom Y Z) (f : Hom X Y) (n : Nat)
    (σ : X.Simplex n) :
    comp g f n σ = g n (f n σ) :=
  rfl

@[simp]
theorem id_comp {X Y : SSet} (f : Hom X Y) :
    comp (id Y) f = f := by
  ext n σ
  rfl

@[simp]
theorem comp_id {X Y : SSet} (f : Hom X Y) :
    comp f (id X) = f := by
  ext n σ
  rfl

theorem comp_assoc {W X Y Z : SSet}
    (h : Hom Y Z) (g : Hom X Y) (f : Hom W X) :
    comp h (comp g f) = comp (comp h g) f := by
  ext n σ
  rfl

end Hom

/-- Product of simplicial sets (Definition 2.3). -/
def prod (X Y : SSet) : SSet where
  Simplex := fun n => X.Simplex n × Y.Simplex n
  face := fun n i σ => (X.face n i σ.1, Y.face n i σ.2)
  degen := fun n i σ => (X.degen n i σ.1, Y.degen n i σ.2)
  face_degen0_eq := by
    intro σ
    cases σ with
    | mk x y =>
      apply Prod.ext
      · exact X.face_degen0_eq x
      · exact Y.face_degen0_eq y
  face_degen0_succ := by
    intro σ
    cases σ with
    | mk x y =>
      apply Prod.ext
      · exact X.face_degen0_succ x
      · exact Y.face_degen0_succ y
  face_face := by
    intro n σ i j hij hj
    cases σ with
    | mk x y =>
      apply Prod.ext
      · exact X.face_face n x hij hj
      · exact Y.face_face n y hij hj
  face_degen_lt := by
    intro n σ i j hij hj
    cases σ with
    | mk x y =>
      apply Prod.ext
      · exact X.face_degen_lt n x hij hj
      · exact Y.face_degen_lt n y hij hj
  face_degen_eq := by
    intro n σ i hi
    cases σ with
    | mk x y =>
      apply Prod.ext
      · exact X.face_degen_eq n x hi
      · exact Y.face_degen_eq n y hi
  face_degen_succ := by
    intro n σ i hi
    cases σ with
    | mk x y =>
      apply Prod.ext
      · exact X.face_degen_succ n x hi
      · exact Y.face_degen_succ n y hi
  face_degen_gt := by
    intro n σ i j hji hi
    cases σ with
    | mk x y =>
      apply Prod.ext
      · exact X.face_degen_gt n x hji hi
      · exact Y.face_degen_gt n y hji hi
  degen_degen := by
    intro n σ i j hij hj
    cases σ with
    | mk x y =>
      apply Prod.ext
      · exact X.degen_degen n x hij hj
      · exact Y.degen_degen n y hij hj

/-- First projection from a product simplicial set. -/
def fst (X Y : SSet) : Hom (prod X Y) X where
  app := fun _ σ => σ.1
  natural_face := by
    intro n i σ
    rfl
  natural_degen := by
    intro n i σ
    rfl

/-- Second projection from a product simplicial set. -/
def snd (X Y : SSet) : Hom (prod X Y) Y where
  app := fun _ σ => σ.2
  natural_face := by
    intro n i σ
    rfl
  natural_degen := by
    intro n i σ
    rfl

/-- Pairing into a product simplicial set. -/
def pair {X Y Z : SSet} (f : Hom X Y) (g : Hom X Z) : Hom X (prod Y Z) where
  app := fun n σ => (f.app n σ, g.app n σ)
  natural_face := by
    intro n i σ
    calc
      (f.app n (X.face n i σ), g.app n (X.face n i σ))
          = (Y.face n i (f.app (n + 1) σ), Z.face n i (g.app (n + 1) σ)) := by
              rw [f.natural_face, g.natural_face]
      _ = (prod Y Z).face n i (f.app (n + 1) σ, g.app (n + 1) σ) := rfl
  natural_degen := by
    intro n i σ
    calc
      (f.app (n + 1) (X.degen n i σ), g.app (n + 1) (X.degen n i σ))
          = (Y.degen n i (f.app n σ), Z.degen n i (g.app n σ)) := by
              rw [f.natural_degen, g.natural_degen]
      _ = (prod Y Z).degen n i (f.app n σ, g.app n σ) := rfl

/-- A chosen model of the standard `n`-simplex `Δ[n]` of Definition 2.4. The
field `yoneda` records the representable description `Δ(-,[n])`. -/
structure StandardSimplex (n : Nat) where
  toSSet : SSet
  yoneda : ∀ m : Nat, TypeEquiv (toSSet.Simplex m) (DeltaHom m n)

/-- A family of chosen models for all standard simplices. -/
structure StandardSimplexFamily where
  simplex : ∀ n : Nat, StandardSimplex n

/-- A chosen model of the mapping simplicial set of Definition 2.5. The field
`simplexEquiv` expresses the defining identity
`Map(X,Y)_n ≃ sSet(X × Δ[n], Y)`. -/
structure MappingSSet (X Y : SSet) where
  standard : StandardSimplexFamily
  toSSet : SSet
  simplexEquiv :
    ∀ n : Nat,
      TypeEquiv (toSSet.Simplex n) (Hom (prod X (standard.simplex n).toSSet) Y)

/-- Compatible boundary data for an `(n + 1)`-simplex. This is the internalized
form of a map `∂Δ[n + 1] → X`. -/
structure Boundary (X : SSet) (n : Nat) where
  facet : ∀ (i : Nat), i ≤ n + 1 → X.Simplex n
  compatibility :
    match n with
    | 0 => True
    | m + 1 =>
        ∀ {i j : Nat} (hi : i ≤ m + 2) (hj : j ≤ m + 2), i < j →
          X.face m i (facet j hj) =
            X.face m (j - 1) (facet i hi)

/-- Compatible horn data for an `(n + 1)`-simplex with the `missing`-th face
removed. This is the internalized form of Definition 2.6. -/
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

/-- `Horn X n i` is an inner horn exactly when `0 < i < n + 1`, i.e. when it
encodes a map out of `Λ[n + 1, i]` with an interior face missing. -/
def Horn.IsInner {X : SSet} {n i : Nat} (_Λ : Horn X n i) : Prop :=
  0 < i ∧ i < n + 1

/-- `Horn X n i` is a left horn exactly when the missing face is not the final
one. -/
def Horn.IsLeft {X : SSet} {n i : Nat} (_Λ : Horn X n i) : Prop :=
  i < n + 1

/-- `Horn X n i` is a right horn exactly when the missing face is not the
initial one. -/
def Horn.IsRight {X : SSet} {n i : Nat} (_Λ : Horn X n i) : Prop :=
  0 < i

end SSet

/-! ## Exported Aliases

These aliases give later modules stable top-level names independent of the
local namespace structure used internally in this file.
-/

abbrev SimpTypeEquiv := TypeEquiv
abbrev SimpSSet := SSet
abbrev SSetObj := SSet.Obj
abbrev SSetHom := SSet.Hom
abbrev SSetBoundary := SSet.Boundary
abbrev SSetHorn := SSet.Horn
abbrev SSetStandardSimplex := SSet.StandardSimplex
abbrev SSetStandardSimplexFamily := SSet.StandardSimplexFamily
abbrev SSetMapping := SSet.MappingSSet
def sSetProd := SSet.prod
def sSetFst := SSet.fst
def sSetSnd := SSet.snd
abbrev sSetPair {X Y Z : SSet} := @SSet.pair X Y Z

end HigherLambdaModel.Simplicial

abbrev TypeEquiv := HigherLambdaModel.Simplicial.TypeEquiv
abbrev DeltaHom := HigherLambdaModel.Simplicial.DeltaHom
abbrev SSet := HigherLambdaModel.Simplicial.SimpSSet
abbrev SSetObj := HigherLambdaModel.Simplicial.SSetObj
abbrev SSetHom := HigherLambdaModel.Simplicial.SSetHom
abbrev SSetBoundary := HigherLambdaModel.Simplicial.SSetBoundary
abbrev SSetHorn := HigherLambdaModel.Simplicial.SSetHorn
abbrev SSetStandardSimplex := HigherLambdaModel.Simplicial.SSetStandardSimplex
abbrev SSetStandardSimplexFamily := HigherLambdaModel.Simplicial.SSetStandardSimplexFamily
abbrev SSetMapping := HigherLambdaModel.Simplicial.SSetMapping
abbrev sSetProd := HigherLambdaModel.Simplicial.sSetProd
abbrev sSetFst := HigherLambdaModel.Simplicial.sSetFst
abbrev sSetSnd := HigherLambdaModel.Simplicial.sSetSnd
abbrev sSetPair {X Y Z : HigherLambdaModel.Simplicial.SSet} :=
  @HigherLambdaModel.Simplicial.sSetPair X Y Z
