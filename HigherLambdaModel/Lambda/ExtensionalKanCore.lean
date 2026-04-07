/-
# Extensional Kan Complexes and Homotopic λ-Models

This module formalizes the key definitions from Section 2 of
"The Theory of an Arbitrary Higher λ-Model" (arXiv:2111.07092).

## Key Definitions (from the paper)

- **Definition 2.1**: ∞-category (simplicial set with inner horn filling)
- **Definition 2.2**: Kan complex (∞-groupoid, horn filling for all horns)
- **Definition 2.7**: Reflexive Kan complex K with F : K → [K → K], G : [K → K] → K
- **Definition 2.9**: Theory of an extensional Kan complex Th(K)
- **Definition 2.10**: Homotopy Type-Free Theory (HoTFT)

## References

- Martínez-Rivillas & de Queiroz, "The Theory of an Arbitrary Higher λ-Model"
- Lurie, "Higher Topos Theory" (for ∞-category definitions)
-/

import HigherLambdaModel.Lambda.Reduction
import HigherLambdaModel.Lambda.HigherTerms

namespace HigherLambdaModel.Lambda.ExtensionalKan

open Term HigherTerms

/-! ## Simplicial Sets and Kan Complexes -/

/-- A simplicial set presented by face and degeneracy operators satisfying the
standard simplicial identities. Indices are modeled by natural numbers; the
laws only refer to the in-range cases. -/
structure SimplicialSet where
  Simplex : Nat → Type
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
      face (n + 1) i (degen (n + 1) j σ) = degen n (j - 1) (face n i σ)
  face_degen_eq : ∀ (n : Nat) (σ : Simplex (n + 1)) {i : Nat},
      i ≤ n + 1 →
      face (n + 1) i (degen (n + 1) i σ) = σ
  face_degen_succ : ∀ (n : Nat) (σ : Simplex (n + 1)) {i : Nat},
      i ≤ n + 1 →
      face (n + 1) (i + 1) (degen (n + 1) i σ) = σ
  face_degen_gt : ∀ (n : Nat) (σ : Simplex (n + 1)) {i j : Nat},
      j + 1 < i → i ≤ n + 2 →
      face (n + 1) i (degen (n + 1) j σ) = degen n j (face n (i - 1) σ)
  degen_degen : ∀ (n : Nat) (σ : Simplex n) {i j : Nat},
      i ≤ j → j ≤ n →
      degen (n + 1) (j + 1) (degen n i σ) = degen (n + 1) i (degen n j σ)

abbrev SimplicialSet.Obj (S : SimplicialSet) : Type := S.Simplex 0

/-- An `n`-horn missing the `missing`-th face. The compatibility condition is
the usual simplicial horn boundary condition. -/
structure Horn (S : SimplicialSet) (n missing : Nat) where
  missing_le : missing ≤ n + 1
  facet : ∀ (i : Nat), i ≠ missing → S.Simplex n
  compatibility :
    match n with
    | 0 => True
    | m + 1 =>
        ∀ {i j : Nat} (_hi : i ≤ n + 1) (_hj : j ≤ n + 1)
          (hmi : i ≠ missing) (hmj : j ≠ missing),
          i < j →
          S.face m i (facet j hmj) = S.face m (j - 1) (facet i hmi)

/-- A Kan complex is a simplicial set in which every horn has a chosen filler. -/
structure KanComplex extends SimplicialSet where
  fill : ∀ {n missing : Nat}, Horn toSimplicialSet n missing → Simplex (n + 1)
  fill_spec : ∀ {n missing : Nat} (Λ : Horn toSimplicialSet n missing)
      {i : Nat} (_hi : i ≤ n + 1) (hmi : i ≠ missing),
      face n i (fill Λ) = Λ.facet i hmi

/-- A strict Kan complex is a Kan complex whose chosen horn fillers are unique:
any simplex with the prescribed non-missing faces is equal to the chosen filler. -/
structure StrictKanComplex extends KanComplex where
  fill_unique : ∀ {n missing : Nat} (Λ : Horn toSimplicialSet n missing)
      (σ : Simplex (n + 1)),
      (∀ {i : Nat} (_hi : i ≤ n + 1) (hmi : i ≠ missing),
          face n i σ = Λ.facet i hmi) →
      σ = fill Λ

/-- A path from `a` to `b` is a 1-simplex with the prescribed endpoints. We
use the standard simplicial convention that `d₁` is the source and `d₀` the
target. -/
structure KanComplex.PathSpace (K : KanComplex) (a b : K.Obj) where
  simplex : K.Simplex 1
  source : K.face 0 1 simplex = a
  target : K.face 0 0 simplex = b

/-- The reflexive path at `a`, given by the degenerate edge on `a`. -/
def KanComplex.reflPath (K : KanComplex) (a : K.Obj) : K.PathSpace a a where
  simplex := K.degen 0 0 a
  source := K.face_degen0_succ a
  target := K.face_degen0_eq a

/-- A 2-simplex with prescribed three boundary edges. This records the actual
chosen triangle witnessing the composite of two edges or any other simplicial
2-cell with general boundary. -/
structure KanComplex.Triangle (K : KanComplex) {a b c : K.Obj}
    (p : K.PathSpace a b) (m : K.PathSpace a c) (q : K.PathSpace b c) where
  simplex : K.Simplex 2
  face0 : K.face 1 0 simplex = q.simplex
  face1 : K.face 1 1 simplex = m.simplex
  face2 : K.face 1 2 simplex = p.simplex

/-- A 3-simplex with prescribed four boundary triangles. This records the
chosen tetrahedron witnessing a compatibility between 2-cells. -/
structure KanComplex.Tetrahedron (K : KanComplex)
    {a b c d : K.Obj}
    {p01 : K.PathSpace a b} {p02 : K.PathSpace a c} {p03 : K.PathSpace a d}
    {p12 : K.PathSpace b c} {p13 : K.PathSpace b d} {p23 : K.PathSpace c d}
    (τ0 : K.Triangle p12 p13 p23)
    (τ1 : K.Triangle p02 p03 p23)
    (τ2 : K.Triangle p01 p03 p13)
    (τ3 : K.Triangle p01 p02 p12) where
  simplex : K.Simplex 3
  face0 : K.face 2 0 simplex = τ0.simplex
  face1 : K.face 2 1 simplex = τ1.simplex
  face2 : K.face 2 2 simplex = τ2.simplex
  face3 : K.face 2 3 simplex = τ3.simplex

/-- A semantic 2-cell between parallel paths is a 2-simplex whose two nonzero
faces are the given paths and whose remaining face is the reflexive edge at the
common target. This is the standard left-homotopy boundary convention in a Kan
complex. -/
structure KanComplex.Path2 (K : KanComplex) {a b : K.Obj}
    (p q : K.PathSpace a b) where
  simplex : K.Simplex 2
  face0 : K.face 1 0 simplex = (K.reflPath b).simplex
  face1 : K.face 1 1 simplex = q.simplex
  face2 : K.face 1 2 simplex = p.simplex

/-- Every path 2-cell determines a triangle with degenerate third side. -/
def KanComplex.Path2.toTriangle (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} (α : K.Path2 p q) :
    K.Triangle p q (K.reflPath b) where
  simplex := α.simplex
  face0 := α.face0
  face1 := α.face1
  face2 := α.face2

/-- Reflexivity of semantic 2-cells by degenerating a 1-simplex. -/
def KanComplex.reflPath2 (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : K.Path2 p p := by
  refine
    { simplex := K.degen 1 1 p.simplex
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · calc
      K.face 1 0 (K.degen 1 1 p.simplex)
          = K.degen 0 0 (K.face 0 0 p.simplex) := by
              simpa using (K.face_degen_lt 0 p.simplex (i := 0) (j := 1) (by omega) (by omega))
      _ = K.degen 0 0 b := by rw [p.target]
      _ = (K.reflPath b).simplex := rfl
  · simpa using (K.face_degen_eq 0 p.simplex (i := 1) (by omega))
  · simpa using (K.face_degen_succ 0 p.simplex (i := 1) (by omega))

/-- A semantic 3-cell between parallel semantic 2-cells. The boundary follows
the same left-homotopy convention as `Path2`: `d₁` and `d₂` are the target and
source 2-cells, `d₀` is the fully degenerate 2-cell at the common target, and
`d₃` is the degenerate 2-cell on the common source path. -/
structure KanComplex.Path3 (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} (α β : K.Path2 p q) where
  simplex : K.Simplex 3
  face0 : K.face 2 0 simplex = (K.reflPath2 (K.reflPath b)).simplex
  face1 : K.face 2 1 simplex = β.simplex
  face2 : K.face 2 2 simplex = α.simplex
  face3 : K.face 2 3 simplex = (K.reflPath2 p).simplex

/-- Every path 3-cell determines a tetrahedron with degenerate outer faces. -/
def KanComplex.Path3.toTetrahedron (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} {α β : K.Path2 p q} (η : K.Path3 α β) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath b)).toTriangle
      β.toTriangle
      α.toTriangle
      (K.reflPath2 p).toTriangle where
  simplex := η.simplex
  face0 := η.face0
  face1 := η.face1
  face2 := η.face2
  face3 := η.face3

/-- A tetrahedron with the degenerate outer faces of a `Path3` can be read
back as a semantic 3-cell. -/
def KanComplex.Tetrahedron.toPath3 (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} {α β : K.Path2 p q}
    (ω : K.Tetrahedron
      (K.reflPath2 (K.reflPath b)).toTriangle
      β.toTriangle
      α.toTriangle
      (K.reflPath2 p).toTriangle) :
    K.Path3 α β where
  simplex := ω.simplex
  face0 := ω.face0
  face1 := ω.face1
  face2 := ω.face2
  face3 := ω.face3

private theorem KanComplex.reflPath2_reflPath_simplex
    (K : KanComplex) (b : K.Obj) :
    K.degen 1 0 (K.reflPath b).simplex = (K.reflPath2 (K.reflPath b)).simplex := by
  change K.degen 1 0 (K.degen 0 0 b) = K.degen 1 1 (K.degen 0 0 b)
  symm
  simpa using (K.degen_degen 0 b (i := 0) (j := 0) (by omega) (by omega))

/-- Reflexivity of semantic 3-cells by degenerating a semantic 2-cell. -/
def KanComplex.reflPath3 (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} (α : K.Path2 p q) : K.Path3 α α := by
  refine
    { simplex := K.degen 2 1 α.simplex
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · calc
      K.face 2 0 (K.degen 2 1 α.simplex)
          = K.degen 1 0 (K.face 1 0 α.simplex) := by
              simpa using (K.face_degen_lt 1 α.simplex (i := 0) (j := 1) (by omega) (by omega))
      _ = K.degen 1 0 (K.reflPath b).simplex := by rw [α.face0]
      _ = (K.reflPath2 (K.reflPath b)).simplex := K.reflPath2_reflPath_simplex b
  · simpa using (K.face_degen_eq 1 α.simplex (i := 1) (by omega))
  · simpa using (K.face_degen_succ 1 α.simplex (i := 1) (by omega))
  · calc
      K.face 2 3 (K.degen 2 1 α.simplex)
          = K.degen 1 1 (K.face 1 2 α.simplex) := by
              simpa using (K.face_degen_gt 1 α.simplex (i := 3) (j := 1) (by omega) (by omega))
      _ = K.degen 1 1 p.simplex := by rw [α.face2]
      _ = (K.reflPath2 p).simplex := rfl

private theorem KanComplex.reflPath3_reflPath2_reflPath_simplex
    (K : KanComplex) (b : K.Obj) :
    K.degen 2 0 (K.reflPath2 (K.reflPath b)).simplex =
      (K.reflPath3 (K.reflPath2 (K.reflPath b))).simplex := by
  let σ := K.degen 0 0 b
  have h01 : K.degen 1 0 σ = K.degen 1 1 σ := by
    simpa [σ] using K.reflPath2_reflPath_simplex b
  calc
    K.degen 2 0 (K.reflPath2 (K.reflPath b)).simplex
        = K.degen 2 0 (K.degen 1 1 σ) := rfl
    _ = K.degen 2 2 (K.degen 1 0 σ) := by
          symm
          simpa [σ] using
            (K.degen_degen 1 σ (i := 0) (j := 1) (by omega) (by omega))
    _ = K.degen 2 2 (K.degen 1 1 σ) := by rw [h01]
    _ = K.degen 2 1 (K.degen 1 1 σ) := by
          simpa [σ] using
            (K.degen_degen 1 σ (i := 1) (j := 1) (by omega) (by omega))
    _ = (K.reflPath3 (K.reflPath2 (K.reflPath b))).simplex := rfl

/-- A semantic 4-cell between parallel semantic 3-cells. This is the next
left-homotopy layer above `Path3`, with reflexive outer faces at the common
target object, common source 2-cell, and common source path. -/
structure KanComplex.Path4 (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} {α β : K.Path2 p q} (η θ : K.Path3 α β) where
  simplex : K.Simplex 4
  face0 : K.face 3 0 simplex = (K.reflPath3 (K.reflPath2 (K.reflPath b))).simplex
  face1 : K.face 3 1 simplex = θ.simplex
  face2 : K.face 3 2 simplex = η.simplex
  face3 : K.face 3 3 simplex = (K.reflPath3 α).simplex
  face4 : K.face 3 4 simplex = (K.reflPath3 (K.reflPath2 p)).simplex

/-- Reflexivity of semantic 4-cells by degenerating a semantic 3-cell. -/
def KanComplex.reflPath4 (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} {α β : K.Path2 p q}
    (η : K.Path3 α β) : K.Path4 η η := by
  refine
    { simplex := K.degen 3 1 η.simplex
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_
      face4 := ?_ }
  · calc
      K.face 3 0 (K.degen 3 1 η.simplex)
          = K.degen 2 0 (K.face 2 0 η.simplex) := by
              simpa using (K.face_degen_lt 2 η.simplex (i := 0) (j := 1) (by omega) (by omega))
      _ = K.degen 2 0 (K.reflPath2 (K.reflPath b)).simplex := by rw [η.face0]
      _ = (K.reflPath3 (K.reflPath2 (K.reflPath b))).simplex :=
            K.reflPath3_reflPath2_reflPath_simplex b
  · simpa using (K.face_degen_eq 2 η.simplex (i := 1) (by omega))
  · simpa using (K.face_degen_succ 2 η.simplex (i := 1) (by omega))
  · calc
      K.face 3 3 (K.degen 3 1 η.simplex)
          = K.degen 2 1 (K.face 2 2 η.simplex) := by
              simpa using (K.face_degen_gt 2 η.simplex (i := 3) (j := 1) (by omega) (by omega))
      _ = K.degen 2 1 α.simplex := by rw [η.face2]
      _ = (K.reflPath3 α).simplex := rfl
  · calc
      K.face 3 4 (K.degen 3 1 η.simplex)
          = K.degen 2 1 (K.face 2 3 η.simplex) := by
              simpa using (K.face_degen_gt 2 η.simplex (i := 4) (j := 1) (by omega) (by omega))
      _ = K.degen 2 1 (K.reflPath2 p).simplex := by rw [η.face3]
      _ = (K.reflPath3 (K.reflPath2 p)).simplex := rfl

/-- Vertical composition of semantic 3-cells, obtained by filling a 4-horn. -/
def KanComplex.transPath3 (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} {α β γ : K.Path2 p q}
    (η : K.Path3 α β) (θ : K.Path3 β γ) : K.Path3 α γ := by
  let ε := K.reflPath3 (K.reflPath2 (K.reflPath b))
  let ρ := K.reflPath3 (K.reflPath2 p)
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then θ.simplex
        else if h3 : i = 3 then η.simplex
        else ρ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using θ.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using η.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using ρ.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using η.face1.trans θ.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using ρ.face1.trans θ.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using ρ.face3.trans η.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ) (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ε.simplex := by rw [h0]
      _ = (K.reflPath2 (K.reflPath b)).simplex := ε.face1
  · have h1 : K.face 3 1 (K.fill Λ) = θ.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 θ.simplex := by rw [h1]
      _ = γ.simplex := θ.face1
  · have h3 : K.face 3 3 (K.fill Λ) = η.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ) (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 η.simplex := by rw [h3]
      _ = α.simplex := η.face2
  · have h4 : K.face 3 4 (K.fill Λ) = ρ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ) (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 ρ.simplex := by rw [h4]
      _ = (K.reflPath2 p).simplex := ρ.face2

/-- Symmetry of semantic 3-cells, obtained by filling a 4-horn. -/
def KanComplex.symmPath3 (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} {α β : K.Path2 p q}
    (η : K.Path3 α β) : K.Path3 β α := by
  let ε := K.reflPath3 (K.reflPath2 (K.reflPath b))
  let ρ := K.reflPath3 α
  let rp := K.reflPath3 (K.reflPath2 p)
  let Λ : Horn K.toSimplicialSet 3 1 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h2 : i = 2 then ρ.simplex
        else if h3 : i = 3 then η.simplex
        else rp.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h02 | hrest
        · rcases h02 with ⟨rfl, rfl⟩
          simpa using ρ.face0.trans ε.face1.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using η.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using rp.face0.trans ε.face3.symm
            · rcases hrest with h23 | hrest
              · rcases h23 with ⟨rfl, rfl⟩
                simpa using η.face2.trans ρ.face2.symm
              · rcases hrest with h24 | h34
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using rp.face2.trans ρ.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using rp.face3.trans η.face3.symm }
  refine
    { simplex := K.face 3 1 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 1 (K.fill Λ))
          = K.face 2 0 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ) (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 2 0 ε.simplex := by rw [h0]
      _ = (K.reflPath2 (K.reflPath b)).simplex := ε.face0
  · have h2 : K.face 3 2 (K.fill Λ) = ρ.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 2 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ρ.simplex := by rw [h2]
      _ = α.simplex := ρ.face1
  · have h3 : K.face 3 3 (K.fill Λ) = η.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 1 η.simplex := by rw [h3]
      _ = β.simplex := η.face1
  · have h4 : K.face 3 4 (K.fill Λ) = rp.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ) (i := 1) (j := 3) (by omega) (by omega))
      _ = K.face 2 1 rp.simplex := by rw [h4]
      _ = (K.reflPath2 p).simplex := rp.face1

/-- The degenerate triangle at the source of a path. -/
def KanComplex.sourceDegenerateTriangle (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : K.Triangle (K.reflPath a) p p := by
  refine
    { simplex := K.degen 1 0 p.simplex
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · simpa using (K.face_degen_eq 0 p.simplex (i := 0) (by omega))
  · simpa using (K.face_degen_succ 0 p.simplex (i := 0) (by omega))
  · calc
      K.face 1 2 (K.degen 1 0 p.simplex)
          = K.degen 0 0 (K.face 0 1 p.simplex) := by
              simpa using (K.face_degen_gt 0 p.simplex (i := 2) (j := 0) (by omega) (by omega))
      _ = K.degen 0 0 a := by rw [p.source]
      _ = (K.reflPath a).simplex := rfl

private theorem KanComplex.sourceDegenerateTriangle_refl_eq
    (K : KanComplex) (b : K.Obj) :
    K.sourceDegenerateTriangle (K.reflPath b) =
      (K.reflPath2 (K.reflPath b)).toTriangle := by
  simp [KanComplex.sourceDegenerateTriangle, KanComplex.Path2.toTriangle,
    KanComplex.reflPath2, K.reflPath2_reflPath_simplex b]

private def KanComplex.invHorn (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) :
    Horn K.toSimplicialSet 1 0 :=
  { missing_le := by omega
    facet := fun i _ => if h1 : i = 1 then (K.reflPath a).simplex else p.simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hi1 : i = 1 := by omega
      have hj2 : j = 2 := by omega
      subst hi1
      subst hj2
      simp
      exact p.source.trans (K.reflPath a).source.symm }

private def KanComplex.invSimplex (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : K.Simplex 2 :=
  K.fill (K.invHorn p)

/-- A chosen inverse of a semantic path, obtained by filling an outer horn. -/
def KanComplex.invPath (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : K.PathSpace b a := by
  let Λ := K.invHorn p
  refine
    { simplex := K.face 1 0 (K.invSimplex p)
      source := ?_
      target := ?_ }
  · have h2 : K.face 1 2 (K.invSimplex p) = p.simplex := by
      simpa [KanComplex.invSimplex, Λ] using
        (K.fill_spec Λ (i := 2) (by omega) (by omega))
    calc
      K.face 0 1 (K.face 1 0 (K.invSimplex p))
          = K.face 0 0 (K.face 1 2 (K.invSimplex p)) := by
              symm
              simpa [KanComplex.invSimplex] using
                (K.face_face 0 (K.invSimplex p) (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 0 0 p.simplex := by rw [h2]
      _ = b := p.target
  · have h1 : K.face 1 1 (K.invSimplex p) = (K.reflPath a).simplex := by
      simpa [KanComplex.invSimplex, Λ] using
        (K.fill_spec Λ (i := 1) (by omega) (by omega))
    calc
      K.face 0 0 (K.face 1 0 (K.invSimplex p))
          = K.face 0 0 (K.face 1 1 (K.invSimplex p)) := by
              symm
              simpa [KanComplex.invSimplex] using
                (K.face_face 0 (K.invSimplex p) (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 0 0 (K.reflPath a).simplex := by rw [h1]
      _ = a := (K.reflPath a).target

/-- The triangle witnessing that `p` followed by `invPath p` contracts to the
reflexive path at the source. -/
def KanComplex.rightInverseTriangle (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : K.Triangle p (K.reflPath a) (K.invPath p) := by
  let Λ := K.invHorn p
  refine
    { simplex := K.invSimplex p
      face0 := rfl
      face1 := ?_
      face2 := ?_ }
  · simpa [KanComplex.invSimplex, Λ] using
      (K.fill_spec Λ (i := 1) (by omega) (by omega))
  · simpa [KanComplex.invSimplex, Λ] using
      (K.fill_spec Λ (i := 2) (by omega) (by omega))

private def KanComplex.coinvHorn (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) :
    Horn K.toSimplicialSet 1 2 :=
  { missing_le := by omega
    facet := fun i _ => if h0 : i = 0 then p.simplex else (K.reflPath b).simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hi0 : i = 0 := by omega
      have hj1 : j = 1 := by omega
      subst hi0
      subst hj1
      simp
      exact (K.reflPath b).target.trans p.target.symm }

private def KanComplex.coinvSimplex (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : K.Simplex 2 :=
  K.fill (K.coinvHorn p)

private def KanComplex.coinvPath (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : K.PathSpace b a := by
  let Λ := K.coinvHorn p
  refine
    { simplex := K.face 1 2 (K.coinvSimplex p)
      source := ?_
      target := ?_ }
  · have h1 : K.face 1 1 (K.coinvSimplex p) = (K.reflPath b).simplex := by
      simpa [KanComplex.coinvSimplex, Λ] using
        (K.fill_spec Λ (i := 1) (by omega) (by omega))
    calc
      K.face 0 1 (K.face 1 2 (K.coinvSimplex p))
          = K.face 0 1 (K.face 1 1 (K.coinvSimplex p)) := by
              simpa [KanComplex.coinvSimplex] using
                (K.face_face 0 (K.coinvSimplex p) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 0 1 (K.reflPath b).simplex := by rw [h1]
      _ = b := (K.reflPath b).source
  · have h0 : K.face 1 0 (K.coinvSimplex p) = p.simplex := by
      simpa [KanComplex.coinvSimplex, Λ] using
        (K.fill_spec Λ (i := 0) (by omega) (by omega))
    calc
      K.face 0 0 (K.face 1 2 (K.coinvSimplex p))
          = K.face 0 1 (K.face 1 0 (K.coinvSimplex p)) := by
              simpa [KanComplex.coinvSimplex] using
                (K.face_face 0 (K.coinvSimplex p) (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 0 1 p.simplex := by rw [h0]
      _ = a := p.source

private def KanComplex.compHorn (K : KanComplex) {a b c : K.Obj}
    (p : K.PathSpace a b) (q : K.PathSpace b c) :
    Horn K.toSimplicialSet 1 1 :=
  { missing_le := by omega
    facet := fun i _ => if h0 : i = 0 then q.simplex else p.simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hi0 : i = 0 := by omega
      have hj2 : j = 2 := by omega
      subst hi0
      subst hj2
      simp
      exact p.target.trans q.source.symm }

private def KanComplex.compSimplex (K : KanComplex) {a b c : K.Obj}
    (p : K.PathSpace a b) (q : K.PathSpace b c) : K.Simplex 2 :=
  K.fill (K.compHorn p q)

/-- Compose two semantic paths by filling the inner horn with faces `q` and `p`
and taking the missing middle face as the composite edge. -/
def KanComplex.compPath (K : KanComplex) {a b c : K.Obj}
    (p : K.PathSpace a b) (q : K.PathSpace b c) : K.PathSpace a c := by
  let Λ := K.compHorn p q
  refine
    { simplex := K.face 1 1 (K.compSimplex p q)
      source := ?_
      target := ?_ }
  · have h2 : K.face 1 2 (K.compSimplex p q) = p.simplex := by
      simpa [KanComplex.compSimplex, Λ] using
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 0 1 (K.face 1 1 (K.compSimplex p q))
          = K.face 0 1 (K.face 1 2 (K.compSimplex p q)) := by
              symm
              simpa [KanComplex.compSimplex] using
                (K.face_face 0 (K.compSimplex p q) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 0 1 p.simplex := by rw [h2]
      _ = a := p.source
  · have h0 : K.face 1 0 (K.compSimplex p q) = q.simplex := by
      simpa [KanComplex.compSimplex, Λ] using
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 0 0 (K.face 1 1 (K.compSimplex p q))
          = K.face 0 0 (K.face 1 0 (K.compSimplex p q)) := by
              simpa [KanComplex.compSimplex] using
                (K.face_face 0 (K.compSimplex p q) (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 0 0 q.simplex := by rw [h0]
      _ = c := q.target

/-- The chosen 2-simplex used to compose `p` and `q`. This makes the horn
filler underlying `compPath` available as explicit data for later coherence
arguments. -/
def KanComplex.compTriangle (K : KanComplex) {a b c : K.Obj}
    (p : K.PathSpace a b) (q : K.PathSpace b c) :
    K.Triangle p (K.compPath p q) q := by
  let Λ := K.compHorn p q
  refine
    { simplex := K.compSimplex p q
      face0 := ?_
      face1 := rfl
      face2 := ?_ }
  · simpa [KanComplex.compSimplex, Λ] using
      (K.fill_spec Λ (i := 0) (by omega) (by omega))
  · simpa [KanComplex.compSimplex, Λ] using
      (K.fill_spec Λ (i := 2) (by omega) (by omega))

/-- Vertical composition of semantic 2-cells, obtained by filling a 3-horn. -/
def KanComplex.transPath2 (K : KanComplex) {a b : K.Obj}
    {p q r : K.PathSpace a b} (α : K.Path2 p q) (β : K.Path2 q r) :
    K.Path2 p r := by
  let ε := K.reflPath2 (K.reflPath b)
  let Λ : Horn K.toSimplicialSet 2 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex else if h1 : i = 1 then β.simplex else α.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) := by
          omega
        rcases hij_cases with h01 | h03 | h13
        · rcases h01 with ⟨rfl, rfl⟩
          exact β.face0.trans ε.face0.symm
        · rcases h03 with ⟨rfl, rfl⟩
          exact α.face0.trans ε.face2.symm
        · rcases h13 with ⟨rfl, rfl⟩
          exact α.face1.trans β.face2.symm }
  refine
    { simplex := K.face 2 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 2 (K.fill Λ))
          = K.face 1 1 (K.face 2 0 (K.fill Λ)) := by
              simpa using (K.face_face 1 (K.fill Λ) (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 ε.simplex := by rw [h0]
      _ = (K.reflPath b).simplex := ε.face1
  · have h1 : K.face 2 1 (K.fill Λ) = β.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 2 (K.fill Λ))
          = K.face 1 1 (K.face 2 1 (K.fill Λ)) := by
              simpa using (K.face_face 1 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 β.simplex := by rw [h1]
      _ = r.simplex := β.face1
  · have h3 : K.face 2 3 (K.fill Λ) = α.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 2 (K.fill Λ))
          = K.face 1 2 (K.face 2 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 1 (K.fill Λ) (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 1 2 α.simplex := by rw [h3]
      _ = p.simplex := α.face2

/-- The horn filler used to define `transPath2` is itself a boundary-aware
tetrahedron. It keeps the target factor and source factor as explicit faces,
while its second outer face is the chosen composite 2-cell. -/
def KanComplex.transFillerTetrahedron (K : KanComplex) {a b : K.Obj}
    {p q r : K.PathSpace a b} (α : K.Path2 p q) (β : K.Path2 q r) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath b)).toTriangle
      β.toTriangle
      (K.transPath2 α β).toTriangle
      α.toTriangle := by
  let ε := K.reflPath2 (K.reflPath b)
  let Λ : Horn K.toSimplicialSet 2 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex else if h1 : i = 1 then β.simplex else α.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) := by
          omega
        rcases hij_cases with h01 | h03 | h13
        · rcases h01 with ⟨rfl, rfl⟩
          exact β.face0.trans ε.face0.symm
        · rcases h03 with ⟨rfl, rfl⟩
          exact α.face0.trans ε.face2.symm
        · rcases h13 with ⟨rfl, rfl⟩
          exact α.face1.trans β.face2.symm }
  refine
    { simplex := K.fill Λ
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · simpa using K.fill_spec Λ (i := 0) (by omega) (by omega)
  · simpa using K.fill_spec Λ (i := 1) (by omega) (by omega)
  · change K.face 2 2 (K.fill Λ) = (K.transPath2 α β).simplex
    rfl
  · simpa using K.fill_spec Λ (i := 3) (by omega) (by omega)

/-- Symmetry of semantic 2-cells, obtained by filling a 3-horn. -/
def KanComplex.symmPath2 (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} (α : K.Path2 p q) :
    K.Path2 q p := by
  let ε := K.reflPath2 (K.reflPath b)
  let ρ := K.reflPath2 p
  let Λ : Horn K.toSimplicialSet 2 1 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex else if h2 : i = 2 then ρ.simplex else α.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
          omega
        rcases hij_cases with h02 | h03 | h23
        · rcases h02 with ⟨rfl, rfl⟩
          simpa using ρ.face0.trans ε.face1.symm
        · rcases h03 with ⟨rfl, rfl⟩
          simpa using α.face0.trans ε.face2.symm
        · rcases h23 with ⟨rfl, rfl⟩
          simpa using α.face2.trans ρ.face2.symm }
  refine
    { simplex := K.face 2 1 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 1 (K.fill Λ))
          = K.face 1 0 (K.face 2 0 (K.fill Λ)) := by
              simpa using (K.face_face 1 (K.fill Λ) (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 1 0 ε.simplex := by rw [h0]
      _ = (K.reflPath b).simplex := ε.face0
  · have h2 : K.face 2 2 (K.fill Λ) = ρ.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 1 (K.fill Λ))
          = K.face 1 1 (K.face 2 2 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 1 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 ρ.simplex := by rw [h2]
      _ = p.simplex := ρ.face1
  · have h3 : K.face 2 3 (K.fill Λ) = α.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 1 (K.fill Λ))
          = K.face 1 1 (K.face 2 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 1 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 1 1 α.simplex := by rw [h3]
      _ = q.simplex := α.face1

/-- The tetrahedron filled in the definition of `symmPath2`. -/
def KanComplex.symmTetrahedron (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} (α : K.Path2 p q) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath b)).toTriangle
      (K.symmPath2 α).toTriangle
      (K.reflPath2 p).toTriangle
      α.toTriangle := by
  let ε := K.reflPath2 (K.reflPath b)
  let ρ := K.reflPath2 p
  let Λ : Horn K.toSimplicialSet 2 1 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex else if h2 : i = 2 then ρ.simplex else α.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
          omega
        rcases hij_cases with h02 | h03 | h23
        · rcases h02 with ⟨rfl, rfl⟩
          simpa using ρ.face0.trans ε.face1.symm
        · rcases h03 with ⟨rfl, rfl⟩
          simpa using α.face0.trans ε.face2.symm
        · rcases h23 with ⟨rfl, rfl⟩
          simpa using α.face2.trans ρ.face2.symm }
  refine
    { simplex := K.fill Λ
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · simpa using K.fill_spec Λ (i := 0) (by omega) (by omega)
  · change K.face 2 1 (K.fill Λ) = (K.symmPath2 α).simplex
    rfl
  · simpa using K.fill_spec Λ (i := 2) (by omega) (by omega)
  · simpa using K.fill_spec Λ (i := 3) (by omega) (by omega)

private def KanComplex.triangleComparisonHorn (K : KanComplex) {a b c : K.Obj}
    {p : K.PathSpace a b} {m n : K.PathSpace a c} {q : K.PathSpace b c}
    (τ₁ : K.Triangle p m q) (τ₂ : K.Triangle p n q) :
    Horn K.toSimplicialSet 2 1 :=
  let ε := K.reflPath2 q
  { missing_le := by omega
    facet := fun i _ =>
      if h0 : i = 0 then ε.simplex else if h2 : i = 2 then τ₂.simplex else τ₁.simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
        omega
      rcases hij_cases with h02 | h03 | h23
      · rcases h02 with ⟨rfl, rfl⟩
        simpa using τ₂.face0.trans ε.face1.symm
      · rcases h03 with ⟨rfl, rfl⟩
        simpa using τ₁.face0.trans ε.face2.symm
      · rcases h23 with ⟨rfl, rfl⟩
        simpa using τ₁.face2.trans τ₂.face2.symm }

private def KanComplex.triangleComparisonSimplex (K : KanComplex) {a b c : K.Obj}
    {p : K.PathSpace a b} {m n : K.PathSpace a c} {q : K.PathSpace b c}
    (τ₁ : K.Triangle p m q) (τ₂ : K.Triangle p n q) : K.Simplex 3 :=
  K.fill (K.triangleComparisonHorn τ₁ τ₂)

/-- Two triangles with the same outer boundary induce a semantic 2-cell
between their middle edges. -/
def KanComplex.trianglePath2 (K : KanComplex) {a b c : K.Obj}
    {p : K.PathSpace a b} {m n : K.PathSpace a c} {q : K.PathSpace b c}
    (τ₁ : K.Triangle p m q) (τ₂ : K.Triangle p n q) :
    K.Path2 m n := by
  let Λ := K.triangleComparisonHorn τ₁ τ₂
  refine
    { simplex := K.face 2 1 (K.triangleComparisonSimplex τ₁ τ₂)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.triangleComparisonSimplex τ₁ τ₂) = (K.reflPath2 q).simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 1 (K.triangleComparisonSimplex τ₁ τ₂))
          = K.face 1 0 (K.face 2 0 (K.triangleComparisonSimplex τ₁ τ₂)) := by
              simpa using
                (K.face_face 1 (K.triangleComparisonSimplex τ₁ τ₂)
                  (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 1 0 (K.reflPath2 q).simplex := by rw [h0]
      _ = (K.reflPath c).simplex := (K.reflPath2 q).face0
  · have h2 : K.face 2 2 (K.triangleComparisonSimplex τ₁ τ₂) = τ₂.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 1 (K.triangleComparisonSimplex τ₁ τ₂))
          = K.face 1 1 (K.face 2 2 (K.triangleComparisonSimplex τ₁ τ₂)) := by
              symm
              simpa using
                (K.face_face 1 (K.triangleComparisonSimplex τ₁ τ₂)
                  (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 τ₂.simplex := by rw [h2]
      _ = n.simplex := τ₂.face1
  · have h3 : K.face 2 3 (K.triangleComparisonSimplex τ₁ τ₂) = τ₁.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 1 (K.triangleComparisonSimplex τ₁ τ₂))
          = K.face 1 1 (K.face 2 3 (K.triangleComparisonSimplex τ₁ τ₂)) := by
              symm
              simpa using
                (K.face_face 1 (K.triangleComparisonSimplex τ₁ τ₂)
                  (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 1 1 τ₁.simplex := by rw [h3]
      _ = m.simplex := τ₁.face1

/-- The actual tetrahedron whose middle face is the comparison 2-cell between
two triangles with the same outer boundary. -/
def KanComplex.triangleComparisonTetrahedron (K : KanComplex) {a b c : K.Obj}
    {p : K.PathSpace a b} {m n : K.PathSpace a c} {q : K.PathSpace b c}
    (τ₁ : K.Triangle p m q) (τ₂ : K.Triangle p n q) :
    K.Tetrahedron
      (K.reflPath2 q).toTriangle
      (K.trianglePath2 τ₁ τ₂).toTriangle
      τ₂
      τ₁ := by
  let Λ := K.triangleComparisonHorn τ₁ τ₂
  refine
    { simplex := K.triangleComparisonSimplex τ₁ τ₂
      face0 := ?_
      face1 := rfl
      face2 := ?_
      face3 := ?_ }
  · simpa [KanComplex.triangleComparisonSimplex, KanComplex.triangleComparisonHorn, Λ] using
      (K.fill_spec Λ (i := 0) (by omega) (by omega))
  · simpa [KanComplex.triangleComparisonSimplex, KanComplex.triangleComparisonHorn, Λ] using
      (K.fill_spec Λ (i := 2) (by omega) (by omega))
  · simpa [KanComplex.triangleComparisonSimplex, KanComplex.triangleComparisonHorn, Λ] using
      (K.fill_spec Λ (i := 3) (by omega) (by omega))

/-- Degenerating a triangle along its middle face produces a tetrahedron whose
middle face is the reflexive 2-cell on that middle edge. -/
def KanComplex.reflTriangleTetrahedron (K : KanComplex) {a b c : K.Obj}
    {p : K.PathSpace a b} {m : K.PathSpace a c} {q : K.PathSpace b c}
    (τ : K.Triangle p m q) :
    K.Tetrahedron
      (K.reflPath2 q).toTriangle
      (K.reflPath2 m).toTriangle
      τ
      τ := by
  refine
    { simplex := K.degen 2 2 τ.simplex
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · calc
      K.face 2 0 (K.degen 2 2 τ.simplex)
          = K.degen 1 1 (K.face 1 0 τ.simplex) := by
              simpa using (K.face_degen_lt 1 τ.simplex (i := 0) (j := 2) (by omega) (by omega))
      _ = K.degen 1 1 q.simplex := by rw [τ.face0]
      _ = (K.reflPath2 q).toTriangle.simplex := rfl
  · calc
      K.face 2 1 (K.degen 2 2 τ.simplex)
          = K.degen 1 1 (K.face 1 1 τ.simplex) := by
              simpa using (K.face_degen_lt 1 τ.simplex (i := 1) (j := 2) (by omega) (by omega))
      _ = K.degen 1 1 m.simplex := by rw [τ.face1]
      _ = (K.reflPath2 m).toTriangle.simplex := rfl
  · simpa using (K.face_degen_eq 1 τ.simplex (i := 2) (by omega))
  · simpa using (K.face_degen_succ 1 τ.simplex (i := 2) (by omega))

private def KanComplex.tetrahedronPath3Horn (K : KanComplex) {a b c : K.Obj}
    {p01 : K.PathSpace a b} {p12 p13 : K.PathSpace b c} {p02 p03 : K.PathSpace a c}
    {γ : K.Path2 p12 p13} {α β : K.Path2 p02 p03}
    {τ2 : K.Triangle p01 p03 p13} {τ3 : K.Triangle p01 p02 p12}
    (ω₁ : K.Tetrahedron γ.toTriangle α.toTriangle τ2 τ3)
    (ω₂ : K.Tetrahedron γ.toTriangle β.toTriangle τ2 τ3) :
    Horn K.toSimplicialSet 3 1 :=
  let ε := (K.reflPath3 γ).toTetrahedron
  let ρ := K.reflTriangleTetrahedron τ3
  { missing_le := by omega
    facet := fun i _ =>
      if h0 : i = 0 then ε.simplex
      else if h2 : i = 2 then ω₂.simplex
      else if h3 : i = 3 then ω₁.simplex
      else ρ.simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases :
          (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
            (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
        omega
      rcases hij_cases with h02 | hrest
      · rcases h02 with ⟨rfl, rfl⟩
        simpa using ω₂.face0.trans ε.face1.symm
      · rcases hrest with h03 | hrest
        · rcases h03 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face2.symm
        · rcases hrest with h04 | hrest
          · rcases h04 with ⟨rfl, rfl⟩
            simpa using ρ.face0.trans ε.face3.symm
          · rcases hrest with h23 | hrest
            · rcases h23 with ⟨rfl, rfl⟩
              simpa using ω₁.face2.trans ω₂.face2.symm
            · rcases hrest with h24 | h34
              · rcases h24 with ⟨rfl, rfl⟩
                simpa using ρ.face2.trans ω₂.face3.symm
              · rcases h34 with ⟨rfl, rfl⟩
                simpa using ρ.face3.trans ω₁.face3.symm }

private def KanComplex.tetrahedronPath3Simplex (K : KanComplex) {a b c : K.Obj}
    {p01 : K.PathSpace a b} {p12 p13 : K.PathSpace b c} {p02 p03 : K.PathSpace a c}
    {γ : K.Path2 p12 p13} {α β : K.Path2 p02 p03}
    {τ2 : K.Triangle p01 p03 p13} {τ3 : K.Triangle p01 p02 p12}
    (ω₁ : K.Tetrahedron γ.toTriangle α.toTriangle τ2 τ3)
    (ω₂ : K.Tetrahedron γ.toTriangle β.toTriangle τ2 τ3) : K.Simplex 4 :=
  K.fill (K.tetrahedronPath3Horn ω₁ ω₂)

/-- Two tetrahedra with the same outer boundary and a front face coming from a
semantic 2-cell induce a semantic 3-cell between their middle faces. -/
def KanComplex.tetrahedronPath3 (K : KanComplex) {a b c : K.Obj}
    {p01 : K.PathSpace a b} {p12 p13 : K.PathSpace b c} {p02 p03 : K.PathSpace a c}
    {γ : K.Path2 p12 p13} {α β : K.Path2 p02 p03}
    {τ2 : K.Triangle p01 p03 p13} {τ3 : K.Triangle p01 p02 p12}
    (ω₁ : K.Tetrahedron γ.toTriangle α.toTriangle τ2 τ3)
    (ω₂ : K.Tetrahedron γ.toTriangle β.toTriangle τ2 τ3) :
    K.Path3 α β := by
  let Λ := K.tetrahedronPath3Horn ω₁ ω₂
  let ε := (K.reflPath3 γ).toTetrahedron
  let ρ := K.reflTriangleTetrahedron τ3
  refine
    { simplex := K.face 3 1 (K.tetrahedronPath3Simplex ω₁ ω₂)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.tetrahedronPath3Simplex ω₁ ω₂) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 1 (K.tetrahedronPath3Simplex ω₁ ω₂))
          = K.face 2 0 (K.face 3 0 (K.tetrahedronPath3Simplex ω₁ ω₂)) := by
              simpa using
                (K.face_face 2 (K.tetrahedronPath3Simplex ω₁ ω₂)
                  (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 2 0 ε.simplex := by rw [h0]
      _ = (K.reflPath2 (K.reflPath c)).simplex := ε.face0
  · have h2 : K.face 3 2 (K.tetrahedronPath3Simplex ω₁ ω₂) = ω₂.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 1 (K.tetrahedronPath3Simplex ω₁ ω₂))
          = K.face 2 1 (K.face 3 2 (K.tetrahedronPath3Simplex ω₁ ω₂)) := by
              symm
              simpa using
                (K.face_face 2 (K.tetrahedronPath3Simplex ω₁ ω₂)
                  (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₂.simplex := by rw [h2]
      _ = β.simplex := ω₂.face1
  · have h3 : K.face 3 3 (K.tetrahedronPath3Simplex ω₁ ω₂) = ω₁.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 1 (K.tetrahedronPath3Simplex ω₁ ω₂))
          = K.face 2 1 (K.face 3 3 (K.tetrahedronPath3Simplex ω₁ ω₂)) := by
              symm
              simpa using
                (K.face_face 2 (K.tetrahedronPath3Simplex ω₁ ω₂)
                  (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h3]
      _ = α.simplex := ω₁.face1
  · have h4 : K.face 3 4 (K.tetrahedronPath3Simplex ω₁ ω₂) = ρ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 1 (K.tetrahedronPath3Simplex ω₁ ω₂))
          = K.face 2 1 (K.face 3 4 (K.tetrahedronPath3Simplex ω₁ ω₂)) := by
              symm
              simpa using
                (K.face_face 2 (K.tetrahedronPath3Simplex ω₁ ω₂)
                  (i := 1) (j := 3) (by omega) (by omega))
      _ = K.face 2 1 ρ.simplex := by rw [h4]
      _ = (K.reflPath2 p02).simplex := ρ.face1

/-- A semantic 3-cell between the front faces of two tetrahedra with identical
remaining boundary induces a semantic 3-cell between their middle faces. -/
def KanComplex.tetrahedronFrontPath3 (K : KanComplex) {a b c : K.Obj}
    {p01 : K.PathSpace a b} {p12 p13 : K.PathSpace b c} {p02 p03 : K.PathSpace a c}
    {γ₁ γ₂ : K.Path2 p12 p13} {α β : K.Path2 p02 p03}
    {τ2 : K.Triangle p01 p03 p13} {τ3 : K.Triangle p01 p02 p12}
    (κ : K.Path3 γ₁ γ₂)
    (ω₁ : K.Tetrahedron γ₁.toTriangle α.toTriangle τ2 τ3)
    (ω₂ : K.Tetrahedron γ₂.toTriangle β.toTriangle τ2 τ3) :
    K.Path3 α β := by
  let ρ := K.reflTriangleTetrahedron τ3
  let Λ : Horn K.toSimplicialSet 3 1 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then κ.toTetrahedron.simplex
        else if h2 : i = 2 then ω₂.simplex
        else if h3 : i = 3 then ω₁.simplex
        else ρ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h02 | hrest
        · rcases h02 with ⟨rfl, rfl⟩
          simpa using ω₂.face0.trans κ.toTetrahedron.face1.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₁.face0.trans κ.toTetrahedron.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using ρ.face0.trans κ.toTetrahedron.face3.symm
            · rcases hrest with h23 | hrest
              · rcases h23 with ⟨rfl, rfl⟩
                simpa using ω₁.face2.trans ω₂.face2.symm
              · rcases hrest with h24 | h34
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using ρ.face2.trans ω₂.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using ρ.face3.trans ω₁.face3.symm }
  refine
    { simplex := K.face 3 1 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = κ.toTetrahedron.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 1 (K.fill Λ))
          = K.face 2 0 (K.face 3 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 2 0 κ.toTetrahedron.simplex := by rw [h0]
      _ = (K.reflPath2 (K.reflPath c)).simplex := κ.toTetrahedron.face0
  · have h2 : K.face 3 2 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 2 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₂.simplex := by rw [h2]
      _ = β.simplex := ω₂.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h3]
      _ = α.simplex := ω₁.face1
  · have h4 : K.face 3 4 (K.fill Λ) = ρ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 3) (by omega) (by omega))
      _ = K.face 2 1 ρ.simplex := by rw [h4]
      _ = (K.reflPath2 p02).simplex := ρ.face1

/-- Replace the middle face of a tetrahedron along a semantic 3-cell while
keeping the front and outer faces fixed. -/
def KanComplex.tetrahedronReplaceFace1 (K : KanComplex) {a b c : K.Obj}
    {p01 : K.PathSpace a b} {p12 p13 : K.PathSpace b c}
    {p02 p03 : K.PathSpace a c}
    {γ : K.Path2 p12 p13} {α β : K.Path2 p02 p03}
    {τ2 : K.Triangle p01 p03 p13} {τ3 : K.Triangle p01 p02 p12}
    (Κ : K.Path3 α β)
    (ω : K.Tetrahedron γ.toTriangle α.toTriangle τ2 τ3) :
    K.Tetrahedron γ.toTriangle β.toTriangle τ2 τ3 := by
  let ε := (K.reflPath3 γ).toTetrahedron
  let ρ := K.reflTriangleTetrahedron τ3
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then Κ.toTetrahedron.simplex
        else if h3 : i = 3 then ω.simplex
        else ρ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using Κ.toTetrahedron.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using ρ.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ω.face1.trans Κ.toTetrahedron.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using ρ.face1.trans Κ.toTetrahedron.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using ρ.face3.trans ω.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ε.simplex := by rw [h0]
      _ = γ.toTriangle.simplex := ε.face1
  · have h1 : K.face 3 1 (K.fill Λ) = Κ.toTetrahedron.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 Κ.toTetrahedron.simplex := by rw [h1]
      _ = β.toTriangle.simplex := Κ.toTetrahedron.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω.simplex := by rw [h3]
      _ = τ2.simplex := ω.face2
  · have h4 : K.face 3 4 (K.fill Λ) = ρ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 ρ.simplex := by rw [h4]
      _ = τ3.simplex := ρ.face2

private def KanComplex.tetrahedronComparisonHorn (K : KanComplex) {a b c : K.Obj}
    {p01 : K.PathSpace a b} {p12 p13 : K.PathSpace b c}
    {p021 p022 p03 : K.PathSpace a c}
    {γ : K.Path2 p12 p13} {α : K.Path2 p021 p03} {β : K.Path2 p022 p03}
    {δ : K.Path2 p021 p022}
    {τ2 : K.Triangle p01 p03 p13}
    {τ31 : K.Triangle p01 p021 p12} {τ32 : K.Triangle p01 p022 p12}
    (ω₁ : K.Tetrahedron γ.toTriangle α.toTriangle τ2 τ31)
    (ω₂ : K.Tetrahedron γ.toTriangle β.toTriangle τ2 τ32)
    (κ : K.Tetrahedron (K.reflPath2 p12).toTriangle δ.toTriangle τ32 τ31) :
    Horn K.toSimplicialSet 3 1 :=
  let ε := (K.reflPath3 γ).toTetrahedron
  { missing_le := by omega
    facet := fun i _ =>
      if h0 : i = 0 then ε.simplex
      else if h2 : i = 2 then ω₂.simplex
      else if h3 : i = 3 then ω₁.simplex
      else κ.simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases :
          (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
            (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
        omega
      rcases hij_cases with h02 | hrest
      · rcases h02 with ⟨rfl, rfl⟩
        simpa using ω₂.face0.trans ε.face1.symm
      · rcases hrest with h03 | hrest
        · rcases h03 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face2.symm
        · rcases hrest with h04 | hrest
          · rcases h04 with ⟨rfl, rfl⟩
            simpa using κ.face0.trans ε.face3.symm
          · rcases hrest with h23 | hrest
            · rcases h23 with ⟨rfl, rfl⟩
              simpa using ω₁.face2.trans ω₂.face2.symm
            · rcases hrest with h24 | h34
              · rcases h24 with ⟨rfl, rfl⟩
                simpa using κ.face2.trans ω₂.face3.symm
              · rcases h34 with ⟨rfl, rfl⟩
                simpa using κ.face3.trans ω₁.face3.symm }

private def KanComplex.tetrahedronComparisonSimplex (K : KanComplex) {a b c : K.Obj}
    {p01 : K.PathSpace a b} {p12 p13 : K.PathSpace b c}
    {p021 p022 p03 : K.PathSpace a c}
    {γ : K.Path2 p12 p13} {α : K.Path2 p021 p03} {β : K.Path2 p022 p03}
    {δ : K.Path2 p021 p022}
    {τ2 : K.Triangle p01 p03 p13}
    {τ31 : K.Triangle p01 p021 p12} {τ32 : K.Triangle p01 p022 p12}
    (ω₁ : K.Tetrahedron γ.toTriangle α.toTriangle τ2 τ31)
    (ω₂ : K.Tetrahedron γ.toTriangle β.toTriangle τ2 τ32)
    (κ : K.Tetrahedron (K.reflPath2 p12).toTriangle δ.toTriangle τ32 τ31) :
    K.Simplex 4 :=
  K.fill (K.tetrahedronComparisonHorn ω₁ ω₂ κ)

/-- A 4-simplex comparison between two tetrahedra with the same front face and
same second outer face, but possibly different last outer faces linked by a
comparison 2-cell, yields a new boundary-aware tetrahedron comparing their
middle 2-cells. -/
def KanComplex.tetrahedronComparisonTetrahedron (K : KanComplex) {a b c : K.Obj}
    {p01 : K.PathSpace a b} {p12 p13 : K.PathSpace b c}
    {p021 p022 p03 : K.PathSpace a c}
    {γ : K.Path2 p12 p13} {α : K.Path2 p021 p03} {β : K.Path2 p022 p03}
    {δ : K.Path2 p021 p022}
    {τ2 : K.Triangle p01 p03 p13}
    {τ31 : K.Triangle p01 p021 p12} {τ32 : K.Triangle p01 p022 p12}
    (ω₁ : K.Tetrahedron γ.toTriangle α.toTriangle τ2 τ31)
    (ω₂ : K.Tetrahedron γ.toTriangle β.toTriangle τ2 τ32)
    (κ : K.Tetrahedron (K.reflPath2 p12).toTriangle δ.toTriangle τ32 τ31) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath c)).toTriangle
      β.toTriangle
      α.toTriangle
      δ.toTriangle := by
  let Λ := K.tetrahedronComparisonHorn ω₁ ω₂ κ
  let ε := (K.reflPath3 γ).toTetrahedron
  refine
    { simplex := K.face 3 1 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 1 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ))
          = K.face 2 0 (K.face 3 0 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ)) := by
              simpa using
                (K.face_face 2 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ)
                  (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 2 0 ε.simplex := by rw [h0]
      _ = (K.reflPath2 (K.reflPath c)).simplex := ε.face0
  · have h2 : K.face 3 2 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ) = ω₂.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 1 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ))
          = K.face 2 1 (K.face 3 2 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ)) := by
              symm
              simpa using
                (K.face_face 2 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ)
                  (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₂.simplex := by rw [h2]
      _ = β.simplex := ω₂.face1
  · have h3 : K.face 3 3 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ) = ω₁.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 1 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ))
          = K.face 2 1 (K.face 3 3 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ)) := by
              symm
              simpa using
                (K.face_face 2 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ)
                  (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h3]
      _ = α.simplex := ω₁.face1
  · have h4 : K.face 3 4 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 1 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ))
          = K.face 2 1 (K.face 3 4 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ)) := by
              symm
              simpa using
                (K.face_face 2 (K.tetrahedronComparisonSimplex ω₁ ω₂ κ)
                  (i := 1) (j := 3) (by omega) (by omega))
       _ = K.face 2 1 κ.simplex := by rw [h4]
       _ = δ.simplex := κ.face1

/-- For any triangle `τ : Triangle p m q` the self-comparison 2-cell
`trianglePath2 τ τ` is homotopic to the reflexive 2-cell `reflPath2 m` on the
middle edge.  The proof uses `tetrahedronPath3` on `triangleComparisonTetrahedron τ τ`
(which supplies `trianglePath2 τ τ` as face 1) and `reflTriangleTetrahedron τ`
(which supplies `reflPath2 m` as face 1); both share face 0 = `reflPath2 q` and
faces 2 = 3 = `τ`. -/
def KanComplex.triangleSelfReflPath3 (K : KanComplex) {a b c : K.Obj}
    {p : K.PathSpace a b} {m : K.PathSpace a c} {q : K.PathSpace b c}
    (τ : K.Triangle p m q) :
    K.Path3 (K.trianglePath2 τ τ) (K.reflPath2 m) :=
  K.tetrahedronPath3
    (K.triangleComparisonTetrahedron τ τ)
    (K.reflTriangleTetrahedron τ)

/-- A semantic 3-cell between the last faces of two tetrahedra with identical
front and middle faces induces a semantic 3-cell between their second outer
faces. This is the face-2 analogue of `tetrahedronComparisonTetrahedron`,
specialized to the degenerate front boundary that appears in `trans` fillers. -/
def KanComplex.tetrahedronFace2Path3 (K : KanComplex) {a b : K.Obj}
    {p q r : K.PathSpace a b} {θ : K.Path2 q r}
    {η₁ η₂ : K.Path2 p q} {μ₁ μ₂ : K.Path2 p r}
    (κ : K.Path3 η₁ η₂)
    (ω₁ : K.Tetrahedron
      (K.reflPath2 (K.reflPath b)).toTriangle
      θ.toTriangle
      μ₁.toTriangle
      η₁.toTriangle)
    (ω₂ : K.Tetrahedron
      (K.reflPath2 (K.reflPath b)).toTriangle
      θ.toTriangle
      μ₂.toTriangle
      η₂.toTriangle) :
    K.Path3 μ₁ μ₂ := by
  let ε := (K.reflPath3 (K.reflPath2 (K.reflPath b))).toTetrahedron
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₂.simplex
        else if h2 : i = 2 then ω₁.simplex
        else κ.toTetrahedron.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₂.face0.trans ε.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using ω₁.face0.trans ε.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.toTetrahedron.face0.trans ε.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using ω₁.face1.trans ω₂.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.toTetrahedron.face1.trans ω₂.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using κ.toTetrahedron.face2.trans ω₁.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ε.simplex := by rw [h0]
      _ = (K.reflPath2 (K.reflPath b)).simplex := ε.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h1]
      _ = μ₂.simplex := ω₂.face2
  · have h2 : K.face 3 2 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₁.simplex := by rw [h2]
      _ = μ₁.simplex := ω₁.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.toTetrahedron.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 3) (j := 3) (by omega) (by omega))
       _ = K.face 2 3 κ.toTetrahedron.simplex := by rw [h4]
       _ = (K.reflPath2 p).simplex := κ.toTetrahedron.face3

/-- Vertical composition of semantic 2-cells is congruent in its left argument
up to semantic 3-cells. -/
def KanComplex.transCongrLeftPath3 (K : KanComplex) {a b : K.Obj}
    {p q r : K.PathSpace a b} {η₁ η₂ : K.Path2 p q}
    (Κ : K.Path3 η₁ η₂) (θ : K.Path2 q r) :
    K.Path3 (K.transPath2 η₁ θ) (K.transPath2 η₂ θ) :=
  K.tetrahedronFace2Path3 Κ
    (K.transFillerTetrahedron η₁ θ)
    (K.transFillerTetrahedron η₂ θ)

/-- Vertical composition of semantic 2-cells is congruent in its right argument
up to semantic 3-cells. -/
def KanComplex.transCongrRightPath3 (K : KanComplex) {a b : K.Obj}
    {p q r : K.PathSpace a b} (η : K.Path2 p q)
    {θ₁ θ₂ : K.Path2 q r} (Κ : K.Path3 θ₁ θ₂) :
    K.Path3 (K.transPath2 η θ₁) (K.transPath2 η θ₂) :=
  K.tetrahedronFace2Path3 (K.reflPath3 η)
    (K.tetrahedronReplaceFace1 Κ (K.transFillerTetrahedron η θ₁))
    (K.transFillerTetrahedron η θ₂)

/-- Vertical composition with a reflexive left factor normalizes to the right
factor up to a semantic 3-cell. -/
def KanComplex.transReflLeftPath3 (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} (η : K.Path2 p q) :
    K.Path3 (K.transPath2 (K.reflPath2 p) η) η :=
  K.tetrahedronFace2Path3 (K.reflPath3 (K.reflPath2 p))
    (K.transFillerTetrahedron (K.reflPath2 p) η)
    ((K.reflPath3 η).toTetrahedron)

/-- Vertical composition with a reflexive right factor normalizes to the left
factor up to a semantic 3-cell. -/
def KanComplex.transReflRightPath3 (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} (η : K.Path2 p q) :
    K.Path3 (K.transPath2 η (K.reflPath2 q)) η :=
  K.tetrahedronFace2Path3 (K.reflPath3 η)
    (K.transFillerTetrahedron η (K.reflPath2 q))
    (K.reflTriangleTetrahedron η.toTriangle)

/-- Right composition with a 2-cell followed by its inverse yields the reflexive
2-cell, up to a semantic 3-cell. -/
def KanComplex.transRightCancelPath3 (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} (η : K.Path2 p q) :
    K.Path3 (K.transPath2 η (K.symmPath2 η)) (K.reflPath2 p) :=
  K.tetrahedronFace2Path3 (K.reflPath3 η)
    (K.transFillerTetrahedron η (K.symmPath2 η))
    (K.symmTetrahedron η)

/-- The auxiliary triangle whose comparison with the chosen composition
triangle yields the semantic associator 2-cell. -/
def KanComplex.assocTriangle (K : KanComplex) {a b c d : K.Obj}
    (p : K.PathSpace a b) (q : K.PathSpace b c) (r : K.PathSpace c d) :
    K.Triangle p (K.compPath (K.compPath p q) r) (K.compPath q r) := by
  let Λ : Horn K.toSimplicialSet 2 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then (K.compTriangle q r).simplex
        else if h1 : i = 1 then (K.compTriangle (K.compPath p q) r).simplex
        else (K.compTriangle p q).simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) := by
          omega
        rcases hij_cases with h01 | h03 | h13
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using (K.compTriangle (K.compPath p q) r).face0.trans
            (K.compTriangle q r).face0.symm
        · rcases h03 with ⟨rfl, rfl⟩
          simpa using (K.compTriangle p q).face0.trans
            (K.compTriangle q r).face2.symm
        · rcases h13 with ⟨rfl, rfl⟩
          simpa using (K.compTriangle p q).face1.trans
            (K.compTriangle (K.compPath p q) r).face2.symm }
  refine
    { simplex := K.face 2 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.fill Λ) = (K.compTriangle q r).simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 2 (K.fill Λ))
          = K.face 1 1 (K.face 2 0 (K.fill Λ)) := by
              simpa using (K.face_face 1 (K.fill Λ) (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.compTriangle q r).simplex := by rw [h0]
      _ = (K.compPath q r).simplex := (K.compTriangle q r).face1
  · have h1 : K.face 2 1 (K.fill Λ) = (K.compTriangle (K.compPath p q) r).simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 2 (K.fill Λ))
          = K.face 1 1 (K.face 2 1 (K.fill Λ)) := by
              simpa using (K.face_face 1 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.compTriangle (K.compPath p q) r).simplex := by rw [h1]
      _ = (K.compPath (K.compPath p q) r).simplex := (K.compTriangle (K.compPath p q) r).face1
  · have h3 : K.face 2 3 (K.fill Λ) = (K.compTriangle p q).simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 2 (K.fill Λ))
          = K.face 1 2 (K.face 2 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 1 (K.fill Λ) (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 1 2 (K.compTriangle p q).simplex := by rw [h3]
      _ = p.simplex := (K.compTriangle p q).face2

/-- Associativity of semantic path composition, as a semantic 2-cell. -/
def KanComplex.associatorPath2 (K : KanComplex) {a b c d : K.Obj}
    (p : K.PathSpace a b) (q : K.PathSpace b c) (r : K.PathSpace c d) :
    K.Path2 (K.compPath (K.compPath p q) r) (K.compPath p (K.compPath q r)) :=
  K.trianglePath2 (K.assocTriangle p q r) (K.compTriangle p (K.compPath q r))

/-- The tetrahedron whose middle face is the associator 2-cell. -/
def KanComplex.associatorTetrahedron (K : KanComplex) {a b c d : K.Obj}
    (p : K.PathSpace a b) (q : K.PathSpace b c) (r : K.PathSpace c d) :
    K.Tetrahedron
      (K.reflPath2 (K.compPath q r)).toTriangle
      (K.associatorPath2 p q r).toTriangle
      (K.compTriangle p (K.compPath q r))
      (K.assocTriangle p q r) :=
  K.triangleComparisonTetrahedron
    (K.assocTriangle p q r)
    (K.compTriangle p (K.compPath q r))

/-- The auxiliary triangle whose comparison with the chosen composition
triangle yields right whiskering of a semantic 2-cell. -/
def KanComplex.whiskerRightTriangle (K : KanComplex) {a b c : K.Obj}
    {p q : K.PathSpace a b} (α : K.Path2 p q) (r : K.PathSpace b c) :
    K.Triangle q (K.compPath p r) r := by
  let αinv := K.symmPath2 α
  let Λ : Horn K.toSimplicialSet 2 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then (K.sourceDegenerateTriangle r).simplex
        else if h1 : i = 1 then (K.compTriangle p r).simplex
        else αinv.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) := by
          omega
        rcases hij_cases with h01 | h03 | h13
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using (K.compTriangle p r).face0.trans
            (K.sourceDegenerateTriangle r).face0.symm
        · rcases h03 with ⟨rfl, rfl⟩
          simpa using αinv.face0.trans (K.sourceDegenerateTriangle r).face2.symm
        · rcases h13 with ⟨rfl, rfl⟩
          simpa using αinv.face1.trans (K.compTriangle p r).face2.symm }
  refine
    { simplex := K.face 2 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.fill Λ) = (K.sourceDegenerateTriangle r).simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 2 (K.fill Λ))
          = K.face 1 1 (K.face 2 0 (K.fill Λ)) := by
              simpa using (K.face_face 1 (K.fill Λ) (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.sourceDegenerateTriangle r).simplex := by rw [h0]
      _ = r.simplex := (K.sourceDegenerateTriangle r).face1
  · have h1 : K.face 2 1 (K.fill Λ) = (K.compTriangle p r).simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 2 (K.fill Λ))
          = K.face 1 1 (K.face 2 1 (K.fill Λ)) := by
              simpa using (K.face_face 1 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.compTriangle p r).simplex := by rw [h1]
      _ = (K.compPath p r).simplex := (K.compTriangle p r).face1
  · have h3 : K.face 2 3 (K.fill Λ) = αinv.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 2 (K.fill Λ))
          = K.face 1 2 (K.face 2 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 1 (K.fill Λ) (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 1 2 αinv.simplex := by rw [h3]
      _ = q.simplex := αinv.face2

/-- Right whiskering of semantic 2-cells by a semantic 1-path. -/
def KanComplex.whiskerRightPath2 (K : KanComplex) {a b c : K.Obj}
    {p q : K.PathSpace a b} (α : K.Path2 p q) (r : K.PathSpace b c) :
    K.Path2 (K.compPath p r) (K.compPath q r) :=
  K.trianglePath2 (K.whiskerRightTriangle α r) (K.compTriangle q r)

/-- The tetrahedron whose middle face compares right whiskering against the
chosen composition triangle. -/
def KanComplex.whiskerRightTetrahedron (K : KanComplex) {a b c : K.Obj}
    {p q : K.PathSpace a b} (α : K.Path2 p q) (r : K.PathSpace b c) :
    K.Tetrahedron
      (K.reflPath2 r).toTriangle
      (K.whiskerRightPath2 α r).toTriangle
      (K.compTriangle q r)
      (K.whiskerRightTriangle α r) :=
  K.triangleComparisonTetrahedron (K.whiskerRightTriangle α r) (K.compTriangle q r)

/-- The chosen inverse contracts the right composite back to the reflexive path
at the source. -/
def KanComplex.rightInversePath2 (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : K.Path2 (K.compPath p (K.invPath p)) (K.reflPath a) :=
  K.symmPath2 (K.trianglePath2 (K.rightInverseTriangle p) (K.compTriangle p (K.invPath p)))

private def KanComplex.whiskerLeftHorn (K : KanComplex) {x a b : K.Obj}
    (r : K.PathSpace x a) {p q : K.PathSpace a b} (α : K.Path2 p q) :
    Horn K.toSimplicialSet 2 1 :=
  { missing_le := by omega
    facet := fun i _ =>
      if h0 : i = 0 then α.simplex
      else if h2 : i = 2 then (K.compTriangle r q).simplex
      else (K.compTriangle r p).simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
        omega
      rcases hij_cases with h02 | h03 | h23
      · rcases h02 with ⟨rfl, rfl⟩
        simpa using (K.compTriangle r q).face0.trans α.face1.symm
      · rcases h03 with ⟨rfl, rfl⟩
        simpa using (K.compTriangle r p).face0.trans α.face2.symm
      · rcases h23 with ⟨rfl, rfl⟩
        simpa using (K.compTriangle r p).face2.trans (K.compTriangle r q).face2.symm }

private def KanComplex.whiskerLeftSimplex (K : KanComplex) {x a b : K.Obj}
    (r : K.PathSpace x a) {p q : K.PathSpace a b} (α : K.Path2 p q) :
    K.Simplex 3 :=
  K.fill (K.whiskerLeftHorn r α)

/-- Left whiskering of semantic 2-cells by a semantic 1-path, obtained by
filling the tetrahedron whose other faces are the original 2-cell and the two
composition triangles. -/
def KanComplex.whiskerLeftPath2 (K : KanComplex) {x a b : K.Obj}
    (r : K.PathSpace x a) {p q : K.PathSpace a b} (α : K.Path2 p q) :
    K.Path2 (K.compPath r p) (K.compPath r q) := by
  let Λ := K.whiskerLeftHorn r α
  refine
    { simplex := K.face 2 1 (K.whiskerLeftSimplex r α)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.whiskerLeftSimplex r α) = α.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 1 (K.whiskerLeftSimplex r α))
          = K.face 1 0 (K.face 2 0 (K.whiskerLeftSimplex r α)) := by
              simpa using
                (K.face_face 1 (K.whiskerLeftSimplex r α)
                  (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 1 0 α.simplex := by rw [h0]
      _ = (K.reflPath b).simplex := α.face0
  · have h2 : K.face 2 2 (K.whiskerLeftSimplex r α) = (K.compTriangle r q).simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 1 (K.whiskerLeftSimplex r α))
          = K.face 1 1 (K.face 2 2 (K.whiskerLeftSimplex r α)) := by
              symm
              simpa using
                (K.face_face 1 (K.whiskerLeftSimplex r α)
                  (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.compTriangle r q).simplex := by rw [h2]
      _ = (K.compPath r q).simplex := (K.compTriangle r q).face1
  · have h3 : K.face 2 3 (K.whiskerLeftSimplex r α) = (K.compTriangle r p).simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 1 (K.whiskerLeftSimplex r α))
          = K.face 1 1 (K.face 2 3 (K.whiskerLeftSimplex r α)) := by
              symm
              simpa using
                (K.face_face 1 (K.whiskerLeftSimplex r α)
                  (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 1 1 (K.compTriangle r p).simplex := by rw [h3]
      _ = (K.compPath r p).simplex := (K.compTriangle r p).face1

/-- The tetrahedron filled in the definition of left whiskering. -/
def KanComplex.whiskerLeftTetrahedron (K : KanComplex) {x a b : K.Obj}
    (r : K.PathSpace x a) {p q : K.PathSpace a b} (α : K.Path2 p q) :
    K.Tetrahedron
      α.toTriangle
      (K.whiskerLeftPath2 r α).toTriangle
      (K.compTriangle r q)
      (K.compTriangle r p) := by
  let Λ := K.whiskerLeftHorn r α
  refine
    { simplex := K.whiskerLeftSimplex r α
      face0 := ?_
      face1 := rfl
      face2 := ?_
      face3 := ?_ }
  · simpa [KanComplex.whiskerLeftSimplex, KanComplex.whiskerLeftHorn, Λ] using
      (K.fill_spec Λ (i := 0) (by omega) (by omega))
  · simpa [KanComplex.whiskerLeftSimplex, KanComplex.whiskerLeftHorn, Λ] using
      (K.fill_spec Λ (i := 2) (by omega) (by omega))
  · simpa [KanComplex.whiskerLeftSimplex, KanComplex.whiskerLeftHorn, Λ] using
      (K.fill_spec Λ (i := 3) (by omega) (by omega))

private def KanComplex.interchangePrimeCoreHorn (K : KanComplex) {a b c : K.Obj}
    {p q : K.PathSpace a b} (η : K.Path2 p q)
    {r s : K.PathSpace b c} (θ : K.Path2 r s) :
    Horn K.toSimplicialSet 2 1 :=
  { missing_le := by omega
    facet := fun i _ =>
      if h0 : i = 0 then θ.simplex
      else if h2 : i = 2 then (K.whiskerRightTriangle η s).simplex
      else (K.whiskerRightTriangle η r).simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
        omega
      rcases hij_cases with h02 | h03 | h23
      · rcases h02 with ⟨rfl, rfl⟩
        simpa using (K.whiskerRightTriangle η s).face0.trans θ.face1.symm
      · rcases h03 with ⟨rfl, rfl⟩
        simpa using (K.whiskerRightTriangle η r).face0.trans θ.face2.symm
      · rcases h23 with ⟨rfl, rfl⟩
        simpa using
          (K.whiskerRightTriangle η r).face2.trans
            (K.whiskerRightTriangle η s).face2.symm }

private def KanComplex.interchangePrimeCoreSimplex (K : KanComplex) {a b c : K.Obj}
    {p q : K.PathSpace a b} (η : K.Path2 p q)
    {r s : K.PathSpace b c} (θ : K.Path2 r s) :
    K.Simplex 3 :=
  K.fill (K.interchangePrimeCoreHorn η θ)

/-- The raw square filler behind the alternative interchange route. It keeps the
two `q`-side whiskering triangles explicit and extracts the intermediate
`p`-side 2-cell between the composites with `r` and `s`. -/
def KanComplex.interchangePrimeCorePath2 (K : KanComplex) {a b c : K.Obj}
    {p q : K.PathSpace a b} (η : K.Path2 p q)
    {r s : K.PathSpace b c} (θ : K.Path2 r s) :
    K.Path2 (K.compPath p r) (K.compPath p s) := by
  let Λ := K.interchangePrimeCoreHorn η θ
  refine
    { simplex := K.face 2 1 (K.interchangePrimeCoreSimplex η θ)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.interchangePrimeCoreSimplex η θ) = θ.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 1 (K.interchangePrimeCoreSimplex η θ))
          = K.face 1 0 (K.face 2 0 (K.interchangePrimeCoreSimplex η θ)) := by
              simpa using
                (K.face_face 1 (K.interchangePrimeCoreSimplex η θ)
                  (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 1 0 θ.simplex := by rw [h0]
      _ = (K.reflPath c).simplex := θ.face0
  · have h2 :
        K.face 2 2 (K.interchangePrimeCoreSimplex η θ) =
          (K.whiskerRightTriangle η s).simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 1 (K.interchangePrimeCoreSimplex η θ))
          = K.face 1 1 (K.face 2 2 (K.interchangePrimeCoreSimplex η θ)) := by
              symm
              simpa using
                (K.face_face 1 (K.interchangePrimeCoreSimplex η θ)
                  (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.whiskerRightTriangle η s).simplex := by rw [h2]
      _ = (K.compPath p s).simplex := (K.whiskerRightTriangle η s).face1
  · have h3 :
        K.face 2 3 (K.interchangePrimeCoreSimplex η θ) =
          (K.whiskerRightTriangle η r).simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 1 (K.interchangePrimeCoreSimplex η θ))
          = K.face 1 1 (K.face 2 3 (K.interchangePrimeCoreSimplex η θ)) := by
              symm
              simpa using
                (K.face_face 1 (K.interchangePrimeCoreSimplex η θ)
                  (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 1 1 (K.whiskerRightTriangle η r).simplex := by rw [h3]
      _ = (K.compPath p r).simplex := (K.whiskerRightTriangle η r).face1

/-- The boundary-aware tetrahedron filled by `interchangePrimeCorePath2`. This is
the raw semantic square whose outer faces are the `q`-side right-whiskering
triangles. -/
def KanComplex.interchangePrimeCoreTetrahedron (K : KanComplex) {a b c : K.Obj}
    {p q : K.PathSpace a b} (η : K.Path2 p q)
    {r s : K.PathSpace b c} (θ : K.Path2 r s) :
    K.Tetrahedron
      θ.toTriangle
      (K.interchangePrimeCorePath2 η θ).toTriangle
      (K.whiskerRightTriangle η s)
      (K.whiskerRightTriangle η r) := by
  let Λ := K.interchangePrimeCoreHorn η θ
  refine
    { simplex := K.interchangePrimeCoreSimplex η θ
      face0 := ?_
      face1 := rfl
      face2 := ?_
      face3 := ?_ }
  · simpa [KanComplex.interchangePrimeCoreSimplex, KanComplex.interchangePrimeCoreHorn, Λ] using
      (K.fill_spec Λ (i := 0) (by omega) (by omega))
  · simpa [KanComplex.interchangePrimeCoreSimplex, KanComplex.interchangePrimeCoreHorn, Λ] using
      (K.fill_spec Λ (i := 2) (by omega) (by omega))
  · simpa [KanComplex.interchangePrimeCoreSimplex, KanComplex.interchangePrimeCoreHorn, Λ] using
      (K.fill_spec Λ (i := 3) (by omega) (by omega))

/-- Degenerating a semantic 2-cell along its first face keeps both the front and
middle faces equal to the original 2-cell, while turning the two outer faces
into source-degenerate triangles on its target and source paths. -/
private def KanComplex.path2DegenerateTetrahedron (K : KanComplex)
    {a b : K.Obj} {p q : K.PathSpace a b} (η : K.Path2 p q) :
    K.Tetrahedron
      η.toTriangle
      η.toTriangle
      (K.sourceDegenerateTriangle q)
      (K.sourceDegenerateTriangle p) := by
  refine
    { simplex := K.degen 2 0 η.simplex
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · simpa using (K.face_degen_eq 1 η.simplex (i := 0) (by omega))
  · simpa using (K.face_degen_succ 1 η.simplex (i := 0) (by omega))
  · calc
      K.face 2 2 (K.degen 2 0 η.simplex)
          = K.degen 1 0 (K.face 1 1 η.simplex) := by
              simpa using
                (K.face_degen_gt 1 η.simplex (i := 2) (j := 0) (by omega) (by omega))
      _ = K.degen 1 0 q.simplex := by rw [η.face1]
      _ = (K.sourceDegenerateTriangle q).simplex := rfl
  · calc
      K.face 2 3 (K.degen 2 0 η.simplex)
          = K.degen 1 0 (K.face 1 2 η.simplex) := by
              simpa using
                (K.face_degen_gt 1 η.simplex (i := 3) (j := 0) (by omega) (by omega))
      _ = K.degen 1 0 p.simplex := by rw [η.face2]
      _ = (K.sourceDegenerateTriangle p).simplex := rfl

/-- Boundary-aware tetrahedron for the standard interchange route: whisker
right along `r`, then whisker left along `q`. -/
private def KanComplex.interchangeStandardBoundaryTetrahedron (K : KanComplex)
    {a b c : K.Obj} {p q : K.PathSpace a b} (η : K.Path2 p q)
    {r s : K.PathSpace b c} (θ : K.Path2 r s) :
    K.Tetrahedron
      (K.transPath2 (K.reflPath2 r) θ).toTriangle
      (K.transPath2 (K.whiskerRightPath2 η r) (K.whiskerLeftPath2 q θ)).toTriangle
      (K.compTriangle q s)
      (K.whiskerRightTriangle η r) := by
  let σ := K.transFillerTetrahedron (K.reflPath2 r) θ
  let ω := K.transFillerTetrahedron (K.whiskerRightPath2 η r) (K.whiskerLeftPath2 q θ)
  let κ := K.whiskerLeftTetrahedron q θ
  let τ := K.whiskerRightTetrahedron η r
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then σ.simplex
        else if h1 : i = 1 then ω.simplex
        else if h2 : i = 2 then κ.simplex
        else τ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω.face0.trans σ.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using κ.face0.trans σ.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using τ.face0.trans σ.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using κ.face1.trans ω.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using τ.face1.trans ω.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using τ.face2.trans κ.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = σ.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 σ.simplex := by rw [h0]
      _ = (K.transPath2 (K.reflPath2 r) θ).toTriangle.simplex := σ.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω.simplex := by rw [h1]
      _ =
          (K.transPath2 (K.whiskerRightPath2 η r) (K.whiskerLeftPath2 q θ)).toTriangle.simplex :=
            ω.face2
  · have h2 : K.face 3 2 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h2]
      _ = (K.compTriangle q s).simplex := κ.face2
  · have h4 : K.face 3 4 (K.fill Λ) = τ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 τ.simplex := by rw [h4]
      _ = (K.whiskerRightTriangle η r).simplex := τ.face3

/-- Boundary-aware tetrahedron for the route that first traverses the raw
prime-core square and then whiskers right along `s`. -/
private def KanComplex.interchangePrimeCoreTopBoundaryTetrahedron (K : KanComplex)
    {a b c : K.Obj} {p q : K.PathSpace a b} (η : K.Path2 p q)
    {r s : K.PathSpace b c} (θ : K.Path2 r s) :
    K.Tetrahedron
      (K.transPath2 θ (K.reflPath2 s)).toTriangle
      (K.transPath2 (K.interchangePrimeCorePath2 η θ) (K.whiskerRightPath2 η s)).toTriangle
      (K.compTriangle q s)
      (K.whiskerRightTriangle η r) := by
  let σ := K.transFillerTetrahedron θ (K.reflPath2 s)
  let ω := K.transFillerTetrahedron (K.interchangePrimeCorePath2 η θ) (K.whiskerRightPath2 η s)
  let κ := K.whiskerRightTetrahedron η s
  let τ := K.interchangePrimeCoreTetrahedron η θ
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then σ.simplex
        else if h1 : i = 1 then ω.simplex
        else if h2 : i = 2 then κ.simplex
        else τ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω.face0.trans σ.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using κ.face0.trans σ.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using τ.face0.trans σ.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using κ.face1.trans ω.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using τ.face1.trans ω.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using τ.face2.trans κ.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = σ.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 σ.simplex := by rw [h0]
      _ = (K.transPath2 θ (K.reflPath2 s)).toTriangle.simplex := σ.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω.simplex := by rw [h1]
      _ =
          (K.transPath2 (K.interchangePrimeCorePath2 η θ) (K.whiskerRightPath2 η s)).toTriangle.simplex :=
            ω.face2
  · have h2 : K.face 3 2 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h2]
      _ = (K.compTriangle q s).simplex := κ.face2
  · have h4 : K.face 3 4 (K.fill Λ) = τ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 τ.simplex := by rw [h4]
      _ = (K.whiskerRightTriangle η r).simplex := τ.face3

/-- The standard interchange route and the route that first traverses the raw
prime-core square then whiskers right along `s` agree up to a semantic 3-cell.
This is the reusable low-level square comparison exposed by
`interchangePrimeCoreTetrahedron`. -/
def KanComplex.interchangePrimeCoreSquarePath3 (K : KanComplex)
    {a b c : K.Obj} {p q : K.PathSpace a b} (η : K.Path2 p q)
    {r s : K.PathSpace b c} (θ : K.Path2 r s) :
    K.Path3
      (K.transPath2 (K.whiskerRightPath2 η r) (K.whiskerLeftPath2 q θ))
      (K.transPath2 (K.interchangePrimeCorePath2 η θ) (K.whiskerRightPath2 η s)) := by
  let κ :
      K.Path3
        (K.transPath2 (K.reflPath2 r) θ)
        (K.transPath2 θ (K.reflPath2 s)) :=
    K.transPath3 (K.transReflLeftPath3 θ)
      (K.symmPath3 (K.transReflRightPath3 θ))
  exact K.tetrahedronFrontPath3 κ
    (K.interchangeStandardBoundaryTetrahedron η θ)
    (K.interchangePrimeCoreTopBoundaryTetrahedron η θ)

/-- Boundary-aware comparison tetrahedron relating left whiskering of a vertical
composite to vertical composition of the left-whiskered 2-cells. -/
private def KanComplex.whiskerLeftTransBoundaryTetrahedron (K : KanComplex)
    {x a b : K.Obj} (r : K.PathSpace x a) {p q s : K.PathSpace a b}
    (α : K.Path2 p q) (β : K.Path2 q s) :
    K.Tetrahedron
      (K.transPath2 α β).toTriangle
      (K.transPath2 (K.whiskerLeftPath2 r α) (K.whiskerLeftPath2 r β)).toTriangle
      (K.compTriangle r s)
      (K.compTriangle r p) := by
  let σ := K.transFillerTetrahedron α β
  let ω := K.transFillerTetrahedron (K.whiskerLeftPath2 r α) (K.whiskerLeftPath2 r β)
  let κ := K.whiskerLeftTetrahedron r β
  let θ := K.whiskerLeftTetrahedron r α
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then σ.simplex
        else if h1 : i = 1 then ω.simplex
        else if h2 : i = 2 then κ.simplex
        else θ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω.face0.trans σ.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using κ.face0.trans σ.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using θ.face0.trans σ.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using κ.face1.trans ω.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using θ.face1.trans ω.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using θ.face2.trans κ.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = σ.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 σ.simplex := by rw [h0]
      _ = (K.transPath2 α β).simplex := σ.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω.simplex := by rw [h1]
      _ = (K.transPath2 (K.whiskerLeftPath2 r α) (K.whiskerLeftPath2 r β)).simplex := ω.face2
  · have h2 : K.face 3 2 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h2]
      _ = (K.compTriangle r s).simplex := κ.face2
  · have h4 : K.face 3 4 (K.fill Λ) = θ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 θ.simplex := by rw [h4]
      _ = (K.compTriangle r p).simplex := θ.face3

/-- Left whiskering commutes with vertical composition up to a semantic 3-cell. -/
def KanComplex.whiskerLeftTransPath3 (K : KanComplex) {x a b : K.Obj}
    (r : K.PathSpace x a) {p q s : K.PathSpace a b}
    (α : K.Path2 p q) (β : K.Path2 q s) :
    K.Path3
      (K.whiskerLeftPath2 r (K.transPath2 α β))
      (K.transPath2 (K.whiskerLeftPath2 r α) (K.whiskerLeftPath2 r β)) :=
  K.tetrahedronPath3
    (K.whiskerLeftTetrahedron r (K.transPath2 α β))
    (K.whiskerLeftTransBoundaryTetrahedron r α β)

/-- Boundary-aware comparison tetrahedron relating left whiskering of a 2-cell
inverse to the inverse of the left-whiskered 2-cell. -/
private def KanComplex.whiskerLeftSymmBoundaryTetrahedron (K : KanComplex)
    {x a b : K.Obj} (r : K.PathSpace x a) {p q : K.PathSpace a b}
    (α : K.Path2 p q) :
    K.Tetrahedron
      (K.symmPath2 α).toTriangle
      (K.symmPath2 (K.whiskerLeftPath2 r α)).toTriangle
      (K.compTriangle r p)
      (K.compTriangle r q) := by
  let σ := K.symmTetrahedron α
  let ω := K.symmTetrahedron (K.whiskerLeftPath2 r α)
  let ρ := K.reflTriangleTetrahedron (K.compTriangle r p)
  let κ := K.whiskerLeftTetrahedron r α
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then σ.simplex
        else if h1 : i = 1 then ω.simplex
        else if h3 : i = 3 then ρ.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω.face0.trans σ.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ρ.face0.trans σ.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans σ.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ρ.face1.trans ω.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ρ.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = σ.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 σ.simplex := by rw [h0]
      _ = (K.symmPath2 α).simplex := σ.face1
  · have h1 : K.face 3 1 (K.fill Λ) = ω.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω.simplex := by rw [h1]
      _ = (K.symmPath2 (K.whiskerLeftPath2 r α)).simplex := ω.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ρ.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ρ.simplex := by rw [h3]
      _ = (K.compTriangle r p).simplex := ρ.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h4]
      _ = (K.compTriangle r q).simplex := κ.face2

/-- Left whiskering commutes with symmetry up to a semantic 3-cell. -/
def KanComplex.whiskerLeftSymmPath3 (K : KanComplex) {x a b : K.Obj}
    (r : K.PathSpace x a) {p q : K.PathSpace a b} (α : K.Path2 p q) :
    K.Path3
      (K.whiskerLeftPath2 r (K.symmPath2 α))
      (K.symmPath2 (K.whiskerLeftPath2 r α)) :=
  K.tetrahedronPath3
    (K.whiskerLeftTetrahedron r (K.symmPath2 α))
    (K.whiskerLeftSymmBoundaryTetrahedron r α)

private def KanComplex.leftUnitorHorn (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : Horn K.toSimplicialSet 2 1 :=
  { missing_le := by omega
    facet := fun i _ =>
      if h0 : i = 0 then (K.reflPath2 p).simplex
      else if h2 : i = 2 then (K.sourceDegenerateTriangle p).simplex
      else (K.compTriangle (K.reflPath a) p).simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
        omega
      rcases hij_cases with h02 | h03 | h23
      · rcases h02 with ⟨rfl, rfl⟩
        simpa using (K.sourceDegenerateTriangle p).face0.trans (K.reflPath2 p).face1.symm
      · rcases h03 with ⟨rfl, rfl⟩
        simpa using (K.compTriangle (K.reflPath a) p).face0.trans (K.reflPath2 p).face2.symm
      · rcases h23 with ⟨rfl, rfl⟩
        simpa using (K.compTriangle (K.reflPath a) p).face2.trans
          (K.sourceDegenerateTriangle p).face2.symm }

private def KanComplex.leftUnitorSimplex (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : K.Simplex 3 :=
  K.fill (K.leftUnitorHorn p)

/-- Left unitor for semantic path composition, as a semantic 2-cell. -/
def KanComplex.leftUnitorPath2 (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : K.Path2 (K.compPath (K.reflPath a) p) p := by
  let Λ := K.leftUnitorHorn p
  refine
    { simplex := K.face 2 1 (K.leftUnitorSimplex p)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.leftUnitorSimplex p) = (K.reflPath2 p).simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 1 (K.leftUnitorSimplex p))
          = K.face 1 0 (K.face 2 0 (K.leftUnitorSimplex p)) := by
              simpa using
                (K.face_face 1 (K.leftUnitorSimplex p)
                  (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 1 0 (K.reflPath2 p).simplex := by rw [h0]
      _ = (K.reflPath b).simplex := (K.reflPath2 p).face0
  · have h2 : K.face 2 2 (K.leftUnitorSimplex p) = (K.sourceDegenerateTriangle p).simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 1 (K.leftUnitorSimplex p))
          = K.face 1 1 (K.face 2 2 (K.leftUnitorSimplex p)) := by
              symm
              simpa using
                (K.face_face 1 (K.leftUnitorSimplex p)
                  (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.sourceDegenerateTriangle p).simplex := by rw [h2]
      _ = p.simplex := (K.sourceDegenerateTriangle p).face1
  · have h3 : K.face 2 3 (K.leftUnitorSimplex p) = (K.compTriangle (K.reflPath a) p).simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 1 (K.leftUnitorSimplex p))
          = K.face 1 1 (K.face 2 3 (K.leftUnitorSimplex p)) := by
              symm
              simpa using
                (K.face_face 1 (K.leftUnitorSimplex p)
                  (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 1 1 (K.compTriangle (K.reflPath a) p).simplex := by rw [h3]
      _ = (K.compPath (K.reflPath a) p).simplex := (K.compTriangle (K.reflPath a) p).face1

/-- The tetrahedron filled in the definition of the left unitor. -/
def KanComplex.leftUnitorTetrahedron (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) :
    K.Tetrahedron
      (K.reflPath2 p).toTriangle
      (K.leftUnitorPath2 p).toTriangle
      (K.sourceDegenerateTriangle p)
      (K.compTriangle (K.reflPath a) p) := by
  let Λ := K.leftUnitorHorn p
  refine
    { simplex := K.leftUnitorSimplex p
      face0 := ?_
      face1 := rfl
      face2 := ?_
      face3 := ?_ }
  · simpa [KanComplex.leftUnitorSimplex, KanComplex.leftUnitorHorn, Λ] using
      (K.fill_spec Λ (i := 0) (by omega) (by omega))
  · simpa [KanComplex.leftUnitorSimplex, KanComplex.leftUnitorHorn, Λ] using
      (K.fill_spec Λ (i := 2) (by omega) (by omega))
  · simpa [KanComplex.leftUnitorSimplex, KanComplex.leftUnitorHorn, Λ] using
      (K.fill_spec Λ (i := 3) (by omega) (by omega))

private def KanComplex.rightUnitorHorn (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : Horn K.toSimplicialSet 2 1 :=
  { missing_le := by omega
    facet := fun i _ =>
      if h0 : i = 0 then (K.reflPath2 (K.reflPath b)).simplex
      else if h2 : i = 2 then (K.reflPath2 p).simplex
      else (K.compTriangle p (K.reflPath b)).simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
        omega
      rcases hij_cases with h02 | h03 | h23
      · rcases h02 with ⟨rfl, rfl⟩
        simpa using (K.reflPath2 p).face0.trans (K.reflPath2 (K.reflPath b)).face1.symm
      · rcases h03 with ⟨rfl, rfl⟩
        simpa using (K.compTriangle p (K.reflPath b)).face0.trans
          (K.reflPath2 (K.reflPath b)).face2.symm
      · rcases h23 with ⟨rfl, rfl⟩
        simpa using (K.compTriangle p (K.reflPath b)).face2.trans (K.reflPath2 p).face2.symm }

private def KanComplex.rightUnitorSimplex (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : K.Simplex 3 :=
  K.fill (K.rightUnitorHorn p)

/-- Right unitor for semantic path composition, as a semantic 2-cell. -/
def KanComplex.rightUnitorPath2 (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : K.Path2 (K.compPath p (K.reflPath b)) p := by
  let Λ := K.rightUnitorHorn p
  refine
    { simplex := K.face 2 1 (K.rightUnitorSimplex p)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.rightUnitorSimplex p) = (K.reflPath2 (K.reflPath b)).simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 1 (K.rightUnitorSimplex p))
          = K.face 1 0 (K.face 2 0 (K.rightUnitorSimplex p)) := by
              simpa using
                (K.face_face 1 (K.rightUnitorSimplex p)
                  (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 1 0 (K.reflPath2 (K.reflPath b)).simplex := by rw [h0]
      _ = (K.reflPath b).simplex := (K.reflPath2 (K.reflPath b)).face0
  · have h2 : K.face 2 2 (K.rightUnitorSimplex p) = (K.reflPath2 p).simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 1 (K.rightUnitorSimplex p))
          = K.face 1 1 (K.face 2 2 (K.rightUnitorSimplex p)) := by
              symm
              simpa using
                (K.face_face 1 (K.rightUnitorSimplex p)
                  (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.reflPath2 p).simplex := by rw [h2]
      _ = p.simplex := (K.reflPath2 p).face1
  · have h3 : K.face 2 3 (K.rightUnitorSimplex p) = (K.compTriangle p (K.reflPath b)).simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 1 (K.rightUnitorSimplex p))
          = K.face 1 1 (K.face 2 3 (K.rightUnitorSimplex p)) := by
              symm
              simpa using
                (K.face_face 1 (K.rightUnitorSimplex p)
                  (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 1 1 (K.compTriangle p (K.reflPath b)).simplex := by rw [h3]
      _ = (K.compPath p (K.reflPath b)).simplex := (K.compTriangle p (K.reflPath b)).face1

/-- The tetrahedron filled in the definition of the right unitor. -/
def KanComplex.rightUnitorTetrahedron (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath b)).toTriangle
      (K.rightUnitorPath2 p).toTriangle
      (K.reflPath2 p).toTriangle
      (K.compTriangle p (K.reflPath b)) := by
  let Λ := K.rightUnitorHorn p
  refine
    { simplex := K.rightUnitorSimplex p
      face0 := ?_
      face1 := rfl
      face2 := ?_
      face3 := ?_ }
  · simpa [KanComplex.rightUnitorSimplex, KanComplex.rightUnitorHorn, Λ] using
      (K.fill_spec Λ (i := 0) (by omega) (by omega))
  · simpa [KanComplex.rightUnitorSimplex, KanComplex.rightUnitorHorn, Λ] using
      (K.fill_spec Λ (i := 2) (by omega) (by omega))
  · simpa [KanComplex.rightUnitorSimplex, KanComplex.rightUnitorHorn, Λ] using
      (K.fill_spec Λ (i := 3) (by omega) (by omega))

/-- On a reflexive 1-cell, the left and right unitors are connected by the
common tetrahedral boundary once the source-degenerate face is identified with
the reflexive triangle. -/
private def KanComplex.reflUnitorsPath3 (K : KanComplex) (b : K.Obj) :
    K.Path3
      (K.leftUnitorPath2 (K.reflPath b))
      (K.rightUnitorPath2 (K.reflPath b)) := by
  let ωR :
      K.Tetrahedron
        (K.reflPath2 (K.reflPath b)).toTriangle
        (K.rightUnitorPath2 (K.reflPath b)).toTriangle
        (K.sourceDegenerateTriangle (K.reflPath b))
        (K.compTriangle (K.reflPath b) (K.reflPath b)) := by
    simpa [K.sourceDegenerateTriangle_refl_eq b] using
      (K.rightUnitorTetrahedron (K.reflPath b))
  exact K.tetrahedronPath3
    (K.leftUnitorTetrahedron (K.reflPath b))
    ωR

/-- Degenerating the chosen composition triangle along its middle face gives an
explicit tetrahedron whose outer boundary is the source-degenerate triangle,
the composition triangle, and the reflexive 2-cell on the left factor. -/
private def KanComplex.compTriangleDegenerateTetrahedron (K : KanComplex)
    {a b c : K.Obj} (p : K.PathSpace a b) (r : K.PathSpace b c) :
    K.Tetrahedron
      (K.sourceDegenerateTriangle r)
      (K.compTriangle p r)
      (K.compTriangle p r)
      (K.reflPath2 p).toTriangle := by
  let τ := K.compTriangle p r
  refine
    { simplex := K.degen 2 1 τ.simplex
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · calc
      K.face 2 0 (K.degen 2 1 τ.simplex)
          = K.degen 1 0 (K.face 1 0 τ.simplex) := by
              simpa using (K.face_degen_lt 1 τ.simplex
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.degen 1 0 r.simplex := by rw [τ.face0]
      _ = (K.sourceDegenerateTriangle r).simplex := rfl
  · simpa using (K.face_degen_eq 1 τ.simplex (i := 1) (by omega))
  · simpa using (K.face_degen_succ 1 τ.simplex (i := 1) (by omega))
  · calc
      K.face 2 3 (K.degen 2 1 τ.simplex)
          = K.degen 1 1 (K.face 1 2 τ.simplex) := by
              simpa using (K.face_degen_gt 1 τ.simplex
                (i := 3) (j := 1) (by omega) (by omega))
      _ = K.degen 1 1 p.simplex := by rw [τ.face2]
      _ = (K.reflPath2 p).toTriangle.simplex := rfl

/-- The horn filler used to define `whiskerRightTriangle` is itself a
boundary-aware tetrahedron whose final face is the symmetric 2-cell. -/
private def KanComplex.whiskerRightTriangleFillerTetrahedron (K : KanComplex)
    {a b c : K.Obj} {p q : K.PathSpace a b} (α : K.Path2 p q) (r : K.PathSpace b c) :
    K.Tetrahedron
      (K.sourceDegenerateTriangle r)
      (K.compTriangle p r)
      (K.whiskerRightTriangle α r)
      (K.symmPath2 α).toTriangle := by
  let αinv := K.symmPath2 α
  let Λ : Horn K.toSimplicialSet 2 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then (K.sourceDegenerateTriangle r).simplex
        else if h1 : i = 1 then (K.compTriangle p r).simplex
        else αinv.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) := by
          omega
        rcases hij_cases with h01 | h03 | h13
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using (K.compTriangle p r).face0.trans
            (K.sourceDegenerateTriangle r).face0.symm
        · rcases h03 with ⟨rfl, rfl⟩
          simpa using αinv.face0.trans (K.sourceDegenerateTriangle r).face2.symm
        · rcases h13 with ⟨rfl, rfl⟩
          simpa using αinv.face1.trans (K.compTriangle p r).face2.symm }
  refine
    { simplex := K.fill Λ
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · simpa using K.fill_spec Λ (i := 0) (by omega) (by omega)
  · simpa using K.fill_spec Λ (i := 1) (by omega) (by omega)
  · change K.face 2 2 (K.fill Λ) = (K.whiskerRightTriangle α r).simplex
    rfl
  · simpa using K.fill_spec Λ (i := 3) (by omega) (by omega)

/-- Auxiliary front bridge for triangle coherence: it keeps the left unitor as
both middle and second outer faces while normalizing the remaining front and
last faces to the degenerate ones needed by a `trans` filler. -/
private def KanComplex.triangleFrontBridgeTetrahedron (K : KanComplex)
    {b c : K.Obj} (q : K.PathSpace b c) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath c)).toTriangle
      (K.leftUnitorPath2 q).toTriangle
      (K.leftUnitorPath2 q).toTriangle
      (K.reflPath2 (K.compPath (K.reflPath b) q)).toTriangle :=
  K.tetrahedronComparisonTetrahedron
    (K.path2DegenerateTetrahedron (K.leftUnitorPath2 q))
    (K.path2DegenerateTetrahedron (K.leftUnitorPath2 q))
    (K.reflTriangleTetrahedron
      (K.sourceDegenerateTriangle (K.compPath (K.reflPath b) q)))

/-- Boundary-aware tetrahedron packaging the left side of triangle coherence:
associator followed by the whiskered left unitor, with the left-unitor front
made explicit. -/
private def KanComplex.triangleLeftBoundaryTetrahedron (K : KanComplex)
    {a b c : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c) :
    K.Tetrahedron
      (K.leftUnitorPath2 q).toTriangle
      (K.transPath2
        (K.associatorPath2 p (K.reflPath b) q)
        (K.whiskerLeftPath2 p (K.leftUnitorPath2 q))).toTriangle
      (K.compTriangle p q)
      (K.assocTriangle p (K.reflPath b) q) := by
  let σ := K.triangleFrontBridgeTetrahedron q
  let ω := K.transFillerTetrahedron
    (K.associatorPath2 p (K.reflPath b) q)
    (K.whiskerLeftPath2 p (K.leftUnitorPath2 q))
  let κ := K.whiskerLeftTetrahedron p (K.leftUnitorPath2 q)
  let θ := K.associatorTetrahedron p (K.reflPath b) q
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then σ.simplex
        else if h1 : i = 1 then ω.simplex
        else if h2 : i = 2 then κ.simplex
        else θ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω.face0.trans σ.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using κ.face0.trans σ.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using θ.face0.trans σ.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using κ.face1.trans ω.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using θ.face1.trans ω.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using θ.face2.trans κ.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = σ.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 σ.simplex := by rw [h0]
      _ = (K.leftUnitorPath2 q).toTriangle.simplex := σ.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω.simplex := by rw [h1]
      _ = (K.transPath2
            (K.associatorPath2 p (K.reflPath b) q)
            (K.whiskerLeftPath2 p (K.leftUnitorPath2 q))).toTriangle.simplex := ω.face2
  · have h2 : K.face 3 2 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h2]
      _ = (K.compTriangle p q).simplex := κ.face2
  · have h4 : K.face 3 4 (K.fill Λ) = θ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 θ.simplex := by rw [h4]
      _ = (K.assocTriangle p (K.reflPath b) q).simplex := θ.face3

/-- Boundary-aware tetrahedron that replaces the two source-degenerate side
faces of `interchangePrimeCoreTetrahedron` by the corresponding chosen
composition triangles, keeping the same front face `θ`. -/
private def KanComplex.interchangePrimeCoreLeftBoundaryTetrahedron (K : KanComplex)
    {a b c : K.Obj} {p q : K.PathSpace a b} (η : K.Path2 p q)
    {r s : K.PathSpace b c} (θ : K.Path2 r s) :
    K.Tetrahedron
      θ.toTriangle
      (K.whiskerLeftPath2 p θ).toTriangle
      (K.whiskerRightTriangle η s)
      (K.whiskerRightTriangle η r) := by
  let σ := K.path2DegenerateTetrahedron θ
  let ω := K.whiskerLeftTetrahedron p θ
  let ρ := K.whiskerRightTriangleFillerTetrahedron η s
  let κ := K.whiskerRightTriangleFillerTetrahedron η r
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then σ.simplex
        else if h1 : i = 1 then ω.simplex
        else if h3 : i = 3 then ρ.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω.face0.trans σ.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ρ.face0.trans σ.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans σ.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ρ.face1.trans ω.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ρ.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = σ.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 σ.simplex := by rw [h0]
      _ = θ.toTriangle.simplex := σ.face1
  · have h1 : K.face 3 1 (K.fill Λ) = ω.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω.simplex := by rw [h1]
      _ = (K.whiskerLeftPath2 p θ).toTriangle.simplex := ω.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ρ.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ρ.simplex := by rw [h3]
      _ = (K.whiskerRightTriangle η s).simplex := ρ.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h4]
      _ = (K.whiskerRightTriangle η r).simplex := κ.face2

/-- The raw `p`-side 2-cell extracted from `interchangePrimeCoreTetrahedron`
agrees with ordinary left whiskering by `p` up to a semantic 3-cell. -/
def KanComplex.interchangePrimeCoreLeftPath3 (K : KanComplex)
    {a b c : K.Obj} {p q : K.PathSpace a b} (η : K.Path2 p q)
    {r s : K.PathSpace b c} (θ : K.Path2 r s) :
    K.Path3
      (K.interchangePrimeCorePath2 η θ)
      (K.whiskerLeftPath2 p θ) :=
  K.tetrahedronPath3
    (K.interchangePrimeCoreTetrahedron η θ)
    (K.interchangePrimeCoreLeftBoundaryTetrahedron η θ)

/-- Alternative interchange: whisker left along `p`, then whisker right along
`s`. -/
def KanComplex.interchangePrimePath3 (K : KanComplex)
    {a b c : K.Obj} {p q : K.PathSpace a b} (η : K.Path2 p q)
    {r s : K.PathSpace b c} (θ : K.Path2 r s) :
    K.Path3
      (K.transPath2 (K.whiskerRightPath2 η r) (K.whiskerLeftPath2 q θ))
      (K.transPath2 (K.whiskerLeftPath2 p θ) (K.whiskerRightPath2 η s)) :=
  K.transPath3
    (K.interchangePrimeCoreSquarePath3 η θ)
    (K.transCongrLeftPath3 (K.interchangePrimeCoreLeftPath3 η θ)
      (K.whiskerRightPath2 η s))

/-- Degenerating the source-degenerate triangle along its middle face produces
the explicit tetrahedron needed to keep the front boundary fixed while
replacing the last face of the whiskering horn. -/
private def KanComplex.sourceDegenerateTriangleDegenerateTetrahedron (K : KanComplex)
    {b c : K.Obj} (r : K.PathSpace b c) :
    K.Tetrahedron
      (K.sourceDegenerateTriangle r)
      (K.sourceDegenerateTriangle r)
      (K.sourceDegenerateTriangle r)
      (K.reflPath2 (K.reflPath b)).toTriangle := by
  let τ := K.sourceDegenerateTriangle r
  refine
    { simplex := K.degen 2 1 τ.simplex
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · calc
      K.face 2 0 (K.degen 2 1 τ.simplex)
          = K.degen 1 0 (K.face 1 0 τ.simplex) := by
              simpa using (K.face_degen_lt 1 τ.simplex
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.degen 1 0 r.simplex := by rw [τ.face0]
      _ = τ.simplex := rfl
  · simpa using (K.face_degen_eq 1 τ.simplex (i := 1) (by omega))
  · simpa using (K.face_degen_succ 1 τ.simplex (i := 1) (by omega))
  · calc
      K.face 2 3 (K.degen 2 1 τ.simplex)
          = K.degen 1 1 (K.face 1 2 τ.simplex) := by
              simpa using (K.face_degen_gt 1 τ.simplex
                (i := 3) (j := 1) (by omega) (by omega))
      _ = K.degen 1 1 (K.reflPath b).simplex := by rw [τ.face2]
      _ = (K.reflPath2 (K.reflPath b)).toTriangle.simplex := rfl

/-- A normalized boundary tetrahedron for right whiskering whose last face is the
original 2-cell rather than its symmetry. -/
private def KanComplex.whiskerRightTriangleBoundaryTetrahedron (K : KanComplex)
    {a b c : K.Obj} {p q : K.PathSpace a b} (α : K.Path2 p q) (r : K.PathSpace b c) :
    K.Tetrahedron
      (K.sourceDegenerateTriangle r)
      (K.whiskerRightTriangle α r)
      (K.compTriangle p r)
      α.toTriangle := by
  let ρ := K.sourceDegenerateTriangleDegenerateTetrahedron r
  let ω₁ := K.whiskerRightTriangleFillerTetrahedron α r
  let ω₂ := K.compTriangleDegenerateTetrahedron p r
  let κ := K.symmTetrahedron α
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ρ.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h2 : i = 2 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ρ.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ρ.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ρ.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using κ.face2.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ρ.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ρ.simplex := by rw [h0]
      _ = (K.sourceDegenerateTriangle r).simplex := ρ.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₁.simplex := by rw [h1]
      _ = (K.whiskerRightTriangle α r).simplex := ω₁.face2
  · have h2 : K.face 3 2 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h2]
      _ = (K.compTriangle p r).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 κ.simplex := by rw [h4]
      _ = α.toTriangle.simplex := κ.face3

/-- The raw tetrahedron filled to define `assocTriangle`. -/
private def KanComplex.assocTriangleFillerTetrahedron (K : KanComplex)
    {a b c d : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c) (r : K.PathSpace c d) :
    K.Tetrahedron
      (K.compTriangle q r)
      (K.compTriangle (K.compPath p q) r)
      (K.assocTriangle p q r)
      (K.compTriangle p q) := by
  let Λ : Horn K.toSimplicialSet 2 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then (K.compTriangle q r).simplex
        else if h1 : i = 1 then (K.compTriangle (K.compPath p q) r).simplex
        else (K.compTriangle p q).simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) := by
          omega
        rcases hij_cases with h01 | h03 | h13
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using (K.compTriangle (K.compPath p q) r).face0.trans
            (K.compTriangle q r).face0.symm
        · rcases h03 with ⟨rfl, rfl⟩
          simpa using (K.compTriangle p q).face0.trans
            (K.compTriangle q r).face2.symm
        · rcases h13 with ⟨rfl, rfl⟩
          simpa using (K.compTriangle p q).face1.trans
            (K.compTriangle (K.compPath p q) r).face2.symm }
  refine
    { simplex := K.fill Λ
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · simpa using K.fill_spec Λ (i := 0) (by omega) (by omega)
  · simpa using K.fill_spec Λ (i := 1) (by omega) (by omega)
  · change K.face 2 2 (K.fill Λ) = (K.assocTriangle p q r).simplex
    rfl
  · simpa using K.fill_spec Λ (i := 3) (by omega) (by omega)

/-- Composing `q` on the left with the chosen composition triangle for `(r, s)`
produces the triangle whose outer edges are `q · r` and `s`. -/
private def KanComplex.whiskerLeftCompHorn (K : KanComplex)
    {b c d e : K.Obj} (q : K.PathSpace b c) (r : K.PathSpace c d)
    (s : K.PathSpace d e) :
    Horn K.toSimplicialSet 2 1 :=
  { missing_le := by omega
    facet := fun i _ =>
      if h0 : i = 0 then (K.compTriangle r s).simplex
      else if h2 : i = 2 then (K.compTriangle q (K.compPath r s)).simplex
      else (K.compTriangle q r).simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
        omega
      rcases hij_cases with h02 | h03 | h23
      · rcases h02 with ⟨rfl, rfl⟩
        simpa using (K.compTriangle q (K.compPath r s)).face0.trans
          (K.compTriangle r s).face1.symm
      · rcases h03 with ⟨rfl, rfl⟩
        simpa using (K.compTriangle q r).face0.trans
          (K.compTriangle r s).face2.symm
      · rcases h23 with ⟨rfl, rfl⟩
        simpa using (K.compTriangle q r).face2.trans
          (K.compTriangle q (K.compPath r s)).face2.symm }

/-- The left-whiskered composition triangle whose edges are `q · r`,
`q · (r · s)`, and `s`. -/
private def KanComplex.whiskerLeftCompTriangle (K : KanComplex)
    {b c d e : K.Obj} (q : K.PathSpace b c) (r : K.PathSpace c d)
    (s : K.PathSpace d e) :
    K.Triangle
      (K.compPath q r)
      (K.compPath q (K.compPath r s))
      s := by
  let Λ := K.whiskerLeftCompHorn q r s
  refine
    { simplex := K.face 2 1 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.fill Λ) = (K.compTriangle r s).simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 1 (K.fill Λ))
          = K.face 1 0 (K.face 2 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 1 (K.fill Λ) (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 1 0 (K.compTriangle r s).simplex := by rw [h0]
      _ = s.simplex := (K.compTriangle r s).face0
  · have h2 : K.face 2 2 (K.fill Λ) = (K.compTriangle q (K.compPath r s)).simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 1 (K.fill Λ))
          = K.face 1 1 (K.face 2 2 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 1 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.compTriangle q (K.compPath r s)).simplex := by rw [h2]
      _ = (K.compPath q (K.compPath r s)).simplex := (K.compTriangle q (K.compPath r s)).face1
  · have h3 : K.face 2 3 (K.fill Λ) = (K.compTriangle q r).simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 1 (K.fill Λ))
          = K.face 1 1 (K.face 2 3 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 1 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 1 1 (K.compTriangle q r).simplex := by rw [h3]
      _ = (K.compPath q r).simplex := (K.compTriangle q r).face1

/-- The raw tetrahedron filled to define `whiskerLeftCompTriangle`. -/
private def KanComplex.whiskerLeftCompTriangleFillerTetrahedron (K : KanComplex)
    {b c d e : K.Obj} (q : K.PathSpace b c) (r : K.PathSpace c d)
    (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.compTriangle r s)
      (K.whiskerLeftCompTriangle q r s)
      (K.compTriangle q (K.compPath r s))
      (K.compTriangle q r) := by
  let Λ := K.whiskerLeftCompHorn q r s
  refine
    { simplex := K.fill Λ
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · simpa using K.fill_spec Λ (i := 0) (by omega) (by omega)
  · change K.face 2 1 (K.fill Λ) = (K.whiskerLeftCompTriangle q r s).simplex
    rfl
  · simpa using K.fill_spec Λ (i := 2) (by omega) (by omega)
  · simpa using K.fill_spec Λ (i := 3) (by omega) (by omega)

/-- The right-back triangle for pentagon coherence: it keeps the left edge `p`
fixed, uses the fully right-associated tail `q · (r · s)` as the outer edge,
and lands at the fully left-associated composite `((p · q) · r) · s`. -/
private def KanComplex.pentagonRightBackHorn (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    Horn K.toSimplicialSet 2 2 :=
  { missing_le := by omega
    facet := fun i _ =>
      if h0 : i = 0 then (K.compTriangle q (K.compPath r s)).simplex
      else if h1 : i = 1 then (K.assocTriangle (K.compPath p q) r s).simplex
      else (K.compTriangle p q).simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) := by
        omega
      rcases hij_cases with h01 | h03 | h13
      · rcases h01 with ⟨rfl, rfl⟩
        simpa using (K.assocTriangle (K.compPath p q) r s).face0.trans
          (K.compTriangle q (K.compPath r s)).face0.symm
      · rcases h03 with ⟨rfl, rfl⟩
        simpa using (K.compTriangle p q).face0.trans
          (K.compTriangle q (K.compPath r s)).face2.symm
      · rcases h13 with ⟨rfl, rfl⟩
        simpa using (K.compTriangle p q).face1.trans
          (K.assocTriangle (K.compPath p q) r s).face2.symm }

/-- The triangle on the back face of the pentagon comparison: it compares the
fully right-associated tail `q · (r · s)` against the fully left-associated
composite `((p · q) · r) · s` while keeping the left edge `p` explicit. -/
def KanComplex.pentagonRightBackTriangle (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Triangle
      p
      (K.compPath (K.compPath (K.compPath p q) r) s)
      (K.compPath q (K.compPath r s)) := by
  let Λ := K.pentagonRightBackHorn p q r s
  refine
    { simplex := K.face 2 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.fill Λ) = (K.compTriangle q (K.compPath r s)).simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 2 (K.fill Λ))
          = K.face 1 1 (K.face 2 0 (K.fill Λ)) := by
              simpa using (K.face_face 1 (K.fill Λ)
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.compTriangle q (K.compPath r s)).simplex := by rw [h0]
      _ = (K.compPath q (K.compPath r s)).simplex := (K.compTriangle q (K.compPath r s)).face1
  · have h1 : K.face 2 1 (K.fill Λ) = (K.assocTriangle (K.compPath p q) r s).simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 2 (K.fill Λ))
          = K.face 1 1 (K.face 2 1 (K.fill Λ)) := by
              simpa using (K.face_face 1 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.assocTriangle (K.compPath p q) r s).simplex := by rw [h1]
      _ = (K.compPath (K.compPath (K.compPath p q) r) s).simplex :=
        (K.assocTriangle (K.compPath p q) r s).face1
  · have h3 : K.face 2 3 (K.fill Λ) = (K.compTriangle p q).simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 2 (K.fill Λ))
          = K.face 1 2 (K.face 2 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 1 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 1 2 (K.compTriangle p q).simplex := by rw [h3]
      _ = p.simplex := (K.compTriangle p q).face2

/-- The raw tetrahedron filled to define `pentagonRightBackTriangle`. -/
private def KanComplex.pentagonRightBackFillerTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.compTriangle q (K.compPath r s))
      (K.assocTriangle (K.compPath p q) r s)
      (K.pentagonRightBackTriangle p q r s)
      (K.compTriangle p q) := by
  let Λ := K.pentagonRightBackHorn p q r s
  refine
    { simplex := K.fill Λ
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · simpa using K.fill_spec Λ (i := 0) (by omega) (by omega)
  · simpa using K.fill_spec Λ (i := 1) (by omega) (by omega)
  · change K.face 2 2 (K.fill Λ) = (K.pentagonRightBackTriangle p q r s).simplex
    rfl
  · simpa using K.fill_spec Λ (i := 3) (by omega) (by omega)

private def KanComplex.pentagonInnerBackHorn (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    Horn K.toSimplicialSet 2 2 :=
  { missing_le := by omega
    facet := fun i _ =>
      if h0 : i = 0 then (K.whiskerLeftCompTriangle q r s).simplex
      else if h1 : i = 1 then
        (K.whiskerRightTriangle (K.associatorPath2 p q r) s).simplex
      else (K.compTriangle p (K.compPath q r)).simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases : (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 1 ∧ j = 3) := by
        omega
      rcases hij_cases with h01 | h03 | h13
      · rcases h01 with ⟨rfl, rfl⟩
        simpa using
          (K.whiskerRightTriangle (K.associatorPath2 p q r) s).face0.trans
            (K.whiskerLeftCompTriangle q r s).face0.symm
      · rcases h03 with ⟨rfl, rfl⟩
        simpa using
          (K.compTriangle p (K.compPath q r)).face0.trans
            (K.whiskerLeftCompTriangle q r s).face2.symm
      · rcases h13 with ⟨rfl, rfl⟩
        simpa using
          (K.compTriangle p (K.compPath q r)).face1.trans
            (K.whiskerRightTriangle (K.associatorPath2 p q r) s).face2.symm }

/-- Auxiliary back triangle for the corrected pentagon step-1 geometry. It has the
same outer boundary as `pentagonRightBackTriangle`, but is obtained directly from
the whiskered front and right faces. -/
def KanComplex.pentagonInnerBackTriangle (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Triangle
      p
      (K.compPath (K.compPath (K.compPath p q) r) s)
      (K.compPath q (K.compPath r s)) := by
  let Λ := K.pentagonInnerBackHorn p q r s
  refine
    { simplex := K.face 2 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.fill Λ) = (K.whiskerLeftCompTriangle q r s).simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 2 (K.fill Λ))
          = K.face 1 1 (K.face 2 0 (K.fill Λ)) := by
              simpa using (K.face_face 1 (K.fill Λ)
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.whiskerLeftCompTriangle q r s).simplex := by rw [h0]
      _ = (K.compPath q (K.compPath r s)).simplex := (K.whiskerLeftCompTriangle q r s).face1
  · have h1 :
      K.face 2 1 (K.fill Λ) =
        (K.whiskerRightTriangle (K.associatorPath2 p q r) s).simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 2 (K.fill Λ))
          = K.face 1 1 (K.face 2 1 (K.fill Λ)) := by
              simpa using (K.face_face 1 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.whiskerRightTriangle (K.associatorPath2 p q r) s).simplex := by
            rw [h1]
      _ = (K.compPath (K.compPath (K.compPath p q) r) s).simplex :=
            (K.whiskerRightTriangle (K.associatorPath2 p q r) s).face1
  · have h3 : K.face 2 3 (K.fill Λ) = (K.compTriangle p (K.compPath q r)).simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 2 (K.fill Λ))
          = K.face 1 2 (K.face 2 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 1 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 1 2 (K.compTriangle p (K.compPath q r)).simplex := by rw [h3]
      _ = p.simplex := (K.compTriangle p (K.compPath q r)).face2

/-- The raw tetrahedron filled to define `pentagonInnerBackTriangle`. -/
private def KanComplex.pentagonInnerBackFillerTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.whiskerLeftCompTriangle q r s)
      (K.whiskerRightTriangle (K.associatorPath2 p q r) s)
      (K.pentagonInnerBackTriangle p q r s)
      (K.compTriangle p (K.compPath q r)) := by
  let Λ := K.pentagonInnerBackHorn p q r s
  refine
    { simplex := K.fill Λ
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · simpa using K.fill_spec Λ (i := 0) (by omega) (by omega)
  · simpa using K.fill_spec Λ (i := 1) (by omega) (by omega)
  · change K.face 2 2 (K.fill Λ) = (K.pentagonInnerBackTriangle p q r s).simplex
    rfl
  · simpa using K.fill_spec Λ (i := 3) (by omega) (by omega)

/-- Comparison tetrahedron between the directly whiskered back triangle and the
canonical right-back triangle already used in the pentagon route. -/
def KanComplex.pentagonInnerBackComparisonTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s)).toTriangle
      (K.pentagonRightBackTriangle p q r s)
      (K.pentagonInnerBackTriangle p q r s) :=
  K.triangleComparisonTetrahedron
    (K.pentagonInnerBackTriangle p q r s)
    (K.pentagonRightBackTriangle p q r s)

/-- Boundary-aware back-face comparison for the pentagon law: it packages the
left-side associator `((p · q), r, s)` against the triangle on the right route
whose outer edge is `q · (r · s)`. -/
def KanComplex.pentagonBackComparisonTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle
      (K.associatorPath2 (K.compPath p q) r s).toTriangle
      (K.assocTriangle p q (K.compPath r s))
      (K.pentagonRightBackTriangle p q r s) := by
  let ε := K.reflTriangleTetrahedron (K.compTriangle q (K.compPath r s))
  let ω₁ := K.associatorTetrahedron (K.compPath p q) r s
  let ω₂ := K.assocTriangleFillerTetrahedron p q (K.compPath r s)
  let κ := K.pentagonRightBackFillerTetrahedron p q r s
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h3 : i = 3 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ε.simplex := by rw [h0]
      _ = (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle.simplex := ε.face1
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h1]
      _ = (K.associatorPath2 (K.compPath p q) r s).toTriangle.simplex := ω₁.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h3]
      _ = (K.assocTriangle p q (K.compPath r s)).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h4]
      _ = (K.pentagonRightBackTriangle p q r s).simplex := κ.face2

/-- Front bridge for pentagon coherence: it compares the reflexive front face on
`q · (r · s)` with the actual associator `(q, r, s)`, while exposing the
triangle comparison between the two outer triangles as the last face. -/
private def KanComplex.pentagonFrontBridgeTetrahedron (K : KanComplex)
    {b c d e : K.Obj} (q : K.PathSpace b c) (r : K.PathSpace c d)
    (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath e)).toTriangle
      (K.associatorPath2 q r s).toTriangle
      (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle
      (K.trianglePath2
        (K.compTriangle q (K.compPath r s))
        (K.assocTriangle q r s)).toTriangle :=
  K.tetrahedronComparisonTetrahedron
    (K.reflTriangleTetrahedron (K.compTriangle q (K.compPath r s)))
    (K.associatorTetrahedron q r s)
    (K.triangleComparisonTetrahedron
      (K.compTriangle q (K.compPath r s))
      (K.assocTriangle q r s))

/-- The front 2-cell obtained by comparing the directly whiskered composition
triangle against the ordinary composition triangle on `(q · r, s)`. -/
private def KanComplex.pentagonWhiskerFrontPath2 (K : KanComplex)
    {b c d e : K.Obj} (q : K.PathSpace b c) (r : K.PathSpace c d)
    (s : K.PathSpace d e) :
    K.Path2
      (K.compPath q (K.compPath r s))
      (K.compPath (K.compPath q r) s) :=
  K.trianglePath2
    (K.whiskerLeftCompTriangle q r s)
    (K.compTriangle (K.compPath q r) s)


/-- A front-boundary tetrahedron comparing the whiskered front pentagon face with
the reverse triangle comparison attached to the associator on `(q, r, s)`. -/
private def KanComplex.pentagonFrontComparisonTetrahedron (K : KanComplex)
    {b c d e : K.Obj} (q : K.PathSpace b c) (r : K.PathSpace c d)
    (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 s).toTriangle
      (K.trianglePath2
        (K.compTriangle q (K.compPath r s))
        (K.assocTriangle q r s)).toTriangle
      (K.compTriangle (K.compPath q r) s)
      (K.whiskerLeftCompTriangle q r s) := by
  let ε := K.reflTriangleTetrahedron (K.compTriangle r s)
  let ω₂ := K.triangleComparisonTetrahedron
    (K.compTriangle q (K.compPath r s))
    (K.assocTriangle q r s)
  let ω₁ := K.assocTriangleFillerTetrahedron q r s
  let ρ := K.whiskerLeftCompTriangleFillerTetrahedron q r s
  let Λ : Horn K.toSimplicialSet 3 1 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h2 : i = 2 then ω₂.simplex
        else if h3 : i = 3 then ω₁.simplex
        else ρ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h02 | hrest
        · rcases h02 with ⟨rfl, rfl⟩
          simpa using ω₂.face0.trans ε.face1.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₁.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using ρ.face0.trans ε.face3.symm
            · rcases hrest with h23 | hrest
              · rcases h23 with ⟨rfl, rfl⟩
                simpa using ω₁.face2.trans ω₂.face2.symm
              · rcases hrest with h24 | h34
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using ρ.face2.trans ω₂.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using ρ.face3.trans ω₁.face3.symm }
  refine
    { simplex := K.face 3 1 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 1 (K.fill Λ))
          = K.face 2 0 (K.face 3 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 2 0 ε.simplex := by rw [h0]
      _ = (K.reflPath2 s).toTriangle.simplex := ε.face0
  · have h2 : K.face 3 2 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 2 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₂.simplex := by rw [h2]
      _ =
        (K.trianglePath2
          (K.compTriangle q (K.compPath r s))
          (K.assocTriangle q r s)).toTriangle.simplex := ω₂.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h3]
      _ = (K.compTriangle (K.compPath q r) s).simplex := ω₁.face1
  · have h4 : K.face 3 4 (K.fill Λ) = ρ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 3) (by omega) (by omega))
      _ = K.face 2 1 ρ.simplex := by rw [h4]
      _ = (K.whiskerLeftCompTriangle q r s).simplex := ρ.face1

/-- The directly whiskered front pentagon 2-cell is 3-homotopic to the reverse
front comparison built from the chosen associator triangle. -/
private def KanComplex.pentagonWhiskerFrontComparisonPath3 (K : KanComplex)
    {b c d e : K.Obj} (q : K.PathSpace b c) (r : K.PathSpace c d)
    (s : K.PathSpace d e) :
    K.Path3
      (K.pentagonWhiskerFrontPath2 q r s)
      (K.trianglePath2
        (K.compTriangle q (K.compPath r s))
        (K.assocTriangle q r s)) :=
  K.tetrahedronPath3
    (K.triangleComparisonTetrahedron
      (K.whiskerLeftCompTriangle q r s)
      (K.compTriangle (K.compPath q r) s))
    (K.pentagonFrontComparisonTetrahedron q r s)

/-- Right-side boundary tetrahedron for the triangle law. -/
private def KanComplex.triangleRightBoundaryTetrahedron (K : KanComplex)
    {a b c : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c) :
    K.Tetrahedron
      (K.compTriangle (K.reflPath b) q)
      (K.whiskerRightTriangle (K.rightUnitorPath2 p) q)
      (K.assocTriangle p (K.reflPath b) q)
      (K.reflPath2 p).toTriangle := by
  let ε := K.compTriangleDegenerateTetrahedron (K.reflPath b) q
  let ω₁ := K.whiskerRightTriangleBoundaryTetrahedron (K.rightUnitorPath2 p) q
  let ω₂ := K.assocTriangleFillerTetrahedron p (K.reflPath b) q
  let κ := K.rightUnitorTetrahedron p
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h3 : i = 3 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ε.simplex := by rw [h0]
      _ = (K.compTriangle (K.reflPath b) q).simplex := ε.face1
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h1]
      _ = (K.whiskerRightTriangle (K.rightUnitorPath2 p) q).simplex := ω₁.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h3]
      _ = (K.assocTriangle p (K.reflPath b) q).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h4]
      _ = (K.reflPath2 p).toTriangle.simplex := κ.face2

/-- Boundary-aware tetrahedron whose middle face is the right-unitor route in the
triangle law. -/
private def KanComplex.triangleBoundaryTetrahedron (K : KanComplex)
    {a b c : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c) :
    K.Tetrahedron
      (K.leftUnitorPath2 q).toTriangle
      (K.whiskerRightPath2 (K.rightUnitorPath2 p) q).toTriangle
      (K.compTriangle p q)
      (K.assocTriangle p (K.reflPath b) q) := by
  let ε := K.leftUnitorTetrahedron q
  let ω₁ := K.whiskerRightTetrahedron (K.rightUnitorPath2 p) q
  let ω₂ := K.compTriangleDegenerateTetrahedron p q
  let κ := K.triangleRightBoundaryTetrahedron p q
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h3 : i = 3 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ε.simplex := by rw [h0]
      _ = (K.leftUnitorPath2 q).toTriangle.simplex := ε.face1
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h1]
      _ = (K.whiskerRightPath2 (K.rightUnitorPath2 p) q).toTriangle.simplex := ω₁.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h3]
      _ = (K.compTriangle p q).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h4]
      _ = (K.assocTriangle p (K.reflPath b) q).simplex := κ.face2

/-- Boundary-aware tetrahedron whose second outer face is the right-unitor route
and whose last face is the associator in the triangle law. -/
private def KanComplex.trianglePath3Tetrahedron (K : KanComplex)
    {a b c : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath c)).toTriangle
      (K.whiskerLeftPath2 p (K.leftUnitorPath2 q)).toTriangle
      (K.whiskerRightPath2 (K.rightUnitorPath2 p) q).toTriangle
      (K.associatorPath2 p (K.reflPath b) q).toTriangle :=
  K.tetrahedronComparisonTetrahedron
    (p12 := K.compPath (K.reflPath b) q)
    (p13 := q)
    (p021 := K.compPath (K.compPath p (K.reflPath b)) q)
    (p022 := K.compPath p (K.compPath (K.reflPath b) q))
    (p03 := K.compPath p q)
    (γ := K.leftUnitorPath2 q)
    (α := K.whiskerRightPath2 (K.rightUnitorPath2 p) q)
    (β := K.whiskerLeftPath2 p (K.leftUnitorPath2 q))
    (δ := K.associatorPath2 p (K.reflPath b) q)
    (τ2 := K.compTriangle p q)
    (τ31 := K.assocTriangle p (K.reflPath b) q)
    (τ32 := K.compTriangle p (K.compPath (K.reflPath b) q))
    (K.triangleBoundaryTetrahedron p q)
    (K.whiskerLeftTetrahedron p (K.leftUnitorPath2 q))
    (K.associatorTetrahedron p (K.reflPath b) q)

/-- Triangle coherence for semantic path composition. -/
def KanComplex.trianglePath3 (K : KanComplex) {a b c : K.Obj}
    (p : K.PathSpace a b) (q : K.PathSpace b c) :
    K.Path3
      (K.transPath2
        (K.associatorPath2 p (K.reflPath b) q)
        (K.whiskerLeftPath2 p (K.leftUnitorPath2 q)))
      (K.whiskerRightPath2 (K.rightUnitorPath2 p) q) := by
  let α := K.associatorPath2 p (K.reflPath b) q
  let β := K.whiskerLeftPath2 p (K.leftUnitorPath2 q)
  exact K.tetrahedronFace2Path3
    (K.reflPath3 α)
    (K.transFillerTetrahedron α β)
    (K.trianglePath3Tetrahedron p q)

/-- Front bridge for the right-unitor-on-composites coherence: keep the
right unitor visible on both front faces while normalizing the remaining outer
faces to the degenerate ones expected by a `trans` filler. -/
private def KanComplex.rightUnitorFrontBridgeTetrahedron (K : KanComplex)
    {b c : K.Obj} (q : K.PathSpace b c) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath c)).toTriangle
      (K.rightUnitorPath2 q).toTriangle
      (K.rightUnitorPath2 q).toTriangle
      (K.reflPath2 (K.compPath q (K.reflPath c))).toTriangle :=
  K.tetrahedronComparisonTetrahedron
    (K.path2DegenerateTetrahedron (K.rightUnitorPath2 q))
    (K.path2DegenerateTetrahedron (K.rightUnitorPath2 q))
    (K.reflTriangleTetrahedron
      (K.sourceDegenerateTriangle (K.compPath q (K.reflPath c))))

/-- Boundary-aware tetrahedron packaging the left-hand route for the coherence
`assoc ; (p ◁ ρ_q) ~ ρ_(p·q)`. -/
private def KanComplex.rightUnitorLeftBoundaryTetrahedron (K : KanComplex)
    {a b c : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c) :
    K.Tetrahedron
      (K.rightUnitorPath2 q).toTriangle
      (K.transPath2
        (K.associatorPath2 p q (K.reflPath c))
        (K.whiskerLeftPath2 p (K.rightUnitorPath2 q))).toTriangle
      (K.compTriangle p q)
      (K.assocTriangle p q (K.reflPath c)) := by
  let σ := K.rightUnitorFrontBridgeTetrahedron q
  let ω := K.transFillerTetrahedron
    (K.associatorPath2 p q (K.reflPath c))
    (K.whiskerLeftPath2 p (K.rightUnitorPath2 q))
  let κ := K.whiskerLeftTetrahedron p (K.rightUnitorPath2 q)
  let θ := K.associatorTetrahedron p q (K.reflPath c)
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then σ.simplex
        else if h1 : i = 1 then ω.simplex
        else if h2 : i = 2 then κ.simplex
        else θ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω.face0.trans σ.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using κ.face0.trans σ.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using θ.face0.trans σ.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using κ.face1.trans ω.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using θ.face1.trans ω.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using θ.face2.trans κ.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = σ.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 σ.simplex := by rw [h0]
      _ = (K.rightUnitorPath2 q).toTriangle.simplex := σ.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω.simplex := by rw [h1]
      _ = (K.transPath2
            (K.associatorPath2 p q (K.reflPath c))
            (K.whiskerLeftPath2 p (K.rightUnitorPath2 q))).toTriangle.simplex := ω.face2
  · have h2 : K.face 3 2 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h2]
      _ = (K.compTriangle p q).simplex := κ.face2
  · have h4 : K.face 3 4 (K.fill Λ) = θ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 θ.simplex := by rw [h4]
      _ = (K.assocTriangle p q (K.reflPath c)).simplex := θ.face3

/-- Boundary-aware tetrahedron whose middle face is the normalized
right-unitor-on-composites route. -/
private def KanComplex.rightUnitorBoundaryTetrahedron (K : KanComplex)
    {a b c : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c) :
    K.Tetrahedron
      (K.rightUnitorPath2 q).toTriangle
      (K.rightUnitorPath2 (K.compPath p q)).toTriangle
      (K.compTriangle p q)
      (K.assocTriangle p q (K.reflPath c)) := by
  let ε := K.rightUnitorTetrahedron q
  let ω₁ := K.rightUnitorTetrahedron (K.compPath p q)
  let ω₂ := K.reflTriangleTetrahedron (K.compTriangle p q)
  let κ := K.assocTriangleFillerTetrahedron p q (K.reflPath c)
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h3 : i = 3 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ε.simplex := by rw [h0]
      _ = (K.rightUnitorPath2 q).toTriangle.simplex := ε.face1
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h1]
      _ = (K.rightUnitorPath2 (K.compPath p q)).toTriangle.simplex := ω₁.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h3]
      _ = (K.compTriangle p q).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h4]
      _ = (K.assocTriangle p q (K.reflPath c)).simplex := κ.face2

/-- Right unitor on a composite decomposes as associator followed by left
whiskering of the right unitor. -/
def KanComplex.rightUnitorCompPath3 (K : KanComplex) {a b c : K.Obj}
    (p : K.PathSpace a b) (q : K.PathSpace b c) :
    K.Path3
      (K.transPath2
        (K.associatorPath2 p q (K.reflPath c))
        (K.whiskerLeftPath2 p (K.rightUnitorPath2 q)))
      (K.rightUnitorPath2 (K.compPath p q)) :=
  K.tetrahedronPath3
    (K.rightUnitorLeftBoundaryTetrahedron p q)
    (K.rightUnitorBoundaryTetrahedron p q)

/-- The reflexive 2-cell on `p` is connected to its chosen symmetry by a
normalized tetrahedron. -/
private def KanComplex.symmReflPath2BridgeTetrahedron (K : KanComplex)
    {a b : K.Obj} (p : K.PathSpace a b) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath b)).toTriangle
      (K.reflPath2 p).toTriangle
      (K.symmPath2 (K.reflPath2 p)).toTriangle
      (K.reflPath2 p).toTriangle :=
  (K.tetrahedronPath3
    (K.symmTetrahedron (K.reflPath2 p))
    (K.reflTriangleTetrahedron (K.reflPath2 p).toTriangle)).toTetrahedron

/-- First auxiliary boundary replacement for `whiskerRightRefl`: keep the
source-degenerate front face and the composition triangle fixed, but replace
the back face `symm (refl p)` by `refl p`. -/
private def KanComplex.whiskerRightReflAuxTetrahedron (K : KanComplex)
    {a b c : K.Obj} (p : K.PathSpace a b) (r : K.PathSpace b c) :
    K.Tetrahedron
      (K.sourceDegenerateTriangle r)
      (K.compTriangle p r)
      (K.whiskerRightTriangle (K.reflPath2 p) r)
      (K.reflPath2 p).toTriangle := by
  let u := K.sourceDegenerateTriangle r
  let τ := K.compTriangle p r
  let ω₁ := K.compTriangleDegenerateTetrahedron p r
  let ω₂ := K.whiskerRightTriangleFillerTetrahedron (K.reflPath2 p) r
  let ρ := K.sourceDegenerateTriangleDegenerateTetrahedron r
  let κ := K.symmReflPath2BridgeTetrahedron p
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ρ.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h2 : i = 2 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ρ.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ρ.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ρ.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using κ.face2.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ρ.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ρ.simplex := by rw [h0]
      _ = u.simplex := ρ.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₁.simplex := by rw [h1]
      _ = τ.simplex := ω₁.face2
  · have h2 : K.face 3 2 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h2]
      _ = (K.whiskerRightTriangle (K.reflPath2 p) r).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 κ.simplex := by rw [h4]
      _ = (K.reflPath2 p).toTriangle.simplex := κ.face3

/-- Second auxiliary boundary replacement for `whiskerRightRefl`: promote the
previous correction to the exact tetrahedron needed as the extra boundary face
in the 4-simplex comparison between the whiskering tetrahedron and the
reflexive tetrahedron on the composite. -/
private def KanComplex.whiskerRightReflBoundaryTetrahedron (K : KanComplex)
    {a b c : K.Obj} (p : K.PathSpace a b) (r : K.PathSpace b c) :
    K.Tetrahedron
      (K.reflPath2 r).toTriangle
      (K.reflPath2 (K.compPath p r)).toTriangle
      (K.compTriangle p r)
      (K.whiskerRightTriangle (K.reflPath2 p) r) := by
  let u := K.sourceDegenerateTriangle r
  let τ := K.compTriangle p r
  let ε := K.reflTriangleTetrahedron u
  let ω₁ := K.compTriangleDegenerateTetrahedron p r
  let ω₂ := K.whiskerRightReflAuxTetrahedron p r
  let ρ := K.reflTriangleTetrahedron τ
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ρ.simplex
        else if h3 : i = 3 then ω₁.simplex
        else ω₂.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ρ.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₁.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using ω₂.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ω₁.face1.trans ρ.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using ω₂.face1.trans ρ.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using ω₂.face3.trans ω₁.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ε.simplex := by rw [h0]
      _ = (K.reflPath2 r).toTriangle.simplex := ε.face1
  · have h1 : K.face 3 1 (K.fill Λ) = ρ.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ρ.simplex := by rw [h1]
      _ = (K.reflPath2 (K.compPath p r)).toTriangle.simplex := ρ.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₁.simplex := by rw [h3]
      _ = τ.simplex := ω₁.face2
  · have h4 : K.face 3 4 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h4]
      _ = (K.whiskerRightTriangle (K.reflPath2 p) r).simplex := ω₂.face2

/-- Right whiskering preserves reflexive semantic 2-cells up to a semantic
3-cell. The proof replaces the non-normalized boundary face coming from
`whiskerRightTriangle` by an explicit reflexive face and then applies the
existing 4-simplex comparison machinery. -/
def KanComplex.whiskerRightReflPath3 (K : KanComplex) {a b c : K.Obj}
    (p : K.PathSpace a b) (r : K.PathSpace b c) :
    K.Path3
      (K.whiskerRightPath2 (K.reflPath2 p) r)
      (K.reflPath2 (K.compPath p r)) :=
  (K.tetrahedronComparisonTetrahedron
    (K.whiskerRightTetrahedron (K.reflPath2 p) r)
    (K.reflTriangleTetrahedron (K.compTriangle p r))
    (K.whiskerRightReflBoundaryTetrahedron p r)).toPath3

/-- Auxiliary tetrahedron for symmetry of triangle comparisons: it fixes the two
outer triangles and replaces the front reflexive face by its chosen symmetry. -/
private def KanComplex.trianglePath2SymmAuxTetrahedron (K : KanComplex)
    {a b c : K.Obj} {p : K.PathSpace a b} {m n : K.PathSpace a c}
    {q : K.PathSpace b c} (τ₁ : K.Triangle p m q) (τ₂ : K.Triangle p n q) :
    K.Tetrahedron
      (K.symmPath2 (K.reflPath2 q)).toTriangle
      (K.symmPath2 (K.trianglePath2 τ₁ τ₂)).toTriangle
      τ₁
      τ₂ := by
  let σ := K.symmTetrahedron (K.reflPath2 q)
  let ω := K.symmTetrahedron (K.trianglePath2 τ₁ τ₂)
  let ρ := K.reflTriangleTetrahedron τ₁
  let κ := K.triangleComparisonTetrahedron τ₁ τ₂
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then σ.simplex
        else if h1 : i = 1 then ω.simplex
        else if h3 : i = 3 then ρ.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω.face0.trans σ.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ρ.face0.trans σ.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans σ.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ρ.face1.trans ω.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ρ.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = σ.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 σ.simplex := by rw [h0]
      _ = (K.symmPath2 (K.reflPath2 q)).toTriangle.simplex := σ.face1
  · have h1 : K.face 3 1 (K.fill Λ) = ω.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω.simplex := by rw [h1]
      _ = (K.symmPath2 (K.trianglePath2 τ₁ τ₂)).toTriangle.simplex := ω.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ρ.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ρ.simplex := by rw [h3]
      _ = τ₁.simplex := ρ.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h4]
      _ = τ₂.simplex := κ.face2

/-- Boundary-aware tetrahedron relating comparison with the first and last
triangle directly to the composite of the two intermediate comparison 2-cells. -/
private def KanComplex.trianglePath2TransBoundaryTetrahedron (K : KanComplex)
    {a b c : K.Obj} {p : K.PathSpace a b} {l m n : K.PathSpace a c}
    {q : K.PathSpace b c}
    (τ₁ : K.Triangle p l q) (τ₂ : K.Triangle p m q) (τ₃ : K.Triangle p n q) :
    K.Tetrahedron
      (K.reflPath2 q).toTriangle
      (K.transPath2 (K.trianglePath2 τ₁ τ₂) (K.trianglePath2 τ₂ τ₃)).toTriangle
      τ₃
      τ₁ := by
  let ε := K.reflTriangleTetrahedron ((K.reflPath2 q).toTriangle)
  let ω₁ :=
    K.transFillerTetrahedron
      (K.trianglePath2 τ₁ τ₂)
      (K.trianglePath2 τ₂ τ₃)
  let ω₂ := K.triangleComparisonTetrahedron τ₂ τ₃
  let κ := K.triangleComparisonTetrahedron τ₁ τ₂
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h2 : i = 2 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using κ.face2.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ε.simplex := by rw [h0]
      _ = (K.reflPath2 q).toTriangle.simplex := ε.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₁.simplex := by rw [h1]
      _ = (K.transPath2 (K.trianglePath2 τ₁ τ₂) (K.trianglePath2 τ₂ τ₃)).toTriangle.simplex := ω₁.face2
  · have h2 : K.face 3 2 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h2]
      _ = τ₃.simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 κ.simplex := by rw [h4]
      _ = τ₁.simplex := κ.face3

/-- Triangle comparison is compatible with vertical composition along a common
boundary triangle, up to a semantic 3-cell. -/
private def KanComplex.trianglePath2ReflPath3 (K : KanComplex)
    {a b c : K.Obj} {p : K.PathSpace a b} {m : K.PathSpace a c}
    {q : K.PathSpace b c} (τ : K.Triangle p m q) :
    K.Path3 (K.trianglePath2 τ τ) (K.reflPath2 m) :=
  K.tetrahedronPath3
    (K.triangleComparisonTetrahedron τ τ)
    (K.reflTriangleTetrahedron τ)

/-- Triangle comparison is compatible with vertical composition along a common
boundary triangle, up to a semantic 3-cell. -/
private def KanComplex.trianglePath2TransPath3 (K : KanComplex)
    {a b c : K.Obj} {p : K.PathSpace a b} {l m n : K.PathSpace a c}
    {q : K.PathSpace b c}
    (τ₁ : K.Triangle p l q) (τ₂ : K.Triangle p m q) (τ₃ : K.Triangle p n q) :
    K.Path3
      (K.trianglePath2 τ₁ τ₃)
      (K.transPath2 (K.trianglePath2 τ₁ τ₂) (K.trianglePath2 τ₂ τ₃)) :=
  K.tetrahedronPath3
    (K.triangleComparisonTetrahedron τ₁ τ₃)
    (K.trianglePath2TransBoundaryTetrahedron τ₁ τ₂ τ₃)

/-- Reversing the order of a triangle comparison computes the symmetry of the
original comparison 2-cell, up to a semantic 3-cell. -/
private def KanComplex.trianglePath2SymmPath3 (K : KanComplex)
    {a b c : K.Obj} {p : K.PathSpace a b} {m n : K.PathSpace a c}
    {q : K.PathSpace b c} (τ₁ : K.Triangle p m q) (τ₂ : K.Triangle p n q) :
    K.Path3
      (K.trianglePath2 τ₂ τ₁)
      (K.symmPath2 (K.trianglePath2 τ₁ τ₂)) :=
  K.symmPath3
    (K.tetrahedronFrontPath3
      ((K.symmReflPath2BridgeTetrahedron q).toPath3)
      (K.trianglePath2SymmAuxTetrahedron τ₁ τ₂)
      (K.triangleComparisonTetrahedron τ₂ τ₁))

/-- Comparing a semantic 2-cell against the reflexive triangle on its source
path recovers the chosen symmetry of that 2-cell. -/
private def KanComplex.trianglePath2ToReflPath3 (K : KanComplex)
    {a b : K.Obj} {p q : K.PathSpace a b} (α : K.Path2 p q) :
    K.Path3
      (K.trianglePath2 α.toTriangle (K.reflPath2 p).toTriangle)
      (K.symmPath2 α) :=
  K.tetrahedronPath3
    (K.triangleComparisonTetrahedron α.toTriangle (K.reflPath2 p).toTriangle)
    (K.symmTetrahedron α)

/-- Comparing the reflexive triangle on the source path against a semantic
2-cell recovers that 2-cell itself. -/
private def KanComplex.trianglePath2FromReflPath3 (K : KanComplex)
    {a b : K.Obj} {p q : K.PathSpace a b} (α : K.Path2 p q) :
    K.Path3
      (K.trianglePath2 (K.reflPath2 p).toTriangle α.toTriangle)
      α :=
  K.tetrahedronPath3
    (K.triangleComparisonTetrahedron (K.reflPath2 p).toTriangle α.toTriangle)
    ((K.reflPath3 α).toTetrahedron)

/-- Comparing `α.toTriangle` against the triangle of its composite with `β`
recovers the right factor `β`. -/
private def KanComplex.trianglePath2ToTransPath3 (K : KanComplex)
    {a b : K.Obj} {p q r : K.PathSpace a b}
    (α : K.Path2 p q) (β : K.Path2 q r) :
    K.Path3
      (K.trianglePath2 α.toTriangle (K.transPath2 α β).toTriangle)
      β :=
  K.tetrahedronPath3
    (K.triangleComparisonTetrahedron α.toTriangle (K.transPath2 α β).toTriangle)
    (K.transFillerTetrahedron α β)

/-- Re-extending the comparison between `α.toTriangle` and a target triangle back
along `α` recovers that target 2-cell. -/
private def KanComplex.transFromTriangleComparisonPath3 (K : KanComplex)
    {a b : K.Obj} {p q r : K.PathSpace a b}
    (α : K.Path2 p q) (β : K.Path2 p r) :
    K.Path3
      (K.transPath2 α (K.trianglePath2 α.toTriangle β.toTriangle))
      β :=
  K.tetrahedronFace2Path3
    (K.reflPath3 α)
    (K.transFillerTetrahedron α (K.trianglePath2 α.toTriangle β.toTriangle))
    (K.triangleComparisonTetrahedron α.toTriangle β.toTriangle)

/-- Degenerating a triangle along its first face keeps both front faces equal to the
original triangle, while turning the two outer faces into source-degenerate
triangles on its middle and source edges. -/
private def KanComplex.triangleFirstFaceDegenerateTetrahedron (K : KanComplex)
    {a b c : K.Obj} {u : K.PathSpace a b} {m : K.PathSpace a c}
    {v : K.PathSpace b c} (τ : K.Triangle u m v) :
    K.Tetrahedron τ τ (K.sourceDegenerateTriangle m) (K.sourceDegenerateTriangle u) := by
  refine
    { simplex := K.degen 2 0 τ.simplex
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · simpa using (K.face_degen_eq 1 τ.simplex (i := 0) (by omega))
  · simpa using (K.face_degen_succ 1 τ.simplex (i := 0) (by omega))
  · calc
      K.face 2 2 (K.degen 2 0 τ.simplex)
          = K.degen 1 0 (K.face 1 1 τ.simplex) := by
              simpa using
                (K.face_degen_gt 1 τ.simplex (i := 2) (j := 0) (by omega) (by omega))
      _ = K.degen 1 0 m.simplex := by rw [τ.face1]
      _ = (K.sourceDegenerateTriangle m).simplex := rfl
  · calc
      K.face 2 3 (K.degen 2 0 τ.simplex)
          = K.degen 1 0 (K.face 1 2 τ.simplex) := by
              simpa using
                (K.face_degen_gt 1 τ.simplex (i := 3) (j := 0) (by omega) (by omega))
      _ = K.degen 1 0 u.simplex := by rw [τ.face2]
      _ = (K.sourceDegenerateTriangle u).simplex := rfl

/-- Boundary replacement turning the left unitor into its chosen symmetry while
keeping the remaining triangle faces normalized. -/
private def KanComplex.leftUnitorSymmComparisonTetrahedron (K : KanComplex)
    {a b : K.Obj} (p : K.PathSpace a b) :
    K.Tetrahedron
      (K.reflPath2 p).toTriangle
      (K.symmPath2 (K.leftUnitorPath2 p)).toTriangle
      (K.compTriangle (K.reflPath a) p)
      (K.sourceDegenerateTriangle p) := by
  let Κ :
      K.Path3
        (K.trianglePath2
          (K.sourceDegenerateTriangle p)
          (K.compTriangle (K.reflPath a) p))
        (K.symmPath2 (K.leftUnitorPath2 p)) := by
    simpa [KanComplex.leftUnitorPath2, KanComplex.leftUnitorSimplex,
      KanComplex.leftUnitorHorn] using
      (K.trianglePath2SymmPath3
        (K.compTriangle (K.reflPath a) p)
        (K.sourceDegenerateTriangle p))
  exact K.tetrahedronReplaceFace1 Κ
    (K.triangleComparisonTetrahedron
      (K.sourceDegenerateTriangle p)
      (K.compTriangle (K.reflPath a) p))

/-- Triangle-level right boundary for the left-unitor-on-composites coherence. -/
private def KanComplex.leftUnitorCompTriangleBoundaryTetrahedron (K : KanComplex)
    {a b c : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c) :
    K.Tetrahedron
      (K.whiskerRightTriangle (K.reflPath2 p) q)
      (K.whiskerRightTriangle (K.leftUnitorPath2 p) q)
      (K.assocTriangle (K.reflPath a) p q)
      (K.sourceDegenerateTriangle p) := by
  let ε := K.whiskerRightReflAuxTetrahedron p q
  let ω₁ := K.whiskerRightTriangleFillerTetrahedron (K.leftUnitorPath2 p) q
  let ω₂ := K.assocTriangleFillerTetrahedron (K.reflPath a) p q
  let κ := K.leftUnitorSymmComparisonTetrahedron p
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h2 : i = 2 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using κ.face2.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ε.simplex := by rw [h0]
      _ = (K.whiskerRightTriangle (K.reflPath2 p) q).simplex := ε.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₁.simplex := by rw [h1]
      _ = (K.whiskerRightTriangle (K.leftUnitorPath2 p) q).simplex := ω₁.face2
  · have h2 : K.face 3 2 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h2]
      _ = (K.assocTriangle (K.reflPath a) p q).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 κ.simplex := by rw [h4]
      _ = (K.sourceDegenerateTriangle p).simplex := κ.face3

/-- Boundary-aware tetrahedron whose middle face is the normalized right-whiskered
left-unitor route. -/
private def KanComplex.leftUnitorCompBoundaryTetrahedron (K : KanComplex)
    {a b c : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c) :
    K.Tetrahedron
      (K.reflPath2 (K.compPath p q)).toTriangle
      (K.whiskerRightPath2 (K.leftUnitorPath2 p) q).toTriangle
      (K.sourceDegenerateTriangle (K.compPath p q))
      (K.assocTriangle (K.reflPath a) p q) := by
  let ε := K.whiskerRightReflBoundaryTetrahedron p q
  let ω₁ := K.whiskerRightTetrahedron (K.leftUnitorPath2 p) q
  let ω₂ := K.triangleFirstFaceDegenerateTetrahedron (K.compTriangle p q)
  let κ := K.leftUnitorCompTriangleBoundaryTetrahedron p q
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h3 : i = 3 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ε.simplex := by rw [h0]
      _ = (K.reflPath2 (K.compPath p q)).toTriangle.simplex := ε.face1
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h1]
      _ = (K.whiskerRightPath2 (K.leftUnitorPath2 p) q).toTriangle.simplex := ω₁.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h3]
      _ = (K.sourceDegenerateTriangle (K.compPath p q)).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h4]
      _ = (K.assocTriangle (K.reflPath a) p q).simplex := κ.face2

/-- Boundary-aware tetrahedron exposing the left-unitor-on-composites coherence in
the normalized `trans`-filler form. -/
private def KanComplex.leftUnitorCompPath3Tetrahedron (K : KanComplex)
    {a b c : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath c)).toTriangle
      (K.leftUnitorPath2 (K.compPath p q)).toTriangle
      (K.whiskerRightPath2 (K.leftUnitorPath2 p) q).toTriangle
      (K.associatorPath2 (K.reflPath a) p q).toTriangle :=
  K.tetrahedronComparisonTetrahedron
    (K.leftUnitorCompBoundaryTetrahedron p q)
    (K.leftUnitorTetrahedron (K.compPath p q))
    (K.associatorTetrahedron (K.reflPath a) p q)

/-- Left unitor on a composite decomposes as associator followed by right
whiskering of the left unitor. -/
def KanComplex.leftUnitorCompPath3 (K : KanComplex) {a b c : K.Obj}
    (p : K.PathSpace a b) (q : K.PathSpace b c) :
    K.Path3
      (K.transPath2
        (K.associatorPath2 (K.reflPath a) p q)
        (K.leftUnitorPath2 (K.compPath p q)))
      (K.whiskerRightPath2 (K.leftUnitorPath2 p) q) := by
  let α := K.associatorPath2 (K.reflPath a) p q
  exact K.tetrahedronFace2Path3
    (K.reflPath3 α)
    (K.transFillerTetrahedron α (K.leftUnitorPath2 (K.compPath p q)))
    (K.leftUnitorCompPath3Tetrahedron p q)
/-- Left inverse law for semantic 2-cells, derived by reducing the
self-comparison `trianglePath2 α.toTriangle α.toTriangle` along the source-side
reflexive triangle. -/
def KanComplex.transLeftCancelPath3 (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} (α : K.Path2 p q) :
    K.Path3 (K.transPath2 (K.symmPath2 α) α) (K.reflPath2 q) := by
  let compare :=
    K.transPath3
      (K.transCongrLeftPath3
        (K.trianglePath2ToReflPath3 α)
        (K.trianglePath2 (K.reflPath2 p).toTriangle α.toTriangle))
      (K.transCongrRightPath3
        (K.symmPath2 α)
        (K.trianglePath2FromReflPath3 α))
  let contract :=
    K.transPath3
      (K.symmPath3
        (K.trianglePath2TransPath3
          α.toTriangle
          (K.reflPath2 p).toTriangle
          α.toTriangle))
      (K.trianglePath2ReflPath3 α.toTriangle)
  exact K.transPath3 (K.symmPath3 compare) contract

/-- Vertical composition of semantic 2-cells is associative up to a semantic
3-cell. -/
private def KanComplex.transAssocPath3 (K : KanComplex) {a b : K.Obj}
    {p q r s : K.PathSpace a b}
    (α : K.Path2 p q) (β : K.Path2 q r) (γ : K.Path2 r s) :
    K.Path3
      (K.transPath2 (K.transPath2 α β) γ)
      (K.transPath2 α (K.transPath2 β γ)) := by
  let δ :
      K.Path2 q s :=
    K.trianglePath2
      α.toTriangle
      (K.transPath2 (K.transPath2 α β) γ).toTriangle
  let contract :
      K.Path3 δ (K.transPath2 β γ) :=
    K.transPath3
      (K.trianglePath2TransPath3
        α.toTriangle
        (K.transPath2 α β).toTriangle
        (K.transPath2 (K.transPath2 α β) γ).toTriangle)
      (K.transPath3
        (K.transCongrLeftPath3
          (K.trianglePath2ToTransPath3 α β)
          (K.trianglePath2
            (K.transPath2 α β).toTriangle
            (K.transPath2 (K.transPath2 α β) γ).toTriangle))
        (K.transCongrRightPath3
          β
          (K.trianglePath2ToTransPath3
            (K.transPath2 α β)
            γ)))
  exact K.transPath3
    (K.symmPath3
      (K.transFromTriangleComparisonPath3
        α
        (K.transPath2 (K.transPath2 α β) γ)))
    (K.transCongrRightPath3 α contract)

/-- Once the triangle comparison between whiskering by `refl` and the left
unitor is identified with the route `leftUnitor q ; symm η`, the full
left-unitor naturality follows by associativity and left cancellation. -/
private def KanComplex.leftUnitorNaturalityPath3FromTriangleComparison
    (K : KanComplex) {a b : K.Obj} {p q : K.PathSpace a b}
    (η : K.Path2 p q)
    (hTriangle :
      K.Path3
        (K.trianglePath2
          (K.whiskerLeftPath2 (K.reflPath a) η).toTriangle
          (K.leftUnitorPath2 p).toTriangle)
        (K.transPath2 (K.leftUnitorPath2 q) (K.symmPath2 η))) :
    K.Path3
      (K.transPath2
        (K.whiskerLeftPath2 (K.reflPath a) η)
        (K.leftUnitorPath2 q))
      (K.transPath2 (K.leftUnitorPath2 p) η) := by
  let α := K.whiskerLeftPath2 (K.reflPath a) η
  let luP := K.leftUnitorPath2 p
  let luQ := K.leftUnitorPath2 q
  let hToLeftUnitor :
      K.Path3
        (K.transPath2 (K.transPath2 α luQ) (K.symmPath2 η))
        luP := by
    exact K.transPath3
      (K.transAssocPath3 α luQ (K.symmPath2 η))
      (K.transPath3
        (K.symmPath3 (K.transCongrRightPath3 α hTriangle))
        (K.transFromTriangleComparisonPath3 α luP))
  let hComposed :
      K.Path3
        (K.transPath2
          (K.transPath2 (K.transPath2 α luQ) (K.symmPath2 η))
          η)
        (K.transPath2 luP η) :=
    K.transCongrLeftPath3 hToLeftUnitor η
  let hNormalize :
      K.Path3
        (K.transPath2
          (K.transPath2 (K.transPath2 α luQ) (K.symmPath2 η))
          η)
        (K.transPath2 α luQ) := by
    exact K.transPath3
      (K.transAssocPath3 (K.transPath2 α luQ) (K.symmPath2 η) η)
      (K.transPath3
         (K.transCongrRightPath3
           (K.transPath2 α luQ)
           (K.transLeftCancelPath3 η))
         (K.transReflRightPath3 (K.transPath2 α luQ)))
  exact K.transPath3 (K.symmPath3 hNormalize) hComposed

/-- Front bridge for left-unitor naturality: keep `η` visible on both front
faces while normalizing the remaining boundary to the degenerate source face on
`p`. -/
private def KanComplex.leftUnitorNaturalityFrontBridgeTetrahedron (K : KanComplex)
    {a b : K.Obj} {p q : K.PathSpace a b} (η : K.Path2 p q) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath b)).toTriangle
      η.toTriangle
      η.toTriangle
      (K.reflPath2 p).toTriangle :=
  K.tetrahedronComparisonTetrahedron
    (K.path2DegenerateTetrahedron η)
    (K.path2DegenerateTetrahedron η)
    (K.reflTriangleTetrahedron (K.sourceDegenerateTriangle p))

/-- Boundary-aware tetrahedron packaging the right-hand route in left-unitor
naturality: first apply `leftUnitor p`, then `η`. -/
private def KanComplex.leftUnitorNaturalityRightBoundaryTetrahedron
    (K : KanComplex) {a b : K.Obj} {p q : K.PathSpace a b} (η : K.Path2 p q) :
    K.Tetrahedron
      η.toTriangle
      (K.transPath2 (K.leftUnitorPath2 p) η).toTriangle
      (K.sourceDegenerateTriangle q)
      (K.compTriangle (K.reflPath a) p) := by
  let σ := K.leftUnitorNaturalityFrontBridgeTetrahedron η
  let ω := K.transFillerTetrahedron (K.leftUnitorPath2 p) η
  let κ := K.path2DegenerateTetrahedron η
  let θ := K.leftUnitorTetrahedron p
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then σ.simplex
        else if h1 : i = 1 then ω.simplex
        else if h2 : i = 2 then κ.simplex
        else θ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω.face0.trans σ.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using κ.face0.trans σ.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using θ.face0.trans σ.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using κ.face1.trans ω.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using θ.face1.trans ω.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using θ.face2.trans κ.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = σ.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 σ.simplex := by rw [h0]
      _ = η.toTriangle.simplex := σ.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω.simplex := by rw [h1]
      _ = (K.transPath2 (K.leftUnitorPath2 p) η).toTriangle.simplex := ω.face2
  · have h2 : K.face 3 2 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h2]
      _ = (K.sourceDegenerateTriangle q).simplex := κ.face2
  · have h4 : K.face 3 4 (K.fill Λ) = θ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 θ.simplex := by rw [h4]
      _ = (K.compTriangle (K.reflPath a) p).simplex := θ.face3

/-- Boundary-aware tetrahedron whose middle face is `leftUnitor q`, whose
second outer face is the right-hand naturality route, and whose last face is
whiskering `η` by `refl`. -/
private def KanComplex.leftUnitorNaturalityPath3Tetrahedron (K : KanComplex)
    {a b : K.Obj} {p q : K.PathSpace a b} (η : K.Path2 p q) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath b)).toTriangle
      (K.leftUnitorPath2 q).toTriangle
      (K.transPath2 (K.leftUnitorPath2 p) η).toTriangle
      (K.whiskerLeftPath2 (K.reflPath a) η).toTriangle := by
  let ε := K.reflTriangleTetrahedron η.toTriangle
  let ω₁ := K.leftUnitorTetrahedron q
  let ω₂ := K.leftUnitorNaturalityRightBoundaryTetrahedron η
  let κ := K.whiskerLeftTetrahedron (K.reflPath a) η
  let Λ : Horn K.toSimplicialSet 3 1 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h2 : i = 2 then ω₁.simplex
        else if h3 : i = 3 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h02 | hrest
        · rcases h02 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face1.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h23 | hrest
              · rcases h23 with ⟨rfl, rfl⟩
                simpa using ω₂.face2.trans ω₁.face2.symm
              · rcases hrest with h24 | h34
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using κ.face2.trans ω₁.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 1 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 1 (K.fill Λ))
          = K.face 2 0 (K.face 3 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 2 0 ε.simplex := by rw [h0]
      _ = (K.reflPath2 (K.reflPath b)).simplex := ε.face0
  · have h2 : K.face 3 2 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 2 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h2]
      _ = (K.leftUnitorPath2 q).simplex := ω₁.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 1 ω₂.simplex := by rw [h3]
      _ = (K.transPath2 (K.leftUnitorPath2 p) η).simplex := ω₂.face1
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 3) (by omega) (by omega))
      _ = K.face 2 1 κ.simplex := by rw [h4]
      _ = (K.whiskerLeftPath2 (K.reflPath a) η).simplex := κ.face1

/-- Left unitor is natural with respect to semantic 2-cells. -/
def KanComplex.leftUnitorNaturalityPath3 (K : KanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} (η : K.Path2 p q) :
    K.Path3
      (K.transPath2
        (K.whiskerLeftPath2 (K.reflPath a) η)
        (K.leftUnitorPath2 q))
      (K.transPath2 (K.leftUnitorPath2 p) η) := by
  let α := K.whiskerLeftPath2 (K.reflPath a) η
  exact K.tetrahedronFace2Path3
    (K.reflPath3 α)
    (K.transFillerTetrahedron α (K.leftUnitorPath2 q))
    (K.leftUnitorNaturalityPath3Tetrahedron η)

/-- The intermediate 2-cell appearing in the recursive associator step: it keeps
the left-associated source edge `((α · β) · γ)` fixed, replaces the right edge by
`refl`, and lands at the rebracketed composite `α · (β · δ)`. -/
private def KanComplex.associatorStepMidPath2 (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ) :
    K.Path2
      (K.compPath (K.compPath α β) γ)
      (K.compPath α (K.compPath β δ)) := by
  let Λ : Horn K.toSimplicialSet 2 1 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then (K.whiskerLeftPath2 β η).simplex
        else if h2 : i = 2 then (K.compTriangle α (K.compPath β δ)).simplex
        else (K.assocTriangle α β γ).simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
          omega
        rcases hij_cases with h02 | h03 | h23
        · rcases h02 with ⟨rfl, rfl⟩
          simpa using (K.compTriangle α (K.compPath β δ)).face0.trans
            (K.whiskerLeftPath2 β η).face1.symm
        · rcases h03 with ⟨rfl, rfl⟩
          simpa using (K.assocTriangle α β γ).face0.trans
            (K.whiskerLeftPath2 β η).face2.symm
        · rcases h23 with ⟨rfl, rfl⟩
          simpa using (K.assocTriangle α β γ).face2.trans
            (K.compTriangle α (K.compPath β δ)).face2.symm }
  refine
    { simplex := K.face 2 1 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.fill Λ) = (K.whiskerLeftPath2 β η).simplex := by
      simpa using K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 1 (K.fill Λ))
          = K.face 1 0 (K.face 2 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 1 (K.fill Λ) (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 1 0 (K.whiskerLeftPath2 β η).simplex := by rw [h0]
      _ = (K.reflPath d).simplex := (K.whiskerLeftPath2 β η).face0
  · have h2 : K.face 2 2 (K.fill Λ) = (K.compTriangle α (K.compPath β δ)).simplex := by
      simpa using K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 1 (K.fill Λ))
          = K.face 1 1 (K.face 2 2 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 1 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.compTriangle α (K.compPath β δ)).simplex := by rw [h2]
      _ = (K.compPath α (K.compPath β δ)).simplex := (K.compTriangle α (K.compPath β δ)).face1
  · have h3 : K.face 2 3 (K.fill Λ) = (K.assocTriangle α β γ).simplex := by
      simpa using K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 1 (K.fill Λ))
          = K.face 1 1 (K.face 2 3 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 1 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 1 1 (K.assocTriangle α β γ).simplex := by rw [h3]
      _ = (K.compPath (K.compPath α β) γ).simplex := (K.assocTriangle α β γ).face1

/-- The raw tetrahedron filled to define `associatorStepMidTriangle`. -/
private def KanComplex.associatorStepMidFillerTetrahedron (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ) :
    K.Tetrahedron
      (K.whiskerLeftPath2 β η).toTriangle
      (K.associatorStepMidPath2 α β η).toTriangle
      (K.compTriangle α (K.compPath β δ))
      (K.assocTriangle α β γ) := by
  let Λ : Horn K.toSimplicialSet 2 1 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then (K.whiskerLeftPath2 β η).simplex
        else if h2 : i = 2 then (K.compTriangle α (K.compPath β δ)).simplex
        else (K.assocTriangle α β γ).simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
          omega
        rcases hij_cases with h02 | h03 | h23
        · rcases h02 with ⟨rfl, rfl⟩
          simpa using (K.compTriangle α (K.compPath β δ)).face0.trans
            (K.whiskerLeftPath2 β η).face1.symm
        · rcases h03 with ⟨rfl, rfl⟩
          simpa using (K.assocTriangle α β γ).face0.trans
            (K.whiskerLeftPath2 β η).face2.symm
        · rcases h23 with ⟨rfl, rfl⟩
          simpa using (K.assocTriangle α β γ).face2.trans
            (K.compTriangle α (K.compPath β δ)).face2.symm }
  refine
    { simplex := K.fill Λ
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · simpa using K.fill_spec Λ (i := 0) (by omega) (by omega)
  · change K.face 2 1 (K.fill Λ) = (K.associatorStepMidPath2 α β η).simplex
    rfl
  · simpa using K.fill_spec Λ (i := 2) (by omega) (by omega)
  · simpa using K.fill_spec Λ (i := 3) (by omega) (by omega)

/-- The triangle attached to `associatorStepMidPath2`. -/
private abbrev KanComplex.associatorStepMidTriangle (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ) :
    K.Triangle
      (K.compPath (K.compPath α β) γ)
      (K.compPath α (K.compPath β δ))
      (K.reflPath d) :=
  (K.associatorStepMidPath2 α β η).toTriangle

/-- The comparison between the associator triangle and the recursive middle
triangle is exactly left whiskering twice by `α` and `β`. -/
private def KanComplex.associatorStepMidPath3 (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ) :
    K.Path3
      (K.trianglePath2
        (K.associatorPath2 α β γ).toTriangle
        (K.associatorStepMidTriangle α β η))
      (K.whiskerLeftPath2 α (K.whiskerLeftPath2 β η)) :=
  K.tetrahedronPath3
    (K.triangleComparisonTetrahedron
      (K.associatorPath2 α β γ).toTriangle
      (K.associatorStepMidPath2 α β η).toTriangle)
    (K.tetrahedronComparisonTetrahedron
      (K.associatorStepMidFillerTetrahedron α β η)
      (K.whiskerLeftTetrahedron α (K.whiskerLeftPath2 β η))
      (K.associatorTetrahedron α β γ))

/-- If the midpoint filler is compared directly against a naturality tetrahedron
whose middle face is `whiskerLeft (α·β) η ; associator α β δ`, then the
remaining midpoint step is reduced to that single tetrahedral comparison. -/
private def KanComplex.associatorStepMidPath3FromNaturalityTetrahedron
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ)
    (ωNat :
      K.Tetrahedron
        (K.whiskerLeftPath2 β η).toTriangle
        (K.transPath2
          (K.whiskerLeftPath2 (K.compPath α β) η)
          (K.associatorPath2 α β δ)).toTriangle
        (K.compTriangle α (K.compPath β δ))
        (K.assocTriangle α β γ)) :
    K.Path3
      (K.associatorStepMidPath2 α β η)
      (K.transPath2
        (K.whiskerLeftPath2 (K.compPath α β) η)
        (K.associatorPath2 α β δ)) :=
  K.tetrahedronPath3
    (K.associatorStepMidFillerTetrahedron α β η)
    ωNat

/-- Exact right-half comparison still needed for the recursive associator step.
Passing it in explicitly isolates the remaining local obstruction. -/
private def KanComplex.associatorStepMidRightPath3 (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ)
    (hRight :
      K.Path3
        (K.trianglePath2
          (K.associatorStepMidTriangle α β η)
          (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle)
        (K.symmPath2 (K.associatorPath2 α β δ))) :
    K.Path3
      (K.trianglePath2
        (K.associatorStepMidTriangle α β η)
        (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle)
      (K.symmPath2 (K.associatorPath2 α β δ)) :=
  hRight

/-- Once the right-hand comparison from the recursive middle triangle to the
chosen whiskered triangle is identified with the symmetric associator at `δ`,
the full associator step follows by triangle-comparison transitivity. -/
private def KanComplex.associatorStepPath3FromRightComparison (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ)
    (hRight :
      K.Path3
        (K.trianglePath2
          (K.associatorStepMidTriangle α β η)
          (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle)
        (K.symmPath2 (K.associatorPath2 α β δ))) :
    K.Path3
      (K.trianglePath2
        (K.associatorPath2 α β γ).toTriangle
        (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle)
      (K.transPath2
        (K.whiskerLeftPath2 α (K.whiskerLeftPath2 β η))
        (K.symmPath2 (K.associatorPath2 α β δ))) := by
  exact K.transPath3
    (K.trianglePath2TransPath3
      (K.associatorPath2 α β γ).toTriangle
      (K.associatorStepMidTriangle α β η)
      (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle)
    (K.transPath3
      (K.transCongrLeftPath3
        (K.associatorStepMidPath3 α β η)
        (K.trianglePath2
          (K.associatorStepMidTriangle α β η)
          (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle))
      (K.transCongrRightPath3
        (K.whiskerLeftPath2 α (K.whiskerLeftPath2 β η))
        hRight))

/-- Boundary tetrahedron whose missing middle face is exactly the comparison
between the recursive midpoint triangle and the pentagon whisker-front triangle. -/
private def KanComplex.associatorStepMidPentagonBoundaryTetrahedron
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ) :
    K.Tetrahedron
      η.toTriangle
      (K.associatorStepMidTriangle α β η)
      (K.whiskerLeftCompTriangle α β δ)
      (K.compTriangle (K.compPath α β) γ) := by
  let ε := K.whiskerLeftTetrahedron β η
  let ω₁ := K.associatorStepMidFillerTetrahedron α β η
  let ω₂ := K.whiskerLeftCompTriangleFillerTetrahedron α β δ
  let κ := K.assocTriangleFillerTetrahedron α β γ
  let Λ : Horn K.toSimplicialSet 3 1 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h2 : i = 2 then ω₁.simplex
        else if h3 : i = 3 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h02 | hrest
        · rcases h02 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face1.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h23 | hrest
              · rcases h23 with ⟨rfl, rfl⟩
                simpa using ω₂.face2.trans ω₁.face2.symm
              · rcases hrest with h24 | h34
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using κ.face2.trans ω₁.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 1 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 1 (K.fill Λ))
          = K.face 2 0 (K.face 3 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 2 0 ε.simplex := by rw [h0]
      _ = η.toTriangle.simplex := ε.face0
  · have h2 : K.face 3 2 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 2 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h2]
      _ = (K.associatorStepMidTriangle α β η).simplex := ω₁.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 1 ω₂.simplex := by rw [h3]
      _ = (K.whiskerLeftCompTriangle α β δ).simplex := ω₂.face1
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 3) (by omega) (by omega))
      _ = K.face 2 1 κ.simplex := by rw [h4]
      _ = (K.compTriangle (K.compPath α β) γ).simplex := κ.face1

/-- Comparison tetrahedron whose middle face is the desired midpoint-to-pentagon
front 3-cell. -/
private def KanComplex.associatorStepMidToPentagonWhiskerFrontComparisonTetrahedron
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ) :
    K.Tetrahedron
      (K.reflPath2 δ).toTriangle
      (K.trianglePath2
        (K.associatorStepMidTriangle α β η)
        (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle).toTriangle
      (K.compTriangle (K.compPath α β) δ)
      (K.whiskerLeftCompTriangle α β δ) := by
  let ε := K.reflTriangleTetrahedron η.toTriangle
  let ω₁ := K.triangleComparisonTetrahedron
    (K.associatorStepMidTriangle α β η)
    (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle
  let ω₂ := K.whiskerLeftTetrahedron (K.compPath α β) η
  let κ := K.associatorStepMidPentagonBoundaryTetrahedron α β η
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h3 : i = 3 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ε.simplex := by rw [h0]
      _ = ((K.reflPath2 δ).toTriangle).simplex := ε.face1
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h1]
      _ = (K.trianglePath2
            (K.associatorStepMidTriangle α β η)
            (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle).toTriangle.simplex := ω₁.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h3]
      _ = (K.compTriangle (K.compPath α β) δ).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 2 (K.fill Λ) (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h4]
      _ = (K.whiskerLeftCompTriangle α β δ).simplex := κ.face2

/-- The missing right-half midpoint/front comparison is already the middle face
of the boundary tetrahedron built from the recursive midpoint triangle and the
direct whisker-front pentagon triangle. -/
private def KanComplex.associatorStepMidToPentagonWhiskerFrontPath3
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ) :
    K.Path3
      (K.trianglePath2
        (K.associatorStepMidTriangle α β η)
        (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle)
      (K.pentagonWhiskerFrontPath2 α β δ) :=
  K.tetrahedronPath3
    (K.associatorStepMidToPentagonWhiskerFrontComparisonTetrahedron α β η)
    (K.triangleComparisonTetrahedron
      (K.whiskerLeftCompTriangle α β δ)
      (K.compTriangle (K.compPath α β) δ))

/-- The scratch pentagon front face `χ` is the symmetry of the ordinary
associator `(q, r, s)` up to a semantic 3-cell. -/
private def KanComplex.pentagonFrontSymmAssociatorPath3 (K : KanComplex)
    {b c d e : K.Obj} (q : K.PathSpace b c) (r : K.PathSpace c d)
    (s : K.PathSpace d e) :
    K.Path3
      (K.trianglePath2
        (K.compTriangle q (K.compPath r s))
        (K.assocTriangle q r s))
      (K.symmPath2 (K.associatorPath2 q r s)) :=
  K.trianglePath2SymmPath3
    (K.assocTriangle q r s)
    (K.compTriangle q (K.compPath r s))

/-- It suffices to compare the recursive midpoint/front triangle comparison
directly to the whiskered front pentagon face. The remaining route to the
symmetric associator at `δ` is already available from the pentagon-front
comparison and the front/symmetric-associator identification. -/
private def KanComplex.associatorStepMidRightPath3FromPentagonWhiskerFront
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ)
    (hMidFront :
      K.Path3
        (K.trianglePath2
          (K.associatorStepMidTriangle α β η)
          (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle)
        (K.pentagonWhiskerFrontPath2 α β δ)) :
    K.Path3
      (K.trianglePath2
        (K.associatorStepMidTriangle α β η)
        (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle)
      (K.symmPath2 (K.associatorPath2 α β δ)) := by
  exact K.transPath3
    hMidFront
    (K.transPath3
      (K.pentagonWhiskerFrontComparisonPath3 α β δ)
      (K.pentagonFrontSymmAssociatorPath3 α β δ))

/-- A midpoint-to-front comparison already suffices to recover the full reduced
associator-step comparison. -/
private def KanComplex.associatorStepPath3FromPentagonWhiskerFront
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ)
    (hMidFront :
      K.Path3
        (K.trianglePath2
          (K.associatorStepMidTriangle α β η)
          (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle)
        (K.pentagonWhiskerFrontPath2 α β δ)) :
    K.Path3
      (K.trianglePath2
        (K.associatorPath2 α β γ).toTriangle
        (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle)
      (K.transPath2
        (K.whiskerLeftPath2 α (K.whiskerLeftPath2 β η))
        (K.symmPath2 (K.associatorPath2 α β δ))) :=
  K.associatorStepPath3FromRightComparison α β η <|
    K.associatorStepMidRightPath3FromPentagonWhiskerFront α β η hMidFront

/-- The older midpoint/right comparison can now be recovered directly from the
concrete midpoint/front bridge, without introducing any separate naturality
tetrahedron as primitive data. -/
private def KanComplex.associatorStepMidPath3FromPentagonWhiskerFront
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ)
    (hMidFront :
      K.Path3
        (K.trianglePath2
          (K.associatorStepMidTriangle α β η)
          (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle)
        (K.pentagonWhiskerFrontPath2 α β δ)) :
    K.Path3
      (K.associatorStepMidPath2 α β η)
      (K.transPath2
        (K.whiskerLeftPath2 (K.compPath α β) η)
        (K.associatorPath2 α β δ)) := by
  let M := K.associatorStepMidPath2 α β η
  let W := K.whiskerLeftPath2 (K.compPath α β) η
  let A := K.associatorPath2 α β δ
  let T := K.transPath2 W A
  have hPent :
      K.Path3
        (K.pentagonWhiskerFrontPath2 α β δ)
        (K.symmPath2 A) := by
    exact K.transPath3
      (K.pentagonWhiskerFrontComparisonPath3 α β δ)
      (K.pentagonFrontSymmAssociatorPath3 α β δ)
  have hLoop :
      K.Path3
        (K.trianglePath2 (K.associatorStepMidTriangle α β η) T.toTriangle)
        (K.reflPath2 (K.compPath α (K.compPath β δ))) := by
    exact K.transPath3
      (K.trianglePath2TransPath3
        (K.associatorStepMidTriangle α β η)
        W.toTriangle
        T.toTriangle)
      (K.transPath3
        (K.transPath3
          (K.transCongrRightPath3
            (K.trianglePath2
              (K.associatorStepMidTriangle α β η)
              W.toTriangle)
            (K.trianglePath2ToTransPath3 W A))
          (K.transCongrLeftPath3 hMidFront A))
        (K.transPath3
          (K.transCongrLeftPath3 hPent A)
          (K.transLeftCancelPath3 A)))
  exact K.symmPath3 <|
    K.transPath3
      (K.symmPath3 (K.transFromTriangleComparisonPath3 M T))
      (K.transPath3
        (K.transCongrRightPath3 M hLoop)
        (K.transReflRightPath3 M))

/-- The naturality-style tetrahedron is now a consequence of the concrete
midpoint/front comparison, rather than an independent frontier object. -/
private def KanComplex.associatorStepMidNaturalityTetrahedronFromPentagonWhiskerFront
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ)
    (hMidFront :
      K.Path3
        (K.trianglePath2
          (K.associatorStepMidTriangle α β η)
          (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle)
        (K.pentagonWhiskerFrontPath2 α β δ)) :
    K.Tetrahedron
      (K.whiskerLeftPath2 β η).toTriangle
      (K.transPath2
        (K.whiskerLeftPath2 (K.compPath α β) η)
        (K.associatorPath2 α β δ)).toTriangle
      (K.compTriangle α (K.compPath β δ))
      (K.assocTriangle α β γ) :=
  K.tetrahedronReplaceFace1
    (K.associatorStepMidPath3FromPentagonWhiskerFront α β η hMidFront)
    (K.associatorStepMidFillerTetrahedron α β η)

/-- Once the reduced triangle comparison for whiskering over a composite is
identified, the full associator/whiskering comparison follows by re-extending
along the left associator. -/
private def KanComplex.whiskerLeftCompPath3FromTriangleComparison (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ)
    (hTri :
      K.Path3
        (K.trianglePath2
          (K.associatorPath2 α β γ).toTriangle
          (K.whiskerLeftPath2 (K.compPath α β) η).toTriangle)
        (K.transPath2
          (K.whiskerLeftPath2 α (K.whiskerLeftPath2 β η))
          (K.symmPath2 (K.associatorPath2 α β δ)))) :
    K.Path3
      (K.whiskerLeftPath2 (K.compPath α β) η)
      (K.transPath2
        (K.associatorPath2 α β γ)
        (K.transPath2
          (K.whiskerLeftPath2 α (K.whiskerLeftPath2 β η))
          (K.symmPath2 (K.associatorPath2 α β δ)))) := by
  let Aγ := K.associatorPath2 α β γ
  let W := K.whiskerLeftPath2 (K.compPath α β) η
  exact K.transPath3
    (K.symmPath3 (K.transFromTriangleComparisonPath3 Aγ W))
    (K.transCongrRightPath3 Aγ hTri)

/-- The composite-whiskering comparison follows by combining the constructive
midpoint/front bridge with the generic re-extension from the reduced triangle
comparison. -/
private def KanComplex.whiskerLeftCompPath3 (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b) (β : K.PathSpace b c)
    {γ δ : K.PathSpace c d} (η : K.Path2 γ δ) :
    K.Path3
      (K.whiskerLeftPath2 (K.compPath α β) η)
      (K.transPath2
        (K.associatorPath2 α β γ)
        (K.transPath2
          (K.whiskerLeftPath2 α (K.whiskerLeftPath2 β η))
          (K.symmPath2 (K.associatorPath2 α β δ)))) :=
  K.whiskerLeftCompPath3FromTriangleComparison α β η <|
    K.associatorStepPath3FromPentagonWhiskerFront α β η <|
      K.associatorStepMidToPentagonWhiskerFrontPath3 α β η

/-- Midpoint horn for the source-side square comparing
`(α ◁ η) ▷ δ` against `α ◁ (η ▷ δ)`. -/
private def KanComplex.whiskerLeftWhiskerRightMidHorn (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    Horn K.toSimplicialSet 2 1 :=
  { missing_le := by omega
    facet := fun i _ =>
      if h0 : i = 0 then (K.whiskerRightPath2 η δ).simplex
      else if h2 : i = 2 then (K.compTriangle α (K.compPath γ δ)).simplex
      else (K.assocTriangle α β δ).simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
        omega
      rcases hij_cases with h02 | h03 | h23
      · rcases h02 with ⟨rfl, rfl⟩
        simpa using (K.compTriangle α (K.compPath γ δ)).face0.trans
          (K.whiskerRightPath2 η δ).face1.symm
      · rcases h03 with ⟨rfl, rfl⟩
        simpa using (K.assocTriangle α β δ).face0.trans
          (K.whiskerRightPath2 η δ).face2.symm
      · rcases h23 with ⟨rfl, rfl⟩
        simpa using (K.assocTriangle α β δ).face2.trans
          (K.compTriangle α (K.compPath γ δ)).face2.symm }

/-- Midpoint 2-cell whose left comparison is already constructive; the remaining
obstruction for `whiskerLeftWhiskerRight` is its right comparison against the
right-whiskered route. -/
def KanComplex.whiskerLeftWhiskerRightMidPath2 (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    K.Path2 (K.compPath (K.compPath α β) δ) (K.compPath α (K.compPath γ δ)) := by
  let Λ := K.whiskerLeftWhiskerRightMidHorn α η δ
  refine
    { simplex := K.face 2 1 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.fill Λ) = (K.whiskerRightPath2 η δ).simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 1 (K.fill Λ))
          = K.face 1 0 (K.face 2 0 (K.fill Λ)) := by
              simpa using
                (K.face_face 1 (K.fill Λ) (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 1 0 (K.whiskerRightPath2 η δ).simplex := by rw [h0]
      _ = (K.reflPath d).simplex := (K.whiskerRightPath2 η δ).face0
  · have h2 : K.face 2 2 (K.fill Λ) = (K.compTriangle α (K.compPath γ δ)).simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 1 (K.fill Λ))
          = K.face 1 1 (K.face 2 2 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 1 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.compTriangle α (K.compPath γ δ)).simplex := by rw [h2]
      _ = (K.compPath α (K.compPath γ δ)).simplex := (K.compTriangle α (K.compPath γ δ)).face1
  · have h3 : K.face 2 3 (K.fill Λ) = (K.assocTriangle α β δ).simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 1 (K.fill Λ))
          = K.face 1 1 (K.face 2 3 (K.fill Λ)) := by
              symm
              simpa using
                (K.face_face 1 (K.fill Λ) (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 1 1 (K.assocTriangle α β δ).simplex := by rw [h3]
      _ = (K.compPath (K.compPath α β) δ).simplex := (K.assocTriangle α β δ).face1

/-- The midpoint horn itself, packaged as a tetrahedron. -/
private def KanComplex.whiskerLeftWhiskerRightMidFillerTetrahedron (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    K.Tetrahedron
      (K.whiskerRightPath2 η δ).toTriangle
      (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle
      (K.compTriangle α (K.compPath γ δ))
      (K.assocTriangle α β δ) := by
  let Λ := K.whiskerLeftWhiskerRightMidHorn α η δ
  refine
    { simplex := K.fill Λ
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · simpa using K.fill_spec Λ (i := 0) (by omega) (by omega)
  · change K.face 2 1 (K.fill Λ) = (K.whiskerLeftWhiskerRightMidPath2 α η δ).simplex
    rfl
  · simpa using K.fill_spec Λ (i := 2) (by omega) (by omega)
  · simpa using K.fill_spec Λ (i := 3) (by omega) (by omega)

/-- Boundary-aware tetrahedron encoding the already-proved left half of the source
square for `whiskerLeftWhiskerRight`. -/
private def KanComplex.whiskerLeftWhiskerRightMidLeftComparisonTetrahedron
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath d)).toTriangle
      (K.whiskerLeftPath2 α (K.whiskerRightPath2 η δ)).toTriangle
      (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle
      (K.associatorPath2 α β δ).toTriangle :=
  K.tetrahedronComparisonTetrahedron
    (K.whiskerLeftWhiskerRightMidFillerTetrahedron α η δ)
    (K.whiskerLeftTetrahedron α (K.whiskerRightPath2 η δ))
    (K.associatorTetrahedron α β δ)

/-- The left half of the midpoint decomposition is constructive; only the right half
remains open. -/
private def KanComplex.whiskerLeftWhiskerRightMidLeftPath3 (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    K.Path3
      (K.trianglePath2
        (K.associatorPath2 α β δ).toTriangle
        (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle)
      (K.whiskerLeftPath2 α (K.whiskerRightPath2 η δ)) :=
  K.tetrahedronPath3
    (K.triangleComparisonTetrahedron
      (K.associatorPath2 α β δ).toTriangle
      (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle)
    (K.whiskerLeftWhiskerRightMidLeftComparisonTetrahedron α η δ)

/-- Once the midpoint/right comparison is identified, the reduced triangle
comparison for `whiskerLeftWhiskerRight` follows by composing it with the
constructive left half. -/
def KanComplex.whiskerLeftWhiskerRightTriangleComparisonFromMidpointRightComparison
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d)
    (hRight :
      K.Path3
        (K.trianglePath2
          (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle
          (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).toTriangle)
        (K.symmPath2 (K.associatorPath2 α γ δ))) :
    K.Path3
      (K.trianglePath2
        (K.associatorPath2 α β δ).toTriangle
        (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).toTriangle)
      (K.transPath2
        (K.whiskerLeftPath2 α (K.whiskerRightPath2 η δ))
        (K.symmPath2 (K.associatorPath2 α γ δ))) := by
  let Aβ := K.associatorPath2 α β δ
  let M := K.whiskerLeftWhiskerRightMidPath2 α η δ
  let W := K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ
  let L := K.whiskerLeftPath2 α (K.whiskerRightPath2 η δ)
  exact K.transPath3
    (K.trianglePath2TransPath3 Aβ.toTriangle M.toTriangle W.toTriangle)
    (K.transPath3
      (K.transCongrRightPath3
        (K.trianglePath2 Aβ.toTriangle M.toTriangle)
        hRight)
      (K.transCongrLeftPath3
        (K.whiskerLeftWhiskerRightMidLeftPath3 α η δ)
        (K.symmPath2 (K.associatorPath2 α γ δ))))

/-- A normalized comparison `M ; symm Aγ ~ W` already suffices to recover the
right half of the midpoint decomposition. -/
private def KanComplex.whiskerLeftWhiskerRightMidRightPath3FromNormalizedComparison
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d)
    (hNorm :
      K.Path3
        (K.transPath2
          (K.whiskerLeftWhiskerRightMidPath2 α η δ)
          (K.symmPath2 (K.associatorPath2 α γ δ)))
        (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ)) :
    K.Path3
      (K.trianglePath2
        (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle
        (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).toTriangle)
      (K.symmPath2 (K.associatorPath2 α γ δ)) := by
  let M := K.whiskerLeftWhiskerRightMidPath2 α η δ
  let A := K.symmPath2 (K.associatorPath2 α γ δ)
  let W := K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ
  have hToTrans :
      K.Path3
        (K.transPath2 M (K.trianglePath2 M.toTriangle W.toTriangle))
        (K.transPath2 M A) := by
    exact K.transPath3
      (K.transFromTriangleComparisonPath3 M W)
      (K.symmPath3 hNorm)
  have hPrep :
      K.Path3
        (K.transPath2 (K.symmPath2 M)
          (K.transPath2 M (K.trianglePath2 M.toTriangle W.toTriangle)))
        (K.transPath2 (K.symmPath2 M) (K.transPath2 M A)) := by
    exact K.transCongrRightPath3 (K.symmPath2 M) hToTrans
  have hLeftSimp :
      K.Path3
        (K.transPath2 (K.symmPath2 M)
          (K.transPath2 M (K.trianglePath2 M.toTriangle W.toTriangle)))
        (K.trianglePath2 M.toTriangle W.toTriangle) := by
    exact K.transPath3
      (K.symmPath3
        (K.transAssocPath3
          (K.symmPath2 M)
          M
          (K.trianglePath2 M.toTriangle W.toTriangle)))
      (K.transPath3
        (K.transCongrLeftPath3
          (K.transLeftCancelPath3 M)
          (K.trianglePath2 M.toTriangle W.toTriangle))
        (K.transReflLeftPath3 (K.trianglePath2 M.toTriangle W.toTriangle)))
  have hRightSimp :
      K.Path3
        (K.transPath2 (K.symmPath2 M) (K.transPath2 M A))
        A := by
    exact K.transPath3
      (K.symmPath3 (K.transAssocPath3 (K.symmPath2 M) M A))
      (K.transPath3
        (K.transCongrLeftPath3 (K.transLeftCancelPath3 M) A)
        (K.transReflLeftPath3 A))
  exact K.transPath3
    (K.symmPath3 hLeftSimp)
    (K.transPath3 hPrep hRightSimp)

/-- The remaining right half can be reduced further to a single boundary-aware
tetrahedron in the normalized `trans`-filler form. -/
private def KanComplex.whiskerLeftWhiskerRightMidRightPath3FromBoundaryTetrahedron
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d)
    (Ω :
      K.Tetrahedron
        (K.reflPath2 (K.reflPath d)).toTriangle
        (K.symmPath2 (K.associatorPath2 α γ δ)).toTriangle
        (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).toTriangle
        (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle) :
    K.Path3
      (K.trianglePath2
        (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle
        (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).toTriangle)
      (K.symmPath2 (K.associatorPath2 α γ δ)) := by
  let M := K.whiskerLeftWhiskerRightMidPath2 α η δ
  let A := K.symmPath2 (K.associatorPath2 α γ δ)
  exact K.whiskerLeftWhiskerRightMidRightPath3FromNormalizedComparison α η δ <|
    K.tetrahedronFace2Path3
      (K.reflPath3 M)
      (K.transFillerTetrahedron M A)
      Ω

/-- The direct Horn[2,0]-filler whose remaining faces are the target symmetry,
the direct right whisker, and the midpoint route. -/
private def KanComplex.whiskerLeftWhiskerRightMidRightHorn (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    Horn K.toSimplicialSet 2 0 :=
  let A := (K.symmPath2 (K.associatorPath2 α γ δ)).toTriangle
  let W := (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).toTriangle
  let M := (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle
  { missing_le := by omega
    facet := fun i _ =>
      if h1 : i = 1 then A.simplex
      else if h2 : i = 2 then W.simplex
      else M.simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases : (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
        omega
      rcases hij_cases with h12 | h13 | h23
      · rcases h12 with ⟨rfl, rfl⟩
        simpa [A, W] using W.face1.trans A.face1.symm
      · rcases h13 with ⟨rfl, rfl⟩
        simpa [A, M] using M.face1.trans A.face2.symm
      · rcases h23 with ⟨rfl, rfl⟩
        simpa [W, M] using M.face2.trans W.face2.symm }

/-- The raw 3-simplex filling the direct Horn[2,0] for the remaining right half
of `whiskerLeftWhiskerRight`. -/
private def KanComplex.whiskerLeftWhiskerRightMidRightSimplex (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    K.Simplex 3 :=
  K.fill (K.whiskerLeftWhiskerRightMidRightHorn α η δ)

/-- The unresolved front loop on `reflPath d` extracted from the direct
Horn[2,0]-filler for the remaining right half. -/
def KanComplex.whiskerLeftWhiskerRightMidRightFrontPath2 (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    K.Path2 (K.reflPath d) (K.reflPath d) := by
  let Λ := K.whiskerLeftWhiskerRightMidRightHorn α η δ
  refine
    { simplex := K.face 2 0 (K.whiskerLeftWhiskerRightMidRightSimplex α η δ)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h1 :
        K.face 2 1 (K.whiskerLeftWhiskerRightMidRightSimplex α η δ) =
          ((K.symmPath2 (K.associatorPath2 α γ δ)).toTriangle).simplex := by
      simpa [KanComplex.whiskerLeftWhiskerRightMidRightSimplex, Λ] using
        (K.fill_spec Λ (i := 1) (by omega) (by omega))
    calc
      K.face 1 0 (K.face 2 0 (K.whiskerLeftWhiskerRightMidRightSimplex α η δ))
          = K.face 1 0 (K.face 2 1 (K.whiskerLeftWhiskerRightMidRightSimplex α η δ)) := by
              symm
              simpa using
                (K.face_face 1 (K.whiskerLeftWhiskerRightMidRightSimplex α η δ)
                  (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 1 0 ((K.symmPath2 (K.associatorPath2 α γ δ)).toTriangle).simplex := by
            rw [h1]
      _ = (K.reflPath d).simplex := (K.symmPath2 (K.associatorPath2 α γ δ)).face0
  · have h2 :
        K.face 2 2 (K.whiskerLeftWhiskerRightMidRightSimplex α η δ) =
          ((K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).toTriangle).simplex := by
      simpa [KanComplex.whiskerLeftWhiskerRightMidRightSimplex, Λ] using
        (K.fill_spec Λ (i := 2) (by omega) (by omega))
    calc
      K.face 1 1 (K.face 2 0 (K.whiskerLeftWhiskerRightMidRightSimplex α η δ))
          = K.face 1 0 (K.face 2 2 (K.whiskerLeftWhiskerRightMidRightSimplex α η δ)) := by
              symm
              simpa using
                (K.face_face 1 (K.whiskerLeftWhiskerRightMidRightSimplex α η δ)
                  (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 1 0
            ((K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).toTriangle).simplex := by
              rw [h2]
      _ = (K.reflPath d).simplex :=
            (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).face0
  · have h3 :
        K.face 2 3 (K.whiskerLeftWhiskerRightMidRightSimplex α η δ) =
          (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle.simplex := by
      simpa [KanComplex.whiskerLeftWhiskerRightMidRightSimplex, Λ] using
        (K.fill_spec Λ (i := 3) (by omega) (by omega))
    calc
      K.face 1 2 (K.face 2 0 (K.whiskerLeftWhiskerRightMidRightSimplex α η δ))
          = K.face 1 0 (K.face 2 3 (K.whiskerLeftWhiskerRightMidRightSimplex α η δ)) := by
              symm
              simpa using
                (K.face_face 1 (K.whiskerLeftWhiskerRightMidRightSimplex α η δ)
                  (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 1 0 (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle.simplex := by
            rw [h3]
      _ = (K.reflPath d).simplex :=
            (K.whiskerLeftWhiskerRightMidPath2 α η δ).face0

/-- The direct Horn[2,0]-filler already packages the three desired non-front
faces for the right half of `whiskerLeftWhiskerRight`. -/
private def KanComplex.whiskerLeftWhiskerRightMidRightCandidateTetrahedron
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    K.Tetrahedron
      (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ).toTriangle
      (K.symmPath2 (K.associatorPath2 α γ δ)).toTriangle
      (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).toTriangle
      (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle := by
  let Λ := K.whiskerLeftWhiskerRightMidRightHorn α η δ
  refine
    { simplex := K.whiskerLeftWhiskerRightMidRightSimplex α η δ
      face0 := rfl
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · simpa [KanComplex.whiskerLeftWhiskerRightMidRightSimplex, Λ] using
      (K.fill_spec Λ (i := 1) (by omega) (by omega))
  · simpa [KanComplex.whiskerLeftWhiskerRightMidRightSimplex, Λ] using
      (K.fill_spec Λ (i := 2) (by omega) (by omega))
  · simpa [KanComplex.whiskerLeftWhiskerRightMidRightSimplex, Λ] using
      (K.fill_spec Λ (i := 3) (by omega) (by omega))

/-- Contracting the direct front loop suffices to recover the reduced right-half
comparison for `whiskerLeftWhiskerRight`. -/
def KanComplex.whiskerLeftWhiskerRightMidRightPath3OfFrontPath3
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d)
    (frontContract :
      K.Path3
        (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ)
        (K.reflPath2 (K.reflPath d))) :
    K.Path3
      (K.trianglePath2
        (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle
        (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).toTriangle)
      (K.symmPath2 (K.associatorPath2 α γ δ)) := by
  let A := K.symmPath2 (K.associatorPath2 α γ δ)
  let W := K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ
  let M := K.whiskerLeftWhiskerRightMidPath2 α η δ
  exact K.symmPath3 <|
    K.tetrahedronFrontPath3 frontContract
      (K.whiskerLeftWhiskerRightMidRightCandidateTetrahedron α η δ)
      (K.triangleComparisonTetrahedron M.toTriangle W.toTriangle)

/-- A contraction of the direct WLWR front loop reconstructs the exact boundary
tetrahedron `Ω` needed by the older normalized right-half reduction. -/
private def KanComplex.whiskerLeftWhiskerRightBoundaryTetrahedronFromFrontPath3
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d)
    (frontContract :
      K.Path3
        (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ)
        (K.reflPath2 (K.reflPath d))) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath d)).toTriangle
      (K.symmPath2 (K.associatorPath2 α γ δ)).toTriangle
      (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).toTriangle
      (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle := by
  let M := K.whiskerLeftWhiskerRightMidPath2 α η δ
  let W := K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ
  let hRight := K.whiskerLeftWhiskerRightMidRightPath3OfFrontPath3 α η δ frontContract
  exact K.tetrahedronReplaceFace1 hRight
    (K.triangleComparisonTetrahedron M.toTriangle W.toTriangle)

/-- The weaker front contraction to `symm (refl (refl d))` already suffices to
recover the WLWR boundary tetrahedron, via the standard bridge from
`symm (refl)` back to `refl`. -/
private def KanComplex.whiskerLeftWhiskerRightBoundaryTetrahedronFromSymmFrontPath3
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d)
    (frontContract :
      K.Path3
        (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ)
        (K.symmPath2 (K.reflPath2 (K.reflPath d)))) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath d)).toTriangle
      (K.symmPath2 (K.associatorPath2 α γ δ)).toTriangle
      (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).toTriangle
      (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle := by
  have frontToRefl :
      K.Path3
        (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ)
        (K.reflPath2 (K.reflPath d)) :=
    K.transPath3 frontContract
      ((K.symmReflPath2BridgeTetrahedron (K.reflPath d)).toPath3)
  exact K.whiskerLeftWhiskerRightBoundaryTetrahedronFromFrontPath3 α η δ
    frontToRefl

/-- Once the reduced triangle comparison for right whiskering a left whisker is
identified, the full associator/interchange comparison follows by re-extending
along the left associator at `(α, β, δ)`. -/
def KanComplex.whiskerLeftWhiskerRightPath3FromTriangleComparison
    (K : KanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d)
    (hTri :
      K.Path3
        (K.trianglePath2
          (K.associatorPath2 α β δ).toTriangle
          (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).toTriangle)
        (K.transPath2
          (K.whiskerLeftPath2 α (K.whiskerRightPath2 η δ))
          (K.symmPath2 (K.associatorPath2 α γ δ)))) :
    K.Path3
      (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ)
      (K.transPath2
        (K.associatorPath2 α β δ)
        (K.transPath2
          (K.whiskerLeftPath2 α (K.whiskerRightPath2 η δ))
          (K.symmPath2 (K.associatorPath2 α γ δ)))) := by
  let Aβ := K.associatorPath2 α β δ
  let W := K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ
  exact K.transPath3
    (K.symmPath3 (K.transFromTriangleComparisonPath3 Aβ W))
    (K.transCongrRightPath3 Aβ hTri)

/-- First corrected pentagon step-1 tetrahedron: it uses the directly whiskered
front route and the directly whiskered back route, postponing normalization to
the scratch `χ`-front and canonical right-back triangle to separate comparison
steps. -/
private def KanComplex.pentagonStep1CoreTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.pentagonWhiskerFrontPath2 q r s).toTriangle
      (K.whiskerRightPath2 (K.associatorPath2 p q r) s).toTriangle
      (K.assocTriangle p (K.compPath q r) s)
      (K.pentagonInnerBackTriangle p q r s) := by
  let ε :=
    K.triangleComparisonTetrahedron
      (K.whiskerLeftCompTriangle q r s)
      (K.compTriangle (K.compPath q r) s)
  let ω₁ := K.whiskerRightTetrahedron (K.associatorPath2 p q r) s
  let ω₂ := K.assocTriangleFillerTetrahedron p (K.compPath q r) s
  let κ := K.pentagonInnerBackFillerTetrahedron p q r s
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h3 : i = 3 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ε.simplex := by rw [h0]
      _ = (K.pentagonWhiskerFrontPath2 q r s).toTriangle.simplex := ε.face1
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h1]
      _ = (K.whiskerRightPath2 (K.associatorPath2 p q r) s).toTriangle.simplex := ω₁.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h3]
      _ = (K.assocTriangle p (K.compPath q r) s).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h4]
      _ = (K.pentagonInnerBackTriangle p q r s).simplex := κ.face2

/-- The front-normalized pentagon step-1 tetrahedron: it replaces the whiskered
front comparison by the ordinary front comparison while keeping the same
whiskered middle face and inner back face. -/
private def KanComplex.pentagonStep1BoundaryCoreTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.trianglePath2
        (K.compTriangle q (K.compPath r s))
        (K.assocTriangle q r s)).toTriangle
      (K.whiskerRightPath2 (K.associatorPath2 p q r) s).toTriangle
      (K.assocTriangle p (K.compPath q r) s)
      (K.pentagonInnerBackTriangle p q r s) := by
  let ε := K.pentagonFrontComparisonTetrahedron q r s
  let ω₁ := K.whiskerRightTetrahedron (K.associatorPath2 p q r) s
  let ω₂ := K.assocTriangleFillerTetrahedron p (K.compPath q r) s
  let κ := K.pentagonInnerBackFillerTetrahedron p q r s
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h3 : i = 3 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ε.simplex := by rw [h0]
      _ =
        (K.trianglePath2
          (K.compTriangle q (K.compPath r s))
          (K.assocTriangle q r s)).toTriangle.simplex := ε.face1
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h1]
      _ = (K.whiskerRightPath2 (K.associatorPath2 p q r) s).toTriangle.simplex := ω₁.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h3]
      _ = (K.assocTriangle p (K.compPath q r) s).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h4]
      _ = (K.pentagonInnerBackTriangle p q r s).simplex := κ.face2

/-- Corrected pentagon step-1/2 tetrahedron: after the first whiskered step, it
adds the associator on `(p, q·r, s)` while keeping the directly whiskered front
and back routes. -/
private def KanComplex.pentagonStep12CoreTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.pentagonWhiskerFrontPath2 q r s).toTriangle
      (K.transPath2
        (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
        (K.associatorPath2 p (K.compPath q r) s)).toTriangle
      (K.compTriangle p (K.compPath (K.compPath q r) s))
      (K.pentagonInnerBackTriangle p q r s) := by
  let ε := K.reflTriangleTetrahedron ((K.pentagonWhiskerFrontPath2 q r s).toTriangle)
  let ω₁ := K.transFillerTetrahedron
    (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
    (K.associatorPath2 p (K.compPath q r) s)
  let ω₂ := K.associatorTetrahedron p (K.compPath q r) s
  let κ := K.pentagonStep1CoreTetrahedron p q r s
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h2 : i = 2 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using κ.face2.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ε.simplex := by rw [h0]
      _ = (K.pentagonWhiskerFrontPath2 q r s).toTriangle.simplex := ε.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₁.simplex := by rw [h1]
      _ =
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s)).toTriangle.simplex := ω₁.face2
  · have h2 : K.face 3 2 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h2]
      _ = (K.compTriangle p (K.compPath (K.compPath q r) s)).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 κ.simplex := by rw [h4]
      _ = (K.pentagonInnerBackTriangle p q r s).simplex := κ.face3

/-- Boundary-aware step-1/2 tetrahedron with the normalized front face and the
inner back face still explicit. -/
private def KanComplex.pentagonStep12BoundaryCoreTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.trianglePath2
        (K.compTriangle q (K.compPath r s))
        (K.assocTriangle q r s)).toTriangle
      (K.transPath2
        (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
        (K.associatorPath2 p (K.compPath q r) s)).toTriangle
      (K.compTriangle p (K.compPath (K.compPath q r) s))
      (K.pentagonInnerBackTriangle p q r s) := by
  let ε := K.reflTriangleTetrahedron
    ((K.trianglePath2
      (K.compTriangle q (K.compPath r s))
      (K.assocTriangle q r s)).toTriangle)
  let ω₁ := K.transFillerTetrahedron
    (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
    (K.associatorPath2 p (K.compPath q r) s)
  let ω₂ := K.associatorTetrahedron p (K.compPath q r) s
  let κ := K.pentagonStep1BoundaryCoreTetrahedron p q r s
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h2 : i = 2 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using κ.face2.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ε.simplex := by rw [h0]
      _ =
        (K.trianglePath2
          (K.compTriangle q (K.compPath r s))
          (K.assocTriangle q r s)).toTriangle.simplex := ε.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₁.simplex := by rw [h1]
      _ =
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s)).toTriangle.simplex := ω₁.face2
  · have h2 : K.face 3 2 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h2]
      _ = (K.compTriangle p (K.compPath (K.compPath q r) s)).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 κ.simplex := by rw [h4]
      _ = (K.pentagonInnerBackTriangle p q r s).simplex := κ.face3

/-- Boundary-aware step-1/2/3 tetrahedron: the front is now normalized all the
way to the reflexive 2-cell on `q · (r · s)`, and the only remaining noncanonical
face is the directly whiskered inner back triangle. -/
def KanComplex.pentagonStep123BoundaryCoreTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
      (K.compTriangle p (K.compPath q (K.compPath r s)))
      (K.pentagonInnerBackTriangle p q r s) := by
  let ε := K.pentagonFrontBridgeTetrahedron q r s
  let ω₁ := K.transFillerTetrahedron
    (K.transPath2
      (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
      (K.associatorPath2 p (K.compPath q r) s))
    (K.whiskerLeftPath2 p (K.associatorPath2 q r s))
  let ω₂ := K.whiskerLeftTetrahedron p (K.associatorPath2 q r s)
  let κ := K.pentagonStep12BoundaryCoreTetrahedron p q r s
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h2 : i = 2 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using κ.face2.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ε.simplex := by rw [h0]
      _ = (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle.simplex := ε.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₁.simplex := by rw [h1]
      _ =
        (K.transPath2
          (K.transPath2
            (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
            (K.associatorPath2 p (K.compPath q r) s))
          (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle.simplex := ω₁.face2
  · have h2 : K.face 3 2 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h2]
      _ = (K.compTriangle p (K.compPath q (K.compPath r s))).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 κ.simplex := by rw [h4]
      _ = (K.pentagonInnerBackTriangle p q r s).simplex := κ.face3

/-- Canonical right boundary for the left-associated composite side of the
pentagon: it already has the reflexive front and chosen right-back face, but it
stops before comparing against the whiskered-right route. -/
def KanComplex.pentagonRightBoundaryCoreTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s))).toTriangle
      (K.compTriangle p (K.compPath q (K.compPath r s)))
      (K.pentagonRightBackTriangle p q r s) := by
  let ε := K.reflTriangleTetrahedron
    ((K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle)
  let ω₁ := K.transFillerTetrahedron
    (K.associatorPath2 (K.compPath p q) r s)
    (K.associatorPath2 p q (K.compPath r s))
  let ω₂ := K.associatorTetrahedron p q (K.compPath r s)
  let κ := K.pentagonBackComparisonTetrahedron p q r s
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h2 : i = 2 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using κ.face2.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ε.simplex := by rw [h0]
      _ = (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle.simplex := ε.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₁.simplex := by rw [h1]
      _ =
        (K.transPath2
          (K.associatorPath2 (K.compPath p q) r s)
          (K.associatorPath2 p q (K.compPath r s))).toTriangle.simplex := ω₁.face2
  · have h2 : K.face 3 2 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h2]
      _ = (K.compTriangle p (K.compPath q (K.compPath r s))).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 κ.simplex := by rw [h4]
      _ = (K.pentagonRightBackTriangle p q r s).simplex := κ.face3

/-- Boundary-aware tetrahedron comparing a vertical composite with the symmetry of
its right factor, while keeping the left factor explicit on the boundary. -/
private def KanComplex.transPath2SymmBoundaryTetrahedron (K : KanComplex)
    {a b : K.Obj} {p q r : K.PathSpace a b}
    (α : K.Path2 p q) (β : K.Path2 q r) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath b)).toTriangle
      (K.symmPath2 β).toTriangle
      α.toTriangle
      (K.transPath2 α β).toTriangle := by
  let ε := K.reflTriangleTetrahedron ((K.reflPath2 (K.reflPath b)).toTriangle)
  let ω₁ := K.symmTetrahedron β
  let ω₂ := K.reflTriangleTetrahedron α.toTriangle
  let κ := K.transFillerTetrahedron α β
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h3 : i = 3 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ε.simplex := by rw [h0]
      _ = (K.reflPath2 (K.reflPath b)).toTriangle.simplex := ε.face1
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h1]
      _ = (K.symmPath2 β).toTriangle.simplex := ω₁.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h3]
      _ = α.toTriangle.simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h4]
      _ = (K.transPath2 α β).toTriangle.simplex := κ.face2

/-- Boundary-aware tetrahedron relating the symmetry of a composite to the
symmetries of its factors. -/
private def KanComplex.symmTransBoundaryTetrahedron (K : KanComplex)
    {a b : K.Obj} {p q r : K.PathSpace a b}
    (α : K.Path2 p q) (β : K.Path2 q r) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath b)).toTriangle
      (K.symmPath2 α).toTriangle
      (K.symmPath2 (K.transPath2 α β)).toTriangle
      (K.symmPath2 β).toTriangle := by
  let ε := K.reflTriangleTetrahedron ((K.reflPath2 (K.reflPath b)).toTriangle)
  let ω₁ := K.symmTetrahedron α
  let ω₂ := K.symmTetrahedron (K.transPath2 α β)
  let κ := K.transPath2SymmBoundaryTetrahedron α β
  let Λ : Horn K.toSimplicialSet 3 1 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h2 : i = 2 then ω₁.simplex
        else if h3 : i = 3 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h02 | hrest
        · rcases h02 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face1.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h23 | hrest
              · rcases h23 with ⟨rfl, rfl⟩
                simpa using ω₂.face2.trans ω₁.face2.symm
              · rcases hrest with h24 | h34
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using κ.face2.trans ω₁.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 1 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 1 (K.fill Λ))
          = K.face 2 0 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 2 0 ε.simplex := by rw [h0]
      _ = (K.reflPath2 (K.reflPath b)).toTriangle.simplex := ε.face0
  · have h2 : K.face 3 2 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 2 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h2]
      _ = (K.symmPath2 α).toTriangle.simplex := ω₁.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 1 ω₂.simplex := by rw [h3]
      _ = (K.symmPath2 (K.transPath2 α β)).toTriangle.simplex := ω₂.face1
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 1 (K.fill Λ))
          = K.face 2 1 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 3) (by omega) (by omega))
       _ = K.face 2 1 κ.simplex := by rw [h4]
       _ = (K.symmPath2 β).toTriangle.simplex := κ.face1

/-- The symmetry of a vertical composite agrees, up to a semantic 3-cell, with
the vertical composite of the symmetries of its factors in reverse order. -/
def KanComplex.symmTransPath3 (K : KanComplex) {a b : K.Obj}
    {p q r : K.PathSpace a b} (α : K.Path2 p q) (β : K.Path2 q r) :
    K.Path3
      (K.symmPath2 (K.transPath2 α β))
      (K.transPath2 (K.symmPath2 β) (K.symmPath2 α)) :=
  K.tetrahedronFace2Path3 (K.reflPath3 (K.symmPath2 β))
    (K.symmTransBoundaryTetrahedron α β)
    (K.transFillerTetrahedron (K.symmPath2 β) (K.symmPath2 α))

/-- Boundary-aware tetrahedron fixing the source-degenerate front face while
comparing right whiskering of a composite against the first whiskering step. -/
private def KanComplex.whiskerRightTransTriangleBoundaryTetrahedron (K : KanComplex)
    {a b c : K.Obj} {p q s : K.PathSpace a b}
    (α : K.Path2 p q) (β : K.Path2 q s) (r : K.PathSpace b c) :
    K.Tetrahedron
      (K.sourceDegenerateTriangle r)
      (K.whiskerRightTriangle α r)
      (K.whiskerRightTriangle (K.transPath2 α β) r)
      (K.symmPath2 β).toTriangle := by
  let ρ := K.sourceDegenerateTriangleDegenerateTetrahedron r
  let ω₁ := K.whiskerRightTriangleFillerTetrahedron α r
  let ω₂ := K.whiskerRightTriangleFillerTetrahedron (K.transPath2 α β) r
  let κ := K.symmTransBoundaryTetrahedron α β
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ρ.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h2 : i = 2 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ρ.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ρ.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ρ.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using κ.face2.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ρ.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ρ.simplex := by rw [h0]
      _ = (K.sourceDegenerateTriangle r).simplex := ρ.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₁.simplex := by rw [h1]
      _ = (K.whiskerRightTriangle α r).simplex := ω₁.face2
  · have h2 : K.face 3 2 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h2]
      _ = (K.whiskerRightTriangle (K.transPath2 α β) r).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 κ.simplex := by rw [h4]
      _ = (K.symmPath2 β).toTriangle.simplex := κ.face3

/-- Boundary-aware tetrahedron comparing the triangle bridge above with the
normalized right-whisker tetrahedron. -/
private def KanComplex.whiskerRightTransComparisonTetrahedron (K : KanComplex)
    {a b c : K.Obj} {p q s : K.PathSpace a b}
    (α : K.Path2 p q) (β : K.Path2 q s) (r : K.PathSpace b c) :
    K.Tetrahedron
      (K.reflPath2 r).toTriangle
      (K.whiskerRightPath2 α r).toTriangle
      (K.whiskerRightTriangle β r)
      (K.whiskerRightTriangle (K.transPath2 α β) r) := by
  let ε := K.reflTriangleTetrahedron (K.sourceDegenerateTriangle r)
  let ω₁ := K.whiskerRightTetrahedron α r
  let ω₂ := K.whiskerRightTriangleFillerTetrahedron β r
  let κ := K.whiskerRightTransTriangleBoundaryTetrahedron α β r
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h3 : i = 3 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ε.simplex := by rw [h0]
      _ = (K.reflPath2 r).toTriangle.simplex := ε.face1
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h1]
      _ = (K.whiskerRightPath2 α r).toTriangle.simplex := ω₁.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h3]
      _ = (K.whiskerRightTriangle β r).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h4]
      _ = (K.whiskerRightTriangle (K.transPath2 α β) r).simplex := κ.face2

/-- Right whiskering commutes with vertical composition up to a semantic 3-cell. -/
def KanComplex.whiskerRightTransPath3 (K : KanComplex) {a b c : K.Obj}
    {p q s : K.PathSpace a b}
    (α : K.Path2 p q) (β : K.Path2 q s) (r : K.PathSpace b c) :
    K.Path3
      (K.whiskerRightPath2 (K.transPath2 α β) r)
      (K.transPath2 (K.whiskerRightPath2 α r) (K.whiskerRightPath2 β r)) := by
  let η :
      K.Path3
        (K.trianglePath2
          (K.whiskerRightTriangle (K.transPath2 α β) r)
          (K.whiskerRightTriangle β r))
        (K.whiskerRightPath2 α r) :=
    K.tetrahedronPath3
      (K.triangleComparisonTetrahedron
        (K.whiskerRightTriangle (K.transPath2 α β) r)
        (K.whiskerRightTriangle β r))
      (K.whiskerRightTransComparisonTetrahedron α β r)
  exact K.transPath3
    (K.trianglePath2TransPath3
      (K.whiskerRightTriangle (K.transPath2 α β) r)
      (K.whiskerRightTriangle β r)
      (K.compTriangle s r))
    (K.transCongrLeftPath3 η (K.whiskerRightPath2 β r))

/-- Boundary-aware tetrahedron relating the right-whisker filler for a symmetric
2-cell to the original symmetric back face. -/
private def KanComplex.whiskerRightTriangleSymmBoundaryTetrahedron (K : KanComplex)
    {a b c : K.Obj} {p q : K.PathSpace a b} (α : K.Path2 p q)
    (r : K.PathSpace b c) :
    K.Tetrahedron
      (K.sourceDegenerateTriangle r)
      (K.whiskerRightTriangle (K.symmPath2 α) r)
      (K.compTriangle q r)
      (K.symmPath2 α).toTriangle := by
  let ρ := K.sourceDegenerateTriangleDegenerateTetrahedron r
  let ω₁ := K.whiskerRightTriangleFillerTetrahedron (K.symmPath2 α) r
  let ω₂ := K.compTriangleDegenerateTetrahedron q r
  let κ := K.symmTetrahedron (K.symmPath2 α)
  let Λ : Horn K.toSimplicialSet 3 3 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ρ.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h2 : i = 2 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 4) ∨ (i = 2 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ρ.face0.symm
        · rcases hrest with h02 | hrest
          · rcases h02 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ρ.face1.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ρ.face3.symm
            · rcases hrest with h12 | hrest
              · rcases h12 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face1.symm
              · rcases hrest with h14 | h24
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h24 with ⟨rfl, rfl⟩
                  simpa using κ.face2.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 3 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ρ.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ρ.simplex := by rw [h0]
      _ = (K.sourceDegenerateTriangle r).simplex := ρ.face2
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₁.simplex := by rw [h1]
      _ = (K.whiskerRightTriangle (K.symmPath2 α) r).simplex := ω₁.face2
  · have h2 : K.face 3 2 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 3 (K.fill Λ))
          = K.face 2 2 (K.face 3 2 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h2]
      _ = (K.compTriangle q r).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 3 (K.fill Λ))
          = K.face 2 3 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 3) (j := 3) (by omega) (by omega))
      _ = K.face 2 3 κ.simplex := by rw [h4]
      _ = (K.symmPath2 α).toTriangle.simplex := κ.face3

/-- Boundary-aware tetrahedron comparing right whiskering of a symmetric 2-cell
to the reversed triangle comparison used by right whiskering. -/
private def KanComplex.whiskerRightSymmComparisonTetrahedron (K : KanComplex)
    {a b c : K.Obj} {p q : K.PathSpace a b} (α : K.Path2 p q)
    (r : K.PathSpace b c) :
    K.Tetrahedron
      (K.reflPath2 r).toTriangle
      (K.whiskerRightPath2 (K.symmPath2 α) r).toTriangle
      (K.whiskerRightTriangle α r)
      (K.compTriangle q r) := by
  let ε := K.reflTriangleTetrahedron (K.sourceDegenerateTriangle r)
  let ω₁ := K.whiskerRightTetrahedron (K.symmPath2 α) r
  let ω₂ := K.whiskerRightTriangleFillerTetrahedron α r
  let κ := K.whiskerRightTriangleSymmBoundaryTetrahedron α r
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then ω₁.simplex
        else if h3 : i = 3 then ω₂.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using ω₁.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω₂.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ω₂.face1.trans ω₁.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans ω₁.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω₂.face3.symm }
  refine
    { simplex := K.face 3 2 (K.fill Λ)
      face0 := ?_
      face1 := ?_
      face2 := ?_
      face3 := ?_ }
  · have h0 : K.face 3 0 (K.fill Λ) = ε.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 2 0 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 0 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 0) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ε.simplex := by rw [h0]
      _ = (K.reflPath2 r).toTriangle.simplex := ε.face1
  · have h1 : K.face 3 1 (K.fill Λ) = ω₁.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 ω₁.simplex := by rw [h1]
      _ = (K.whiskerRightPath2 (K.symmPath2 α) r).toTriangle.simplex := ω₁.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω₂.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω₂.simplex := by rw [h3]
      _ = (K.whiskerRightTriangle α r).simplex := ω₂.face2
  · have h4 : K.face 3 4 (K.fill Λ) = κ.simplex :=
      K.fill_spec Λ (i := 4) (by omega) (by omega)
    calc
      K.face 2 3 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 4 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 3) (by omega) (by omega))
      _ = K.face 2 2 κ.simplex := by rw [h4]
      _ = (K.compTriangle q r).simplex := κ.face2

/-- Right whiskering commutes with symmetry up to a semantic 3-cell. -/
def KanComplex.whiskerRightSymmPath3 (K : KanComplex) {a b c : K.Obj}
    {p q : K.PathSpace a b} (α : K.Path2 p q) (r : K.PathSpace b c) :
    K.Path3
      (K.whiskerRightPath2 (K.symmPath2 α) r)
      (K.symmPath2 (K.whiskerRightPath2 α r)) :=
  K.transPath3
    (K.tetrahedronPath3
      (K.whiskerRightSymmComparisonTetrahedron α r)
      (K.triangleComparisonTetrahedron
        (K.compTriangle q r) (K.whiskerRightTriangle α r)))
    (K.trianglePath2SymmPath3
      (K.whiskerRightTriangle α r) (K.compTriangle q r))

private def KanComplex.leftInverseTriangleCandidate (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : K.Triangle (K.coinvPath p) (K.reflPath b) p := by
  let Λ := K.coinvHorn p
  refine
    { simplex := K.coinvSimplex p
      face0 := ?_
      face1 := ?_
      face2 := rfl }
  · simpa [KanComplex.coinvSimplex, Λ] using
      (K.fill_spec Λ (i := 0) (by omega) (by omega))
  · simpa [KanComplex.coinvSimplex, Λ] using
      (K.fill_spec Λ (i := 1) (by omega) (by omega))

private def KanComplex.leftInverseCandidatePath2 (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) :
    K.Path2 (K.compPath (K.coinvPath p) p) (K.reflPath b) :=
  K.symmPath2
    (K.trianglePath2 (K.leftInverseTriangleCandidate p) (K.compTriangle (K.coinvPath p) p))

private def KanComplex.coinvToInvPath2 (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) :
    K.Path2 (K.coinvPath p) (K.invPath p) :=
  let q := K.coinvPath p
  let r := K.invPath p
  K.transPath2
    (K.symmPath2 (K.rightUnitorPath2 q))
    (K.transPath2
      (K.whiskerLeftPath2 q (K.symmPath2 (K.rightInversePath2 p)))
      (K.transPath2
        (K.symmPath2 (K.associatorPath2 q p r))
        (K.transPath2
          (K.whiskerRightPath2 (K.leftInverseCandidatePath2 p) r)
          (K.leftUnitorPath2 r))))

/-- The chosen inverse also contracts on the left, by comparison with a second
outer-horn inverse candidate and uniqueness of inverses up to semantic
2-cells. -/
def KanComplex.leftInversePath2 (K : KanComplex) {a b : K.Obj}
    (p : K.PathSpace a b) : K.Path2 (K.compPath (K.invPath p) p) (K.reflPath b) :=
  K.transPath2
    (K.whiskerRightPath2 (K.symmPath2 (K.coinvToInvPath2 p)) p)
    (K.leftInverseCandidatePath2 p)

def FunctorSpace (K : KanComplex) : Type := K.Obj → K.Obj

/-! ## Reflexive Kan Complexes (Definition 2.7) -/

/-- A reflexive Kan complex (Definition 2.7) is a Kan complex K equipped with:
    - F : K → [K → K] (evaluation/application map)
    - G : [K → K] → K (abstraction map)
    - η-law: F(G(f))(x) = f(x) for all functions f and objects x

    This captures the idea that K has enough structure to interpret λ-abstraction
    and application, with the η-law ensuring that abstracting and then applying
    gives back the original function. -/
structure ReflexiveKanComplex extends KanComplex where
  F : toKanComplex.Obj → FunctorSpace toKanComplex
  G : FunctorSpace toKanComplex → toKanComplex.Obj
  eta : ∀ (f : FunctorSpace toKanComplex) (x : toKanComplex.Obj), F (G f) x = f x

/-! ## Extensional Kan Complexes -/

/-- An extensional Kan complex adds the ε-law to a reflexive Kan complex:
    ε: x = G(F(x)) for all objects x

    This ensures that every object can be recovered from its "function behavior",
    making the model fully extensional. Together with η, this gives us:
    - η: F(G(f)) = f (functions are determined by their graphs)
    - ε: G(F(x)) = x (objects are determined by their function behavior)

    In such models, β-reduction and η-reduction are both sound. -/
structure ExtensionalKanComplex extends ReflexiveKanComplex where
  epsilon : ∀ (x : toReflexiveKanComplex.Obj), x = G (F x)

/-- A strict extensional Kan complex is an extensional Kan complex whose chosen
horn fillers are unique. This is the semantic strengthening that makes the
remaining pentagon coherence axiom-free. -/
structure StrictExtensionalKanComplex extends ExtensionalKanComplex where
  fill_unique : ∀ {n missing : Nat}
      (Λ : Horn toReflexiveKanComplex.toKanComplex.toSimplicialSet n missing)
      (σ : toReflexiveKanComplex.toKanComplex.Simplex (n + 1)),
      (∀ {i : Nat} (_hi : i ≤ n + 1) (hmi : i ≠ missing),
        toReflexiveKanComplex.toKanComplex.face n i σ =
          Λ.facet i hmi) →
      σ = toReflexiveKanComplex.toKanComplex.fill Λ

namespace StrictExtensionalKanComplex

/-- Forget the λ-model structure and retain the underlying strict Kan complex. -/
def toStrictKanComplex (K : StrictExtensionalKanComplex) : StrictKanComplex where
  toKanComplex := K.toReflexiveKanComplex.toKanComplex
  fill_unique := K.fill_unique

end StrictExtensionalKanComplex

/-! ## Application in Kan Complexes (Definition 2.8) -/

def ReflexiveKanComplex.app (K : ReflexiveKanComplex) (a b : K.Obj) : K.Obj :=
  K.F a b

scoped infixl:70 " ·ₖ " => ReflexiveKanComplex.app

/-! ## Interpretation of λ-terms (Definition 2.8) -/

/-- A valuation assigns an object in K to each de Bruijn index.
    ρ(n) gives the interpretation of the variable with index n. -/
def Valuation (K : ReflexiveKanComplex) := Nat → K.Obj

/-- The interpretation function ⟦-⟧ : Term → (Valuation K → K.Obj) (Definition 2.8).

    This gives the denotational semantics of λ-terms in a reflexive Kan complex:
    - ⟦var n⟧ρ = ρ(n)              (variables look up in the valuation)
    - ⟦M N⟧ρ = F(⟦M⟧ρ)(⟦N⟧ρ)       (application uses the F map)
    - ⟦λM⟧ρ = G(f ↦ ⟦M⟧ρ[f/0])    (abstraction uses the G map)

    The key property is that β-reduction is sound when K is reflexive (using η-law),
    and η-reduction is sound when K is extensional (using ε-law). -/
noncomputable def interpret (K : ReflexiveKanComplex) (ρ : Valuation K) : Term → K.Obj
  | Term.var n => ρ n
  | Term.app M N => K.app (interpret K ρ M) (interpret K ρ N)
  | Term.lam M => K.G (fun f => interpret K (fun n => if n = 0 then f else ρ (n - 1)) M)

/-! ## Valuation Update -/

def Valuation.update {K : ReflexiveKanComplex} (ρ : Valuation K) (v : K.Obj) : Valuation K :=
  fun n => if n = 0 then v else ρ (n - 1)

/-! ## Shift and Substitution Lemmas

These are standard de Bruijn properties proven by careful induction
with case analysis on variable indices. -/

/-- Helper: (n : Nat) + (1 : Int) converted back to Nat equals n + 1 -/
private theorem nat_add_one_toNat (n : Nat) : (↑n + (1 : Int)).toNat = n + 1 := by
  have h : (↑n : Int) + 1 = ↑(n + 1) := by omega
  rw [h]
  exact Int.toNat_natCast (n + 1)

/-- General shift lemma: shifting and adjusting valuation preserves interpretation -/
private theorem interpret_shift_aux (K : ReflexiveKanComplex) (M : Term) :
    ∀ (ρ₁ ρ₂ : Valuation K) (c : Nat),
    (∀ n, n < c → ρ₁ n = ρ₂ n) →
    (∀ n, n ≥ c → ρ₁ (n + 1) = ρ₂ n) →
    interpret K ρ₁ (Term.shift 1 c M) = interpret K ρ₂ M := by
  induction M with
  | var n =>
    intro ρ₁ ρ₂ c h_lt h_ge
    simp only [Term.shift, interpret]
    split
    · rename_i h; exact h_lt n h
    · rename_i h_nlt
      have h : n ≥ c := Nat.le_of_not_lt h_nlt
      simp only [nat_add_one_toNat, interpret]
      exact h_ge n h
  | app M₁ M₂ ih₁ ih₂ =>
    intro ρ₁ ρ₂ c h_lt h_ge
    simp only [Term.shift, interpret, ReflexiveKanComplex.app]
    rw [ih₁ ρ₁ ρ₂ c h_lt h_ge, ih₂ ρ₁ ρ₂ c h_lt h_ge]
  | lam M ih =>
    intro ρ₁ ρ₂ c h_lt h_ge
    simp only [Term.shift, interpret]
    congr 1
    funext f
    apply ih
    · intro n hn
      cases n with
      | zero => rfl
      | succ n => simp only [Nat.succ_sub_one]; exact h_lt n (by omega)
    · intro n hn
      cases n with
      | zero => omega
      | succ n => simp only [Nat.succ_sub_one]; exact h_ge n (by omega)

/-- Shifting by 1 at cutoff 0 with extended valuation -/
private theorem interpret_shift1 (K : ReflexiveKanComplex) (N : Term) (ρ : Valuation K) (f : K.Obj) :
    interpret K (fun n => if n = 0 then f else ρ (n - 1)) (Term.shift1 N) =
    interpret K ρ N := by
  apply interpret_shift_aux
  · intro n hn; omega
  · intro n _
    cases n with
    | zero => rfl
    | succ n =>
      have h1 : n + 1 + 1 ≠ 0 := by omega
      have h2 : n + 1 + 1 - 1 = n + 1 := by omega
      simp only [h1, ↓reduceIte, h2]

/-- Generalized substitution lemma -/
private theorem interpret_subst_aux (K : ReflexiveKanComplex) (M : Term) :
    ∀ (N : Term) (ρ : Valuation K) (j : Nat),
    interpret K ρ (Term.subst j N M) =
    interpret K (fun n => if n = j then interpret K ρ N
                          else if n > j then ρ (n - 1)
                          else ρ n) M := by
  induction M with
  | var n =>
    intro N ρ j
    simp only [Term.subst, interpret]
    split
    · rfl
    · split <;> simp only [interpret]
  | app M₁ M₂ ih₁ ih₂ =>
    intro N ρ j
    simp only [Term.subst, interpret, ReflexiveKanComplex.app]
    rw [ih₁, ih₂]
  | lam M ih =>
    intro N ρ j
    simp only [Term.subst, interpret]
    congr 1
    funext g
    let ρ' := fun n => if n = 0 then g else ρ (n - 1)
    rw [ih (Term.shift1 N) ρ' (j + 1)]
    congr 1
    funext n
    cases n with
    | zero =>
      have h1 : ¬(0 = j + 1) := by omega
      have h2 : ¬(0 > j + 1) := by omega
      simp only [if_neg h1, if_neg h2, ↓reduceIte]
      rfl
    | succ n =>
      simp only [Nat.succ_sub_one]
      split
      · rename_i heq
        have hneq : n = j := by omega
        simp only [hneq, ↓reduceIte]
        exact interpret_shift1 K N ρ g
      · split
        · rename_i hne hgt
          have hgt' : n > j := by omega
          have hne' : n ≠ j := by omega
          have hn0 : n ≠ 0 := by omega
          simp only [if_neg hne', if_pos hgt']
          show (if n = 0 then g else ρ (n - 1)) = ρ (n - 1)
          simp only [if_neg hn0]
        · rename_i hne hng
          have hne' : n ≠ j := by omega
          have hng' : ¬(n > j) := by omega
          have hn0 : n + 1 ≠ 0 := by omega
          simp only [if_neg hne', if_neg hng']
          show (if n + 1 = 0 then g else ρ (n + 1 - 1)) = ρ n
          simp only [if_neg hn0, Nat.add_sub_cancel]

/-- The main substitution lemma (fundamental for soundness):

    ⟦M[N/0]⟧ρ = ⟦M⟧(ρ[⟦N⟧ρ/0])

    This states that interpreting a substituted term M[N/0] is the same as
    interpreting M in an updated valuation where variable 0 maps to ⟦N⟧ρ.

    This lemma is critical for proving β-soundness, as it shows that the
    semantic effect of substitution matches the syntactic operation. The
    proof requires careful tracking of de Bruijn indices through shifting
    and substitution operations. -/
theorem interpret_subst (K : ReflexiveKanComplex) (M N : Term) (ρ : Valuation K) :
    interpret K ρ (M[N]) = interpret K (ρ.update (interpret K ρ N)) M := by
  simp only [Term.subst0]
  rw [interpret_subst_aux K M N ρ 0]
  congr 1
  funext n
  simp only [Valuation.update]
  cases n with
  | zero => simp only [↓reduceIte]
  | succ n =>
    have h1 : n + 1 ≠ 0 := by omega
    have h2 : n + 1 > 0 := by omega
    have h3 : n + 1 - 1 = n := by omega
    simp only [if_neg h1, if_pos h2, h3]

/-- Shift lemma for closed terms -/
theorem interpret_shift_closed (K : ReflexiveKanComplex) (M : Term) (ρ : Valuation K) (v : K.Obj)
    (_h : Term.hasFreeVar 0 M = false) :
    interpret K (fun n => if n = 0 then v else ρ (n - 1)) (Term.shift 1 0 M) = interpret K ρ M := by
  apply interpret_shift_aux
  · intro n hn; omega
  · intro n _
    cases n with
    | zero => rfl
    | succ n =>
      have h1 : n + 1 + 1 ≠ 0 := by omega
      have h2 : n + 1 + 1 - 1 = n + 1 := by omega
      simp only [h1, ↓reduceIte, h2]

/-- Helper: (n : Nat) + (-1 : Int) converted to Nat when n ≥ 1 -/
private theorem nat_sub_one_toNat (n : Nat) (h : n ≥ 1) : (↑n + (-1 : Int)).toNat = n - 1 := by
  have h' : (↑n : Int) + (-1) = ↑(n - 1) := by omega
  rw [h']
  exact Int.toNat_natCast (n - 1)

/-- General unshift lemma: unshifting and adjusting valuation preserves interpretation
    when the variable at cutoff is not free -/
theorem interpret_unshift_aux (K : ReflexiveKanComplex) (M : Term) :
    ∀ (ρ₁ ρ₂ : Valuation K) (c : Nat),
    (∀ n, n < c → ρ₁ n = ρ₂ n) →
    (∀ n, n > c → ρ₁ n = ρ₂ (n - 1)) →
    Term.hasFreeVar c M = false →
    interpret K ρ₁ M = interpret K ρ₂ (Term.shift (-1) c M) := by
  induction M with
  | var n =>
    intro ρ₁ ρ₂ c h_lt h_gt hfv
    simp only [Term.hasFreeVar] at hfv
    simp only [Term.shift, interpret]
    by_cases hn : n < c
    · simp only [hn, ↓reduceIte, interpret]
      exact h_lt n hn
    · -- n ≥ c and n ≠ c (from hfv), so n > c
      have hne : n ≠ c := by
        intro heq
        simp only [heq, decide_true, Bool.true_eq_false] at hfv
      have hn_gt : n > c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hn) (Ne.symm hne)
      simp only [hn, ↓reduceIte]
      have hn_ge1 : n ≥ 1 := by omega
      simp only [nat_sub_one_toNat n hn_ge1, interpret]
      exact h_gt n hn_gt
  | app M₁ M₂ ih₁ ih₂ =>
    intro ρ₁ ρ₂ c h_lt h_gt hfv
    simp only [Term.hasFreeVar, Bool.or_eq_false_iff] at hfv
    simp only [Term.shift, interpret, ReflexiveKanComplex.app]
    rw [ih₁ ρ₁ ρ₂ c h_lt h_gt hfv.1, ih₂ ρ₁ ρ₂ c h_lt h_gt hfv.2]
  | lam M ih =>
    intro ρ₁ ρ₂ c h_lt h_gt hfv
    simp only [Term.hasFreeVar] at hfv
    simp only [Term.shift, interpret]
    congr 1
    funext g
    let ρ₁' : Valuation K := fun n => if n = 0 then g else ρ₁ (n - 1)
    let ρ₂' : Valuation K := fun n => if n = 0 then g else ρ₂ (n - 1)
    apply ih ρ₁' ρ₂' (c + 1)
    · -- h_lt for c + 1
      intro n hn
      cases n with
      | zero => rfl
      | succ n =>
        simp only [Nat.succ_sub_one, ρ₁', ρ₂']
        exact h_lt n (by omega)
    · -- h_gt for c + 1
      intro n hn
      cases n with
      | zero => omega
      | succ n =>
        -- n + 1 > c + 1 means n > c, so n ≥ 1 and n > 0
        have hn' : n > c := by omega
        have hn0 : n ≠ 0 := by omega
        simp only [Nat.succ_sub_one, ρ₁', ρ₂', hn0, ↓reduceIte]
        exact h_gt n hn'
    · exact hfv

/-- Unshift lemma for terms without free var 0:
    If var 0 doesn't appear free in M, then interpreting M under an extended
    valuation equals interpreting the unshifted term under the original valuation -/
theorem interpret_unshift (K : ReflexiveKanComplex) (M : Term) (ρ : Valuation K) (f : K.Obj)
    (h : Term.hasFreeVar 0 M = false) :
    interpret K (fun n => if n = 0 then f else ρ (n - 1)) M =
    interpret K ρ (Term.shift (-1) 0 M) := by
  apply interpret_unshift_aux
  · intro n hn; omega
  · intro n hn
    have h1 : n ≠ 0 := by omega
    simp only [h1, ↓reduceIte]
  · exact h

/-! ## The Theory of an Extensional Kan Complex (Definition 2.9) -/

def TheoryEq (K : ExtensionalKanComplex) (M N : Term) : Prop :=
  ∀ (ρ : Valuation K.toReflexiveKanComplex), interpret K.toReflexiveKanComplex ρ M = interpret K.toReflexiveKanComplex ρ N

scoped notation:50 M " =ₖ[" K "] " N => TheoryEq K M N

/-- A proof-relevant semantic 1-conversion between interpreted terms in an
extensional Kan complex. Unlike `TheoryEq`, this keeps an explicit 1-simplex
in the model's path space. -/
def Theory1 (K : ExtensionalKanComplex) (M N : Term) : Sort _ :=
  ∀ (ρ : Valuation K.toReflexiveKanComplex),
    K.PathSpace
      (interpret K.toReflexiveKanComplex ρ M)
      (interpret K.toReflexiveKanComplex ρ N)

/-- Composition of proof-relevant semantic 1-conversions in a fixed model. -/
noncomputable def Theory1.comp (K : ExtensionalKanComplex) {L M N : Term}
    (α : Theory1 K L M) (β : Theory1 K M N) : Theory1 K L N :=
  fun ρ => K.compPath (α ρ) (β ρ)

/-- Inversion of proof-relevant semantic 1-conversions in a fixed model. -/
noncomputable def Theory1.inv (K : ExtensionalKanComplex) {M N : Term}
    (α : Theory1 K M N) : Theory1 K N M :=
  fun ρ => K.invPath (α ρ)

/-- Reflexivity of proof-relevant semantic 1-conversions. -/
noncomputable def Theory1.refl (K : ExtensionalKanComplex) (M : Term) : Theory1 K M M :=
  fun ρ => K.reflPath (interpret K.toReflexiveKanComplex ρ M)

/-- Equality of interpretations induces a proof-relevant semantic 1-conversion. -/
noncomputable def Theory1.ofTheoryEq (K : ExtensionalKanComplex) {M N : Term}
    (h : TheoryEq K M N) : Theory1 K M N := by
  intro ρ
  let x := interpret K.toReflexiveKanComplex ρ M
  let y := interpret K.toReflexiveKanComplex ρ N
  have hxy : x = y := h ρ
  exact
    { simplex := K.degen 0 0 x
      source := K.face_degen0_succ x
      target := by simpa [hxy] using K.face_degen0_eq x }

/-- A proof-relevant semantic 2-conversion between parallel semantic
1-conversions in a fixed extensional Kan complex, represented by actual
2-simplices with the expected boundary. -/
def Theory2 (K : ExtensionalKanComplex) {M N : Term}
    (α β : Theory1 K M N) : Sort _ :=
  ∀ (ρ : Valuation K.toReflexiveKanComplex), K.Path2 (α ρ) (β ρ)

/-- Reflexivity of semantic 2-conversions. -/
noncomputable def Theory2.refl (K : ExtensionalKanComplex) {M N : Term}
    (α : Theory1 K M N) : Theory2 K α α :=
  fun ρ => K.reflPath2 (α ρ)

/-- Symmetry of semantic 2-conversions in a fixed model. -/
noncomputable def Theory2.symm (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} :
    Theory2 K α β → Theory2 K β α
  | η => fun ρ => K.symmPath2 (η ρ)

/-- Vertical composition of semantic 2-conversions in a fixed model. -/
noncomputable def Theory2.trans (K : ExtensionalKanComplex) {M N : Term}
    {α β γ : Theory1 K M N} :
    Theory2 K α β → Theory2 K β γ → Theory2 K α γ
  | η₁, η₂ => fun ρ => K.transPath2 (η₁ ρ) (η₂ ρ)

/-- Left whiskering of semantic 2-conversions by a semantic 1-conversion. -/
noncomputable def Theory2.whiskerLeft (K : ExtensionalKanComplex) {L M N : Term}
    (α : Theory1 K L M) {β γ : Theory1 K M N} :
    Theory2 K β γ → Theory2 K (Theory1.comp K α β) (Theory1.comp K α γ)
  | η => fun ρ => K.whiskerLeftPath2 (α ρ) (η ρ)

/-- Right whiskering of semantic 2-conversions by a semantic 1-conversion. -/
noncomputable def Theory2.whiskerRight (K : ExtensionalKanComplex) {L M N : Term}
    {α β : Theory1 K L M} (η : Theory2 K α β) (γ : Theory1 K M N) :
    Theory2 K (Theory1.comp K α γ) (Theory1.comp K β γ) :=
  fun ρ => K.whiskerRightPath2 (η ρ) (γ ρ)

/-- Horizontal composition of semantic 2-conversions. -/
noncomputable def Theory2.hcomp (K : ExtensionalKanComplex) {L M N : Term}
    {α α' : Theory1 K L M} {β β' : Theory1 K M N}
    (η : Theory2 K α α') (θ : Theory2 K β β') :
    Theory2 K (Theory1.comp K α β) (Theory1.comp K α' β') :=
  Theory2.trans K
    (Theory2.whiskerRight K η β)
    (Theory2.whiskerLeft K α' θ)

/-- Associator for semantic 1-cell composition. -/
noncomputable def Theory2.associator (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (β : Theory1 K M N) (γ : Theory1 K N P) :
    Theory2 K (Theory1.comp K (Theory1.comp K α β) γ)
      (Theory1.comp K α (Theory1.comp K β γ)) :=
  fun ρ => K.associatorPath2 (α ρ) (β ρ) (γ ρ)

/-- Right inverse law for semantic 1-cell composition. -/
noncomputable def Theory2.rightInverse (K : ExtensionalKanComplex) {M N : Term}
    (α : Theory1 K M N) :
    Theory2 K (Theory1.comp K α (Theory1.inv K α)) (Theory1.refl K M) :=
  fun ρ => K.rightInversePath2 (α ρ)

/-- Left inverse law for semantic 1-cell composition. -/
noncomputable def Theory2.leftInverse (K : ExtensionalKanComplex) {M N : Term}
    (α : Theory1 K M N) :
    Theory2 K (Theory1.comp K (Theory1.inv K α) α) (Theory1.refl K N) :=
  fun ρ => K.leftInversePath2 (α ρ)

/-- Left unitor for semantic 1-cell composition. -/
noncomputable def Theory2.leftUnitor (K : ExtensionalKanComplex) {M N : Term}
    (α : Theory1 K M N) : Theory2 K (Theory1.comp K (Theory1.refl K M) α) α :=
  fun ρ => K.leftUnitorPath2 (α ρ)

/-- Right unitor for semantic 1-cell composition. -/
noncomputable def Theory2.rightUnitor (K : ExtensionalKanComplex) {M N : Term}
    (α : Theory1 K M N) : Theory2 K (Theory1.comp K α (Theory1.refl K N)) α :=
  fun ρ => K.rightUnitorPath2 (α ρ)

/-- Equality of semantic 1-conversions induces a semantic 2-conversion. -/
noncomputable def Theory2.ofEq (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} (h : α = β) : Theory2 K α β := by
  cases h
  exact Theory2.refl K α

/-- A proof-relevant semantic triangle between semantic 1-cells in a fixed
extensional Kan complex, represented modelwise by actual 2-simplices. -/
def TheoryTriangle (K : ExtensionalKanComplex) {M₀ M₁ M₂ : Term}
    (α01 : Theory1 K M₀ M₁) (α02 : Theory1 K M₀ M₂) (α12 : Theory1 K M₁ M₂) : Sort _ :=
  ∀ (ρ : Valuation K.toReflexiveKanComplex), K.Triangle (α01 ρ) (α02 ρ) (α12 ρ)

/-- Every semantic 2-cell determines a semantic triangle with degenerate third
side. -/
noncomputable def Theory2.toTriangle (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} (η : Theory2 K α β) :
    TheoryTriangle K α β (Theory1.refl K N) :=
  fun ρ => (η ρ).toTriangle

/-- The chosen composition triangle at the semantic layer. -/
noncomputable def Theory1.compTriangle (K : ExtensionalKanComplex) {L M N : Term}
    (α : Theory1 K L M) (β : Theory1 K M N) :
    TheoryTriangle K α (Theory1.comp K α β) β :=
  fun ρ => K.compTriangle (α ρ) (β ρ)

/-- The chosen source-degenerate triangle at the semantic layer. -/
noncomputable def Theory1.sourceDegenerateTriangle
    (K : ExtensionalKanComplex) {M N : Term} (α : Theory1 K M N) :
    TheoryTriangle K (Theory1.refl K M) α α :=
  fun ρ => K.sourceDegenerateTriangle (α ρ)

/-- The auxiliary semantic triangle behind the associator 2-cell. -/
noncomputable def Theory1.assocTriangle (K : ExtensionalKanComplex)
    {L M N P : Term} (α : Theory1 K L M) (β : Theory1 K M N) (γ : Theory1 K N P) :
    TheoryTriangle K α
      (Theory1.comp K (Theory1.comp K α β) γ)
      (Theory1.comp K β γ) :=
  fun ρ => K.assocTriangle (α ρ) (β ρ) (γ ρ)

/-- The auxiliary semantic triangle behind right whiskering. -/
noncomputable def Theory1.whiskerRightTriangle (K : ExtensionalKanComplex)
    {L M N : Term} {α β : Theory1 K L M} (η : Theory2 K α β) (γ : Theory1 K M N) :
    TheoryTriangle K β (Theory1.comp K α γ) γ :=
  fun ρ => K.whiskerRightTriangle (η ρ) (γ ρ)

/-- A proof-relevant semantic tetrahedron between semantic triangles in a fixed
extensional Kan complex, represented modelwise by actual 3-simplices. -/
def TheoryTetrahedron (K : ExtensionalKanComplex)
    {M₀ M₁ M₂ M₃ : Term}
    {α01 : Theory1 K M₀ M₁} {α02 : Theory1 K M₀ M₂} {α03 : Theory1 K M₀ M₃}
    {α12 : Theory1 K M₁ M₂} {α13 : Theory1 K M₁ M₃} {α23 : Theory1 K M₂ M₃}
    (τ0 : TheoryTriangle K α12 α13 α23)
    (τ1 : TheoryTriangle K α02 α03 α23)
    (τ2 : TheoryTriangle K α01 α03 α13)
    (τ3 : TheoryTriangle K α01 α02 α12) : Sort _ :=
  ∀ (ρ : Valuation K.toReflexiveKanComplex), K.Tetrahedron (τ0 ρ) (τ1 ρ) (τ2 ρ) (τ3 ρ)

/-- Degenerating a semantic triangle along its middle face produces a semantic
tetrahedron whose middle face is the reflexive semantic 2-cell on that middle
edge. -/
noncomputable def TheoryTriangle.reflTetrahedron
    (K : ExtensionalKanComplex) {M₀ M₁ M₂ : Term}
    {α01 : Theory1 K M₀ M₁} {α02 : Theory1 K M₀ M₂} {α12 : Theory1 K M₁ M₂}
    (τ : TheoryTriangle K α01 α02 α12) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K α12))
      (Theory2.toTriangle K (Theory2.refl K α02))
      τ
      τ :=
  fun ρ => K.reflTriangleTetrahedron (τ ρ)

/-- A proof-relevant semantic 3-conversion between parallel semantic
2-conversions in a fixed extensional Kan complex, represented by actual
3-simplices with the expected reflexive outer faces. -/
def Theory3 (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} (η θ : Theory2 K α β) : Sort _ :=
  ∀ (ρ : Valuation K.toReflexiveKanComplex), K.Path3 (η ρ) (θ ρ)

/-- Reflexivity of semantic 3-conversions. -/
def Theory3.refl (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} (η : Theory2 K α β) : Theory3 K η η :=
  fun ρ => K.reflPath3 (η ρ)

/-- Symmetry of semantic 3-conversions in a fixed model. -/
noncomputable def Theory3.symm (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} {η θ : Theory2 K α β} :
    Theory3 K η θ → Theory3 K θ η
  | Γ => fun ρ => K.symmPath3 (Γ ρ)

/-- Vertical composition of semantic 3-conversions in a fixed model. -/
noncomputable def Theory3.trans (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} {η θ ι : Theory2 K α β} :
    Theory3 K η θ → Theory3 K θ ι → Theory3 K η ι
  | Γ, Δ => fun ρ => K.transPath3 (Γ ρ) (Δ ρ)

/-- Equality of semantic 2-conversions induces a semantic 3-conversion. -/
def Theory3.ofEq (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} {η θ : Theory2 K α β} (h : η = θ) :
    Theory3 K η θ := by
  cases h
  exact Theory3.refl K η

/-- Two boundary-aware semantic tetrahedra with the same outer boundary and a
front face coming from a semantic 2-cell induce a semantic 3-cell between
their middle faces. -/
noncomputable def TheoryTetrahedron.path3
    (K : ExtensionalKanComplex) {L M N : Term}
    {ρ : Theory1 K L M} {σ τ : Theory1 K M N} {μ ν : Theory1 K L N}
    {γ : Theory2 K σ τ} {α β : Theory2 K μ ν}
    {τ2 : TheoryTriangle K ρ ν τ} {τ3 : TheoryTriangle K ρ μ σ}
    (Ω₁ : TheoryTetrahedron K (Theory2.toTriangle K γ) (Theory2.toTriangle K α) τ2 τ3)
    (Ω₂ : TheoryTetrahedron K (Theory2.toTriangle K γ) (Theory2.toTriangle K β) τ2 τ3) :
    Theory3 K α β :=
  fun v => K.tetrahedronPath3 (Ω₁ v) (Ω₂ v)

/-- A proof-relevant semantic 3-cell between the front faces of two
boundary-aware tetrahedra with identical remaining boundary induces a semantic
3-cell between their middle faces. -/
noncomputable def TheoryTetrahedron.frontPath3
    (K : ExtensionalKanComplex) {L M N : Term}
    {ρ : Theory1 K L M} {σ τ : Theory1 K M N} {μ ν : Theory1 K L N}
    {γ₁ γ₂ : Theory2 K σ τ} {α β : Theory2 K μ ν}
    {τ2 : TheoryTriangle K ρ ν τ} {τ3 : TheoryTriangle K ρ μ σ}
    (Κ : Theory3 K γ₁ γ₂)
    (Ω₁ : TheoryTetrahedron K (Theory2.toTriangle K γ₁) (Theory2.toTriangle K α) τ2 τ3)
    (Ω₂ : TheoryTetrahedron K (Theory2.toTriangle K γ₂) (Theory2.toTriangle K β) τ2 τ3) :
    Theory3 K α β :=
  fun v => K.tetrahedronFrontPath3 (Κ v) (Ω₁ v) (Ω₂ v)

/-- A proof-relevant semantic 3-cell between the last faces of two
boundary-aware tetrahedra with identical front and middle faces induces a
semantic 3-cell between their second outer faces. -/
noncomputable def TheoryTetrahedron.face2Path3
    (K : ExtensionalKanComplex) {M N : Term}
    {α β γ : Theory1 K M N}
    {η₁ η₂ : Theory2 K α β} {θ : Theory2 K β γ}
    {μ₁ μ₂ : Theory2 K α γ}
    (Κ : Theory3 K η₁ η₂)
    (Ω₁ : TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (Theory1.refl K N)))
      (Theory2.toTriangle K θ)
      (Theory2.toTriangle K μ₁)
      (Theory2.toTriangle K η₁))
    (Ω₂ : TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (Theory1.refl K N)))
      (Theory2.toTriangle K θ)
      (Theory2.toTriangle K μ₂)
      (Theory2.toTriangle K η₂)) :
    Theory3 K μ₁ μ₂ :=
  fun v => K.tetrahedronFace2Path3 (Κ v) (Ω₁ v) (Ω₂ v)

/-- A boundary-aware semantic 4-simplex comparison between tetrahedra with the
same front face and same second outer face, but potentially different last
outer faces. The extracted 3-simplex is still packaged as a semantic
tetrahedron rather than forced into the normalized `Theory3` interface. -/
noncomputable def TheoryTetrahedron.comparison
    (K : ExtensionalKanComplex) {L M N : Term}
    {ρ : Theory1 K L M} {σ τ : Theory1 K M N} {μ ν : Theory1 K L N}
    {γ : Theory2 K σ τ} {α β : Theory2 K μ ν} {δ : Theory2 K μ μ}
    {τ2 : TheoryTriangle K ρ ν τ}
    {τ31 τ32 : TheoryTriangle K ρ μ σ}
    (Ω₁ : TheoryTetrahedron K (Theory2.toTriangle K γ) (Theory2.toTriangle K α) τ2 τ31)
    (Ω₂ : TheoryTetrahedron K (Theory2.toTriangle K γ) (Theory2.toTriangle K β) τ2 τ32)
    (Κ : TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K σ))
      (Theory2.toTriangle K δ)
      τ32 τ31) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (Theory1.refl K N)))
      (Theory2.toTriangle K β)
      (Theory2.toTriangle K α)
      (Theory2.toTriangle K δ) :=
  fun v => K.tetrahedronComparisonTetrahedron (Ω₁ v) (Ω₂ v) (Κ v)

/-- Interchange at the semantic 3-cell layer is immediate from the definition
of semantic horizontal composition. -/
noncomputable def Theory3.interchange (K : ExtensionalKanComplex) {L M N : Term}
    {α α' : Theory1 K L M} {β β' : Theory1 K M N}
    (η : Theory2 K α α') (θ : Theory2 K β β') :
    Theory3 K (Theory2.hcomp K η θ)
      (Theory2.trans K
        (Theory2.whiskerRight K η β)
        (Theory2.whiskerLeft K α' θ)) :=
  Theory3.ofEq K rfl

/-- Alternative interchange at the semantic 3-cell layer: whisker left along
the source edge first, then whisker right along the target edge. -/
noncomputable def Theory3.interchange' (K : ExtensionalKanComplex) {L M N : Term}
    {α α' : Theory1 K L M} {β β' : Theory1 K M N}
    (η : Theory2 K α α') (θ : Theory2 K β β') :
    Theory3 K (Theory2.hcomp K η θ)
      (Theory2.trans K
        (Theory2.whiskerLeft K α θ)
        (Theory2.whiskerRight K η β')) :=
  fun ρ => K.interchangePrimePath3 (η ρ) (θ ρ)

/-- Triangle coherence for semantic 1-cell composition. -/
noncomputable def Theory3.triangle (K : ExtensionalKanComplex) {L M N : Term}
    (α : Theory1 K L M) (β : Theory1 K M N) :
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K α (Theory1.refl K M) β)
        (Theory2.whiskerLeft K α (Theory2.leftUnitor K β)))
      (Theory2.whiskerRight K (Theory2.rightUnitor K α) β) :=
  fun ρ => K.trianglePath3 (α ρ) (β ρ)

/-- Right unitor on a semantic composite is coherently the associator followed
by left whiskering of the right unitor. -/
noncomputable def Theory3.rightUnitorComp (K : ExtensionalKanComplex)
    {L M N : Term} (α : Theory1 K L M) (β : Theory1 K M N) :
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K α β (Theory1.refl K N))
        (Theory2.whiskerLeft K α (Theory2.rightUnitor K β)))
      (Theory2.rightUnitor K (Theory1.comp K α β)) :=
  fun ρ => K.rightUnitorCompPath3 (α ρ) (β ρ)

/-- Left unitor on a semantic composite is coherently the associator followed by
right whiskering of the left unitor. -/
noncomputable def Theory3.leftUnitorComp (K : ExtensionalKanComplex)
    {L M N : Term} (α : Theory1 K L M) (β : Theory1 K M N) :
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K (Theory1.refl K L) α β)
        (Theory2.leftUnitor K (Theory1.comp K α β)))
      (Theory2.whiskerRight K (Theory2.leftUnitor K α) β) :=
  fun ρ => K.leftUnitorCompPath3 (α ρ) (β ρ)

/-- Left unitor is natural with respect to semantic 2-cells. -/
noncomputable def Theory3.leftUnitorNaturality (K : ExtensionalKanComplex)
    {L M : Term} {α β : Theory1 K L M} (η : Theory2 K α β) :
    Theory3 K
      (Theory2.trans K
        (Theory2.whiskerLeft K (Theory1.refl K L) η)
        (Theory2.leftUnitor K β))
      (Theory2.trans K (Theory2.leftUnitor K α) η) :=
  fun ρ => K.leftUnitorNaturalityPath3 (η ρ)

/-- Left and right unitors agree on reflexive semantic 1-cells. -/
noncomputable def Theory3.reflUnitors (K : ExtensionalKanComplex) {M : Term} :
    Theory3 K
      (Theory2.leftUnitor K (Theory1.refl K M))
      (Theory2.rightUnitor K (Theory1.refl K M)) :=
  fun ρ => K.reflUnitorsPath3 (interpret K.toReflexiveKanComplex ρ M)

/-- The modelwise tetrahedron whose middle face is the semantic associator
2-cell. This is the boundary-aware 3-simplex behind `Theory2.associator`. -/
noncomputable def Theory3.associatorTetrahedron
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (β : Theory1 K M N) (γ : Theory1 K N P) :
    ∀ (ρ : Valuation K.toReflexiveKanComplex),
      K.Tetrahedron
        ((Theory2.refl K (Theory1.comp K β γ)) ρ).toTriangle
        ((Theory2.associator K α β γ) ρ).toTriangle
        (K.compTriangle (α ρ) ((Theory1.comp K β γ) ρ))
        (K.assocTriangle (α ρ) (β ρ) (γ ρ))
  | ρ =>
      K.triangleComparisonTetrahedron
        (K.assocTriangle (α ρ) (β ρ) (γ ρ))
        (K.compTriangle (α ρ) ((Theory1.comp K β γ) ρ))

/-- The modelwise tetrahedron whose middle face is left whiskering of a
semantic 2-cell. This keeps the nondegenerate outer faces that are hidden by
the normalized `Theory3` interface. -/
noncomputable def Theory3.whiskerLeftTetrahedron
    (K : ExtensionalKanComplex) {L M N : Term}
    (α : Theory1 K L M) {β γ : Theory1 K M N}
    (η : Theory2 K β γ) :
    ∀ (ρ : Valuation K.toReflexiveKanComplex),
      K.Tetrahedron
        ((η ρ).toTriangle)
        ((Theory2.whiskerLeft K α η) ρ).toTriangle
        (K.compTriangle (α ρ) (γ ρ))
        (K.compTriangle (α ρ) (β ρ))
  | ρ => K.whiskerLeftTetrahedron (α ρ) (η ρ)

/-- Left whiskering is congruent on semantic 3-cells. -/
noncomputable def Theory3.whiskerLeftCongr
    (K : ExtensionalKanComplex) {L M N : Term}
    (α : Theory1 K L M) {β γ : Theory1 K M N}
    {η θ : Theory2 K β γ} (Κ : Theory3 K η θ) :
    Theory3 K (Theory2.whiskerLeft K α η) (Theory2.whiskerLeft K α θ) :=
  TheoryTetrahedron.frontPath3 K Κ
    (Theory3.whiskerLeftTetrahedron K α η)
    (Theory3.whiskerLeftTetrahedron K α θ)

/-- Left whiskering preserves reflexive semantic 2-cells up to semantic
3-cells. -/
noncomputable def Theory3.whiskerLeftRefl
    (K : ExtensionalKanComplex) {L M N : Term}
    (α : Theory1 K L M) (β : Theory1 K M N) :
    Theory3 K (Theory2.whiskerLeft K α (Theory2.refl K β))
      (Theory2.refl K (Theory1.comp K α β)) :=
  TheoryTetrahedron.path3 K
    (Theory3.whiskerLeftTetrahedron K α (Theory2.refl K β))
    (TheoryTriangle.reflTetrahedron K (Theory1.compTriangle K α β))

/-- Left whiskering of an equality-generated semantic 2-cell agrees with the
equality-generated 2-cell on the whiskered semantic 1-cells. -/
noncomputable def Theory3.whiskerLeftOfEq
    (K : ExtensionalKanComplex) {L M N : Term}
    (α : Theory1 K L M) {β γ : Theory1 K M N} (h : β = γ) :
    Theory3 K (Theory2.whiskerLeft K α (Theory2.ofEq K h))
      (Theory2.ofEq K (congrArg (fun δ => Theory1.comp K α δ) h)) := by
  cases h
  exact Theory3.whiskerLeftRefl K α β

/-- If a semantic 2-cell is already connected to an equality-generated target,
left whiskering preserves that comparison and lands on the corresponding
equality-generated whisker. This packages the bookkeeping step that closes many
recursive coherence arguments after the geometric head normalization has been
handled separately. -/
noncomputable def Theory3.whiskerLeftCongrOfEq
    (K : ExtensionalKanComplex) {L M N : Term}
    (α : Theory1 K L M) {β γ : Theory1 K M N}
    {η : Theory2 K β γ} (h : β = γ) :
    Theory3 K η (Theory2.ofEq K h) →
      Theory3 K (Theory2.whiskerLeft K α η)
        (Theory2.ofEq K (congrArg (fun δ => Theory1.comp K α δ) h))
  | Κ =>
      Theory3.trans K
        (Theory3.whiskerLeftCongr K α Κ)
        (Theory3.whiskerLeftOfEq K α h)

/-- Left whiskering commutes with vertical composition up to semantic 3-cells. -/
noncomputable def Theory3.whiskerLeftTrans
    (K : ExtensionalKanComplex) {L M N : Term}
    (α : Theory1 K L M) {β γ δ : Theory1 K M N}
    (η : Theory2 K β γ) (θ : Theory2 K γ δ) :
    Theory3 K
      (Theory2.whiskerLeft K α (Theory2.trans K η θ))
      (Theory2.trans K (Theory2.whiskerLeft K α η) (Theory2.whiskerLeft K α θ)) :=
  fun ρ =>
    K.toReflexiveKanComplex.toKanComplex.whiskerLeftTransPath3
      (α ρ) (η ρ) (θ ρ)

/-- If the reduced triangle comparison for whiskering over a composite is
available pointwise, it lifts to the full semantic associator/whiskering
comparison. -/
noncomputable def Theory3.whiskerLeftComp
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (β : Theory1 K M N) {γ δ : Theory1 K N P}
    (η : Theory2 K γ δ) :
    Theory3 K
      (Theory2.whiskerLeft K (Theory1.comp K α β) η)
      (Theory2.trans K
        (Theory2.associator K α β γ)
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.whiskerLeft K β η))
          (Theory2.symm K (Theory2.associator K α β δ)))) :=
  fun ρ =>
    K.toReflexiveKanComplex.toKanComplex.whiskerLeftCompPath3
      (α ρ) (β ρ) (η ρ)

/-- If the reduced triangle comparison for whiskering over a composite is
available pointwise, it lifts to the full semantic associator/whiskering
comparison. -/
noncomputable def Theory3.whiskerLeftCompFromTriangleComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) (β : Theory1 K M N) {γ δ : Theory1 K N P}
    (η : Theory2 K γ δ)
    (hTri :
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (β ρ) (γ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (K.toReflexiveKanComplex.toKanComplex.compPath (α ρ) (β ρ))
              (η ρ)).toTriangle)
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.transPath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2 (α ρ)
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (β ρ) (η ρ)))
            (K.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (β ρ) (δ ρ))))) :
    Theory3 K
      (Theory2.whiskerLeft K (Theory1.comp K α β) η)
      (Theory2.trans K
        (Theory2.associator K α β γ)
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.whiskerLeft K β η))
          (Theory2.symm K (Theory2.associator K α β δ)))) :=
  fun ρ =>
    K.toReflexiveKanComplex.toKanComplex.whiskerLeftCompPath3FromTriangleComparison
      (α ρ) (β ρ) (η ρ) (hTri ρ)

/-- If the reduced triangle comparison for right whiskering a left whisker is
available pointwise, it lifts to the full semantic associator/interchange
comparison. -/
noncomputable def Theory3.whiskerLeftWhiskerRightFromTriangleComparison
    (K : ExtensionalKanComplex) {L M N P : Term}
    (α : Theory1 K L M) {β γ : Theory1 K M N}
    (η : Theory2 K β γ) (δ : Theory1 K N P)
    (hTri :
      Theory3 K
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toReflexiveKanComplex.toKanComplex.associatorPath2
              (α ρ) (β ρ) (δ ρ)).toTriangle
            (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
              (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
                (α ρ) (η ρ))
              (δ ρ)).toTriangle)
        (fun ρ =>
          K.toReflexiveKanComplex.toKanComplex.transPath2
            (K.toReflexiveKanComplex.toKanComplex.whiskerLeftPath2
              (α ρ)
              (K.toReflexiveKanComplex.toKanComplex.whiskerRightPath2
                (η ρ) (δ ρ)))
            (K.toReflexiveKanComplex.toKanComplex.symmPath2
              (K.toReflexiveKanComplex.toKanComplex.associatorPath2
                (α ρ) (γ ρ) (δ ρ))))) :
    Theory3 K
      (Theory2.whiskerRight K (Theory2.whiskerLeft K α η) δ)
      (Theory2.trans K
        (Theory2.associator K α β δ)
        (Theory2.trans K
          (Theory2.whiskerLeft K α (Theory2.whiskerRight K η δ))
          (Theory2.symm K (Theory2.associator K α γ δ)))) :=
  fun ρ =>
    K.toReflexiveKanComplex.toKanComplex.whiskerLeftWhiskerRightPath3FromTriangleComparison
      (α ρ) (η ρ) (δ ρ) (hTri ρ)

/-- Left whiskering commutes with symmetry up to semantic 3-cells. -/
noncomputable def Theory3.whiskerLeftSymm
    (K : ExtensionalKanComplex) {L M N : Term}
    (α : Theory1 K L M) {β γ : Theory1 K M N}
    (η : Theory2 K β γ) :
    Theory3 K
      (Theory2.whiskerLeft K α (Theory2.symm K η))
      (Theory2.symm K (Theory2.whiskerLeft K α η)) :=
  fun ρ => K.whiskerLeftSymmPath3 (α ρ) (η ρ)

/-- The inverse direction of left-whisker symmetry. -/
noncomputable def Theory3.invWhiskerLeft
    (K : ExtensionalKanComplex) {L M N : Term}
    (α : Theory1 K L M) {β γ : Theory1 K M N}
    (η : Theory2 K β γ) :
    Theory3 K
      (Theory2.symm K (Theory2.whiskerLeft K α η))
      (Theory2.whiskerLeft K α (Theory2.symm K η)) :=
  Theory3.symm K (Theory3.whiskerLeftSymm K α η)

/-- Right whiskering commutes with vertical composition up to semantic 3-cells. -/
noncomputable def Theory3.whiskerRightTrans
    (K : ExtensionalKanComplex) {L M N : Term}
    {α β δ : Theory1 K L M} (η : Theory2 K α β) (θ : Theory2 K β δ)
    (γ : Theory1 K M N) :
    Theory3 K
      (Theory2.whiskerRight K (Theory2.trans K η θ) γ)
      (Theory2.trans K
        (Theory2.whiskerRight K η γ)
        (Theory2.whiskerRight K θ γ)) :=
  fun ρ => K.whiskerRightTransPath3 (η ρ) (θ ρ) (γ ρ)

/-- Right whiskering commutes with symmetry up to semantic 3-cells. -/
noncomputable def Theory3.whiskerRightSymm
    (K : ExtensionalKanComplex) {L M N : Term}
    {α β : Theory1 K L M} (η : Theory2 K α β)
    (γ : Theory1 K M N) :
    Theory3 K
      (Theory2.whiskerRight K (Theory2.symm K η) γ)
      (Theory2.symm K (Theory2.whiskerRight K η γ)) :=
  fun ρ => K.whiskerRightSymmPath3 (η ρ) (γ ρ)

/-- The inverse direction of right-whisker symmetry. -/
noncomputable def Theory3.invWhiskerRight
    (K : ExtensionalKanComplex) {L M N : Term}
    {α β : Theory1 K L M} (η : Theory2 K α β)
    (γ : Theory1 K M N) :
    Theory3 K
      (Theory2.symm K (Theory2.whiskerRight K η γ))
      (Theory2.whiskerRight K (Theory2.symm K η) γ) :=
  Theory3.symm K (Theory3.whiskerRightSymm K η γ)

/-- Right whiskering preserves reflexive semantic 2-cells up to semantic
3-cells. -/
noncomputable def Theory3.whiskerRightRefl
    (K : ExtensionalKanComplex) {L M N : Term}
    (α : Theory1 K L M) (β : Theory1 K M N) :
    Theory3 K (Theory2.whiskerRight K (Theory2.refl K α) β)
      (Theory2.refl K (Theory1.comp K α β)) :=
  fun ρ => K.whiskerRightReflPath3 (α ρ) (β ρ)

/-- Right whiskering of an equality-generated semantic 2-cell agrees with the
equality-generated 2-cell on the whiskered semantic 1-cells. -/
noncomputable def Theory3.whiskerRightOfEq
    (K : ExtensionalKanComplex) {L M N : Term}
    {α β : Theory1 K L M} (h : α = β) (γ : Theory1 K M N) :
    Theory3 K (Theory2.whiskerRight K (Theory2.ofEq K h) γ)
      (Theory2.ofEq K (congrArg (fun δ => Theory1.comp K δ γ) h)) := by
  cases h
  exact Theory3.whiskerRightRefl K α γ

/-- The modelwise tetrahedron whose middle face is right whiskering of a
semantic 2-cell. -/
noncomputable def Theory3.whiskerRightTetrahedron
    (K : ExtensionalKanComplex) {L M N : Term}
    {α β : Theory1 K L M} (η : Theory2 K α β)
    (γ : Theory1 K M N) :
    ∀ (ρ : Valuation K.toReflexiveKanComplex),
      K.Tetrahedron
        ((Theory2.refl K γ) ρ).toTriangle
        ((Theory2.whiskerRight K η γ) ρ).toTriangle
        (K.compTriangle (β ρ) (γ ρ))
        (K.whiskerRightTriangle (η ρ) (γ ρ))
  | ρ => K.whiskerRightTetrahedron (η ρ) (γ ρ)

/-- The modelwise tetrahedron whose middle face is the semantic left unitor
2-cell. -/
noncomputable def Theory3.leftUnitorTetrahedron
    (K : ExtensionalKanComplex) {M N : Term}
    (α : Theory1 K M N) :
    ∀ (ρ : Valuation K.toReflexiveKanComplex),
      K.Tetrahedron
        ((Theory2.refl K α) ρ).toTriangle
        ((Theory2.leftUnitor K α) ρ).toTriangle
        (K.sourceDegenerateTriangle (α ρ))
        (K.compTriangle ((Theory1.refl K M) ρ) (α ρ))
  | ρ => K.leftUnitorTetrahedron (α ρ)

/-- The modelwise tetrahedron whose middle face is the semantic right unitor
2-cell. -/
noncomputable def Theory3.rightUnitorTetrahedron
    (K : ExtensionalKanComplex) {M N : Term}
    (α : Theory1 K M N) :
    ∀ (ρ : Valuation K.toReflexiveKanComplex),
      K.Tetrahedron
        ((Theory2.refl K (Theory1.refl K N)) ρ).toTriangle
        ((Theory2.rightUnitor K α) ρ).toTriangle
        ((Theory2.refl K α) ρ).toTriangle
        (K.compTriangle (α ρ) ((Theory1.refl K N) ρ))
  | ρ => K.rightUnitorTetrahedron (α ρ)

/-- The modelwise tetrahedron filled by the definition of `Theory2.trans`. It
exposes the raw horn filler whose second outer face is the semantic composite,
with the original right and left factors still visible on the remaining
boundary faces. -/
noncomputable def Theory3.transFillerTetrahedron
    (K : ExtensionalKanComplex) {M N : Term}
    {α β γ : Theory1 K M N} (η : Theory2 K α β) (θ : Theory2 K β γ) :
    ∀ (ρ : Valuation K.toReflexiveKanComplex),
      K.Tetrahedron
        ((Theory2.refl K (Theory1.refl K N)) ρ).toTriangle
        (θ ρ).toTriangle
        ((Theory2.trans K η θ) ρ).toTriangle
        (η ρ).toTriangle
  | ρ => K.transFillerTetrahedron (η ρ) (θ ρ)

/-- Vertical composition of semantic 2-cells is congruent in its left argument
up to semantic 3-cells. -/
noncomputable def Theory3.transCongrLeft (K : ExtensionalKanComplex) {M N : Term}
    {α β γ : Theory1 K M N} {η₁ η₂ : Theory2 K α β}
    (Κ : Theory3 K η₁ η₂) (θ : Theory2 K β γ) :
    Theory3 K (Theory2.trans K η₁ θ) (Theory2.trans K η₂ θ) :=
  TheoryTetrahedron.face2Path3 K Κ
    (Theory3.transFillerTetrahedron K η₁ θ)
    (Theory3.transFillerTetrahedron K η₂ θ)

/-- Vertical composition of semantic 2-cells is congruent in its right argument
up to semantic 3-cells. -/
noncomputable def Theory3.transCongrRight (K : ExtensionalKanComplex) {M N : Term}
    {α β γ : Theory1 K M N} (η : Theory2 K α β)
    {θ₁ θ₂ : Theory2 K β γ} (Κ : Theory3 K θ₁ θ₂) :
    Theory3 K (Theory2.trans K η θ₁) (Theory2.trans K η θ₂) :=
  fun ρ => K.transCongrRightPath3 (η ρ) (Κ ρ)

/-- Vertical composition with a reflexive left factor normalizes to the right
factor up to a semantic 3-cell. -/
noncomputable def Theory3.transReflLeft (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} (η : Theory2 K α β) :
    Theory3 K (Theory2.trans K (Theory2.refl K α) η) η :=
  fun ρ => K.transReflLeftPath3 (η ρ)

/-- Vertical composition with a reflexive right factor normalizes to the left
factor up to a semantic 3-cell. The witness is a degenerate tetrahedron formed
by degenerating the source 2-cell along its second face map. -/
noncomputable def Theory3.transReflRight (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} (η : Theory2 K α β) :
    Theory3 K (Theory2.trans K η (Theory2.refl K β)) η :=
  fun ρ => K.transReflRightPath3 (η ρ)

/-- Right composition with a 2-cell followed by its inverse yields the reflexive
2-cell, up to a semantic 3-cell. -/
noncomputable def Theory3.transRightCancel (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} (η : Theory2 K α β) :
    Theory3 K (Theory2.trans K η (Theory2.symm K η)) (Theory2.refl K α) :=
  fun ρ => K.transRightCancelPath3 (η ρ)

/-- Left composition with the inverse of a 2-cell yields the reflexive target
2-cell, up to a semantic 3-cell. -/
noncomputable def Theory3.transLeftCancel (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} (η : Theory2 K α β) :
    Theory3 K (Theory2.trans K (Theory2.symm K η) η) (Theory2.refl K β) :=
  fun ρ => K.transLeftCancelPath3 (η ρ)

/-- Right whiskering preserves left cancellation of a semantic 2-cell. -/
noncomputable def Theory3.whiskerRightLeftCancel
    (K : ExtensionalKanComplex) {L M N : Term}
    {α β : Theory1 K L M} (η : Theory2 K α β) (γ : Theory1 K M N) :
    Theory3 K
      (Theory2.trans K
        (Theory2.whiskerRight K (Theory2.symm K η) γ)
        (Theory2.whiskerRight K η γ))
      (Theory2.refl K (Theory1.comp K β γ)) :=
  Theory3.trans K
    (Theory3.transCongrLeft K (Theory3.whiskerRightSymm K η γ)
      (Theory2.whiskerRight K η γ))
    (Theory3.transLeftCancel K (Theory2.whiskerRight K η γ))

/-- Vertical composition of semantic 2-cells is associative up to semantic
3-cells. -/
noncomputable def Theory3.transAssoc (K : ExtensionalKanComplex) {M N : Term}
    {α β γ δ : Theory1 K M N}
    (η : Theory2 K α β) (θ : Theory2 K β γ) (ι : Theory2 K γ δ) :
    Theory3 K
      (Theory2.trans K (Theory2.trans K η θ) ι)
      (Theory2.trans K η (Theory2.trans K θ ι)) :=
  fun ρ => K.transAssocPath3 (η ρ) (θ ρ) (ι ρ)

/-- The symmetry of a semantic vertical composite agrees with the composite of
the symmetries of its factors in reverse order, up to a semantic 3-cell. -/
noncomputable def Theory3.symmTrans (K : ExtensionalKanComplex) {M N : Term}
    {α β γ : Theory1 K M N} (η : Theory2 K α β) (θ : Theory2 K β γ) :
    Theory3 K (Theory2.symm K (Theory2.trans K η θ))
      (Theory2.trans K (Theory2.symm K θ) (Theory2.symm K η)) :=
  fun ρ => K.symmTransPath3 (η ρ) (θ ρ)

/-- Right-cancel a common semantic right factor from a semantic 3-cell between
two composites. -/
noncomputable def Theory3.transRightCancelCongr (K : ExtensionalKanComplex)
    {M N : Term} {α β γ : Theory1 K M N}
    {η₁ η₂ : Theory2 K α β} (θ : Theory2 K β γ) :
    Theory3 K (Theory2.trans K η₁ θ) (Theory2.trans K η₂ θ) →
      Theory3 K η₁ η₂
  | Κ => by
      exact Theory3.trans K
        (Theory3.symm K (Theory3.transReflRight K η₁))
        (Theory3.trans K
          (Theory3.transCongrRight K η₁
            (Theory3.symm K (Theory3.transRightCancel K θ)))
          (Theory3.trans K
            (Theory3.symm K (Theory3.transAssoc K η₁ θ (Theory2.symm K θ)))
            (Theory3.trans K
              (Theory3.transCongrLeft K Κ (Theory2.symm K θ))
              (Theory3.trans K
                (Theory3.transAssoc K η₂ θ (Theory2.symm K θ))
                (Theory3.trans K
                  (Theory3.transCongrRight K η₂ (Theory3.transRightCancel K θ))
                  (Theory3.transReflRight K η₂))))))

/-- Symmetry is congruent on semantic 3-cells. -/
noncomputable def Theory3.symmCongr (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} {η θ : Theory2 K α β} :
    Theory3 K η θ → Theory3 K (Theory2.symm K η) (Theory2.symm K θ)
  | Κ =>
      Theory3.symm K <|
        Theory3.transRightCancelCongr K η <|
          Theory3.trans K
            (Theory3.transCongrRight K (Theory2.symm K θ) Κ)
            (Theory3.trans K
              (Theory3.transLeftCancel K θ)
              (Theory3.symm K (Theory3.transLeftCancel K η)))

/-- Double symmetry on a semantic 2-cell contracts back to the original 2-cell
up to a semantic 3-cell. -/
noncomputable def Theory3.symmSymm (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} (η : Theory2 K α β) :
    Theory3 K (Theory2.symm K (Theory2.symm K η)) η := by
  let ηss := Theory2.symm K (Theory2.symm K η)
  have h_cancel :
      Theory3 K
        (Theory2.trans K (Theory2.symm K η) η)
        (Theory2.trans K (Theory2.symm K η) ηss) := by
    exact Theory3.trans K
      (Theory3.transLeftCancel K η)
      (Theory3.symm K (Theory3.transRightCancel K (Theory2.symm K η)))
  have h_whisk :
      Theory3 K
        (Theory2.trans K η (Theory2.trans K (Theory2.symm K η) η))
        (Theory2.trans K η (Theory2.trans K (Theory2.symm K η) ηss)) := by
    exact Theory3.transCongrRight K η h_cancel
  have h_assoc :
      Theory3 K
        (Theory2.trans K (Theory2.trans K η (Theory2.symm K η)) η)
        (Theory2.trans K (Theory2.trans K η (Theory2.symm K η)) ηss) := by
    exact Theory3.trans K
      (Theory3.transAssoc K η (Theory2.symm K η) η)
      (Theory3.trans K h_whisk
        (Theory3.symm K (Theory3.transAssoc K η (Theory2.symm K η) ηss)))
  have h_contract :
      Theory3 K
        (Theory2.trans K (Theory2.refl K α) η)
        (Theory2.trans K (Theory2.refl K α) ηss) := by
    exact Theory3.trans K
      (Theory3.symm K
        (Theory3.transCongrLeft K (Theory3.transRightCancel K η) η))
      (Theory3.trans K h_assoc
        (Theory3.transCongrLeft K (Theory3.transRightCancel K η) ηss))
  exact Theory3.trans K
    (Theory3.symm K (Theory3.transReflLeft K ηss))
    (Theory3.trans K
      (Theory3.symm K h_contract)
      (Theory3.transReflLeft K η))

/-- A proof-relevant semantic 4-conversion between parallel semantic
3-conversions in a fixed extensional Kan complex, represented by actual
4-simplices with the expected reflexive outer faces. -/
def Theory4 (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} {η θ : Theory2 K α β} (Γ Δ : Theory3 K η θ) : Sort _ :=
  ∀ (ρ : Valuation K.toReflexiveKanComplex), K.Path4 (Γ ρ) (Δ ρ)

/-- Reflexivity of semantic 4-conversions. -/
def Theory4.refl (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} {η θ : Theory2 K α β}
    (Γ : Theory3 K η θ) : Theory4 K Γ Γ :=
  fun ρ => K.reflPath4 (Γ ρ)

/-- Equality of semantic 3-conversions induces a semantic 4-conversion. -/
def Theory4.ofEq (K : ExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K M N} {η θ : Theory2 K α β}
    {Γ Δ : Theory3 K η θ} (h : Γ = Δ) : Theory4 K Γ Δ := by
  cases h
  exact Theory4.refl K Γ

theorem Theory1.refl_eq_ofTheoryEq_refl
    (K : ExtensionalKanComplex) (M : Term) :
    Theory1.refl K M = Theory1.ofTheoryEq K (fun _ => rfl) := by
  funext ρ
  rfl

private noncomputable def theoryEqTransTriangle
    (K : ExtensionalKanComplex) {L M N : Term}
    (hLM : TheoryEq K L M) (hMN : TheoryEq K M N)
    (ρ : Valuation K.toReflexiveKanComplex) :
    K.Triangle
      ((Theory1.ofTheoryEq K hLM) ρ)
      ((Theory1.ofTheoryEq K (fun ρ => (hLM ρ).trans (hMN ρ))) ρ)
      ((Theory1.ofTheoryEq K hMN) ρ) := by
  let x := interpret K.toReflexiveKanComplex ρ L
  let y := interpret K.toReflexiveKanComplex ρ M
  let z := interpret K.toReflexiveKanComplex ρ N
  have hxy : x = y := hLM ρ
  have hyz : y = z := hMN ρ
  refine
    { simplex := K.degen 1 0 (K.degen 0 0 x)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · calc
      K.face 1 0 (K.degen 1 0 (K.degen 0 0 x))
          = K.degen 0 0 x := by
              simpa using (K.face_degen_eq 0 (K.degen 0 0 x) (i := 0) (by omega))
      _ = K.degen 0 0 y := by rw [hxy]
      _ = ((Theory1.ofTheoryEq K hMN) ρ).simplex := rfl
  · calc
      K.face 1 1 (K.degen 1 0 (K.degen 0 0 x))
          = K.degen 0 0 x := by
              simpa using (K.face_degen_succ 0 (K.degen 0 0 x) (i := 0) (by omega))
      _ = ((Theory1.ofTheoryEq K (fun ρ => (hLM ρ).trans (hMN ρ))) ρ).simplex := rfl
  · calc
      K.face 1 2 (K.degen 1 0 (K.degen 0 0 x))
          = K.degen 0 0 (K.face 0 1 (K.degen 0 0 x)) := by
              simpa using
                (K.face_degen_gt 0 (K.degen 0 0 x) (i := 2) (j := 0) (by omega) (by omega))
      _ = K.degen 0 0 x := by rw [K.face_degen0_succ x]
      _ = ((Theory1.ofTheoryEq K hLM) ρ).simplex := rfl

/-- Composition of equality-generated semantic 1-conversions is structurally
homotopic to the equality-generated semantic 1-conversion induced by
transitivity of the underlying interpretation equalities. -/
noncomputable def Theory2.ofTheoryEqTrans
    (K : ExtensionalKanComplex) {L M N : Term}
    (hLM : TheoryEq K L M) (hMN : TheoryEq K M N) :
    Theory2 K
      (Theory1.comp K (Theory1.ofTheoryEq K hLM) (Theory1.ofTheoryEq K hMN))
      (Theory1.ofTheoryEq K (fun ρ => (hLM ρ).trans (hMN ρ))) :=
  fun ρ =>
    K.symmPath2
      (K.trianglePath2
        (theoryEqTransTriangle K hLM hMN ρ)
        (K.compTriangle ((Theory1.ofTheoryEq K hLM) ρ) ((Theory1.ofTheoryEq K hMN) ρ)))

/-! ## β-reduction Soundness (Remark 2.1) -/

/-- β-reduction is already sound in a reflexive Kan complex; extensionality is
not needed for the β-law itself. -/
theorem beta_sound_reflexive
    (K : ReflexiveKanComplex) (M N : Term) (ρ : Valuation K) :
    interpret K ρ (Term.app (Term.lam M) N) =
    interpret K ρ (M[N]) := by
  simp only [interpret, ReflexiveKanComplex.app]
  rw [K.eta, interpret_subst]
  rfl

/-- Proposition 2.1 at the equality-based semantic layer used in this
development: the two β-reduction orders for a nested redex have the same
interpretation in every reflexive Kan complex. -/
theorem beta_nested_compat
    (K : ReflexiveKanComplex) (M N P : Term) (ρ : Valuation K) :
    interpret K ρ (M[Term.app (Term.lam N) P]) =
    interpret K ρ (M[N[P]]) := by
  rw [interpret_subst]
  have hβ : interpret K ρ (Term.app (Term.lam N) P) =
      interpret K ρ (N[P]) :=
    beta_sound_reflexive K N P ρ
  rw [hβ]
  rw [← interpret_subst]

/-- β-reduction is sound in extensional Kan complexes (Remark 2.1):

    ⟦(λM)N⟧ρ = ⟦M[N/0]⟧ρ

    This fundamental theorem shows that the β-reduction rule (λx.M)N →β M[N/x]
    preserves meaning in any extensional Kan complex. The proof uses:
    1. The η-law of the reflexive Kan complex: F(G(f)) = f
    2. The substitution lemma: interpret_subst

    This is the semantic justification for β-reduction in homotopic λ-models. -/
theorem beta_sound (K : ExtensionalKanComplex) (M N : Term) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ (Term.app (Term.lam M) N) =
    interpret K.toReflexiveKanComplex ρ (M[N]) := by
  exact beta_sound_reflexive K.toReflexiveKanComplex M N ρ

/-! ## η-reduction Soundness -/

/-- η-reduction is sound in extensional Kan complexes:

    ⟦λx.Mx⟧ρ = ⟦M⟧ρ  (when x ∉ FV(M))

    This theorem shows that the η-reduction rule λx.Mx →η M preserves meaning
    when x is not free in M. The proof uses:
    1. The ε-law (extensionality): x = G(F(x))
    2. The shift lemma for terms without free variable 0

    This requires the full extensionality principle, unlike β-soundness which
    only needs the η-law. This is the semantic justification for η-reduction. -/
theorem eta_sound (K : ExtensionalKanComplex) (M : Term) (ρ : Valuation K.toReflexiveKanComplex)
    (h : Term.hasFreeVar 0 M = false) :
    interpret K.toReflexiveKanComplex ρ (Term.lam (Term.app (Term.shift 1 0 M) (Term.var 0))) =
    interpret K.toReflexiveKanComplex ρ M := by
  simp only [interpret, ReflexiveKanComplex.app]
  have key : ∀ f, interpret K.toReflexiveKanComplex
                    (fun n => if n = 0 then f else ρ (n - 1))
                    (Term.shift 1 0 M) =
                 interpret K.toReflexiveKanComplex ρ M := fun f =>
    interpret_shift_closed K.toReflexiveKanComplex M ρ f h
  simp only [key]
  have simp_if : (fun f => K.F (interpret K.toReflexiveKanComplex ρ M) (if True then f else ρ (0 - 1))) =
                 (fun f => K.F (interpret K.toReflexiveKanComplex ρ M) f) := by funext f; simp
  rw [simp_if]
  exact (K.epsilon (interpret K.toReflexiveKanComplex ρ M)).symm

end HigherLambdaModel.Lambda.ExtensionalKan
