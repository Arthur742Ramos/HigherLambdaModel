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
private def KanComplex.tetrahedronReplaceFace1 (K : KanComplex) {a b c : K.Obj}
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
private def KanComplex.pentagonRightBackTriangle (K : KanComplex)
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
private def KanComplex.pentagonInnerBackTriangle (K : KanComplex)
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
private def KanComplex.pentagonInnerBackComparisonTetrahedron (K : KanComplex)
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
private def KanComplex.pentagonBackComparisonTetrahedron (K : KanComplex)
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
private def KanComplex.pentagonStep123BoundaryCoreTetrahedron (K : KanComplex)
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
private def KanComplex.pentagonRightBoundaryCoreTetrahedron (K : KanComplex)
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

/-- The symmetry of a semantic vertical composite agrees with the composite of
the symmetries of its factors in reverse order, up to a semantic 3-cell. -/
noncomputable def Theory3.symmTrans (K : ExtensionalKanComplex) {M N : Term}
    {α β γ : Theory1 K M N} (η : Theory2 K α β) (θ : Theory2 K β γ) :
    Theory3 K (Theory2.symm K (Theory2.trans K η θ))
      (Theory2.trans K (Theory2.symm K θ) (Theory2.symm K η)) :=
  fun ρ => K.symmTransPath3 (η ρ) (θ ρ)

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

private theorem Theory1.refl_eq_ofTheoryEq_refl
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

/-! ## Homotopy Type-Free Theory (Definition 2.10) -/

/-- Soundness of a single β-step in an extensional Kan complex. -/
theorem betaStep_sound
    (K : ExtensionalKanComplex) (M N : Term)
    (h : BetaStep M N) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M =
    interpret K.toReflexiveKanComplex ρ N := by
  induction h generalizing ρ with
  | beta M N =>
    exact beta_sound K M N ρ
  | appL _ ih =>
    simp only [interpret, ReflexiveKanComplex.app]
    rw [ih]
  | appR _ ih =>
    simp only [interpret, ReflexiveKanComplex.app]
    rw [ih]
  | lam _ ih =>
    simp only [interpret]
    congr 1
    funext f
    exact ih (fun n => if n = 0 then f else ρ (n - 1))

/-- Soundness of a single η-step in an extensional Kan complex. -/
theorem etaStep_sound
    (K : ExtensionalKanComplex) (M N : Term)
    (h : EtaStep M N) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M =
    interpret K.toReflexiveKanComplex ρ N := by
  induction h generalizing ρ with
  | eta M hfv =>
    have h_not_free : Term.hasFreeVar 0 M = false := by
      simp at hfv
      exact hfv
    simp only [interpret, ReflexiveKanComplex.app]
    have key : ∀ f, interpret K.toReflexiveKanComplex
                      (fun n => if n = 0 then f else ρ (n - 1)) M =
                   interpret K.toReflexiveKanComplex ρ (Term.shift (-1) 0 M) := by
      intro f
      exact interpret_unshift K.toReflexiveKanComplex M ρ f h_not_free
    have inner_eq : (fun f => K.F (interpret K.toReflexiveKanComplex
                                     (fun n => if n = 0 then f else ρ (n - 1)) M)
                                   (if True then f else ρ (0 - 1))) =
                    K.F (interpret K.toReflexiveKanComplex ρ (Term.shift (-1) 0 M)) := by
      funext f
      simp only [ite_true, key]
    rw [inner_eq]
    exact (K.epsilon (interpret K.toReflexiveKanComplex ρ (Term.shift (-1) 0 M))).symm
  | appL _ ih =>
    simp only [interpret, ReflexiveKanComplex.app]
    rw [ih]
  | appR _ ih =>
    simp only [interpret, ReflexiveKanComplex.app]
    rw [ih]
  | lam _ ih =>
    simp only [interpret]
    congr 1
    funext f
    exact ih (fun n => if n = 0 then f else ρ (n - 1))

/-- Soundness of a single βη-step in an extensional Kan complex. -/
theorem betaEtaStep_sound
    (K : ExtensionalKanComplex) (M N : Term)
    (h : BetaEtaStep M N) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M =
    interpret K.toReflexiveKanComplex ρ N := by
  cases h with
  | beta hb => exact betaStep_sound K M N hb ρ
  | eta he => exact etaStep_sound K M N he ρ

/-- A single forward βη-step induces a semantic 1-conversion. At present this
basic edge is still obtained from equality soundness and is therefore
degenerate; nontrivial path structure enters when longer paths are composed via
`KanComplex.compPath`. -/
noncomputable def betaEtaStep_in_Theory1
    (K : ExtensionalKanComplex) (M N : Term) (h : BetaEtaStep M N) :
    Theory1 K M N :=
  Theory1.ofTheoryEq K (fun ρ => betaEtaStep_sound K M N h ρ)

/-- A single backward βη-step induces a semantic 1-conversion in the reverse
direction. -/
noncomputable def betaEtaStepInv_in_Theory1
    (K : ExtensionalKanComplex) (M N : Term) (h : BetaEtaStep N M) :
    Theory1 K M N :=
  Theory1.ofTheoryEq K (fun ρ => (betaEtaStep_sound K N M h ρ).symm)

/-- Equality-generated semantic 1-cell corresponding to the endpoint equality in
Proposition 2.1. -/
noncomputable def beta_nested_eq_in_Theory1
    (K : ExtensionalKanComplex) (M N P : Term) :
    Theory1 K (M[Term.app (Term.lam N) P]) (M[N[P]]) :=
  Theory1.ofTheoryEq K (fun ρ => beta_nested_compat K.toReflexiveKanComplex M N P ρ)

/-- Proof-relevant refinement of Proposition 2.1 in a fixed extensional Kan
complex: the outer-first and inner-first β-reduction orders for a nested redex
are related by a semantic 2-cell. -/
noncomputable def beta_nested_compat_in_Theory2
    (K : ExtensionalKanComplex) (M N P : Term) :
    Theory2 K
      (Theory1.comp K
        (betaEtaStep_in_Theory1 K _ _
          (BetaEtaStep.beta (BetaStep.beta M (Term.app (Term.lam N) P))))
        (beta_nested_eq_in_Theory1 K M N P))
      (Theory1.comp K
        (betaEtaStep_in_Theory1 K _ _
          (BetaEtaStep.beta (BetaStep.appR (BetaStep.beta N P))))
        (betaEtaStep_in_Theory1 K _ _
          (BetaEtaStep.beta (BetaStep.beta M (N[P]))))) := by
  let hOuter :
      TheoryEq K (Term.app (Term.lam M) (Term.app (Term.lam N) P))
        (M[Term.app (Term.lam N) P]) :=
    fun ρ =>
      betaEtaStep_sound K _ _
        (BetaEtaStep.beta (BetaStep.beta M (Term.app (Term.lam N) P))) ρ
  let hLeft :
      TheoryEq K (M[Term.app (Term.lam N) P]) (M[N[P]]) :=
    fun ρ => beta_nested_compat K.toReflexiveKanComplex M N P ρ
  let hInner :
      TheoryEq K (Term.app (Term.lam M) (Term.app (Term.lam N) P))
        (Term.app (Term.lam M) (N[P])) :=
    fun ρ =>
      betaEtaStep_sound K _ _
        (BetaEtaStep.beta (BetaStep.appR (BetaStep.beta N P))) ρ
  let hRight :
      TheoryEq K (Term.app (Term.lam M) (N[P])) (M[N[P]]) :=
    fun ρ =>
      betaEtaStep_sound K _ _
        (BetaEtaStep.beta (BetaStep.beta M (N[P]))) ρ
  let hOuterFirst :
      TheoryEq K (Term.app (Term.lam M) (Term.app (Term.lam N) P)) (M[N[P]]) :=
    fun ρ => (hOuter ρ).trans (hLeft ρ)
  let hInnerFirst :
      TheoryEq K (Term.app (Term.lam M) (Term.app (Term.lam N) P)) (M[N[P]]) :=
    fun ρ => (hInner ρ).trans (hRight ρ)
  have hFinalEq : hOuterFirst = hInnerFirst := by
    funext ρ
    exact Subsingleton.elim _ _
  simpa [beta_nested_eq_in_Theory1, hOuter, hLeft, hInner, hRight, hOuterFirst, hInnerFirst] using
    (Theory2.trans K
      (Theory2.ofTheoryEqTrans K hOuter hLeft)
      (Theory2.trans K
        (Theory2.ofEq K
          (congrArg
            (fun h :
              TheoryEq K (Term.app (Term.lam M) (Term.app (Term.lam N) P)) (M[N[P]]) =>
                Theory1.ofTheoryEq K h)
            hFinalEq))
        (Theory2.symm K (Theory2.ofTheoryEqTrans K hInner hRight))))

/-- Every explicit βη path preserves interpretation in every extensional Kan
complex. This connects the proof-relevant higher-path layer directly to the
semantic equality layer. -/
theorem reductionSeq_sound
    (K : ExtensionalKanComplex) {M N : Term}
    (p : ReductionSeq M N) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M =
    interpret K.toReflexiveKanComplex ρ N := by
  induction p generalizing ρ with
  | refl _ =>
    rfl
  | step s rest ih =>
    exact (betaEtaStep_sound K _ _ s ρ).trans (ih ρ)
  | stepInv s rest ih =>
    exact (betaEtaStep_sound K _ _ s ρ).symm.trans (ih ρ)

/-- Equality-generated semantic path interpretation of an explicit βη path.
This auxiliary bridge is used internally to compare the structural path
interpretation with the underlying equality semantics. -/
noncomputable def reductionSeq_eq_in_Theory1
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory1 K M N :=
  Theory1.ofTheoryEq K (fun ρ => reductionSeq_sound K p ρ)

/-- Structural semantic path interpretation of an explicit βη path. Single
steps still interpret to degenerate edges, but longer paths are composed using
the Kan-complex horn-filling operation and therefore need not collapse through
proof irrelevance. -/
noncomputable def reductionSeq_in_Theory1
    (K : ExtensionalKanComplex) {M N : Term} :
    ReductionSeq M N → Theory1 K M N
  | .refl M => fun ρ => K.reflPath (interpret K.toReflexiveKanComplex ρ M)
  | .step s rest => fun ρ =>
      Theory1.comp K (betaEtaStep_in_Theory1 K _ _ s) (reductionSeq_in_Theory1 K rest) ρ
  | .stepInv s rest => fun ρ =>
      Theory1.comp K (betaEtaStepInv_in_Theory1 K _ _ s) (reductionSeq_in_Theory1 K rest) ρ

/-- Any two parallel explicit βη paths induce the same equality-generated
semantic 1-conversion in a fixed model. This uses proof irrelevance at the
equality layer. -/
theorem reductionSeq_eq_in_Theory1_eq
    (K : ExtensionalKanComplex) {M N : Term}
    (p q : ReductionSeq M N) :
    reductionSeq_eq_in_Theory1 K p = reductionSeq_eq_in_Theory1 K q := by
  unfold reductionSeq_eq_in_Theory1
  have hproof :
      (fun ρ => reductionSeq_sound K p ρ) =
      (fun ρ => reductionSeq_sound K q ρ) :=
    Subsingleton.elim _ _
  exact congrArg (Theory1.ofTheoryEq K) hproof

/-- Every explicit βη path is structurally homotopic to its equality-generated
semantic interpretation in a fixed model. -/
noncomputable def reductionSeq_in_eq_in_Theory2
    (K : ExtensionalKanComplex) :
    {M N : Term} → (p : ReductionSeq M N) →
      Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_eq_in_Theory1 K p)
  | _, _, .refl M =>
      Theory2.ofEq K (Theory1.refl_eq_ofTheoryEq_refl K M)
  | _, _, .step s rest =>
      Theory2.trans K
        (Theory2.whiskerLeft K (betaEtaStep_in_Theory1 K _ _ s)
          (reductionSeq_in_eq_in_Theory2 K rest))
        (Theory2.ofTheoryEqTrans K
          (fun ρ => betaEtaStep_sound K _ _ s ρ)
          (fun ρ => reductionSeq_sound K rest ρ))
  | _, _, .stepInv s rest =>
      Theory2.trans K
        (Theory2.whiskerLeft K (betaEtaStepInv_in_Theory1 K _ _ s)
          (reductionSeq_in_eq_in_Theory2 K rest))
        (Theory2.ofTheoryEqTrans K
          (fun ρ => (betaEtaStep_sound K _ _ s ρ).symm)
          (fun ρ => reductionSeq_sound K rest ρ))

def HoTFT_eq (M N : Term) : Prop :=
  ∀ (K : ExtensionalKanComplex), TheoryEq K M N

scoped notation:50 M " =_HoTFT " N => HoTFT_eq M N

/-- Proof-relevant HoTFT 1-conversions: every extensional Kan complex supplies
an explicit semantic 1-simplex between the interpretations of the terms. -/
def HoTFT1 (M N : Term) : Sort _ :=
  ∀ (K : ExtensionalKanComplex), Theory1 K M N

/-- Proof-relevant HoTFT 2-conversions between parallel proof-relevant HoTFT
1-conversions. -/
def HoTFT2 {M N : Term} (α β : HoTFT1 M N) : Sort _ :=
  ∀ (K : ExtensionalKanComplex), Theory2 K (α K) (β K)

/-- Composition of proof-relevant HoTFT 1-conversions, modelwise. -/
noncomputable def HoTFT1.comp {L M N : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) : HoTFT1 L N :=
  fun K => Theory1.comp K (α K) (β K)

/-- Inversion of proof-relevant HoTFT 1-conversions, modelwise. -/
noncomputable def HoTFT1.inv {M N : Term} (α : HoTFT1 M N) : HoTFT1 N M :=
  fun K => Theory1.inv K (α K)

/-- Reflexivity of proof-relevant HoTFT 1-conversions. -/
noncomputable def HoTFT1.refl (M : Term) : HoTFT1 M M :=
  fun K => Theory1.refl K M

/-- Any equality-level HoTFT fact induces a proof-relevant HoTFT 1-conversion. -/
noncomputable def HoTFT1.ofHoTFTEq {M N : Term} (h : HoTFT_eq M N) : HoTFT1 M N :=
  fun K => Theory1.ofTheoryEq K (h K)

/-- A single forward βη-step induces a proof-relevant HoTFT 1-conversion. -/
noncomputable def betaEtaStep_in_HoTFT1 (M N : Term) (h : BetaEtaStep M N) :
    HoTFT1 M N :=
  fun K => betaEtaStep_in_Theory1 K M N h

/-- A single backward βη-step induces a proof-relevant HoTFT 1-conversion. -/
noncomputable def betaEtaStepInv_in_HoTFT1 (M N : Term) (h : BetaEtaStep N M) :
    HoTFT1 M N :=
  fun K => betaEtaStepInv_in_Theory1 K M N h

/-- Reflexivity of proof-relevant HoTFT 2-conversions. -/
noncomputable def HoTFT2.refl {M N : Term} (α : HoTFT1 M N) : HoTFT2 α α :=
  fun K => Theory2.refl K (α K)

/-- Symmetry of proof-relevant HoTFT 2-conversions, modelwise. -/
noncomputable def HoTFT2.symm {M N : Term} {α β : HoTFT1 M N} :
    HoTFT2 α β → HoTFT2 β α
  | η => fun K => Theory2.symm K (η K)

/-- Vertical composition of proof-relevant HoTFT 2-conversions, modelwise. -/
noncomputable def HoTFT2.trans {M N : Term} {α β γ : HoTFT1 M N} :
    HoTFT2 α β → HoTFT2 β γ → HoTFT2 α γ
  | η₁, η₂ => fun K => Theory2.trans K (η₁ K) (η₂ K)

/-- Left whiskering of proof-relevant HoTFT 2-conversions, modelwise. -/
noncomputable def HoTFT2.whiskerLeft {L M N : Term} (α : HoTFT1 L M)
    {β γ : HoTFT1 M N} :
    HoTFT2 β γ → HoTFT2 (HoTFT1.comp α β) (HoTFT1.comp α γ)
  | η => fun K => Theory2.whiskerLeft K (α K) (η K)

/-- Right whiskering of proof-relevant HoTFT 2-conversions, modelwise. -/
noncomputable def HoTFT2.whiskerRight {L M N : Term}
    {α β : HoTFT1 L M} (η : HoTFT2 α β) (γ : HoTFT1 M N) :
    HoTFT2 (HoTFT1.comp α γ) (HoTFT1.comp β γ) :=
  fun K => Theory2.whiskerRight K (η K) (γ K)

/-- A proof-relevant HoTFT triangle, represented modelwise by semantic
triangles. -/
def HoTFTTriangle {M₀ M₁ M₂ : Term}
    (α01 : HoTFT1 M₀ M₁) (α02 : HoTFT1 M₀ M₂) (α12 : HoTFT1 M₁ M₂) : Sort _ :=
  ∀ (K : ExtensionalKanComplex), TheoryTriangle K (α01 K) (α02 K) (α12 K)

/-- Every HoTFT 2-cell determines a HoTFT triangle with degenerate third
side. -/
noncomputable def HoTFT2.toTriangle {M N : Term}
    {α β : HoTFT1 M N} (η : HoTFT2 α β) :
    HoTFTTriangle α β (HoTFT1.refl N) :=
  fun K => Theory2.toTriangle K (η K)

/-- The chosen composition triangle at the HoTFT layer. -/
noncomputable def HoTFT1.compTriangle {L M N : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) :
    HoTFTTriangle α (HoTFT1.comp α β) β :=
  fun K => Theory1.compTriangle K (α K) (β K)

/-- The chosen source-degenerate triangle at the HoTFT layer. -/
noncomputable def HoTFT1.sourceDegenerateTriangle {M N : Term}
    (α : HoTFT1 M N) :
    HoTFTTriangle (HoTFT1.refl M) α α :=
  fun K => Theory1.sourceDegenerateTriangle K (α K)

/-- The auxiliary HoTFT triangle behind the associator 2-cell. -/
noncomputable def HoTFT1.assocTriangle {L M N P : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) (γ : HoTFT1 N P) :
    HoTFTTriangle α
      (HoTFT1.comp (HoTFT1.comp α β) γ)
      (HoTFT1.comp β γ) :=
  fun K => Theory1.assocTriangle K (α K) (β K) (γ K)

/-- The auxiliary HoTFT triangle behind right whiskering. -/
noncomputable def HoTFT1.whiskerRightTriangle {L M N : Term}
    {α β : HoTFT1 L M} (η : HoTFT2 α β) (γ : HoTFT1 M N) :
    HoTFTTriangle β (HoTFT1.comp α γ) γ :=
  fun K => Theory1.whiskerRightTriangle K (η K) (γ K)

/-- A proof-relevant HoTFT tetrahedron, represented modelwise by semantic
tetrahedra. -/
def HoTFTTetrahedron
    {M₀ M₁ M₂ M₃ : Term}
    {α01 : HoTFT1 M₀ M₁} {α02 : HoTFT1 M₀ M₂} {α03 : HoTFT1 M₀ M₃}
    {α12 : HoTFT1 M₁ M₂} {α13 : HoTFT1 M₁ M₃} {α23 : HoTFT1 M₂ M₃}
    (τ0 : HoTFTTriangle α12 α13 α23)
    (τ1 : HoTFTTriangle α02 α03 α23)
    (τ2 : HoTFTTriangle α01 α03 α13)
    (τ3 : HoTFTTriangle α01 α02 α12) : Sort _ :=
  ∀ (K : ExtensionalKanComplex), TheoryTetrahedron K (τ0 K) (τ1 K) (τ2 K) (τ3 K)

/-- Degenerating a HoTFT triangle along its middle face produces a HoTFT
tetrahedron whose middle face is the reflexive HoTFT 2-cell on that middle
edge. -/
noncomputable def HoTFTTriangle.reflTetrahedron
    {M₀ M₁ M₂ : Term}
    {α01 : HoTFT1 M₀ M₁} {α02 : HoTFT1 M₀ M₂} {α12 : HoTFT1 M₁ M₂}
    (τ : HoTFTTriangle α01 α02 α12) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl α12))
      (HoTFT2.toTriangle (HoTFT2.refl α02))
      τ
      τ :=
  fun K => TheoryTriangle.reflTetrahedron K (τ K)

/-- Horizontal composition of proof-relevant HoTFT 2-conversions, modelwise. -/
noncomputable def HoTFT2.hcomp {L M N : Term}
    {α α' : HoTFT1 L M} {β β' : HoTFT1 M N}
    (η : HoTFT2 α α') (θ : HoTFT2 β β') :
    HoTFT2 (HoTFT1.comp α β) (HoTFT1.comp α' β') :=
  HoTFT2.trans
    (HoTFT2.whiskerRight η β)
    (HoTFT2.whiskerLeft α' θ)

/-- Associator for proof-relevant HoTFT 1-cell composition. -/
noncomputable def HoTFT2.associator {L M N P : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) (γ : HoTFT1 N P) :
    HoTFT2 (HoTFT1.comp (HoTFT1.comp α β) γ)
      (HoTFT1.comp α (HoTFT1.comp β γ)) :=
  fun K => Theory2.associator K (α K) (β K) (γ K)

/-- Right inverse law for proof-relevant HoTFT 1-cell composition. -/
noncomputable def HoTFT2.rightInverse {M N : Term} (α : HoTFT1 M N) :
    HoTFT2 (HoTFT1.comp α (HoTFT1.inv α)) (HoTFT1.refl M) :=
  fun K => Theory2.rightInverse K (α K)

/-- Left inverse law for proof-relevant HoTFT 1-cell composition. -/
noncomputable def HoTFT2.leftInverse {M N : Term} (α : HoTFT1 M N) :
    HoTFT2 (HoTFT1.comp (HoTFT1.inv α) α) (HoTFT1.refl N) :=
  fun K => Theory2.leftInverse K (α K)

/-- Left unitor for proof-relevant HoTFT 1-cell composition. -/
noncomputable def HoTFT2.leftUnitor {M N : Term} (α : HoTFT1 M N) :
    HoTFT2 (HoTFT1.comp (HoTFT1.refl M) α) α :=
  fun K => Theory2.leftUnitor K (α K)

/-- Right unitor for proof-relevant HoTFT 1-cell composition. -/
noncomputable def HoTFT2.rightUnitor {M N : Term} (α : HoTFT1 M N) :
    HoTFT2 (HoTFT1.comp α (HoTFT1.refl N)) α :=
  fun K => Theory2.rightUnitor K (α K)

/-- Equality of proof-relevant HoTFT 1-conversions induces a HoTFT 2-conversion. -/
noncomputable def HoTFT2.ofEq {M N : Term} {α β : HoTFT1 M N} (h : α = β) : HoTFT2 α β := by
  cases h
  exact HoTFT2.refl α

/-- HoTFT 1-cell corresponding to the endpoint equality in Proposition 2.1. -/
noncomputable def beta_nested_eq_in_HoTFT1 (M N P : Term) :
    HoTFT1 (M[Term.app (Term.lam N) P]) (M[N[P]]) :=
  fun K => beta_nested_eq_in_Theory1 K M N P

/-- Proof-relevant refinement of Proposition 2.1 in HoTFT: the two β-reduction
orders for a nested redex are related by a HoTFT 2-cell. -/
noncomputable def beta_nested_compat_in_HoTFT2 (M N P : Term) :
    HoTFT2
      (HoTFT1.comp
        (betaEtaStep_in_HoTFT1 _ _
          (BetaEtaStep.beta (BetaStep.beta M (Term.app (Term.lam N) P))))
        (beta_nested_eq_in_HoTFT1 M N P))
      (HoTFT1.comp
        (betaEtaStep_in_HoTFT1 _ _
          (BetaEtaStep.beta (BetaStep.appR (BetaStep.beta N P))))
        (betaEtaStep_in_HoTFT1 _ _
          (BetaEtaStep.beta (BetaStep.beta M (N[P]))))) :=
  fun K => beta_nested_compat_in_Theory2 K M N P

/-- Proof-relevant HoTFT 3-conversions between parallel proof-relevant HoTFT
2-conversions. -/
def HoTFT3 {M N : Term} {α β : HoTFT1 M N} (η θ : HoTFT2 α β) : Sort _ :=
  ∀ (K : ExtensionalKanComplex), Theory3 K (α := α K) (β := β K) (η K) (θ K)

/-- Reflexivity of proof-relevant HoTFT 3-conversions. -/
def HoTFT3.refl {M N : Term} {α β : HoTFT1 M N}
    (η : HoTFT2 α β) : HoTFT3 η η :=
  fun K => Theory3.refl K (η K)

/-- Symmetry of proof-relevant HoTFT 3-conversions. -/
noncomputable def HoTFT3.symm {M N : Term} {α β : HoTFT1 M N} {η θ : HoTFT2 α β} :
    HoTFT3 η θ → HoTFT3 θ η
  | Γ => fun K => Theory3.symm K (Γ K)

/-- Vertical composition of proof-relevant HoTFT 3-conversions. -/
noncomputable def HoTFT3.trans {M N : Term} {α β : HoTFT1 M N} {η θ ι : HoTFT2 α β} :
    HoTFT3 η θ → HoTFT3 θ ι → HoTFT3 η ι
  | Γ, Δ => fun K => Theory3.trans K (Γ K) (Δ K)

/-- Equality of proof-relevant HoTFT 2-conversions induces a HoTFT
3-conversion. -/
def HoTFT3.ofEq {M N : Term} {α β : HoTFT1 M N}
    {η θ : HoTFT2 α β} (h : η = θ) : HoTFT3 η θ := by
  cases h
  exact HoTFT3.refl η

/-- Two boundary-aware HoTFT tetrahedra with the same outer boundary and a
front face coming from a HoTFT 2-cell induce a proof-relevant HoTFT 3-cell
between their middle faces. -/
noncomputable def HoTFTTetrahedron.path3
    {L M N : Term}
    {ρ : HoTFT1 L M} {σ τ : HoTFT1 M N} {μ ν : HoTFT1 L N}
    {γ : HoTFT2 σ τ} {α β : HoTFT2 μ ν}
    {τ2 : HoTFTTriangle ρ ν τ} {τ3 : HoTFTTriangle ρ μ σ}
    (Ω₁ : HoTFTTetrahedron (HoTFT2.toTriangle γ) (HoTFT2.toTriangle α) τ2 τ3)
    (Ω₂ : HoTFTTetrahedron (HoTFT2.toTriangle γ) (HoTFT2.toTriangle β) τ2 τ3) :
    HoTFT3 α β :=
  fun K => TheoryTetrahedron.path3 K (Ω₁ K) (Ω₂ K)

/-- A proof-relevant HoTFT 3-cell between the front faces of two
boundary-aware HoTFT tetrahedra with identical remaining boundary induces a
proof-relevant HoTFT 3-cell between their middle faces. -/
noncomputable def HoTFTTetrahedron.frontPath3
    {L M N : Term}
    {ρ : HoTFT1 L M} {σ τ : HoTFT1 M N} {μ ν : HoTFT1 L N}
    {γ₁ γ₂ : HoTFT2 σ τ} {α β : HoTFT2 μ ν}
    {τ2 : HoTFTTriangle ρ ν τ} {τ3 : HoTFTTriangle ρ μ σ}
    (Κ : HoTFT3 γ₁ γ₂)
    (Ω₁ : HoTFTTetrahedron (HoTFT2.toTriangle γ₁) (HoTFT2.toTriangle α) τ2 τ3)
    (Ω₂ : HoTFTTetrahedron (HoTFT2.toTriangle γ₂) (HoTFT2.toTriangle β) τ2 τ3) :
    HoTFT3 α β :=
  fun K => TheoryTetrahedron.frontPath3 K (Κ K) (Ω₁ K) (Ω₂ K)

/-- A boundary-aware HoTFT 4-simplex comparison between tetrahedra with the
same front face and same second outer face, but potentially different last
outer faces. -/
noncomputable def HoTFTTetrahedron.comparison
    {L M N : Term}
    {ρ : HoTFT1 L M} {σ τ : HoTFT1 M N} {μ ν : HoTFT1 L N}
    {γ : HoTFT2 σ τ} {α β : HoTFT2 μ ν} {δ : HoTFT2 μ μ}
    {τ2 : HoTFTTriangle ρ ν τ}
    {τ31 τ32 : HoTFTTriangle ρ μ σ}
    (Ω₁ : HoTFTTetrahedron (HoTFT2.toTriangle γ) (HoTFT2.toTriangle α) τ2 τ31)
    (Ω₂ : HoTFTTetrahedron (HoTFT2.toTriangle γ) (HoTFT2.toTriangle β) τ2 τ32)
    (Κ : HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl σ))
      (HoTFT2.toTriangle δ)
      τ32 τ31) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle β)
      (HoTFT2.toTriangle α)
      (HoTFT2.toTriangle δ) :=
  fun K => TheoryTetrahedron.comparison K (Ω₁ K) (Ω₂ K) (Κ K)

/-- Interchange at the HoTFT 3-cell layer is immediate from the definition of
modelwise horizontal composition. -/
noncomputable def HoTFT3.interchange {L M N : Term}
    {α α' : HoTFT1 L M} {β β' : HoTFT1 M N}
    (η : HoTFT2 α α') (θ : HoTFT2 β β') :
    HoTFT3 (HoTFT2.hcomp η θ)
      (HoTFT2.trans
        (HoTFT2.whiskerRight η β)
        (HoTFT2.whiskerLeft α' θ)) :=
  HoTFT3.ofEq rfl

/-- Alternative interchange at the HoTFT 3-cell layer. -/
noncomputable def HoTFT3.interchange' {L M N : Term}
    {α α' : HoTFT1 L M} {β β' : HoTFT1 M N}
    (η : HoTFT2 α α') (θ : HoTFT2 β β') :
    HoTFT3 (HoTFT2.hcomp η θ)
      (HoTFT2.trans
        (HoTFT2.whiskerLeft α θ)
        (HoTFT2.whiskerRight η β')) :=
  fun K => Theory3.interchange' K (η K) (θ K)

/-- The boundary-aware tetrahedron whose middle face is the HoTFT semantic
associator 2-cell. -/
noncomputable def HoTFT3.associatorTetrahedron {L M N P : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) (γ : HoTFT1 N P) :=
  fun K => Theory3.associatorTetrahedron K (α K) (β K) (γ K)

/-- Triangle coherence at the HoTFT semantic 3-cell layer. -/
noncomputable def HoTFT3.triangle {L M N : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.associator α (HoTFT1.refl M) β)
        (HoTFT2.whiskerLeft α (HoTFT2.leftUnitor β)))
      (HoTFT2.whiskerRight (HoTFT2.rightUnitor α) β) :=
  fun K => Theory3.triangle K (α K) (β K)

/-- The boundary-aware tetrahedron whose middle face is left whiskering at the
HoTFT semantic layer. -/
noncomputable def HoTFT3.whiskerLeftTetrahedron {L M N : Term}
    (α : HoTFT1 L M) {β γ : HoTFT1 M N} (η : HoTFT2 β γ) :=
  fun K => Theory3.whiskerLeftTetrahedron K (α K) (η K)

/-- Left whiskering is congruent on HoTFT 3-cells. -/
noncomputable def HoTFT3.whiskerLeftCongr {L M N : Term}
    (α : HoTFT1 L M) {β γ : HoTFT1 M N}
    {η θ : HoTFT2 β γ} (Κ : HoTFT3 η θ) :
    HoTFT3 (HoTFT2.whiskerLeft α η) (HoTFT2.whiskerLeft α θ) :=
  fun K => Theory3.whiskerLeftCongr K (α K) (Κ K)

/-- Left whiskering commutes with vertical composition up to proof-relevant HoTFT
3-cells. -/
noncomputable def HoTFT3.whiskerLeftTrans {L M N : Term}
    (α : HoTFT1 L M) {β γ δ : HoTFT1 M N}
    (η : HoTFT2 β γ) (θ : HoTFT2 γ δ) :
    HoTFT3
      (HoTFT2.whiskerLeft α (HoTFT2.trans η θ))
      (HoTFT2.trans (HoTFT2.whiskerLeft α η) (HoTFT2.whiskerLeft α θ)) :=
  fun K => Theory3.whiskerLeftTrans K (α K) (η K) (θ K)

/-- Left whiskering commutes with symmetry up to proof-relevant HoTFT
3-cells. -/
noncomputable def HoTFT3.whiskerLeftSymm {L M N : Term}
    (α : HoTFT1 L M) {β γ : HoTFT1 M N}
    (η : HoTFT2 β γ) :
    HoTFT3
      (HoTFT2.whiskerLeft α (HoTFT2.symm η))
      (HoTFT2.symm (HoTFT2.whiskerLeft α η)) :=
  fun K => Theory3.whiskerLeftSymm K (α K) (η K)

/-- The inverse direction of left-whisker symmetry at the HoTFT semantic
layer. -/
noncomputable def HoTFT3.invWhiskerLeft {L M N : Term}
    (α : HoTFT1 L M) {β γ : HoTFT1 M N}
    (η : HoTFT2 β γ) :
    HoTFT3
      (HoTFT2.symm (HoTFT2.whiskerLeft α η))
      (HoTFT2.whiskerLeft α (HoTFT2.symm η)) :=
  HoTFT3.symm (HoTFT3.whiskerLeftSymm α η)

/-- Right whiskering commutes with vertical composition up to proof-relevant HoTFT
3-cells. -/
noncomputable def HoTFT3.whiskerRightTrans {L M N : Term}
    {α β δ : HoTFT1 L M} (η : HoTFT2 α β) (θ : HoTFT2 β δ)
    (γ : HoTFT1 M N) :
    HoTFT3
      (HoTFT2.whiskerRight (HoTFT2.trans η θ) γ)
      (HoTFT2.trans
        (HoTFT2.whiskerRight η γ)
        (HoTFT2.whiskerRight θ γ)) :=
  fun K => Theory3.whiskerRightTrans K (η K) (θ K) (γ K)

/-- Right whiskering commutes with symmetry up to proof-relevant HoTFT
3-cells. -/
noncomputable def HoTFT3.whiskerRightSymm {L M N : Term}
    {α β : HoTFT1 L M} (η : HoTFT2 α β) (γ : HoTFT1 M N) :
    HoTFT3
      (HoTFT2.whiskerRight (HoTFT2.symm η) γ)
      (HoTFT2.symm (HoTFT2.whiskerRight η γ)) :=
  fun K => Theory3.whiskerRightSymm K (η K) (γ K)

/-- The inverse direction of right-whisker symmetry at the HoTFT semantic
layer. -/
noncomputable def HoTFT3.invWhiskerRight {L M N : Term}
    {α β : HoTFT1 L M} (η : HoTFT2 α β) (γ : HoTFT1 M N) :
    HoTFT3
      (HoTFT2.symm (HoTFT2.whiskerRight η γ))
      (HoTFT2.whiskerRight (HoTFT2.symm η) γ) :=
  HoTFT3.symm (HoTFT3.whiskerRightSymm η γ)

/-- The boundary-aware tetrahedron whose middle face is right whiskering at the
HoTFT semantic layer. -/
noncomputable def HoTFT3.whiskerRightTetrahedron {L M N : Term}
    {α β : HoTFT1 L M} (η : HoTFT2 α β) (γ : HoTFT1 M N) :=
  fun K => Theory3.whiskerRightTetrahedron K (η K) (γ K)

/-- The boundary-aware tetrahedron whose middle face is the HoTFT semantic
left unitor 2-cell. -/
noncomputable def HoTFT3.leftUnitorTetrahedron {M N : Term}
    (α : HoTFT1 M N) :=
  fun K => Theory3.leftUnitorTetrahedron K (α K)

/-- The boundary-aware tetrahedron whose middle face is the HoTFT semantic
right unitor 2-cell. -/
noncomputable def HoTFT3.rightUnitorTetrahedron {M N : Term}
    (α : HoTFT1 M N) :=
  fun K => Theory3.rightUnitorTetrahedron K (α K)

/-- The boundary-aware tetrahedron filled by the HoTFT semantic vertical
composition operation. Its second outer face is the composite HoTFT 2-cell,
while the original right and left factors remain explicit on the boundary. -/
noncomputable def HoTFT3.transFillerTetrahedron {M N : Term}
    {α β γ : HoTFT1 M N} (η : HoTFT2 α β) (θ : HoTFT2 β γ) :=
  fun K => Theory3.transFillerTetrahedron K (η K) (θ K)

/-- Vertical composition of HoTFT 2-cells is congruent in its left argument up
to HoTFT 3-cells. -/
noncomputable def HoTFT3.transCongrLeft {M N : Term}
    {α β γ : HoTFT1 M N} {η₁ η₂ : HoTFT2 α β}
    (Κ : HoTFT3 η₁ η₂) (θ : HoTFT2 β γ) :
    HoTFT3 (HoTFT2.trans η₁ θ) (HoTFT2.trans η₂ θ) :=
  fun K => Theory3.transCongrLeft K (Κ K) (θ K)

/-- Vertical composition of HoTFT 2-cells is congruent in its right argument up
to HoTFT 3-cells. -/
noncomputable def HoTFT3.transCongrRight {M N : Term}
    {α β γ : HoTFT1 M N} (η : HoTFT2 α β)
    {θ₁ θ₂ : HoTFT2 β γ} (Κ : HoTFT3 θ₁ θ₂) :
    HoTFT3 (HoTFT2.trans η θ₁) (HoTFT2.trans η θ₂) :=
  fun K => Theory3.transCongrRight K (η K) (Κ K)

/-- Vertical composition with a reflexive left factor normalizes to the right
factor at the HoTFT semantic layer. -/
noncomputable def HoTFT3.transReflLeft {M N : Term}
    {α β : HoTFT1 M N} (η : HoTFT2 α β) :
    HoTFT3 (HoTFT2.trans (HoTFT2.refl α) η) η :=
  fun K => Theory3.transReflLeft K (η K)

/-- Vertical composition with a reflexive right factor normalizes to the left
factor at the HoTFT semantic layer. -/
noncomputable def HoTFT3.transReflRight {M N : Term}
    {α β : HoTFT1 M N} (η : HoTFT2 α β) :
    HoTFT3 (HoTFT2.trans η (HoTFT2.refl β)) η :=
  fun K => Theory3.transReflRight K (η K)

/-- Right composition with a 2-cell followed by its inverse yields the reflexive
2-cell at the HoTFT semantic layer. -/
noncomputable def HoTFT3.transRightCancel {M N : Term}
    {α β : HoTFT1 M N} (η : HoTFT2 α β) :
    HoTFT3 (HoTFT2.trans η (HoTFT2.symm η)) (HoTFT2.refl α) :=
  fun K => Theory3.transRightCancel K (η K)

/-- The symmetry of a HoTFT vertical composite agrees with the composite of the
symmetries of its factors in reverse order, up to a HoTFT 3-cell. -/
noncomputable def HoTFT3.symmTrans {M N : Term}
    {α β γ : HoTFT1 M N} (η : HoTFT2 α β) (θ : HoTFT2 β γ) :
    HoTFT3 (HoTFT2.symm (HoTFT2.trans η θ))
      (HoTFT2.trans (HoTFT2.symm θ) (HoTFT2.symm η)) :=
  fun K => Theory3.symmTrans K (η K) (θ K)

/-- Proof-relevant HoTFT 4-conversions between parallel proof-relevant HoTFT
3-conversions. -/
def HoTFT4 {M N : Term} {α β : HoTFT1 M N} {η θ : HoTFT2 α β}
    (Γ Δ : HoTFT3 η θ) : Sort _ :=
  ∀ (K : ExtensionalKanComplex),
    Theory4 K (α := α K) (β := β K) (η := η K) (θ := θ K) (Γ K) (Δ K)

/-- Reflexivity of proof-relevant HoTFT 4-conversions. -/
def HoTFT4.refl {M N : Term} {α β : HoTFT1 M N} {η θ : HoTFT2 α β}
    (Γ : HoTFT3 η θ) : HoTFT4 Γ Γ :=
  fun K => Theory4.refl K (Γ K)

/-- Equality of proof-relevant HoTFT 3-conversions induces a HoTFT
4-conversion. -/
def HoTFT4.ofEq {M N : Term} {α β : HoTFT1 M N} {η θ : HoTFT2 α β}
    {Γ Δ : HoTFT3 η θ} (h : Γ = Δ) : HoTFT4 Γ Δ := by
  cases h
  exact HoTFT4.refl Γ

/-- Every explicit βη path induces HoTFT equality between its endpoints. -/
theorem reductionSeq_in_HoTFT {M N : Term} (p : ReductionSeq M N) :
    HoTFT_eq M N := by
  intro K ρ
  exact reductionSeq_sound K p ρ

/-- Every explicit βη path induces a proof-relevant HoTFT 1-conversion by
recursively composing semantic step edges via horn fillers. -/
noncomputable def reductionSeq_in_HoTFT1 {M N : Term} (p : ReductionSeq M N) :
    HoTFT1 M N :=
  fun K => reductionSeq_in_Theory1 K p

/-- The semantic inverse of the structural 1-cell induced by an explicit βη
path in a fixed model. -/
noncomputable def reductionSeq_inv_in_Theory1
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory1 K N M :=
  Theory1.inv K (reductionSeq_in_Theory1 K p)

/-- The semantic inverse of the structural HoTFT 1-cell induced by an explicit
βη path. -/
noncomputable def reductionSeq_inv_in_HoTFT1
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT1 N M :=
  HoTFT1.inv (reductionSeq_in_HoTFT1 p)

/-- Structural left whiskering of a semantic 2-cell along an explicit βη path
in a fixed model. This is the semantic operation matching the syntactic
`Homotopy2.whiskerLeft` constructor. -/
noncomputable def reductionSeq_whiskerLeft_in_Theory2
    (K : ExtensionalKanComplex) :
    {L M N : Term} → (r : ReductionSeq L M) → {p q : ReductionSeq M N} →
      Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q) →
        Theory2 K (reductionSeq_in_Theory1 K (ReductionSeq.concat r p))
          (reductionSeq_in_Theory1 K (ReductionSeq.concat r q))
  | _, _, _, .refl _, _, _, η => η
  | _, _, _, .step s rest, _, _, η =>
      Theory2.whiskerLeft K (betaEtaStep_in_Theory1 K _ _ s)
        (reductionSeq_whiskerLeft_in_Theory2 K rest η)
  | _, _, _, .stepInv s rest, _, _, η =>
      Theory2.whiskerLeft K (betaEtaStepInv_in_Theory1 K _ _ s)
        (reductionSeq_whiskerLeft_in_Theory2 K rest η)

/-- Structural left whiskering along an explicit βη path is congruent on
semantic 3-cells. -/
noncomputable def reductionSeq_whiskerLeftCongr_in_Theory3
    (K : ExtensionalKanComplex) :
    {L M N : Term} → (r : ReductionSeq L M) → {p q : ReductionSeq M N} →
      {η θ : Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)} →
      Theory3 K η θ →
        Theory3 K (reductionSeq_whiskerLeft_in_Theory2 K r η)
          (reductionSeq_whiskerLeft_in_Theory2 K r θ)
  | _, _, _, .refl _, _, _, _, _, Κ => Κ
  | _, _, _, .step s rest, _, _, _, _, Κ =>
      Theory3.whiskerLeftCongr K (betaEtaStep_in_Theory1 K _ _ s)
        (reductionSeq_whiskerLeftCongr_in_Theory3 K rest Κ)
  | _, _, _, .stepInv s rest, _, _, _, _, Κ =>
      Theory3.whiskerLeftCongr K (betaEtaStepInv_in_Theory1 K _ _ s)
        (reductionSeq_whiskerLeftCongr_in_Theory3 K rest Κ)

/-- Structural left whiskering along an explicit βη path commutes with vertical
composition up to semantic 3-cells. -/
noncomputable def reductionSeq_whiskerLeftTrans_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term} (r : ReductionSeq L M)
    {p q s : ReductionSeq M N}
    (η : Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
    (θ : Theory2 K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K s)) :
    Theory3 K
      (reductionSeq_whiskerLeft_in_Theory2 K r (Theory2.trans K η θ))
      (Theory2.trans K (reductionSeq_whiskerLeft_in_Theory2 K r η)
        (reductionSeq_whiskerLeft_in_Theory2 K r θ)) := by
  induction r with
  | refl _ =>
      exact Theory3.refl K (Theory2.trans K η θ)
  | step t rest ih =>
      exact Theory3.trans K
        (Theory3.whiskerLeftCongr K (betaEtaStep_in_Theory1 K _ _ t)
          (ih η θ))
        (Theory3.whiskerLeftTrans K (betaEtaStep_in_Theory1 K _ _ t)
          (reductionSeq_whiskerLeft_in_Theory2 K rest η)
          (reductionSeq_whiskerLeft_in_Theory2 K rest θ))
  | stepInv t rest ih =>
      exact Theory3.trans K
        (Theory3.whiskerLeftCongr K (betaEtaStepInv_in_Theory1 K _ _ t)
          (ih η θ))
        (Theory3.whiskerLeftTrans K (betaEtaStepInv_in_Theory1 K _ _ t)
          (reductionSeq_whiskerLeft_in_Theory2 K rest η)
          (reductionSeq_whiskerLeft_in_Theory2 K rest θ))

/-- Structural left whiskering along an explicit βη path commutes with symmetry
up to semantic 3-cells. -/
noncomputable def reductionSeq_whiskerLeftSymm_in_Theory3
    (K : ExtensionalKanComplex) :
    {L M N : Term} → (r : ReductionSeq L M) → {p q : ReductionSeq M N} →
      (η : Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)) →
        Theory3 K
          (reductionSeq_whiskerLeft_in_Theory2 K r (Theory2.symm K η))
          (Theory2.symm K (reductionSeq_whiskerLeft_in_Theory2 K r η))
  | _, _, _, .refl _, _, _, η =>
      Theory3.refl K (Theory2.symm K η)
  | _, _, _, .step s rest, _, _, η =>
      Theory3.trans K
        (Theory3.whiskerLeftCongr K (betaEtaStep_in_Theory1 K _ _ s)
          (reductionSeq_whiskerLeftSymm_in_Theory3 K rest η))
        (Theory3.whiskerLeftSymm K (betaEtaStep_in_Theory1 K _ _ s)
          (reductionSeq_whiskerLeft_in_Theory2 K rest η))
  | _, _, _, .stepInv s rest, _, _, η =>
      Theory3.trans K
        (Theory3.whiskerLeftCongr K (betaEtaStepInv_in_Theory1 K _ _ s)
          (reductionSeq_whiskerLeftSymm_in_Theory3 K rest η))
        (Theory3.whiskerLeftSymm K (betaEtaStepInv_in_Theory1 K _ _ s)
          (reductionSeq_whiskerLeft_in_Theory2 K rest η))

/-- Structural comparison between semantic composition of interpreted explicit
βη paths and interpretation of their syntactic concatenation. -/
noncomputable def reductionSeq_comp_in_Theory2
    (K : ExtensionalKanComplex) :
    {L M N : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
      Theory2 K
        (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
        (reductionSeq_in_Theory1 K (ReductionSeq.concat p q))
  | _, _, _, .refl _, q =>
      Theory2.leftUnitor K (reductionSeq_in_Theory1 K q)
  | _, _, _, .step s rest, q =>
      Theory2.trans K
        (Theory2.associator K (betaEtaStep_in_Theory1 K _ _ s)
          (reductionSeq_in_Theory1 K rest) (reductionSeq_in_Theory1 K q))
        (Theory2.whiskerLeft K (betaEtaStep_in_Theory1 K _ _ s)
          (reductionSeq_comp_in_Theory2 K rest q))
  | _, _, _, .stepInv s rest, q =>
      Theory2.trans K
        (Theory2.associator K (betaEtaStepInv_in_Theory1 K _ _ s)
          (reductionSeq_in_Theory1 K rest) (reductionSeq_in_Theory1 K q))
        (Theory2.whiskerLeft K (betaEtaStepInv_in_Theory1 K _ _ s)
          (reductionSeq_comp_in_Theory2 K rest q))

/-- Generic structural right whiskering of a semantic 2-cell along an explicit
βη path in a fixed model.

The full and structural 2-cell interpreters special-case reflexive input and
use the normalized semantic whisker directly. This helper remains the generic
shell used for non-reflexive right whiskering. -/
noncomputable def reductionSeq_whiskerRight_in_Theory2
    (K : ExtensionalKanComplex) {L M N : Term} {p q : ReductionSeq L M}
    (η : Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
    (s : ReductionSeq M N) :
    Theory2 K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s))
      (reductionSeq_in_Theory1 K (ReductionSeq.concat q s)) :=
  Theory2.trans K
    (Theory2.symm K (reductionSeq_comp_in_Theory2 K p s))
    (Theory2.trans K
      (Theory2.whiskerRight K η (reductionSeq_in_Theory1 K s))
      (reductionSeq_comp_in_Theory2 K q s))

/-- Every explicit syntactic 2-cell between parallel βη paths induces a
semantic 2-conversion between the corresponding structural semantic 1-cells in
a fixed extensional Kan complex. -/
noncomputable def homotopy2Deriv_in_Theory2
    (K : ExtensionalKanComplex) :
    {M N : Term} → {p q : ReductionSeq M N} →
      Homotopy2Deriv p q →
        Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)
  | _, _, _, _, .refl p => Theory2.refl K (reductionSeq_in_Theory1 K p)
  | _, _, _, _, .ofEq h =>
      Theory2.ofEq K (congrArg (fun r => reductionSeq_in_Theory1 K r) h)
  | _, _, _, _, .symm α =>
      Theory2.symm K (homotopy2Deriv_in_Theory2 K α)
  | _, _, _, _, .trans α β =>
      Theory2.trans K (homotopy2Deriv_in_Theory2 K α) (homotopy2Deriv_in_Theory2 K β)
  | _, _, _, _, .diamond p₁ p₂ q₁ q₂ =>
      let c₁ := ReductionSeq.concat p₁ q₁
      let c₂ := ReductionSeq.concat p₂ q₂
      Theory2.trans K
        (reductionSeq_in_eq_in_Theory2 K c₁)
        (Theory2.trans K
          (Theory2.ofEq K (reductionSeq_eq_in_Theory1_eq K c₁ c₂))
          (Theory2.symm K (reductionSeq_in_eq_in_Theory2 K c₂)))
  | _, _, _, _, .whiskerLeft r α =>
      reductionSeq_whiskerLeft_in_Theory2 K r (homotopy2Deriv_in_Theory2 K α)
  | _, _, _, _, .whiskerRight (.refl p) s =>
      Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s))
  | _, _, _, _, .whiskerRight α s =>
      reductionSeq_whiskerRight_in_Theory2 K (homotopy2Deriv_in_Theory2 K α) s

/-- Every explicit syntactic 2-cell between parallel βη paths induces a
semantic 2-conversion between the corresponding structural semantic 1-cells in
a fixed extensional Kan complex. -/
noncomputable def homotopy2_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term}
    {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q) :=
  homotopy2Deriv_in_Theory2 K α.deriv

/-- Interpreting a syntactic reflexive 2-cell in a fixed model is
definitionally the reflexive semantic 2-cell on the interpreted path. -/
theorem homotopy2_in_Theory2_refl
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    homotopy2_in_Theory2 K (Homotopy2.refl p) =
      Theory2.refl K (reductionSeq_in_Theory1 K p) :=
  rfl

/-- Interpreting a reflexive syntactic right whisker in a fixed model unfolds
definitionally to the reflexive semantic 2-cell on the interpreted
concatenation. -/
theorem homotopy2_in_Theory2_whiskerRight_refl
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    homotopy2_in_Theory2 K (whiskerRight (Homotopy2.refl p) s) =
      Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s)) :=
  rfl

/-- Semantic 3-cell packaging the definitional bridge from the interpreted
syntactic `whiskerRight` reflexivity source to the reflexive semantic source on
the interpreted concatenation. -/
noncomputable def homotopy2_whiskerRight_refl_source_bridge_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    Theory3 K
      (homotopy2_in_Theory2 K (whiskerRight (Homotopy2.refl p) s))
      (Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s))) :=
  Theory3.ofEq K (homotopy2_in_Theory2_whiskerRight_refl K p s)

/-- Interpreting the reflexive syntactic 2-cell on a concatenated path is
definitionally the reflexive semantic 2-cell on the interpreted concatenation. -/
theorem homotopy2_in_Theory2_refl_concat
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    homotopy2_in_Theory2 K (Homotopy2.refl (ReductionSeq.concat p s)) =
      Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s)) :=
  rfl

/-- Semantic 3-cell packaging the definitional bridge from the interpreted
syntactic reflexive target of `whiskerRightRefl` to the structural semantic
reflexive target on the concatenated path. -/
noncomputable def homotopy2_refl_concat_target_bridge_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    Theory3 K
      (homotopy2_in_Theory2 K (Homotopy2.refl (ReductionSeq.concat p s)))
      (Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s))) :=
  Theory3.ofEq K (homotopy2_in_Theory2_refl_concat K p s)

/-- Every explicit syntactic 2-cell admits a reflexive semantic 3-cell over
its interpreted semantic 2-cell in a fixed model. -/
noncomputable def homotopy2_refl_in_Theory3
    (K : ExtensionalKanComplex) {M N : Term}
    {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    Theory3 K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K α) :=
  Theory3.refl K (homotopy2_in_Theory2 K α)

/-- Equality of explicit syntactic 2-cells induces a semantic 3-cell between
their interpreted semantic 2-cells in a fixed model. -/
noncomputable def homotopy2_eq_in_Theory3
    (K : ExtensionalKanComplex) {M N : Term}
    {p q : ReductionSeq M N} {α β : Homotopy2 p q} (h : α = β) :
    Theory3 K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β) :=
  Theory3.ofEq K (congrArg (fun γ => homotopy2_in_Theory2 K γ) h)

/-- The semantic image of syntactic interchange is already a semantic 3-cell in
the current simplicial layer because semantic horizontal composition is defined
by the corresponding whiskering composite. -/
noncomputable def homotopy2_interchange_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p p' : ReductionSeq L M} {q q' : ReductionSeq M N}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    Theory3 K
      (Theory2.hcomp K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β))
      (Theory2.trans K
        (Theory2.whiskerRight K (homotopy2_in_Theory2 K α) (reductionSeq_in_Theory1 K q))
        (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K p') (homotopy2_in_Theory2 K β))) :=
  Theory3.interchange K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β)

/-- Alternative interchange on interpreted explicit 2-cells at the semantic
3-cell layer. -/
noncomputable def homotopy2_interchange'_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p p' : ReductionSeq L M} {q q' : ReductionSeq M N}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    Theory3 K
      (Theory2.hcomp K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β))
      (Theory2.trans K
        (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K p) (homotopy2_in_Theory2 K β))
        (Theory2.whiskerRight K (homotopy2_in_Theory2 K α) (reductionSeq_in_Theory1 K q'))) :=
  Theory3.interchange' K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β)

/-- Reflexivity of the structural semantic 2-cell associated to an explicit βη
path in a fixed model. -/
noncomputable def reductionSeq_refl_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K p) :=
  Theory2.refl K (reductionSeq_in_Theory1 K p)

/-- Associator for semantic composition of the structural 1-cells induced by
explicit βη paths in a fixed model. -/
noncomputable def reductionSeq_associator_in_Theory2
    (K : ExtensionalKanComplex) {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory2 K
      (Theory1.comp K
        (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
        (reductionSeq_in_Theory1 K r))
      (Theory1.comp K
        (reductionSeq_in_Theory1 K p)
        (Theory1.comp K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))) :=
  Theory2.associator K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)
    (reductionSeq_in_Theory1 K r)

/-- Right inverse law for the semantic 1-cell induced by an explicit βη path in
a fixed model. -/
noncomputable def reductionSeq_rightInverse_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory2 K
      (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_inv_in_Theory1 K p))
      (Theory1.refl K M) :=
  Theory2.rightInverse K (reductionSeq_in_Theory1 K p)

/-- Left inverse law for the semantic 1-cell induced by an explicit βη path in
a fixed model. -/
noncomputable def reductionSeq_leftInverse_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory2 K
      (Theory1.comp K (reductionSeq_inv_in_Theory1 K p) (reductionSeq_in_Theory1 K p))
      (Theory1.refl K N) :=
  Theory2.leftInverse K (reductionSeq_in_Theory1 K p)

/-- Symmetry of the structural semantic 2-cell associated to explicit βη
paths in a fixed model. -/
noncomputable def reductionSeq_symm_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term} {p q : ReductionSeq M N} :
    Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q) →
      Theory2 K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K p)
  | η => Theory2.symm K η

/-- Left unitor for the structural semantic 1-cell associated to an explicit βη
path in a fixed model. -/
noncomputable def reductionSeq_leftUnitor_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory2 K
      (Theory1.comp K (Theory1.refl K M) (reductionSeq_in_Theory1 K p))
      (reductionSeq_in_Theory1 K p) :=
  Theory2.leftUnitor K (reductionSeq_in_Theory1 K p)

/-- Right unitor for the structural semantic 1-cell associated to an explicit βη
path in a fixed model. -/
noncomputable def reductionSeq_rightUnitor_in_Theory2
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    Theory2 K
      (Theory1.comp K (reductionSeq_in_Theory1 K p) (Theory1.refl K N))
      (reductionSeq_in_Theory1 K p) :=
  Theory2.rightUnitor K (reductionSeq_in_Theory1 K p)

/-- Degenerating the semantic composition triangle yields a boundary-aware
semantic tetrahedron whose middle face is the reflexive 2-cell on the semantic
composite path. -/
noncomputable def reductionSeq_comp_refl_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (reductionSeq_in_Theory1 K q)))
      (Theory2.toTriangle K
        (Theory2.refl K
          (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))))
      (Theory1.compTriangle K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
      (Theory1.compTriangle K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)) :=
  TheoryTriangle.reflTetrahedron K
    (Theory1.compTriangle K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))

/-- The interpreted structural associator carries an explicit semantic
tetrahedron with its full boundary triangles. -/
noncomputable def reductionSeq_associator_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    TheoryTetrahedron K
      (Theory2.toTriangle K
        (Theory2.refl K
          (Theory1.comp K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))))
      (Theory2.toTriangle K (reductionSeq_associator_in_Theory2 K p q r))
      (Theory1.compTriangle K (reductionSeq_in_Theory1 K p)
        (Theory1.comp K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r)))
      (Theory1.assocTriangle K (reductionSeq_in_Theory1 K p)
        (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r)) :=
  Theory3.associatorTetrahedron K
    (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r)

/-- The interpreted structural left unitor carries an explicit semantic
tetrahedron with its full boundary triangles. -/
noncomputable def reductionSeq_leftUnitor_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (reductionSeq_in_Theory1 K p)))
      (Theory2.toTriangle K (reductionSeq_leftUnitor_in_Theory2 K p))
      (Theory1.sourceDegenerateTriangle K (reductionSeq_in_Theory1 K p))
      (Theory1.compTriangle K (Theory1.refl K M) (reductionSeq_in_Theory1 K p)) :=
  Theory3.leftUnitorTetrahedron K (reductionSeq_in_Theory1 K p)

/-- The interpreted structural right unitor carries an explicit semantic
tetrahedron with its full boundary triangles. -/
noncomputable def reductionSeq_rightUnitor_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {M N : Term} (p : ReductionSeq M N) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (Theory1.refl K N)))
      (Theory2.toTriangle K (reductionSeq_rightUnitor_in_Theory2 K p))
      (Theory2.toTriangle K (Theory2.refl K (reductionSeq_in_Theory1 K p)))
      (Theory1.compTriangle K (reductionSeq_in_Theory1 K p) (Theory1.refl K N)) :=
  Theory3.rightUnitorTetrahedron K (reductionSeq_in_Theory1 K p)

/-- The interpreted structural vertical composition carries an explicit
semantic tetrahedron with its full boundary triangles. -/
noncomputable def homotopy2_trans_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {M N : Term}
    {p q s : ReductionSeq M N} (α : Homotopy2 p q) (β : Homotopy2 q s) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (Theory1.refl K N)))
      (Theory2.toTriangle K (homotopy2_in_Theory2 K β))
      (Theory2.toTriangle K (homotopy2_in_Theory2 K (Homotopy2.trans α β)))
      (Theory2.toTriangle K (homotopy2_in_Theory2 K α)) :=
  Theory3.transFillerTetrahedron K
    (homotopy2_in_Theory2 K α)
    (homotopy2_in_Theory2 K β)

/-- Left whiskering of an interpreted explicit 2-cell carries an explicit
semantic tetrahedron with its full boundary triangles. -/
noncomputable def homotopy2_whiskerLeft_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {L M N : Term}
    (r : ReductionSeq L M) {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (homotopy2_in_Theory2 K α))
      (Theory2.toTriangle K
        (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r) (homotopy2_in_Theory2 K α)))
      (Theory1.compTriangle K (reductionSeq_in_Theory1 K r) (reductionSeq_in_Theory1 K q))
      (Theory1.compTriangle K (reductionSeq_in_Theory1 K r) (reductionSeq_in_Theory1 K p)) :=
  Theory3.whiskerLeftTetrahedron K (reductionSeq_in_Theory1 K r) (homotopy2_in_Theory2 K α)

/-- Left whiskering commutes with vertical composition for interpreted explicit
2-cells. -/
noncomputable def homotopy2_whiskerLeftTrans_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (r : ReductionSeq L M) {p q s : ReductionSeq M N}
    (α : Homotopy2 p q) (β : Homotopy2 q s) :
    Theory3 K
      (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r)
        (Theory2.trans K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β)))
      (Theory2.trans K
        (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r) (homotopy2_in_Theory2 K α))
        (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r) (homotopy2_in_Theory2 K β))) :=
  Theory3.whiskerLeftTrans K (reductionSeq_in_Theory1 K r)
    (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β)

/-- Left whiskering commutes with symmetry for interpreted explicit 2-cells. -/
noncomputable def homotopy2_whiskerLeftSymm_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (r : ReductionSeq L M) {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    Theory3 K
      (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r)
        (Theory2.symm K (homotopy2_in_Theory2 K α)))
      (Theory2.symm K
        (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r)
          (homotopy2_in_Theory2 K α))) :=
  Theory3.whiskerLeftSymm K (reductionSeq_in_Theory1 K r) (homotopy2_in_Theory2 K α)

/-- The inverse direction of left-whisker symmetry for interpreted explicit
2-cells. -/
noncomputable def homotopy2_invWhiskerLeft_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (r : ReductionSeq L M) {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    Theory3 K
      (Theory2.symm K
        (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r)
          (homotopy2_in_Theory2 K α)))
      (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r)
        (Theory2.symm K (homotopy2_in_Theory2 K α))) :=
  Theory3.invWhiskerLeft K (reductionSeq_in_Theory1 K r) (homotopy2_in_Theory2 K α)

/-- Right whiskering commutes with vertical composition for interpreted explicit
2-cells. -/
noncomputable def homotopy2_whiskerRightTrans_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q s : ReductionSeq L M} (α : Homotopy2 p q) (β : Homotopy2 q s)
    (r : ReductionSeq M N) :
    Theory3 K
      (Theory2.whiskerRight K
        (Theory2.trans K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β))
        (reductionSeq_in_Theory1 K r))
      (Theory2.trans K
        (Theory2.whiskerRight K (homotopy2_in_Theory2 K α)
          (reductionSeq_in_Theory1 K r))
        (Theory2.whiskerRight K (homotopy2_in_Theory2 K β)
          (reductionSeq_in_Theory1 K r))) :=
  Theory3.whiskerRightTrans K
    (homotopy2_in_Theory2 K α)
    (homotopy2_in_Theory2 K β)
    (reductionSeq_in_Theory1 K r)

/-- Right whiskering commutes with symmetry for interpreted explicit 2-cells. -/
noncomputable def homotopy2_whiskerRightSymm_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q : ReductionSeq L M} (α : Homotopy2 p q) (s : ReductionSeq M N) :
    Theory3 K
      (Theory2.whiskerRight K
        (Theory2.symm K (homotopy2_in_Theory2 K α))
        (reductionSeq_in_Theory1 K s))
      (Theory2.symm K
        (Theory2.whiskerRight K (homotopy2_in_Theory2 K α)
          (reductionSeq_in_Theory1 K s))) :=
  Theory3.whiskerRightSymm K (homotopy2_in_Theory2 K α)
    (reductionSeq_in_Theory1 K s)

/-- The inverse direction of right-whisker symmetry for interpreted explicit
2-cells. -/
noncomputable def homotopy2_invWhiskerRight_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q : ReductionSeq L M} (α : Homotopy2 p q) (s : ReductionSeq M N) :
    Theory3 K
      (Theory2.symm K
        (Theory2.whiskerRight K (homotopy2_in_Theory2 K α)
          (reductionSeq_in_Theory1 K s)))
       (Theory2.whiskerRight K
         (Theory2.symm K (homotopy2_in_Theory2 K α))
         (reductionSeq_in_Theory1 K s)) :=
  Theory3.invWhiskerRight K (homotopy2_in_Theory2 K α)
    (reductionSeq_in_Theory1 K s)

/-- Triangle coherence for interpreted explicit paths. -/
noncomputable def reductionSeq_triangle_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) :
    Theory3 K
      (Theory2.trans K
        (reductionSeq_associator_in_Theory2 K p (ReductionSeq.refl M) q)
        (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K p)
          (reductionSeq_leftUnitor_in_Theory2 K q)))
      (Theory2.whiskerRight K
        (reductionSeq_rightUnitor_in_Theory2 K p)
        (reductionSeq_in_Theory1 K q)) :=
  Theory3.triangle K
    (reductionSeq_in_Theory1 K p)
    (reductionSeq_in_Theory1 K q)

/-- Right whiskering of an interpreted explicit 2-cell carries an explicit
semantic tetrahedron with its full boundary triangles. -/
noncomputable def homotopy2_whiskerRight_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {L M N : Term}
    {p q : ReductionSeq L M} (α : Homotopy2 p q) (s : ReductionSeq M N) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (reductionSeq_in_Theory1 K s)))
      (Theory2.toTriangle K
        (Theory2.whiskerRight K (homotopy2_in_Theory2 K α) (reductionSeq_in_Theory1 K s)))
      (Theory1.compTriangle K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K s))
      (Theory1.whiskerRightTriangle K (homotopy2_in_Theory2 K α) (reductionSeq_in_Theory1 K s)) :=
  Theory3.whiskerRightTetrahedron K (homotopy2_in_Theory2 K α) (reductionSeq_in_Theory1 K s)

/-- Left whiskering preserves reflexive interpreted 2-cells up to a semantic
3-cell, obtained by comparing the two boundary-aware tetrahedra with matching
outer boundary. -/
noncomputable def homotopy2_whiskerLeftRefl_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (r : ReductionSeq L M) (p : ReductionSeq M N) :
    Theory3 K
      (Theory2.whiskerLeft K (reductionSeq_in_Theory1 K r)
        (Theory2.refl K (reductionSeq_in_Theory1 K p)))
      (Theory2.refl K
        (Theory1.comp K (reductionSeq_in_Theory1 K r) (reductionSeq_in_Theory1 K p))) :=
  TheoryTetrahedron.path3 K
    (homotopy2_whiskerLeft_in_TheoryTetrahedron K r (Homotopy2.refl p))
    (reductionSeq_comp_refl_in_TheoryTetrahedron K r p)

/-- Structural left whiskering of a reflexive interpreted 2-cell along an
explicit βη path normalizes directly to the reflexive interpreted composite
path. The recursive structural whisker appears as the front face of the
single-step whiskering tetrahedron, while the target tetrahedron has the
reflexive front face coming from the recursive normalization. -/
noncomputable def reductionSeq_whiskerLeftRefl_in_Theory3
    (K : ExtensionalKanComplex) :
    {L M N : Term} → (r : ReductionSeq L M) → (p : ReductionSeq M N) →
      Theory3 K
        (reductionSeq_whiskerLeft_in_Theory2 K r
          (Theory2.refl K (reductionSeq_in_Theory1 K p)))
        (Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat r p)))
  | _, _, _, .refl _, p =>
      Theory3.refl K (Theory2.refl K (reductionSeq_in_Theory1 K p))
  | _, _, _, .step s rest, p =>
      TheoryTetrahedron.frontPath3 K
        (reductionSeq_whiskerLeftRefl_in_Theory3 K rest p)
        (Theory3.whiskerLeftTetrahedron K (betaEtaStep_in_Theory1 K _ _ s)
          (reductionSeq_whiskerLeft_in_Theory2 K rest
            (Theory2.refl K (reductionSeq_in_Theory1 K p))))
        (TheoryTriangle.reflTetrahedron K
          (Theory1.compTriangle K (betaEtaStep_in_Theory1 K _ _ s)
            (reductionSeq_in_Theory1 K (ReductionSeq.concat rest p))))
  | _, _, _, .stepInv s rest, p =>
      TheoryTetrahedron.frontPath3 K
        (reductionSeq_whiskerLeftRefl_in_Theory3 K rest p)
        (Theory3.whiskerLeftTetrahedron K (betaEtaStepInv_in_Theory1 K _ _ s)
          (reductionSeq_whiskerLeft_in_Theory2 K rest
            (Theory2.refl K (reductionSeq_in_Theory1 K p))))
        (TheoryTriangle.reflTetrahedron K
          (Theory1.compTriangle K (betaEtaStepInv_in_Theory1 K _ _ s)
            (reductionSeq_in_Theory1 K (ReductionSeq.concat rest p))))

/-- A first boundary-aware 4-simplex comparison for right whiskering of a
reflexive interpreted 2-cell. This absorbs the mismatch between the source and
target tetrahedra into an explicit extra boundary face, but does not yet
normalize all the way into `Theory3`. -/
noncomputable def homotopy2_whiskerRightRefl_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (Theory1.refl K N)))
      (Theory2.toTriangle K
        (Theory2.refl K
          (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K s))))
      (Theory2.toTriangle K
        (Theory2.whiskerRight K
          (Theory2.refl K (reductionSeq_in_Theory1 K p))
          (reductionSeq_in_Theory1 K s)))
      (Theory2.toTriangle K
        (Theory2.whiskerRight K
          (Theory2.refl K (reductionSeq_in_Theory1 K p))
          (reductionSeq_in_Theory1 K s))) :=
  TheoryTetrahedron.comparison K
    (homotopy2_whiskerRight_in_TheoryTetrahedron K (Homotopy2.refl p) s)
    (reductionSeq_comp_refl_in_TheoryTetrahedron K p s)
    (homotopy2_whiskerRight_in_TheoryTetrahedron K (Homotopy2.refl p) s)

/-- The normalized bridge tetrahedron for `whiskerRightRefl`, obtained by
reading the explicit simplicial bridge `K.whiskerRightReflPath3` back as a
boundary-aware semantic tetrahedron. Unlike the first comparison above, its
fourth face is already the reflexive 2-cell on the composite. -/
noncomputable def homotopy2_whiskerRightRefl_bridge_in_TheoryTetrahedron
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    TheoryTetrahedron K
      (Theory2.toTriangle K (Theory2.refl K (Theory1.refl K N)))
      (Theory2.toTriangle K
        (Theory2.refl K
          (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K s))))
      (Theory2.toTriangle K
        (Theory2.whiskerRight K
          (Theory2.refl K (reductionSeq_in_Theory1 K p))
          (reductionSeq_in_Theory1 K s)))
      (Theory2.toTriangle K
        (Theory2.refl K
          (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K s)))) :=
  fun ρ =>
    (K.whiskerRightReflPath3 (reductionSeq_in_Theory1 K p ρ)
      (reductionSeq_in_Theory1 K s ρ)).toTetrahedron

/-- Right whiskering preserves reflexive interpreted 2-cells up to a semantic
3-cell. This is the final normalized witness extracted from the bridge
tetrahedron above. -/
noncomputable def homotopy2_whiskerRightRefl_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    Theory3 K
      (Theory2.whiskerRight K
        (Theory2.refl K (reductionSeq_in_Theory1 K p))
        (reductionSeq_in_Theory1 K s))
      (Theory2.refl K
        (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K s))) :=
  fun ρ =>
    K.whiskerRightReflPath3 (reductionSeq_in_Theory1 K p ρ)
      (reductionSeq_in_Theory1 K s ρ)

/-- Naming wrapper for the normalized `whiskerRightRefl` simplification step,
for the standalone semantic right-whisker normalization witness. -/
noncomputable def reductionSeq_whiskerRight_refl_simplify_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    Theory3 K
      (Theory2.whiskerRight K
        (Theory2.refl K (reductionSeq_in_Theory1 K p))
        (reductionSeq_in_Theory1 K s))
      (Theory2.refl K
        (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K s))) :=
  homotopy2_whiskerRightRefl_in_Theory3 K p s

/-- The inner composite in the legacy structural right-whisker reflexivity
shell normalizes to the comparison 2-cell `c`. This isolates the remaining
blocker to transporting along the fixed left factor `symm c`. -/
noncomputable def reductionSeq_whiskerRight_refl_inner_in_Theory3
    (K : ExtensionalKanComplex) {L M N : Term}
    (p : ReductionSeq L M) (s : ReductionSeq M N) :
    Theory3 K
      (Theory2.trans K
        (Theory2.whiskerRight K
          (Theory2.refl K (reductionSeq_in_Theory1 K p))
          (reductionSeq_in_Theory1 K s))
        (reductionSeq_comp_in_Theory2 K p s))
      (reductionSeq_comp_in_Theory2 K p s) :=
  Theory3.trans K
    (Theory3.transCongrLeft K
      (reductionSeq_whiskerRight_refl_simplify_in_Theory3 K p s)
      (reductionSeq_comp_in_Theory2 K p s))
    (Theory3.transReflLeft K (reductionSeq_comp_in_Theory2 K p s))

/-- Every structurally supported syntactic 3-cell between parallel explicit
2-cells induces a semantic 3-conversion between the corresponding interpreted
semantic 2-cells in a fixed extensional Kan complex. -/
noncomputable def structuralHomotopy3_in_Theory3
    (K : ExtensionalKanComplex) :
    {M N : Term} → {p q : ReductionSeq M N} → {α β : Homotopy2 p q} →
      HigherLambdaModel.Lambda.HigherTerms.StructuralHomotopy3 α β →
        Theory3 K (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β)
  | _, _, _, _, _, _, .refl α =>
      homotopy2_refl_in_Theory3 K α
  | _, _, _, _, _, _, .ofEq h =>
      homotopy2_eq_in_Theory3 K h
  | _, _, _, _, _, _, .symm η =>
      Theory3.symm K (structuralHomotopy3_in_Theory3 K η)
  | _, _, _, _, _, _, .trans η θ =>
      Theory3.trans K
        (structuralHomotopy3_in_Theory3 K η)
        (structuralHomotopy3_in_Theory3 K θ)
  | _, _, _, _, _, _, .whiskerLeftRefl r p =>
      reductionSeq_whiskerLeftRefl_in_Theory3 K r p
  | _, _, _, _, _, _, .whiskerLeftTrans r α β =>
      reductionSeq_whiskerLeftTrans_in_Theory3 K r
        (homotopy2_in_Theory2 K α) (homotopy2_in_Theory2 K β)
  | _, _, _, _, _, _, .whiskerLeftSymm r α =>
      reductionSeq_whiskerLeftSymm_in_Theory3 K r (homotopy2_in_Theory2 K α)
  | _, _, _, _, _, _, .whiskerRightRefl p s =>
      homotopy2_refl_in_Theory3 K (Homotopy2.refl (ReductionSeq.concat p s))
  | _, _, _, _, _, _, .interchange α β =>
      homotopy2_eq_in_Theory3 K rfl

/-- Every structurally supported syntactic 2-cell between explicit βη paths
induces a semantic 2-conversion between the corresponding structural semantic
1-cells in a fixed model. -/
noncomputable def structuralHomotopy2_in_Theory2
    (K : ExtensionalKanComplex) :
    {M N : Term} → {p q : ReductionSeq M N} →
      StructuralHomotopy2 p q →
        Theory2 K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q)
  | _, _, _, _, .refl p => reductionSeq_refl_in_Theory2 K p
  | _, _, _, _, .ofEq h =>
      Theory2.ofEq K (congrArg (fun r => reductionSeq_in_Theory1 K r) h)
  | _, _, _, _, .symm α =>
      reductionSeq_symm_in_Theory2 K (structuralHomotopy2_in_Theory2 K α)
  | _, _, _, _, .trans α β =>
      Theory2.trans K
        (structuralHomotopy2_in_Theory2 K α)
        (structuralHomotopy2_in_Theory2 K β)
  | _, _, _, _, .whiskerLeft r α =>
      reductionSeq_whiskerLeft_in_Theory2 K r
        (structuralHomotopy2_in_Theory2 K α)
  | _, _, _, _, .whiskerRight (.refl p) s =>
      Theory2.refl K (reductionSeq_in_Theory1 K (ReductionSeq.concat p s))
  | _, _, _, _, .whiskerRight α s =>
      reductionSeq_whiskerRight_in_Theory2 K
        (structuralHomotopy2_in_Theory2 K α) s

/-- Equality-generated HoTFT 1-conversion associated to an explicit βη path.
This auxiliary bridge is used internally to compare the structural HoTFT
interpretation with the underlying equality semantics. -/
noncomputable def reductionSeq_eq_in_HoTFT1 {M N : Term} (p : ReductionSeq M N) :
    HoTFT1 M N :=
  HoTFT1.ofHoTFTEq (reductionSeq_in_HoTFT p)

/-- Any two parallel explicit βη paths induce the same equality-generated
proof-relevant HoTFT 1-conversion. -/
theorem reductionSeq_eq_in_HoTFT1_eq {M N : Term} (p q : ReductionSeq M N) :
    reductionSeq_eq_in_HoTFT1 p = reductionSeq_eq_in_HoTFT1 q := by
  unfold reductionSeq_eq_in_HoTFT1
  have hproof : reductionSeq_in_HoTFT p = reductionSeq_in_HoTFT q :=
    Subsingleton.elim _ _
  exact congrArg HoTFT1.ofHoTFTEq hproof

/-- Every explicit βη path is structurally homotopic to its equality-generated
HoTFT interpretation. -/
noncomputable def reductionSeq_in_eq_in_HoTFT2
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_eq_in_HoTFT1 p) :=
  fun K => reductionSeq_in_eq_in_Theory2 K p

/-- Structural left whiskering of a semantic HoTFT 2-cell along an explicit βη
path. -/
noncomputable def reductionSeq_whiskerLeft_in_HoTFT2
    {L M N : Term} (r : ReductionSeq L M) {p q : ReductionSeq M N} :
    HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q) →
      HoTFT2 (reductionSeq_in_HoTFT1 (ReductionSeq.concat r p))
        (reductionSeq_in_HoTFT1 (ReductionSeq.concat r q))
  | η => fun K => reductionSeq_whiskerLeft_in_Theory2 K r (η K)

/-- Structural left whiskering along an explicit βη path is congruent on HoTFT
3-cells. -/
noncomputable def reductionSeq_whiskerLeftCongr_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M) {p q : ReductionSeq M N}
    {η θ : HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q)}
    (Κ : HoTFT3 η θ) :
    HoTFT3 (reductionSeq_whiskerLeft_in_HoTFT2 r η)
      (reductionSeq_whiskerLeft_in_HoTFT2 r θ) :=
  fun K => reductionSeq_whiskerLeftCongr_in_Theory3 K r (Κ K)

/-- Structural left whiskering along an explicit βη path commutes with vertical
composition up to proof-relevant HoTFT 3-cells. -/
noncomputable def reductionSeq_whiskerLeftTrans_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M) {p q s : ReductionSeq M N}
    (η : HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
    (θ : HoTFT2 (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 s)) :
    HoTFT3
      (reductionSeq_whiskerLeft_in_HoTFT2 r (HoTFT2.trans η θ))
      (HoTFT2.trans (reductionSeq_whiskerLeft_in_HoTFT2 r η)
        (reductionSeq_whiskerLeft_in_HoTFT2 r θ)) :=
  fun K => reductionSeq_whiskerLeftTrans_in_Theory3 K r (η K) (θ K)

/-- Structural left whiskering along an explicit βη path commutes with symmetry
up to proof-relevant HoTFT 3-cells. -/
noncomputable def reductionSeq_whiskerLeftSymm_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M) {p q : ReductionSeq M N}
    (η : HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q)) :
    HoTFT3
      (reductionSeq_whiskerLeft_in_HoTFT2 r (HoTFT2.symm η))
      (HoTFT2.symm (reductionSeq_whiskerLeft_in_HoTFT2 r η)) :=
  fun K => reductionSeq_whiskerLeftSymm_in_Theory3 K r (η K)

/-- Structural comparison between semantic composition of the HoTFT 1-cells
induced by explicit βη paths and interpretation of their syntactic
concatenation. -/
noncomputable def reductionSeq_comp_in_HoTFT2
    {L M N : Term} (p : ReductionSeq L M) (q : ReductionSeq M N) :
    HoTFT2
      (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
      (reductionSeq_in_HoTFT1 (ReductionSeq.concat p q)) :=
  fun K => reductionSeq_comp_in_Theory2 K p q

/-- Generic structural right whiskering of a semantic HoTFT 2-cell along an
explicit βη path.

The structural and full HoTFT interpreters special-case reflexive input and use
the normalized semantic whisker directly. This helper remains the generic shell
for non-reflexive right whiskering. -/
noncomputable def reductionSeq_whiskerRight_in_HoTFT2
    {L M N : Term} {p q : ReductionSeq L M}
    (η : HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
    (s : ReductionSeq M N) :
    HoTFT2 (reductionSeq_in_HoTFT1 (ReductionSeq.concat p s))
      (reductionSeq_in_HoTFT1 (ReductionSeq.concat q s)) :=
  HoTFT2.trans (HoTFT2.symm (reductionSeq_comp_in_HoTFT2 p s))
    (HoTFT2.trans
      (HoTFT2.whiskerRight η (reductionSeq_in_HoTFT1 s))
      (reductionSeq_comp_in_HoTFT2 q s))

/-- Reflexivity of the structural HoTFT 2-cell associated to an explicit βη
path. -/
noncomputable def reductionSeq_refl_in_HoTFT2
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 p) :=
  HoTFT2.refl (reductionSeq_in_HoTFT1 p)

/-- Associator for semantic composition of the structural HoTFT 1-cells
induced by explicit βη paths. -/
noncomputable def reductionSeq_associator_in_HoTFT2
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFT2
      (HoTFT1.comp
        (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
        (reductionSeq_in_HoTFT1 r))
      (HoTFT1.comp
        (reductionSeq_in_HoTFT1 p)
        (HoTFT1.comp (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r))) :=
  HoTFT2.associator (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q)
    (reductionSeq_in_HoTFT1 r)

/-- Right inverse law for the structural HoTFT 1-cell induced by an explicit
βη path. -/
noncomputable def reductionSeq_rightInverse_in_HoTFT2
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT2
      (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_inv_in_HoTFT1 p))
      (HoTFT1.refl M) :=
  HoTFT2.rightInverse (reductionSeq_in_HoTFT1 p)

/-- Left inverse law for the structural HoTFT 1-cell induced by an explicit
βη path. -/
noncomputable def reductionSeq_leftInverse_in_HoTFT2
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT2
      (HoTFT1.comp (reductionSeq_inv_in_HoTFT1 p) (reductionSeq_in_HoTFT1 p))
      (HoTFT1.refl N) :=
  HoTFT2.leftInverse (reductionSeq_in_HoTFT1 p)

/-- Symmetry of the structural HoTFT 2-cell associated to explicit βη paths. -/
noncomputable def reductionSeq_symm_in_HoTFT2
    {M N : Term} {p q : ReductionSeq M N} :
    HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q) →
      HoTFT2 (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 p)
  | η => HoTFT2.symm η

/-- Left unitor for the structural HoTFT 1-cell associated to an explicit βη
path. -/
noncomputable def reductionSeq_leftUnitor_in_HoTFT2
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT2
      (HoTFT1.comp (HoTFT1.refl M) (reductionSeq_in_HoTFT1 p))
      (reductionSeq_in_HoTFT1 p) :=
  HoTFT2.leftUnitor (reductionSeq_in_HoTFT1 p)

/-- Right unitor for the structural HoTFT 1-cell associated to an explicit βη
path. -/
noncomputable def reductionSeq_rightUnitor_in_HoTFT2
    {M N : Term} (p : ReductionSeq M N) :
    HoTFT2
      (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (HoTFT1.refl N))
      (reductionSeq_in_HoTFT1 p) :=
  HoTFT2.rightUnitor (reductionSeq_in_HoTFT1 p)

/-- Degenerating the semantic composition triangle yields a boundary-aware
HoTFT tetrahedron whose middle face is the reflexive 2-cell on the semantic
composite path. -/
noncomputable def reductionSeq_comp_refl_in_HoTFTTetrahedron
    {L M N : Term} (p : ReductionSeq L M) (q : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (reductionSeq_in_HoTFT1 q)))
      (HoTFT2.toTriangle
        (HoTFT2.refl
          (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))))
      (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
      (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q)) :=
  HoTFTTriangle.reflTetrahedron
    (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))

/-- The interpreted structural associator carries an explicit HoTFT
tetrahedron with its full boundary triangles. -/
noncomputable def reductionSeq_associator_in_HoTFTTetrahedron
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle
        (HoTFT2.refl (HoTFT1.comp (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r))))
      (HoTFT2.toTriangle (reductionSeq_associator_in_HoTFT2 p q r))
      (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 p)
        (HoTFT1.comp (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r)))
      (HoTFT1.assocTriangle (reductionSeq_in_HoTFT1 p)
        (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r)) :=
  HoTFT3.associatorTetrahedron
    (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r)

/-- The interpreted structural left unitor carries an explicit HoTFT
tetrahedron with its full boundary triangles. -/
noncomputable def reductionSeq_leftUnitor_in_HoTFTTetrahedron
    {M N : Term} (p : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (reductionSeq_in_HoTFT1 p)))
      (HoTFT2.toTriangle (reductionSeq_leftUnitor_in_HoTFT2 p))
      (HoTFT1.sourceDegenerateTriangle (reductionSeq_in_HoTFT1 p))
      (HoTFT1.compTriangle (HoTFT1.refl M) (reductionSeq_in_HoTFT1 p)) :=
  HoTFT3.leftUnitorTetrahedron (reductionSeq_in_HoTFT1 p)

/-- The interpreted structural right unitor carries an explicit HoTFT
tetrahedron with its full boundary triangles. -/
noncomputable def reductionSeq_rightUnitor_in_HoTFTTetrahedron
    {M N : Term} (p : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle (reductionSeq_rightUnitor_in_HoTFT2 p))
      (HoTFT2.toTriangle (HoTFT2.refl (reductionSeq_in_HoTFT1 p)))
      (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 p) (HoTFT1.refl N)) :=
  HoTFT3.rightUnitorTetrahedron (reductionSeq_in_HoTFT1 p)

/-- Every structurally supported syntactic 2-cell between explicit βη paths
induces a proof-relevant HoTFT 2-conversion between the corresponding
structural HoTFT 1-cells. -/
noncomputable def structuralHomotopy2_in_HoTFT2 :
    {M N : Term} → {p q : ReductionSeq M N} →
      StructuralHomotopy2 p q →
        HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q)
  | _, _, _, _, .refl p => reductionSeq_refl_in_HoTFT2 p
  | _, _, _, _, .ofEq h =>
      HoTFT2.ofEq (congrArg (fun r => reductionSeq_in_HoTFT1 r) h)
  | _, _, _, _, .symm α =>
      reductionSeq_symm_in_HoTFT2 (structuralHomotopy2_in_HoTFT2 α)
  | _, _, _, _, .trans α β =>
      HoTFT2.trans (structuralHomotopy2_in_HoTFT2 α)
        (structuralHomotopy2_in_HoTFT2 β)
  | _, _, _, _, .whiskerLeft r α =>
      reductionSeq_whiskerLeft_in_HoTFT2 r (structuralHomotopy2_in_HoTFT2 α)
  | _, _, _, _, .whiskerRight (.refl p) s =>
      HoTFT2.refl (reductionSeq_in_HoTFT1 (ReductionSeq.concat p s))
  | _, _, _, _, .whiskerRight α s =>
      reductionSeq_whiskerRight_in_HoTFT2
        (structuralHomotopy2_in_HoTFT2 α) s

/-- Every explicit syntactic 2-cell between parallel βη paths induces a
proof-relevant HoTFT 2-conversion carried by actual semantic 2-simplices
between the corresponding structural HoTFT 1-cells. -/
noncomputable def homotopy2_in_HoTFT2 {M N : Term} {p q : ReductionSeq M N}
    (α : Homotopy2 p q) :
    HoTFT2 (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q) :=
  fun K => homotopy2_in_Theory2 K α

/-- The interpreted structural vertical composition carries an explicit HoTFT
tetrahedron with its full boundary triangles. -/
noncomputable def homotopy2_trans_in_HoTFTTetrahedron
    {M N : Term} {p q s : ReductionSeq M N}
    (α : Homotopy2 p q) (β : Homotopy2 q s) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle (homotopy2_in_HoTFT2 β))
      (HoTFT2.toTriangle (homotopy2_in_HoTFT2 (Homotopy2.trans α β)))
      (HoTFT2.toTriangle (homotopy2_in_HoTFT2 α)) :=
  HoTFT3.transFillerTetrahedron
    (homotopy2_in_HoTFT2 α)
    (homotopy2_in_HoTFT2 β)

/-- Interpreting a syntactic reflexive 2-cell at the HoTFT layer is
definitionally the reflexive HoTFT 2-cell on the interpreted path. -/
theorem homotopy2_in_HoTFT2_refl
    {M N : Term} (p : ReductionSeq M N) :
    homotopy2_in_HoTFT2 (Homotopy2.refl p) =
      HoTFT2.refl (reductionSeq_in_HoTFT1 p) :=
  rfl

/-- Interpreting a reflexive syntactic right whisker at the HoTFT layer
unfolds definitionally to the reflexive HoTFT 2-cell on the interpreted
concatenation. -/
theorem homotopy2_in_HoTFT2_whiskerRight_refl
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    homotopy2_in_HoTFT2 (whiskerRight (Homotopy2.refl p) s) =
      HoTFT2.refl (reductionSeq_in_HoTFT1 (ReductionSeq.concat p s)) :=
  rfl

/-- HoTFT 3-cell packaging the definitional bridge from the interpreted
syntactic `whiskerRight` reflexivity source to the reflexive HoTFT source on
the interpreted concatenation. -/
noncomputable def homotopy2_whiskerRight_refl_source_bridge_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFT3
      (homotopy2_in_HoTFT2 (whiskerRight (Homotopy2.refl p) s))
      (HoTFT2.refl (reductionSeq_in_HoTFT1 (ReductionSeq.concat p s))) :=
  HoTFT3.ofEq (homotopy2_in_HoTFT2_whiskerRight_refl p s)

/-- Interpreting the reflexive syntactic 2-cell on a concatenated path is
definitionally the reflexive HoTFT 2-cell on the interpreted concatenation. -/
theorem homotopy2_in_HoTFT2_refl_concat
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    homotopy2_in_HoTFT2 (Homotopy2.refl (ReductionSeq.concat p s)) =
      HoTFT2.refl (reductionSeq_in_HoTFT1 (ReductionSeq.concat p s)) :=
  rfl

/-- Triangle coherence for interpreted explicit paths at the HoTFT layer. -/
noncomputable def reductionSeq_triangle_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (q : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.trans
        (reductionSeq_associator_in_HoTFT2 p (ReductionSeq.refl M) q)
        (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 p)
          (reductionSeq_leftUnitor_in_HoTFT2 q)))
      (HoTFT2.whiskerRight
        (reductionSeq_rightUnitor_in_HoTFT2 p)
        (reductionSeq_in_HoTFT1 q)) :=
  HoTFT3.triangle
    (reductionSeq_in_HoTFT1 p)
    (reductionSeq_in_HoTFT1 q)

/-- HoTFT 3-cell packaging the definitional bridge from the interpreted
syntactic reflexive target of `whiskerRightRefl` to the structural HoTFT
reflexive target on the concatenated path. -/
noncomputable def homotopy2_refl_concat_target_bridge_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFT3
      (homotopy2_in_HoTFT2 (Homotopy2.refl (ReductionSeq.concat p s)))
      (HoTFT2.refl (reductionSeq_in_HoTFT1 (ReductionSeq.concat p s))) :=
  HoTFT3.ofEq (homotopy2_in_HoTFT2_refl_concat p s)

/-- Left whiskering of an interpreted explicit 2-cell carries an explicit
HoTFT tetrahedron with its full boundary triangles. -/
noncomputable def homotopy2_whiskerLeft_in_HoTFTTetrahedron
    {L M N : Term} (r : ReductionSeq L M)
    {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (homotopy2_in_HoTFT2 α))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r) (homotopy2_in_HoTFT2 α)))
      (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 r) (reductionSeq_in_HoTFT1 q))
      (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 r) (reductionSeq_in_HoTFT1 p)) :=
  HoTFT3.whiskerLeftTetrahedron (reductionSeq_in_HoTFT1 r) (homotopy2_in_HoTFT2 α)

/-- Left whiskering commutes with vertical composition for interpreted explicit
HoTFT 2-cells. -/
noncomputable def homotopy2_whiskerLeftTrans_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M)
    {p q s : ReductionSeq M N} (α : Homotopy2 p q) (β : Homotopy2 q s) :
    HoTFT3
      (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r)
        (HoTFT2.trans (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β)))
      (HoTFT2.trans
        (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r) (homotopy2_in_HoTFT2 α))
        (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r) (homotopy2_in_HoTFT2 β))) :=
  HoTFT3.whiskerLeftTrans (reductionSeq_in_HoTFT1 r)
    (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β)

/-- Left whiskering commutes with symmetry for interpreted explicit HoTFT
2-cells. -/
noncomputable def homotopy2_whiskerLeftSymm_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M)
    {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    HoTFT3
      (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r)
        (HoTFT2.symm (homotopy2_in_HoTFT2 α)))
      (HoTFT2.symm
        (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r)
          (homotopy2_in_HoTFT2 α))) :=
  HoTFT3.whiskerLeftSymm (reductionSeq_in_HoTFT1 r) (homotopy2_in_HoTFT2 α)

/-- The inverse direction of left-whisker symmetry for interpreted explicit
HoTFT 2-cells. -/
noncomputable def homotopy2_invWhiskerLeft_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M)
    {p q : ReductionSeq M N} (α : Homotopy2 p q) :
    HoTFT3
      (HoTFT2.symm
        (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r)
          (homotopy2_in_HoTFT2 α)))
      (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r)
        (HoTFT2.symm (homotopy2_in_HoTFT2 α))) :=
  HoTFT3.invWhiskerLeft (reductionSeq_in_HoTFT1 r) (homotopy2_in_HoTFT2 α)

/-- Right whiskering commutes with vertical composition for interpreted explicit
HoTFT 2-cells. -/
noncomputable def homotopy2_whiskerRightTrans_in_HoTFT3
    {L M N : Term} {p q s : ReductionSeq L M}
    (α : Homotopy2 p q) (β : Homotopy2 q s) (r : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.whiskerRight
        (HoTFT2.trans (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β))
        (reductionSeq_in_HoTFT1 r))
      (HoTFT2.trans
        (HoTFT2.whiskerRight (homotopy2_in_HoTFT2 α)
          (reductionSeq_in_HoTFT1 r))
        (HoTFT2.whiskerRight (homotopy2_in_HoTFT2 β)
          (reductionSeq_in_HoTFT1 r))) :=
  HoTFT3.whiskerRightTrans
    (homotopy2_in_HoTFT2 α)
    (homotopy2_in_HoTFT2 β)
    (reductionSeq_in_HoTFT1 r)

/-- Right whiskering commutes with symmetry for interpreted explicit HoTFT
2-cells. -/
noncomputable def homotopy2_whiskerRightSymm_in_HoTFT3
    {L M N : Term} {p q : ReductionSeq L M}
    (α : Homotopy2 p q) (s : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.whiskerRight
        (HoTFT2.symm (homotopy2_in_HoTFT2 α))
        (reductionSeq_in_HoTFT1 s))
      (HoTFT2.symm
        (HoTFT2.whiskerRight (homotopy2_in_HoTFT2 α)
          (reductionSeq_in_HoTFT1 s))) :=
  HoTFT3.whiskerRightSymm (homotopy2_in_HoTFT2 α) (reductionSeq_in_HoTFT1 s)

/-- The inverse direction of right-whisker symmetry for interpreted explicit
HoTFT 2-cells. -/
noncomputable def homotopy2_invWhiskerRight_in_HoTFT3
    {L M N : Term} {p q : ReductionSeq L M}
    (α : Homotopy2 p q) (s : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.symm
        (HoTFT2.whiskerRight (homotopy2_in_HoTFT2 α)
          (reductionSeq_in_HoTFT1 s)))
      (HoTFT2.whiskerRight
        (HoTFT2.symm (homotopy2_in_HoTFT2 α))
        (reductionSeq_in_HoTFT1 s)) :=
  HoTFT3.invWhiskerRight (homotopy2_in_HoTFT2 α) (reductionSeq_in_HoTFT1 s)

/-- Right whiskering of an interpreted explicit 2-cell carries an explicit
HoTFT tetrahedron with its full boundary triangles. -/
noncomputable def homotopy2_whiskerRight_in_HoTFTTetrahedron
    {L M N : Term} {p q : ReductionSeq L M}
    (α : Homotopy2 p q) (s : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (reductionSeq_in_HoTFT1 s)))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerRight (homotopy2_in_HoTFT2 α) (reductionSeq_in_HoTFT1 s)))
      (HoTFT1.compTriangle (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 s))
      (HoTFT1.whiskerRightTriangle (homotopy2_in_HoTFT2 α) (reductionSeq_in_HoTFT1 s)) :=
  HoTFT3.whiskerRightTetrahedron (homotopy2_in_HoTFT2 α) (reductionSeq_in_HoTFT1 s)

/-- Left whiskering preserves reflexive interpreted 2-cells up to a
proof-relevant HoTFT 3-cell. -/
noncomputable def homotopy2_whiskerLeftRefl_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M) (p : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 r)
        (HoTFT2.refl (reductionSeq_in_HoTFT1 p)))
      (HoTFT2.refl
        (HoTFT1.comp (reductionSeq_in_HoTFT1 r) (reductionSeq_in_HoTFT1 p))) :=
  HoTFTTetrahedron.path3
    (homotopy2_whiskerLeft_in_HoTFTTetrahedron r (Homotopy2.refl p))
    (reductionSeq_comp_refl_in_HoTFTTetrahedron r p)

/-- Structural left whiskering of a reflexive HoTFT 2-cell along an explicit
βη path normalizes directly to the reflexive interpreted composite HoTFT
1-cell. -/
noncomputable def reductionSeq_whiskerLeftRefl_in_HoTFT3
    {L M N : Term} (r : ReductionSeq L M) (p : ReductionSeq M N) :
    HoTFT3
      (reductionSeq_whiskerLeft_in_HoTFT2 r
        (HoTFT2.refl (reductionSeq_in_HoTFT1 p)))
      (HoTFT2.refl (reductionSeq_in_HoTFT1 (ReductionSeq.concat r p))) :=
  fun K => reductionSeq_whiskerLeftRefl_in_Theory3 K r p

/-- A first boundary-aware 4-simplex comparison for right whiskering of a
reflexive interpreted 2-cell at the HoTFT layer. The remaining gap is now only
the final normalization of this tetrahedron into `HoTFT3`. -/
noncomputable def homotopy2_whiskerRightRefl_in_HoTFTTetrahedron
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle
        (HoTFT2.refl
          (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 s))))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerRight
          (HoTFT2.refl (reductionSeq_in_HoTFT1 p))
          (reductionSeq_in_HoTFT1 s)))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerRight
          (HoTFT2.refl (reductionSeq_in_HoTFT1 p))
          (reductionSeq_in_HoTFT1 s))) :=
  HoTFTTetrahedron.comparison
    (homotopy2_whiskerRight_in_HoTFTTetrahedron (Homotopy2.refl p) s)
    (reductionSeq_comp_refl_in_HoTFTTetrahedron p s)
    (homotopy2_whiskerRight_in_HoTFTTetrahedron (Homotopy2.refl p) s)

/-- The normalized HoTFT bridge tetrahedron for `whiskerRightRefl`. Its
fourth face is already the reflexive 2-cell on the semantic composite, so it
packages directly into a HoTFT 3-cell. -/
noncomputable def homotopy2_whiskerRightRefl_bridge_in_HoTFTTetrahedron
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFTTetrahedron
      (HoTFT2.toTriangle (HoTFT2.refl (HoTFT1.refl N)))
      (HoTFT2.toTriangle
        (HoTFT2.refl
          (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 s))))
      (HoTFT2.toTriangle
        (HoTFT2.whiskerRight
          (HoTFT2.refl (reductionSeq_in_HoTFT1 p))
          (reductionSeq_in_HoTFT1 s)))
      (HoTFT2.toTriangle
        (HoTFT2.refl
          (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 s)))) :=
  fun K => homotopy2_whiskerRightRefl_bridge_in_TheoryTetrahedron K p s

/-- Right whiskering preserves reflexive interpreted 2-cells up to a
proof-relevant HoTFT 3-cell. -/
noncomputable def homotopy2_whiskerRightRefl_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.whiskerRight
        (HoTFT2.refl (reductionSeq_in_HoTFT1 p))
        (reductionSeq_in_HoTFT1 s))
      (HoTFT2.refl
        (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 s))) :=
  fun K => homotopy2_whiskerRightRefl_in_Theory3 K p s

/-- Naming wrapper for the normalized HoTFT `whiskerRightRefl` simplification
step for the standalone semantic right-whisker normalization witness. -/
noncomputable def reductionSeq_whiskerRight_refl_simplify_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.whiskerRight
        (HoTFT2.refl (reductionSeq_in_HoTFT1 p))
        (reductionSeq_in_HoTFT1 s))
      (HoTFT2.refl
        (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 s))) :=
  homotopy2_whiskerRightRefl_in_HoTFT3 p s

/-- HoTFT counterpart of `reductionSeq_whiskerRight_refl_inner_in_Theory3`. It
collapses the inner `trans w c` shell to `c`, leaving only the missing
left-transport step for the legacy unnormalized structural shell. -/
noncomputable def reductionSeq_whiskerRight_refl_inner_in_HoTFT3
    {L M N : Term} (p : ReductionSeq L M) (s : ReductionSeq M N) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.whiskerRight
          (HoTFT2.refl (reductionSeq_in_HoTFT1 p))
          (reductionSeq_in_HoTFT1 s))
        (reductionSeq_comp_in_HoTFT2 p s))
      (reductionSeq_comp_in_HoTFT2 p s) :=
  HoTFT3.trans
    (HoTFT3.transCongrLeft
      (reductionSeq_whiskerRight_refl_simplify_in_HoTFT3 p s)
      (reductionSeq_comp_in_HoTFT2 p s))
    (HoTFT3.transReflLeft (reductionSeq_comp_in_HoTFT2 p s))

/-- Every explicit syntactic 2-cell admits a reflexive semantic HoTFT 3-cell
over its interpreted HoTFT 2-cell. -/
noncomputable def homotopy2_refl_in_HoTFT3 {M N : Term} {p q : ReductionSeq M N}
    (α : Homotopy2 p q) :
    HoTFT3 (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 α) :=
  HoTFT3.refl (homotopy2_in_HoTFT2 α)

/-- Equality of explicit syntactic 2-cells induces a semantic HoTFT 3-cell
between their interpreted HoTFT 2-cells. -/
noncomputable def homotopy2_eq_in_HoTFT3 {M N : Term} {p q : ReductionSeq M N}
    {α β : Homotopy2 p q} (h : α = β) :
    HoTFT3 (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β) :=
  HoTFT3.ofEq (congrArg (fun γ => homotopy2_in_HoTFT2 γ) h)

/-- The semantic image of syntactic interchange is already a HoTFT 3-cell in
the current modelwise simplicial layer. -/
noncomputable def homotopy2_interchange_in_HoTFT3 {L M N : Term}
    {p p' : ReductionSeq L M} {q q' : ReductionSeq M N}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    HoTFT3
      (HoTFT2.hcomp (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β))
      (HoTFT2.trans
        (HoTFT2.whiskerRight (homotopy2_in_HoTFT2 α) (reductionSeq_in_HoTFT1 q))
        (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 p') (homotopy2_in_HoTFT2 β))) :=
  HoTFT3.interchange (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β)

/-- Alternative interchange on interpreted explicit 2-cells at the HoTFT
3-cell layer. -/
noncomputable def homotopy2_interchange'_in_HoTFT3 {L M N : Term}
    {p p' : ReductionSeq L M} {q q' : ReductionSeq M N}
    (α : Homotopy2 p p') (β : Homotopy2 q q') :
    HoTFT3
      (HoTFT2.hcomp (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β))
      (HoTFT2.trans
        (HoTFT2.whiskerLeft (reductionSeq_in_HoTFT1 p) (homotopy2_in_HoTFT2 β))
        (HoTFT2.whiskerRight (homotopy2_in_HoTFT2 α) (reductionSeq_in_HoTFT1 q'))) :=
  HoTFT3.interchange' (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β)

/-- Every structurally supported syntactic 3-cell between parallel explicit
2-cells induces a proof-relevant HoTFT 3-conversion between the corresponding
interpreted HoTFT 2-cells. -/
noncomputable def structuralHomotopy3_in_HoTFT3 :
    {M N : Term} → {p q : ReductionSeq M N} → {α β : Homotopy2 p q} →
      HigherLambdaModel.Lambda.HigherTerms.StructuralHomotopy3 α β →
        HoTFT3 (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β)
  | _, _, _, _, _, _, .refl α =>
      homotopy2_refl_in_HoTFT3 α
  | _, _, _, _, _, _, .ofEq h =>
      homotopy2_eq_in_HoTFT3 h
  | _, _, _, _, _, _, .symm η =>
      HoTFT3.symm (structuralHomotopy3_in_HoTFT3 η)
  | _, _, _, _, _, _, .trans η θ =>
      HoTFT3.trans
        (structuralHomotopy3_in_HoTFT3 η)
        (structuralHomotopy3_in_HoTFT3 θ)
  | _, _, _, _, _, _, .whiskerLeftRefl r p =>
      reductionSeq_whiskerLeftRefl_in_HoTFT3 r p
  | _, _, _, _, _, _, .whiskerLeftTrans r α β =>
      reductionSeq_whiskerLeftTrans_in_HoTFT3 r
        (homotopy2_in_HoTFT2 α) (homotopy2_in_HoTFT2 β)
  | _, _, _, _, _, _, .whiskerLeftSymm r α =>
      reductionSeq_whiskerLeftSymm_in_HoTFT3 r (homotopy2_in_HoTFT2 α)
  | _, _, _, _, _, _, .whiskerRightRefl p s =>
      homotopy2_refl_in_HoTFT3 (Homotopy2.refl (ReductionSeq.concat p s))
  | _, _, _, _, _, _, .interchange α β =>
      homotopy2_eq_in_HoTFT3 rfl

theorem beta_in_HoTFT (M N : Term) : (Term.app (Term.lam M) N) =_HoTFT (M[N]) := fun K ρ =>
  beta_sound K M N ρ

/-- The β-law also yields a proof-relevant semantic 1-conversion in every model. -/
noncomputable def beta_in_HoTFT1 (M N : Term) : HoTFT1 (Term.app (Term.lam M) N) (M[N]) :=
  betaEtaStep_in_HoTFT1 _ _ (BetaEtaStep.beta (BetaStep.beta M N))

theorem eta_in_HoTFT (M : Term) (h : Term.hasFreeVar 0 M = false) :
    (Term.lam (Term.app (Term.shift 1 0 M) (Term.var 0))) =_HoTFT M := fun K ρ =>
  eta_sound K M ρ h

/-- The η-law also yields a proof-relevant semantic 1-conversion in every model. -/
noncomputable def eta_in_HoTFT1 (M : Term) (h : Term.hasFreeVar 0 M = false) :
    HoTFT1 (Term.lam (Term.app (Term.shift 1 0 M) (Term.var 0))) M :=
  HoTFT1.ofHoTFTEq (eta_in_HoTFT M h)

/-- Every extensional Kan complex packages into the repository's lightweight
`HomotopicLambdaModel` interface. -/
noncomputable def ExtensionalKanComplex.toHomotopicLambdaModel
    (K : ExtensionalKanComplex) : HomotopicLambdaModel where
  carrier := K.Obj
  app := K.app
  lam := K.G
  beta := by
    intro f x
    exact K.eta f x
  ext := by
    intro M N hMN
    have hF : K.F M = K.F N := by
      funext x
      exact hMN x
    calc
      M = K.G (K.F M) := K.epsilon M
      _ = K.G (K.F N) := by rw [hF]
      _ = N := (K.epsilon N).symm
  PathSpace := K.PathSpace
  Path2 := fun {M N} p q => K.Path2 p q
  path2_refl := by
    intro M N p
    exact K.reflPath2 p

/-- The raw horn for the pentagon right-hand-side route: a 2-horn missing face 1
whose remaining faces are the degenerate front triangle on `q · (r · s)`,
the composition triangle, and the pentagon right-back triangle. -/
private def KanComplex.pentagonRHSRawHorn (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    Horn K.toSimplicialSet 2 1 :=
  { missing_le := by omega
    facet := fun i _ =>
      if h0 : i = 0 then (K.reflPath2 (K.compPath q (K.compPath r s))).simplex
      else if h2 : i = 2 then (K.compTriangle p (K.compPath q (K.compPath r s))).simplex
      else (K.pentagonRightBackTriangle p q r s).simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases : (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
        omega
      rcases hij_cases with h02 | h03 | h23
      · rcases h02 with ⟨rfl, rfl⟩
        simpa using (K.compTriangle p (K.compPath q (K.compPath r s))).face0.trans
          (K.reflPath2 (K.compPath q (K.compPath r s))).face1.symm
      · rcases h03 with ⟨rfl, rfl⟩
        simpa using (K.pentagonRightBackTriangle p q r s).face0.trans
          (K.reflPath2 (K.compPath q (K.compPath r s))).face2.symm
      · rcases h23 with ⟨rfl, rfl⟩
        simpa using (K.pentagonRightBackTriangle p q r s).face2.trans
          (K.compTriangle p (K.compPath q (K.compPath r s))).face2.symm }

private def KanComplex.pentagonRHSRawSimplex (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) : K.Simplex 3 :=
  K.fill (K.pentagonRHSRawHorn p q r s)

/-- The raw Path2 extracted from the pentagon RHS horn fill. -/
private def KanComplex.pentagonRHSRawPath2 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path2
      (K.compPath (K.compPath (K.compPath p q) r) s)
      (K.compPath p (K.compPath q (K.compPath r s))) := by
  let Λ := K.pentagonRHSRawHorn p q r s
  refine
    { simplex := K.face 2 1 (K.pentagonRHSRawSimplex p q r s)
      face0 := ?_
      face1 := ?_
      face2 := ?_ }
  · have h0 : K.face 2 0 (K.pentagonRHSRawSimplex p q r s) =
        (K.reflPath2 (K.compPath q (K.compPath r s))).simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 1 0 (K.face 2 1 (K.pentagonRHSRawSimplex p q r s))
          = K.face 1 0 (K.face 2 0 (K.pentagonRHSRawSimplex p q r s)) := by
              simpa using
                (K.face_face 1 (K.pentagonRHSRawSimplex p q r s)
                  (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 1 0 (K.reflPath2 (K.compPath q (K.compPath r s))).simplex := by rw [h0]
      _ = (K.reflPath e).simplex := (K.reflPath2 (K.compPath q (K.compPath r s))).face0
  · have h2 : K.face 2 2 (K.pentagonRHSRawSimplex p q r s) =
        (K.compTriangle p (K.compPath q (K.compPath r s))).simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 1 1 (K.face 2 1 (K.pentagonRHSRawSimplex p q r s))
          = K.face 1 1 (K.face 2 2 (K.pentagonRHSRawSimplex p q r s)) := by
              symm
              simpa using
                (K.face_face 1 (K.pentagonRHSRawSimplex p q r s)
                  (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 1 1 (K.compTriangle p (K.compPath q (K.compPath r s))).simplex := by rw [h2]
      _ = (K.compPath p (K.compPath q (K.compPath r s))).simplex :=
            (K.compTriangle p (K.compPath q (K.compPath r s))).face1
  · have h3 : K.face 2 3 (K.pentagonRHSRawSimplex p q r s) =
        (K.pentagonRightBackTriangle p q r s).simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 1 2 (K.face 2 1 (K.pentagonRHSRawSimplex p q r s))
          = K.face 1 1 (K.face 2 3 (K.pentagonRHSRawSimplex p q r s)) := by
              symm
              simpa using
                (K.face_face 1 (K.pentagonRHSRawSimplex p q r s)
                  (i := 1) (j := 2) (by omega) (by omega))
      _ = K.face 1 1 (K.pentagonRightBackTriangle p q r s).simplex := by rw [h3]
      _ = (K.compPath (K.compPath (K.compPath p q) r) s).simplex :=
            (K.pentagonRightBackTriangle p q r s).face1

/-- The boundary-aware tetrahedron from the pentagon RHS horn fill. -/
private def KanComplex.pentagonRHSRawTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle
      (K.pentagonRHSRawPath2 p q r s).toTriangle
      (K.compTriangle p (K.compPath q (K.compPath r s)))
      (K.pentagonRightBackTriangle p q r s) := by
  let Λ := K.pentagonRHSRawHorn p q r s
  refine
    { simplex := K.pentagonRHSRawSimplex p q r s
      face0 := ?_
      face1 := rfl
      face2 := ?_
      face3 := ?_ }
  · simpa [KanComplex.pentagonRHSRawSimplex, Λ] using
      (K.fill_spec Λ (i := 0) (by omega) (by omega))
  · simpa [KanComplex.pentagonRHSRawSimplex, Λ] using
      (K.fill_spec Λ (i := 2) (by omega) (by omega))
  · simpa [KanComplex.pentagonRHSRawSimplex, Λ] using
      (K.fill_spec Λ (i := 3) (by omega) (by omega))

/-- The pure-Path2 pentagon comparison tetrahedron, obtained by comparing the
raw RHS route against the left-route associator. -/
private def KanComplex.pentagonComparisonTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath e)).toTriangle
      (K.associatorPath2 p q (K.compPath r s)).toTriangle
      (K.pentagonRHSRawPath2 p q r s).toTriangle
      (K.associatorPath2 (K.compPath p q) r s).toTriangle :=
  K.tetrahedronComparisonTetrahedron
    (K.pentagonRHSRawTetrahedron p q r s)
    (K.associatorTetrahedron p q (K.compPath r s))
    (K.pentagonBackComparisonTetrahedron p q r s)

/-- The raw pentagon Path3 from the left route to the horn-fill-determined
right route. -/
private def KanComplex.pentagonRawPath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s)))
      (K.pentagonRHSRawPath2 p q r s) :=
  K.tetrahedronFace2Path3
    (K.reflPath3 (K.associatorPath2 (K.compPath p q) r s))
    (K.transFillerTetrahedron
      (K.associatorPath2 (K.compPath p q) r s)
      (K.associatorPath2 p q (K.compPath r s)))
    (K.pentagonComparisonTetrahedron p q r s)

/-- Contracting the loop comparing the two pentagon back triangles is enough to
normalize the back-face comparison to a reflexive middle face. -/
private def KanComplex.pentagonBackComparisonFromLoopContraction (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e)
    (Κ :
      K.Path3
        (K.trianglePath2
          (K.pentagonInnerBackTriangle p q r s)
          (K.pentagonRightBackTriangle p q r s))
        (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s))) :
    K.Tetrahedron
      (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle
      (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)).toTriangle
      (K.pentagonRightBackTriangle p q r s)
      (K.pentagonInnerBackTriangle p q r s) :=
  K.tetrahedronReplaceFace1 Κ
    (K.pentagonInnerBackComparisonTetrahedron p q r s)

/-- The target 3-fold composite on the right side of the pentagon identity,
connected to the horn-fill raw path by `tetrahedronPath3`. Both tetrahedra
share the same boundary except face 1, so `tetrahedronPath3` extracts the
bridge Path3 between the two face 1 cells.

Current state:

* The normalized-front comparison layer is already implemented via
  `pentagonFrontComparisonTetrahedron`,
  `pentagonWhiskerFrontComparisonPath3`,
  `pentagonStep1BoundaryCoreTetrahedron`, and
  `pentagonStep12BoundaryCoreTetrahedron`.
* The full triple-composite right-hand route also has a boundary-aware
  tetrahedron `pentagonStep123BoundaryCoreTetrahedron`.
* So the remaining gap is now strictly smaller than before: the full boundary
  tetrahedron is no longer postulated directly. It is reconstructed from a
  smaller back-only 3-cell `pentagonBackComparisonReflPath3`, which contracts
  the comparison between `pentagonInnerBackTriangle p q r s` and
  `pentagonRightBackTriangle p q r s` to reflexivity on the common back edge.
-/
private noncomputable def KanComplex.pentagonBoundaryTetrahedronFromMiddleComparison (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e)
    (middleComparison :
      K.Tetrahedron
        (K.reflPath2 (K.reflPath e)).toTriangle
        (K.transPath2
          (K.transPath2
            (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
            (K.associatorPath2 p (K.compPath q r) s))
          (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
        (K.transPath2
          (K.transPath2
            (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
            (K.associatorPath2 p (K.compPath q r) s))
          (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
        (K.trianglePath2
          (K.pentagonInnerBackTriangle p q r s)
          (K.pentagonRightBackTriangle p q r s)).toTriangle) :
    K.Tetrahedron
      (K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
      (K.compTriangle p (K.compPath q (K.compPath r s)))
      (K.pentagonRightBackTriangle p q r s) := by
  let ε := K.reflTriangleTetrahedron
    ((K.reflPath2 (K.compPath q (K.compPath r s))).toTriangle)
  let ω := K.pentagonStep123BoundaryCoreTetrahedron p q r s
  let κ := K.pentagonInnerBackComparisonTetrahedron p q r s
  let Λ : Horn K.toSimplicialSet 3 2 :=
    { missing_le := by omega
      facet := fun i _ =>
        if h0 : i = 0 then ε.simplex
        else if h1 : i = 1 then middleComparison.simplex
        else if h3 : i = 3 then ω.simplex
        else κ.simplex
      compatibility := by
        intro i j hi hj hmi hmj hij
        have hij_cases :
            (i = 0 ∧ j = 1) ∨ (i = 0 ∧ j = 3) ∨ (i = 0 ∧ j = 4) ∨
              (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by
          omega
        rcases hij_cases with h01 | hrest
        · rcases h01 with ⟨rfl, rfl⟩
          simpa using middleComparison.face0.trans ε.face0.symm
        · rcases hrest with h03 | hrest
          · rcases h03 with ⟨rfl, rfl⟩
            simpa using ω.face0.trans ε.face2.symm
          · rcases hrest with h04 | hrest
            · rcases h04 with ⟨rfl, rfl⟩
              simpa using κ.face0.trans ε.face3.symm
            · rcases hrest with h13 | hrest
              · rcases h13 with ⟨rfl, rfl⟩
                simpa using ω.face1.trans middleComparison.face2.symm
              · rcases hrest with h14 | h34
                · rcases h14 with ⟨rfl, rfl⟩
                  simpa using κ.face1.trans middleComparison.face3.symm
                · rcases h34 with ⟨rfl, rfl⟩
                  simpa using κ.face3.trans ω.face3.symm
      }
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
  · have h1 : K.face 3 1 (K.fill Λ) = middleComparison.simplex :=
      K.fill_spec Λ (i := 1) (by omega) (by omega)
    calc
      K.face 2 1 (K.face 3 2 (K.fill Λ))
          = K.face 2 1 (K.face 3 1 (K.fill Λ)) := by
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 2 1 middleComparison.simplex := by rw [h1]
      _ = (K.transPath2
            (K.transPath2
              (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
              (K.associatorPath2 p (K.compPath q r) s))
            (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle.simplex :=
          middleComparison.face1
  · have h3 : K.face 3 3 (K.fill Λ) = ω.simplex :=
      K.fill_spec Λ (i := 3) (by omega) (by omega)
    calc
      K.face 2 2 (K.face 3 2 (K.fill Λ))
          = K.face 2 2 (K.face 3 3 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 2 (K.fill Λ)
                (i := 2) (j := 2) (by omega) (by omega))
      _ = K.face 2 2 ω.simplex := by rw [h3]
      _ = (K.compTriangle p (K.compPath q (K.compPath r s))).simplex := ω.face2
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

/-- Comparing the raw RHS horn-fill tetrahedron against the normalized
step-1/2/3 boundary core keeps the back comparison explicit while isolating the
middle-face difference between the raw horn-fill route and the fully normalized
right-hand composite. -/
private noncomputable def KanComplex.pentagonRawBigComparisonTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath e)).toTriangle
      (K.pentagonRHSRawPath2 p q r s).toTriangle
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s)).toTriangle :=
  K.tetrahedronComparisonTetrahedron
    (K.pentagonStep123BoundaryCoreTetrahedron p q r s)
    (K.pentagonRHSRawTetrahedron p q r s)
    (K.pentagonInnerBackComparisonTetrahedron p q r s)

/-- Comparing the normalized step-1/2/3 boundary core against the canonical
left-hand pentagon boundary keeps the same back-triangle comparison explicit
while isolating the middle-face difference between the normalized right-hand
composite and the left-hand composite route. -/
private noncomputable def KanComplex.pentagonLeftBigComparisonTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath e)).toTriangle
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s))).toTriangle
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s)).toTriangle :=
  K.tetrahedronComparisonTetrahedron
    (K.pentagonStep123BoundaryCoreTetrahedron p q r s)
    (K.pentagonRightBoundaryCoreTetrahedron p q r s)
    (K.pentagonInnerBackComparisonTetrahedron p q r s)

/-- Even before the back comparison contracts, the two big comparison
tetrahedra already give a direct semantic 3-cell from the raw RHS horn-fill
route back to the left-associated pentagon route. This packages the remaining
gap as the comparison between two different left-to-raw proofs. -/
private noncomputable def KanComplex.pentagonRawLeftComparisonPath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.pentagonRHSRawPath2 p q r s)
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s))) :=
  K.tetrahedronPath3
    (K.pentagonRHSRawTetrahedron p q r s)
    (K.pentagonRightBoundaryCoreTetrahedron p q r s)

/-- The left-associated pentagon route also reaches the raw RHS horn-fill route
through the same back-comparison face that remains unresolved later on. -/
private noncomputable def KanComplex.pentagonRawAlternativePath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s)))
      (K.pentagonRHSRawPath2 p q r s) :=
  K.symmPath3 (K.pentagonRawLeftComparisonPath3 p q r s)

/-- If the back-triangle comparison contracts to reflexivity, then the raw RHS
comparison tetrahedron upgrades to the smaller back-normalization tetrahedron
used by `pentagonBoundaryTetrahedronFromMiddleComparison`. -/
private noncomputable def KanComplex.pentagonBackNormalizationTetrahedronFromBackContract
    (K : KanComplex) {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e)
    (backContract :
      K.Path3
        (K.trianglePath2
          (K.pentagonInnerBackTriangle p q r s)
          (K.pentagonRightBackTriangle p q r s))
        (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s))) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath e)).toTriangle
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s)).toTriangle :=
  K.tetrahedronReplaceFace1
    (K.symmPath3
      (K.tetrahedronFace2Path3 backContract
        (K.pentagonRawBigComparisonTetrahedron p q r s)
        ((K.reflPath3 (K.pentagonRHSRawPath2 p q r s)).toTetrahedron)))
    (K.pentagonRawBigComparisonTetrahedron p q r s)

axiom KanComplex.pentagonBackComparisonReflPath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s))
      (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s))

/-- The remaining back-loop contraction also yields the final normalized
right-to-left pentagon comparison directly, without passing through the raw RHS
horn-fill route. -/
private noncomputable def KanComplex.pentagonBigLeftPath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s)))
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s))) :=
  K.tetrahedronFace2Path3
    (K.pentagonBackComparisonReflPath3 p q r s)
    (K.pentagonLeftBigComparisonTetrahedron p q r s)
    ((K.reflPath3
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s)))).toTetrahedron)

private noncomputable def KanComplex.pentagonBackNormalizationTetrahedron (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Tetrahedron
      (K.reflPath2 (K.reflPath e)).toTriangle
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))).toTriangle
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s)).toTriangle :=
  K.pentagonBackNormalizationTetrahedronFromBackContract p q r s
    (K.pentagonBackComparisonReflPath3 p q r s)

private noncomputable def KanComplex.pentagonBoundaryTetrahedron (K : KanComplex)
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
      (K.pentagonRightBackTriangle p q r s) :=
  K.pentagonBoundaryTetrahedronFromMiddleComparison p q r s
    (K.pentagonBackNormalizationTetrahedron p q r s)

/-- The remaining pentagon bridge is extracted from the final
boundary-normalized tetrahedron. -/
noncomputable def KanComplex.pentagonBridgePath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.pentagonRHSRawPath2 p q r s)
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))) :=
  K.tetrahedronPath3
    (K.pentagonRHSRawTetrahedron p q r s)
    (K.pentagonBoundaryTetrahedron p q r s)

/-- Pentagon coherence: the 3-cell witnessing that two different ways of
reassociating four consecutive paths are homotopic. This packages the standard
simplicial pentagon filler for the chosen associators. -/
noncomputable def KanComplex.pentagonPath3 (K : KanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.transPath2
        (K.associatorPath2 (K.compPath p q) r s)
        (K.associatorPath2 p q (K.compPath r s)))
      (K.transPath2
        (K.transPath2
          (K.whiskerRightPath2 (K.associatorPath2 p q r) s)
          (K.associatorPath2 p (K.compPath q r) s))
        (K.whiskerLeftPath2 p (K.associatorPath2 q r s))) :=
  K.symmPath3 (K.pentagonBigLeftPath3 p q r s)

/-- Pentagon coherence at the semantic 3-cell layer. -/
noncomputable def Theory3.pentagon
    (K : ExtensionalKanComplex)
    {L M N P Q : Term}
    (α : Theory1 K L M) (β : Theory1 K M N)
    (γ : Theory1 K N P) (δ : Theory1 K P Q) :
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K (Theory1.comp K α β) γ δ)
        (Theory2.associator K α β (Theory1.comp K γ δ)))
      (Theory2.trans K
        (Theory2.trans K
          (Theory2.whiskerRight K (Theory2.associator K α β γ) δ)
          (Theory2.associator K α (Theory1.comp K β γ) δ))
        (Theory2.whiskerLeft K α (Theory2.associator K β γ δ))) :=
  fun ρ => K.toReflexiveKanComplex.pentagonPath3 (α ρ) (β ρ) (γ ρ) (δ ρ)

/-- Backward-compatible alias for semantic pentagon coherence. -/
noncomputable def Theory3.pentagonPath3
    (K : ExtensionalKanComplex)
    {L M N P Q : Term}
    (α : Theory1 K L M) (β : Theory1 K M N)
    (γ : Theory1 K N P) (δ : Theory1 K P Q) :
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K (Theory1.comp K α β) γ δ)
        (Theory2.associator K α β (Theory1.comp K γ δ)))
      (Theory2.trans K
        (Theory2.trans K
          (Theory2.whiskerRight K (Theory2.associator K α β γ) δ)
          (Theory2.associator K α (Theory1.comp K β γ) δ))
        (Theory2.whiskerLeft K α (Theory2.associator K β γ δ))) :=
  Theory3.pentagon K α β γ δ

/-- Pentagon coherence at the HoTFT 3-cell layer. -/
noncomputable def HoTFT3.pentagon
    {L M N P Q : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N)
    (γ : HoTFT1 N P) (δ : HoTFT1 P Q) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.associator (HoTFT1.comp α β) γ δ)
        (HoTFT2.associator α β (HoTFT1.comp γ δ)))
      (HoTFT2.trans
        (HoTFT2.trans
          (HoTFT2.whiskerRight (HoTFT2.associator α β γ) δ)
          (HoTFT2.associator α (HoTFT1.comp β γ) δ))
        (HoTFT2.whiskerLeft α (HoTFT2.associator β γ δ))) :=
  fun K => Theory3.pentagon K (α K) (β K) (γ K) (δ K)

/-- Backward-compatible alias for HoTFT pentagon coherence. -/
noncomputable def HoTFT3.pentagonPath3
    {L M N P Q : Term}
    (α : HoTFT1 L M) (β : HoTFT1 M N)
    (γ : HoTFT1 N P) (δ : HoTFT1 P Q) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.associator (HoTFT1.comp α β) γ δ)
        (HoTFT2.associator α β (HoTFT1.comp γ δ)))
      (HoTFT2.trans
        (HoTFT2.trans
          (HoTFT2.whiskerRight (HoTFT2.associator α β γ) δ)
          (HoTFT2.associator α (HoTFT1.comp β γ) δ))
        (HoTFT2.whiskerLeft α (HoTFT2.associator β γ δ))) :=
  HoTFT3.pentagon α β γ δ


/-- Pentagon coherence for interpreted explicit reduction sequences in a fixed
extensional Kan complex. -/
noncomputable def reductionSeq_pentagon_in_Theory3
    (K : ExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K
      (Theory2.trans K
        (Theory2.associator K
          (Theory1.comp K (reductionSeq_in_Theory1 K p) (reductionSeq_in_Theory1 K q))
          (reductionSeq_in_Theory1 K r)
          (reductionSeq_in_Theory1 K s))
        (Theory2.associator K
          (reductionSeq_in_Theory1 K p)
          (reductionSeq_in_Theory1 K q)
          (Theory1.comp K (reductionSeq_in_Theory1 K r) (reductionSeq_in_Theory1 K s))))
      (Theory2.trans K
        (Theory2.trans K
          (Theory2.whiskerRight K
            (Theory2.associator K
              (reductionSeq_in_Theory1 K p)
              (reductionSeq_in_Theory1 K q)
              (reductionSeq_in_Theory1 K r))
            (reductionSeq_in_Theory1 K s))
          (Theory2.associator K
            (reductionSeq_in_Theory1 K p)
            (Theory1.comp K (reductionSeq_in_Theory1 K q) (reductionSeq_in_Theory1 K r))
            (reductionSeq_in_Theory1 K s)))
        (Theory2.whiskerLeft K
          (reductionSeq_in_Theory1 K p)
          (Theory2.associator K
            (reductionSeq_in_Theory1 K q)
            (reductionSeq_in_Theory1 K r)
            (reductionSeq_in_Theory1 K s)))) :=
  Theory3.pentagon K
    (reductionSeq_in_Theory1 K p)
    (reductionSeq_in_Theory1 K q)
    (reductionSeq_in_Theory1 K r)
    (reductionSeq_in_Theory1 K s)

/-- Pentagon coherence for interpreted explicit reduction sequences at the HoTFT
3-cell layer. -/
noncomputable def reductionSeq_pentagon_in_HoTFT3
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    HoTFT3
      (HoTFT2.trans
        (HoTFT2.associator
          (HoTFT1.comp (reductionSeq_in_HoTFT1 p) (reductionSeq_in_HoTFT1 q))
          (reductionSeq_in_HoTFT1 r)
          (reductionSeq_in_HoTFT1 s))
        (HoTFT2.associator
          (reductionSeq_in_HoTFT1 p)
          (reductionSeq_in_HoTFT1 q)
          (HoTFT1.comp (reductionSeq_in_HoTFT1 r) (reductionSeq_in_HoTFT1 s))))
      (HoTFT2.trans
        (HoTFT2.trans
          (HoTFT2.whiskerRight
            (HoTFT2.associator
              (reductionSeq_in_HoTFT1 p)
              (reductionSeq_in_HoTFT1 q)
              (reductionSeq_in_HoTFT1 r))
            (reductionSeq_in_HoTFT1 s))
          (HoTFT2.associator
            (reductionSeq_in_HoTFT1 p)
            (HoTFT1.comp (reductionSeq_in_HoTFT1 q) (reductionSeq_in_HoTFT1 r))
            (reductionSeq_in_HoTFT1 s)))
        (HoTFT2.whiskerLeft
          (reductionSeq_in_HoTFT1 p)
          (HoTFT2.associator
            (reductionSeq_in_HoTFT1 q)
            (reductionSeq_in_HoTFT1 r)
            (reductionSeq_in_HoTFT1 s)))) :=
  HoTFT3.pentagon
    (reductionSeq_in_HoTFT1 p)
    (reductionSeq_in_HoTFT1 q)
    (reductionSeq_in_HoTFT1 r)
    (reductionSeq_in_HoTFT1 s)
end HigherLambdaModel.Lambda.ExtensionalKan



