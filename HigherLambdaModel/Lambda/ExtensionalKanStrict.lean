import HigherLambdaModel.Lambda.ExtensionalKanHigher

namespace HigherLambdaModel.Lambda.ExtensionalKan

open Term HigherTerms

namespace StrictKanComplex

private def simplex2Face0Horn (K : StrictKanComplex) {a b c : K.Obj}
    (p : K.PathSpace a b) (m : K.PathSpace a c) :
    Horn K.toSimplicialSet 1 0 :=
  { missing_le := by omega
    facet := fun i _ => if h1 : i = 1 then m.simplex else p.simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hi1 : i = 1 := by omega
      have hj2 : j = 2 := by omega
      subst hi1
      subst hj2
      simp
      exact p.source.trans m.source.symm }

private theorem simplex2_eq_of_face1_face2 (K : StrictKanComplex)
    {a b c : K.Obj} {p : K.PathSpace a b} {m : K.PathSpace a c}
    {q : K.PathSpace b c} (τ : K.Triangle p m q) {σ : K.Simplex 2}
    (h1 : K.face 1 1 σ = m.simplex) (h2 : K.face 1 2 σ = p.simplex) :
    σ = τ.simplex := by
  let Λ := K.simplex2Face0Horn p m
  have hσ : σ = K.fill Λ := by
    apply K.fill_unique Λ σ
    intro i hi hmi
    have hi_cases : i = 1 ∨ i = 2 := by omega
    rcases hi_cases with rfl | rfl
    · simpa [simplex2Face0Horn, Λ] using h1
    · simpa [simplex2Face0Horn, Λ] using h2
  have hτ : τ.simplex = K.fill Λ := by
    apply K.fill_unique Λ τ.simplex
    intro i hi hmi
    have hi_cases : i = 1 ∨ i = 2 := by omega
    rcases hi_cases with rfl | rfl
    · simpa [simplex2Face0Horn, Λ] using τ.face1
    · simpa [simplex2Face0Horn, Λ] using τ.face2
  exact hσ.trans hτ.symm

private def simplex3Face0Horn (K : StrictKanComplex) {a b c : K.Obj}
    {p01 : K.PathSpace a b} {p12 p13 : K.PathSpace b c}
    {p02 p03 : K.PathSpace a c}
    {γ : K.Path2 p12 p13} {α : K.Path2 p02 p03}
    {τ2 : K.Triangle p01 p03 p13} {τ3 : K.Triangle p01 p02 p12}
    (ω : K.Tetrahedron γ.toTriangle α.toTriangle τ2 τ3) :
    Horn K.toSimplicialSet 2 0 :=
  { missing_le := by omega
    facet := fun i _ =>
      if h1 : i = 1 then α.simplex
      else if h2 : i = 2 then τ2.simplex
      else τ3.simplex
    compatibility := by
      intro i j hi hj hmi hmj hij
      have hij_cases : (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by
        omega
      rcases hij_cases with h12 | h13 | h23
      · rcases h12 with ⟨rfl, rfl⟩
        calc
          K.face 1 1 τ2.simplex = K.face 1 1 (K.face 2 2 ω.simplex) := by
            rw [ω.face2]
          _ = K.face 1 1 (K.face 2 1 ω.simplex) := by
            simpa using (K.face_face 1 ω.simplex (i := 1) (j := 1) (by omega) (by omega))
          _ = K.face 1 1 (KanComplex.Path2.toTriangle K.toKanComplex α).simplex := by
            rw [ω.face1]
          _ = K.face 1 1 α.simplex := by
            rfl
      · rcases h13 with ⟨rfl, rfl⟩
        calc
          K.face 1 1 τ3.simplex = K.face 1 1 (K.face 2 3 ω.simplex) := by
            rw [ω.face3]
          _ = K.face 1 2 (K.face 2 1 ω.simplex) := by
            simpa using (K.face_face 1 ω.simplex (i := 1) (j := 2) (by omega) (by omega))
          _ = K.face 1 2 (KanComplex.Path2.toTriangle K.toKanComplex α).simplex := by
            rw [ω.face1]
          _ = K.face 1 2 α.simplex := by
            rfl
      · rcases h23 with ⟨rfl, rfl⟩
        calc
          K.face 1 2 τ3.simplex = K.face 1 2 (K.face 2 3 ω.simplex) := by
            rw [ω.face3]
          _ = K.face 1 2 (K.face 2 2 ω.simplex) := by
            simpa using (K.face_face 1 ω.simplex (i := 2) (j := 2) (by omega) (by omega))
          _ = K.face 1 2 τ2.simplex := by rw [ω.face2] }

private theorem simplex3_eq_of_face1_face2_face3 (K : StrictKanComplex)
    {a b c : K.Obj} {p01 : K.PathSpace a b} {p12 p13 : K.PathSpace b c}
    {p02 p03 : K.PathSpace a c}
    {γ : K.Path2 p12 p13} {α : K.Path2 p02 p03}
    {τ2 : K.Triangle p01 p03 p13} {τ3 : K.Triangle p01 p02 p12}
    (ω : K.Tetrahedron γ.toTriangle α.toTriangle τ2 τ3) {σ : K.Simplex 3}
    (h1 : K.face 2 1 σ = α.simplex)
    (h2 : K.face 2 2 σ = τ2.simplex)
    (h3 : K.face 2 3 σ = τ3.simplex) :
    σ = ω.simplex := by
  let Λ := K.simplex3Face0Horn ω
  have hσ : σ = K.fill Λ := by
    apply K.fill_unique Λ σ
    intro i hi hmi
    have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi_cases with rfl | hrest
    · simpa [simplex3Face0Horn, Λ] using h1
    · rcases hrest with rfl | rfl
      · simpa [simplex3Face0Horn, Λ] using h2
      · simpa [simplex3Face0Horn, Λ] using h3
  have hω : ω.simplex = K.fill Λ := by
    apply K.fill_unique Λ ω.simplex
    intro i hi hmi
    have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi_cases with rfl | hrest
    · simpa [simplex3Face0Horn, Λ] using ω.face1
    · rcases hrest with rfl | rfl
      · simpa [simplex3Face0Horn, Λ] using ω.face2
      · simpa [simplex3Face0Horn, Λ] using ω.face3
  exact hσ.trans hω.symm

theorem path2_eq_of_simplex_eq (K : StrictKanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} (α β : K.Path2 p q)
    (h : α.simplex = β.simplex) : α = β := by
  cases α
  cases β
  cases h
  simp

/-- In a strict Kan complex, parallel 2-cells are uniquely determined by their
boundary and therefore coincide. -/
theorem path2_eq (K : StrictKanComplex) {a b : K.Obj}
    {p q : K.PathSpace a b} (α β : K.Path2 p q) : α = β := by
  have hSimplex : α.simplex = β.simplex := by
    apply K.simplex2_eq_of_face1_face2 (β.toTriangle)
    · simpa using α.face1
    · simpa using α.face2
  exact K.path2_eq_of_simplex_eq α β hSimplex

/-- In a strict Kan complex, the direct front loop for the remaining right half
of `whiskerLeftWhiskerRight` contracts because its two visible boundary faces
already force it to be the reflexive 2-cell on `reflPath d`. -/
noncomputable def whiskerLeftWhiskerRightMidRightFrontReflPath3 (K : StrictKanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    K.Path3
      (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ)
      (K.reflPath2 (K.reflPath d)) := by
  have hFrontSimplex :
      (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ).simplex =
        (K.reflPath2 (K.reflPath d)).simplex := by
    apply K.simplex2_eq_of_face1_face2 ((K.reflPath2 (K.reflPath d)).toTriangle)
    · simpa using (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ).face1
    · simpa using (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ).face2
  have hFront :
      K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ =
        K.reflPath2 (K.reflPath d) :=
    K.path2_eq_of_simplex_eq
      (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ)
      (K.reflPath2 (K.reflPath d))
      hFrontSimplex
  simpa [hFront] using
    (K.reflPath3 (K.whiskerLeftWhiskerRightMidRightFrontPath2 α η δ))

/-- The remaining right half of `whiskerLeftWhiskerRight` is axiom-free in a
strict Kan complex. -/
noncomputable def whiskerLeftWhiskerRightMidRightPath3 (K : StrictKanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    K.Path3
      (K.trianglePath2
        (K.whiskerLeftWhiskerRightMidPath2 α η δ).toTriangle
        (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ).toTriangle)
      (K.symmPath2 (K.associatorPath2 α γ δ)) :=
  K.whiskerLeftWhiskerRightMidRightPath3OfFrontPath3 α η δ
    (K.whiskerLeftWhiskerRightMidRightFrontReflPath3 α η δ)

/-- `whiskerLeftWhiskerRight` coherence is axiom-free in a strict Kan complex. -/
noncomputable def whiskerLeftWhiskerRightPath3 (K : StrictKanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    K.Path3
      (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ)
      (K.transPath2
        (K.associatorPath2 α β δ)
        (K.transPath2
          (K.whiskerLeftPath2 α (K.whiskerRightPath2 η δ))
          (K.symmPath2 (K.associatorPath2 α γ δ)))) :=
  K.whiskerLeftWhiskerRightPath3FromTriangleComparison α η δ <|
    K.whiskerLeftWhiskerRightTriangleComparisonFromMidpointRightComparison α η δ <|
      K.whiskerLeftWhiskerRightMidRightPath3 α η δ

/-- In a strict Kan complex, the two pentagon back triangles coincide because
their shared boundary determines a unique Horn[1,0]-filler. -/
private theorem pentagonInnerBackTriangle_simplex_eq_right (K : StrictKanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    (K.pentagonInnerBackTriangle p q r s).simplex =
      (K.pentagonRightBackTriangle p q r s).simplex := by
  apply K.simplex2_eq_of_face1_face2 (K.pentagonRightBackTriangle p q r s)
  · simpa using (K.pentagonInnerBackTriangle p q r s).face1
  · simpa using (K.pentagonInnerBackTriangle p q r s).face2

/-- The reduced pentagon front-face obstruction contracts in a strict Kan
complex because the canonical Horn[2,0]-filler is uniquely determined by its
other three faces. -/
noncomputable def pentagonInnerRightFrontReflPath3 (K : StrictKanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.pentagonInnerRightFrontPath2 p q r s)
      (K.reflPath2 (K.compPath q (K.compPath r s))) := by
  let τ := K.pentagonRightBackTriangle p q r s
  let ω := K.reflTriangleTetrahedron τ
  let κ := K.pentagonInnerRightReflCandidateTetrahedron p q r s
  have hτ :
      (K.pentagonInnerBackTriangle p q r s).simplex = τ.simplex :=
    K.pentagonInnerBackTriangle_simplex_eq_right p q r s
  have hκ : κ.simplex = ω.simplex := by
    apply K.simplex3_eq_of_face1_face2_face3 ω
    · simpa [κ] using κ.face1
    · simpa [κ] using κ.face2
    · calc
        K.face 2 3 κ.simplex = (K.pentagonInnerBackTriangle p q r s).simplex := by
          simpa [κ] using κ.face3
        _ = τ.simplex := hτ
  have hFrontSimplex :
      (K.pentagonInnerRightFrontPath2 p q r s).simplex =
        (K.reflPath2 (K.compPath q (K.compPath r s))).simplex := by
    have hFace0 := congrArg (K.face 2 0) hκ
    calc
      (K.pentagonInnerRightFrontPath2 p q r s).simplex
          = K.face 2 0 κ.simplex := by
              symm
              simpa [κ] using κ.face0
      _ = K.face 2 0 ω.simplex := hFace0
      _ = (K.reflPath2 (K.compPath q (K.compPath r s))).simplex := by
            simpa [ω] using ω.face0
  have hFront :
      K.pentagonInnerRightFrontPath2 p q r s =
        K.reflPath2 (K.compPath q (K.compPath r s)) :=
    K.path2_eq_of_simplex_eq
      (K.pentagonInnerRightFrontPath2 p q r s)
      (K.reflPath2 (K.compPath q (K.compPath r s)))
      hFrontSimplex
  simpa [hFront] using
    (K.reflPath3 (K.pentagonInnerRightFrontPath2 p q r s))

/-- The old back-comparison loop contracts axiom-free in a strict Kan complex. -/
noncomputable def pentagonBackComparisonReflPath3 (K : StrictKanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s))
      (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)) :=
  K.pentagonBackComparisonReflPath3OfFrontPath3 p q r s
    (K.pentagonInnerRightFrontReflPath3 p q r s)

/-- Pentagon coherence is axiom-free in a strict Kan complex. -/
noncomputable def pentagonPath3 (K : StrictKanComplex)
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
  K.symmPath3 <|
    K.tetrahedronFace2Path3
      (K.pentagonBackComparisonReflPath3 p q r s)
      (K.pentagonLeftBigComparisonTetrahedron p q r s)
      ((K.reflPath3
        (K.transPath2
          (K.associatorPath2 (K.compPath p q) r s)
          (K.associatorPath2 p q (K.compPath r s)))).toTetrahedron)

end StrictKanComplex

/-- The reduced pentagon front-face contraction is axiom-free in a strict
extensional Kan model. -/
noncomputable def StrictExtensionalKanComplex.pentagonInnerRightFrontReflPath3
    (K : StrictExtensionalKanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.pentagonInnerRightFrontPath2 p q r s)
      (K.reflPath2 (K.compPath q (K.compPath r s))) :=
  StrictKanComplex.pentagonInnerRightFrontReflPath3 K.toStrictKanComplex p q r s

/-- The old back-comparison loop is also axiom-free in a strict extensional Kan
model. -/
noncomputable def StrictExtensionalKanComplex.pentagonBackComparisonReflPath3
    (K : StrictExtensionalKanComplex)
    {a b c d e : K.Obj} (p : K.PathSpace a b) (q : K.PathSpace b c)
    (r : K.PathSpace c d) (s : K.PathSpace d e) :
    K.Path3
      (K.trianglePath2
        (K.pentagonInnerBackTriangle p q r s)
        (K.pentagonRightBackTriangle p q r s))
      (K.reflPath2 (K.compPath (K.compPath (K.compPath p q) r) s)) :=
  StrictKanComplex.pentagonBackComparisonReflPath3 K.toStrictKanComplex p q r s

/-- Pentagon coherence is axiom-free in a strict extensional Kan model. -/
noncomputable def StrictExtensionalKanComplex.strictPentagonPath3
    (K : StrictExtensionalKanComplex)
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
  StrictKanComplex.pentagonPath3 K.toStrictKanComplex p q r s

/-- Forget the strict filler-uniqueness proof and retain the stronger coherent
pentagon structure derived from it. -/
noncomputable def StrictExtensionalKanComplex.toCoherentExtensionalKanComplex
    (K : StrictExtensionalKanComplex) :
    CoherentExtensionalKanComplex where
  toExtensionalKanComplex := K.toExtensionalKanComplex
  pentagonPath3 := StrictExtensionalKanComplex.strictPentagonPath3 K
  wlwrPath3 := StrictKanComplex.whiskerLeftWhiskerRightPath3 K.toStrictKanComplex

/-- `whiskerLeftWhiskerRight` specialized to strict extensional Kan models. This
uses the axiom-free strict front-loop contraction rather than the generic open
right-half frontier. -/
noncomputable def StrictExtensionalKanComplex.whiskerLeftWhiskerRightPath3
    (K : StrictExtensionalKanComplex)
    {a b c d : K.Obj} (α : K.PathSpace a b)
    {β γ : K.PathSpace b c} (η : K.Path2 β γ) (δ : K.PathSpace c d) :
    K.Path3
      (K.whiskerRightPath2 (K.whiskerLeftPath2 α η) δ)
      (K.transPath2
        (K.associatorPath2 α β δ)
        (K.transPath2
          (K.whiskerLeftPath2 α (K.whiskerRightPath2 η δ))
          (K.symmPath2 (K.associatorPath2 α γ δ)))) :=
  StrictKanComplex.whiskerLeftWhiskerRightPath3 K.toStrictKanComplex α η δ

/-- `whiskerLeftWhiskerRight` specialized to strict extensional Kan models. This
uses the axiom-free strict front-loop contraction rather than the generic open
right-half frontier. -/
noncomputable def Theory3.strictWhiskerLeftWhiskerRight
    (K : StrictExtensionalKanComplex)
    {L M N P : Term}
    (α : Theory1 K.toExtensionalKanComplex L M)
    {β γ : Theory1 K.toExtensionalKanComplex M N}
    (η : Theory2 K.toExtensionalKanComplex β γ)
    (δ : Theory1 K.toExtensionalKanComplex N P) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.whiskerRight K.toExtensionalKanComplex
        (Theory2.whiskerLeft K.toExtensionalKanComplex α η) δ)
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.associator K.toExtensionalKanComplex α β δ)
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.whiskerLeft K.toExtensionalKanComplex α
            (Theory2.whiskerRight K.toExtensionalKanComplex η δ))
          (Theory2.symm K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex α γ δ)))) :=
  fun ρ =>
    StrictExtensionalKanComplex.whiskerLeftWhiskerRightPath3 K
      (α ρ) (η ρ) (δ ρ)

/-- Pentagon coherence specialized to strict extensional Kan models. This uses
the axiom-free strict filler-uniqueness proof to realize the packaged semantic
pentagon coherence. -/
noncomputable def Theory3.strictPentagon
    (K : StrictExtensionalKanComplex)
    {L M N P Q : Term}
    (α : Theory1 K.toExtensionalKanComplex L M)
    (β : Theory1 K.toExtensionalKanComplex M N)
    (γ : Theory1 K.toExtensionalKanComplex N P)
    (δ : Theory1 K.toExtensionalKanComplex P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.associator K.toExtensionalKanComplex
          (Theory1.comp K.toExtensionalKanComplex α β) γ δ)
        (Theory2.associator K.toExtensionalKanComplex α β
          (Theory1.comp K.toExtensionalKanComplex γ δ)))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.whiskerRight K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex α β γ) δ)
          (Theory2.associator K.toExtensionalKanComplex α
             (Theory1.comp K.toExtensionalKanComplex β γ) δ))
         (Theory2.whiskerLeft K.toExtensionalKanComplex α
           (Theory2.associator K.toExtensionalKanComplex β γ δ))) :=
  fun ρ => StrictExtensionalKanComplex.strictPentagonPath3 K (α ρ) (β ρ) (γ ρ) (δ ρ)

/-- Strict-model wrapper exposing `whiskerLeftWhiskerRight` directly on
interpreted explicit paths and 2-cells. -/
noncomputable def homotopy2_strictWhiskerLeftWhiskerRight_in_Theory3
    (K : StrictExtensionalKanComplex)
    {L M N P : Term}
    (r : ReductionSeq L M) {p q : ReductionSeq M N}
    (α : Homotopy2 p q) (s : ReductionSeq N P) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.whiskerRight K.toExtensionalKanComplex
        (Theory2.whiskerLeft K.toExtensionalKanComplex
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
          (homotopy2_in_Theory2 K.toExtensionalKanComplex α))
        (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.associator K.toExtensionalKanComplex
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.whiskerLeft K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
            (Theory2.whiskerRight K.toExtensionalKanComplex
              (homotopy2_in_Theory2 K.toExtensionalKanComplex α)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)))
          (Theory2.symm K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))))) :=
  Theory3.strictWhiskerLeftWhiskerRight K
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
    (homotopy2_in_Theory2 K.toExtensionalKanComplex α)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)

/-- Strict-model pentagon coherence for interpreted explicit reduction
sequences. This uses the axiom-free strict proof of the packaged pentagon
coherence. -/
noncomputable def reductionSeq_strictPentagon_in_Theory3
    (K : StrictExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.associator K.toExtensionalKanComplex
          (Theory1.comp K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex q))
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))
        (Theory2.associator K.toExtensionalKanComplex
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
          (Theory1.comp K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.whiskerRight K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r))
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))
          (Theory2.associator K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
            (Theory1.comp K.toExtensionalKanComplex
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r))
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)))
        (Theory2.whiskerLeft K.toExtensionalKanComplex
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
          (Theory2.associator K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)))) :=
  Theory3.strictPentagon K
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex p)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
    (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)

/-- In a strict extensional Kan model, any two semantic 2-cells with the same
boundary coincide pointwise. -/
theorem StrictExtensionalKanComplex.theory2_eq
    (K : StrictExtensionalKanComplex) {M N : Term}
    {α β : Theory1 K.toExtensionalKanComplex M N}
    (η θ : Theory2 K.toExtensionalKanComplex α β) :
    η = θ := by
  funext ρ
  exact K.toStrictKanComplex.path2_eq (η ρ) (θ ρ)

/-- In a strict extensional Kan model, every primitive syntactic 3-cell already
has a direct semantic interpretation because its interpreted source and target
2-cells are equal. This gives a full `Homotopy3Deriv` interpretation on the
strict lane even though the generic recursive endpoint bridge is still open. -/
noncomputable def homotopy3Deriv_in_strict_Theory3
    (K : StrictExtensionalKanComplex)
    {M N : Term} {p q : ReductionSeq M N} {α β : Homotopy2 p q}
    (_η : HigherTerms.Homotopy3Deriv α β) :
    Theory3 K.toExtensionalKanComplex
      (homotopy2_in_Theory2 K.toExtensionalKanComplex α)
      (homotopy2_in_Theory2 K.toExtensionalKanComplex β) :=
  Theory3.ofEq K.toExtensionalKanComplex
    (K.theory2_eq
      (homotopy2_in_Theory2 K.toExtensionalKanComplex α)
      (homotopy2_in_Theory2 K.toExtensionalKanComplex β))

/-- Structure-level wrapper for `homotopy3Deriv_in_strict_Theory3`. -/
noncomputable def homotopy3_in_strict_Theory3
    (K : StrictExtensionalKanComplex)
    {M N : Term} {p q : ReductionSeq M N} {α β : Homotopy2 p q}
    (η : HigherTerms.Homotopy3 α β) :
    Theory3 K.toExtensionalKanComplex
      (homotopy2_in_Theory2 K.toExtensionalKanComplex α)
      (homotopy2_in_Theory2 K.toExtensionalKanComplex β) :=
  homotopy3Deriv_in_strict_Theory3 K η.deriv

set_option maxHeartbeats 1200000

/-- Strict-model source-side normalization for the structural associator shell
when the left explicit path begins with a forward βη step. -/
noncomputable def reductionSeq_associator_source_step_strict_in_Theory3
    (K : StrictExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_source_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.step s rest) q r)
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.whiskerLeft K.toExtensionalKanComplex
          (betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s)
          (reductionSeq_associator_source_in_Theory2 K.toExtensionalKanComplex
            rest q r))
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.symm K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex
              (betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s)
              (Theory1.comp K.toExtensionalKanComplex
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex q))
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))
          (Theory2.whiskerRight K.toExtensionalKanComplex
            (Theory2.symm K.toExtensionalKanComplex
              (Theory2.associator K.toExtensionalKanComplex
                (betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)))
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStep_in_Theory1 K0 L M s
  let β := reductionSeq_in_Theory1 K0 rest
  let γ := reductionSeq_in_Theory1 K0 q
  let δ := reductionSeq_in_Theory1 K0 r
  let βγs := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
  let c1 := reductionSeq_comp_in_Theory2 K0 rest q
  let c2 := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.concat rest q) r
  let c1s := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.step s rest) q
  let c2s := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.concat (ReductionSeq.step s rest) q) r
  let A1 := Theory2.associator K0 α β γ
  let A2 := Theory2.associator K0 α βγs δ
  let A2c := Theory2.associator K0 α (Theory1.comp K0 β γ) δ
  let sourceRest := reductionSeq_associator_source_in_Theory2 K0 rest q r
  let wrsc1 := Theory2.whiskerRight K0 (Theory2.symm K0 c1) δ
  let αwrsc1 := Theory2.whiskerLeft K0 α wrsc1
  let wrsA1 := Theory2.whiskerRight K0 (Theory2.symm K0 A1) δ
  have hSymmC2s :
      Theory3 K0
        (Theory2.symm K0 c2s)
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          (Theory2.symm K0 A2)) := by
    exact Theory3.trans K0
      (by
        simpa [c2s, A2, c2, α, βγs, δ, reductionSeq_comp_in_Theory2, ReductionSeq.concat,
          reductionSeq_in_Theory1] using
          (Theory3.symmTrans K0 A2 (Theory2.whiskerLeft K0 α c2)))
      (Theory3.transCongrLeft K0
        (Theory3.invWhiskerLeft K0 α c2)
        (Theory2.symm K0 A2))
  have hWrsC1_left :
      Theory3 K0
        (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
        (Theory2.trans K0 A2
          (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c))) := by
    have hWLWR :
        Theory3 K0
          (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)
          (Theory2.trans K0 A2c
            (Theory2.trans K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
              (Theory2.symm K0 A2))) := by
      simpa [A2c, A2, α, β, γ, δ, c1, reductionSeq_in_Theory1] using
        (Theory3.strictWhiskerLeftWhiskerRight K α c1 δ)
    have hSymm0 :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
          (Theory2.symm K0
            (Theory2.trans K0 A2c
              (Theory2.trans K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
                (Theory2.symm K0 A2)))) :=
      Theory3.symmCongr K0 hWLWR
    have hSymm1 :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.trans K0 A2c
              (Theory2.trans K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
                (Theory2.symm K0 A2))))
          (Theory2.trans K0
            (Theory2.symm K0
              (Theory2.trans K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
                (Theory2.symm K0 A2)))
            (Theory2.symm K0 A2c)) :=
      Theory3.symmTrans K0 A2c
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
          (Theory2.symm K0 A2))
    have hSymm2 :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.trans K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
              (Theory2.symm K0 A2)))
          (Theory2.trans K0
            (Theory2.symm K0 (Theory2.symm K0 A2))
            (Theory2.symm K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))) :=
      Theory3.symmTrans K0
        (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
        (Theory2.symm K0 A2)
    have hA2ss :
        Theory3 K0
          (Theory2.symm K0 (Theory2.symm K0 A2))
          A2 :=
      Theory3.symmSymm K0 A2
    have hLeftSymm :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
          (Theory2.whiskerLeft K0 α
            (Theory2.symm K0 (Theory2.whiskerRight K0 c1 δ))) :=
      Theory3.invWhiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)
    have hRightSymm :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 c1 δ))
          wrsc1 :=
      Theory3.invWhiskerRight K0 c1 δ
    have hInner :
        Theory3 K0
          (Theory2.trans K0
            (Theory2.symm K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
            (Theory2.symm K0 A2c))
          (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c)) := by
      exact Theory3.trans K0
        (Theory3.transCongrLeft K0 hLeftSymm (Theory2.symm K0 A2c))
        (Theory3.transCongrLeft K0
          (Theory3.whiskerLeftCongr K0 α hRightSymm)
          (Theory2.symm K0 A2c))
    exact Theory3.trans K0 hSymm0
      (Theory3.trans K0 hSymm1
        (Theory3.trans K0
          (Theory3.transCongrLeft K0 hSymm2 (Theory2.symm K0 A2c))
          (Theory3.trans K0
            (Theory3.transAssoc K0
              (Theory2.symm K0 (Theory2.symm K0 A2))
              (Theory2.symm K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
              (Theory2.symm K0 A2c))
            (Theory3.trans K0
              (Theory3.transCongrLeft K0 hA2ss
                (Theory2.trans K0
                  (Theory2.symm K0
                    (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
                  (Theory2.symm K0 A2c)))
              (Theory3.transCongrRight K0 A2 hInner)))))
  have hWrsC1 :
      Theory3 K0
        (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)
        (Theory2.trans K0 A2
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))) := by
    have h0 :
        Theory3 K0
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)
          (Theory2.symm K0 (Theory2.whiskerRight K0 c1s δ)) :=
      Theory3.whiskerRightSymm K0 c1s δ
    have h1 :
        Theory3 K0
          (Theory2.whiskerRight K0 c1s δ)
          (Theory2.trans K0
            (Theory2.whiskerRight K0 A1 δ)
            (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)) := by
      simpa [c1s, A1, c1, α, β, γ, reductionSeq_comp_in_Theory2, reductionSeq_in_Theory1] using
        (Theory3.whiskerRightTrans K0 A1 (Theory2.whiskerLeft K0 α c1) δ)
    have h2 :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 c1s δ))
          (Theory2.symm K0
            (Theory2.trans K0
              (Theory2.whiskerRight K0 A1 δ)
              (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))) :=
      Theory3.symmCongr K0 h1
    have h3 :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.trans K0
              (Theory2.whiskerRight K0 A1 δ)
              (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)))
          (Theory2.trans K0
            (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))) :=
      Theory3.symmTrans K0
        (Theory2.whiskerRight K0 A1 δ)
        (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)
    have h4 :
        Theory3 K0
          (Theory2.trans K0
            (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ)))
          (Theory2.trans K0
            (Theory2.trans K0 A2
              (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c)))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))) :=
      Theory3.transCongrLeft K0 hWrsC1_left (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))
    have h5 :
        Theory3 K0
          (Theory2.trans K0
            (Theory2.trans K0 A2
              (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c)))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ)))
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c)
                (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))))) := by
      exact Theory3.trans K0
        (Theory3.transAssoc K0 A2
          (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c))
          (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ)))
        (Theory3.transCongrRight K0 A2
          (Theory3.transAssoc K0 αwrsc1 (Theory2.symm K0 A2c)
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))))
    have h6 :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))
          wrsA1 :=
      Theory3.invWhiskerRight K0 A1 δ
    exact Theory3.trans K0 h0
      (Theory3.trans K0 h2
        (Theory3.trans K0 h3
          (Theory3.trans K0 h4
            (Theory3.trans K0 h5
              (Theory3.transCongrRight K0 A2
                (Theory3.transCongrRight K0 αwrsc1
                  (Theory3.transCongrRight K0 (Theory2.symm K0 A2c) h6)))))))
  have hS0 :
      Theory3 K0
        (Theory2.trans K0 (Theory2.symm K0 c2s)
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ))
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)) :=
    Theory3.transCongrLeft K0 hSymmC2s (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)
  have hS1 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ))
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))) :=
    Theory3.transCongrRight K0
      (Theory2.trans K0
        (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
        (Theory2.symm K0 A2))
      hWrsC1
  have hCancelA2 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.symm K0 A2)
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
        (Theory2.trans K0 αwrsc1
          (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)) := by
    exact Theory3.trans K0
      (Theory3.symm K0
        (Theory3.transAssoc K0 (Theory2.symm K0 A2) A2
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
      (Theory3.trans K0
        (Theory3.transCongrLeft K0 (Theory3.transLeftCancel K0 A2)
          (Theory2.trans K0 αwrsc1 (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))
        (Theory3.transReflLeft K0
          (Theory2.trans K0 αwrsc1 (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
  have hS2 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))) := by
    exact Theory3.trans K0
      (Theory3.transAssoc K0 (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
        (Theory2.symm K0 A2)
        (Theory2.trans K0 A2
          (Theory2.trans K0 αwrsc1 (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
      (Theory3.transCongrRight K0 (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2)) hCancelA2)
  have hCombineSrc :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          αwrsc1)
        (Theory2.whiskerLeft K0 α sourceRest) := by
    simpa [sourceRest, reductionSeq_associator_source_in_Theory2, wrsc1, c2, c1] using
      (Theory3.symm K0 (Theory3.whiskerLeftTrans K0 α (Theory2.symm K0 c2) wrsc1))
  have hS3 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α sourceRest)
          (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)) := by
    exact Theory3.trans K0
      (Theory3.symm K0
        (Theory3.transAssoc K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2)) αwrsc1
          (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))
      (Theory3.transCongrLeft K0 hCombineSrc
        (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))
  simpa [reductionSeq_associator_source_in_Theory2, c1s, c2s, sourceRest, wrsc1, αwrsc1, wrsA1,
    A1, A2, A2c, α, β, γ, δ, βγs, c1, c2, reductionSeq_comp_in_Theory2,
    reductionSeq_in_Theory1, ReductionSeq.concat] using
    (Theory3.trans K0 hS0 (Theory3.trans K0 hS1 (Theory3.trans K0 hS2 hS3)))

/-- Strict-model middle contraction for the forward associator step-head
bridge. -/
noncomputable def reductionSeq_associator_middle_step_strict_in_Theory3
    (K : StrictExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.symm K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex
              (betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s)
              (Theory1.comp K.toExtensionalKanComplex
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex q))
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))
          (Theory2.whiskerRight K.toExtensionalKanComplex
            (Theory2.symm K.toExtensionalKanComplex
              (Theory2.associator K.toExtensionalKanComplex
                (betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)))
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))
        (Theory2.trans K.toExtensionalKanComplex
          (reductionSeq_associator_in_Theory2 K.toExtensionalKanComplex
            (ReductionSeq.step s rest) q r)
          (Theory2.associator K.toExtensionalKanComplex
            (betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
            (Theory1.comp K.toExtensionalKanComplex
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))))
      (Theory2.whiskerLeft K.toExtensionalKanComplex
        (betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s)
        (reductionSeq_associator_in_Theory2 K.toExtensionalKanComplex rest q r)) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStep_in_Theory1 K0 L M s
  let β := reductionSeq_in_Theory1 K0 rest
  let γ := reductionSeq_in_Theory1 K0 q
  let δ := reductionSeq_in_Theory1 K0 r
  let A1 := Theory2.associator K0 α β γ
  let A2c := Theory2.associator K0 α (Theory1.comp K0 β γ) δ
  let A3 := Theory2.associator K0 α β (Theory1.comp K0 γ δ)
  let assocStep := reductionSeq_associator_in_Theory2 K0 (ReductionSeq.step s rest) q r
  let assocRest := reductionSeq_associator_in_Theory2 K0 rest q r
  let wrA1 := Theory2.whiskerRight K0 A1 δ
  let αassocRest := Theory2.whiskerLeft K0 α assocRest
  have hPent :
      Theory3 K0
        (Theory2.trans K0 assocStep A3)
        (Theory2.trans K0
          (Theory2.trans K0 wrA1 A2c)
          αassocRest) := by
    simpa [assocStep, assocRest, A1, A2c, A3, wrA1, α, β, γ, δ, αassocRest,
      reductionSeq_associator_in_Theory2, reductionSeq_in_Theory1] using
      (Theory3.strictPentagon K α β γ δ)
  have hSymmWr :
      Theory3 K0
        (Theory2.whiskerRight K0 (Theory2.symm K0 A1) δ)
        (Theory2.symm K0 wrA1) :=
    Theory3.whiskerRightSymm K0 A1 δ
  have h0 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.whiskerRight K0 (Theory2.symm K0 A1) δ))
          (Theory2.trans K0 assocStep A3))
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.symm K0 wrA1))
          (Theory2.trans K0 assocStep A3)) :=
    Theory3.transCongrLeft K0
      (Theory3.transCongrRight K0 (Theory2.symm K0 A2c) hSymmWr)
      (Theory2.trans K0 assocStep A3)
  have h1 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.symm K0 wrA1))
          (Theory2.trans K0 assocStep A3))
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.symm K0 wrA1))
          (Theory2.trans K0
            (Theory2.trans K0 wrA1 A2c)
            αassocRest)) :=
    Theory3.transCongrRight K0
      (Theory2.trans K0 (Theory2.symm K0 A2c)
        (Theory2.symm K0 wrA1))
      hPent
  have h2a :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c) (Theory2.symm K0 wrA1))
          (Theory2.trans K0
            (Theory2.trans K0 wrA1 A2c)
            αassocRest))
        (Theory2.trans K0
          (Theory2.symm K0 A2c)
          (Theory2.trans K0
            (Theory2.symm K0 wrA1)
            (Theory2.trans K0
              (Theory2.trans K0 wrA1 A2c)
              αassocRest))) :=
    Theory3.transAssoc K0 (Theory2.symm K0 A2c) (Theory2.symm K0 wrA1)
      (Theory2.trans K0 (Theory2.trans K0 wrA1 A2c) αassocRest)
  have h2b_inner :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.symm K0 wrA1)
          (Theory2.trans K0
            (Theory2.trans K0 wrA1 A2c)
            αassocRest))
        (Theory2.trans K0 A2c αassocRest) := by
    exact Theory3.trans K0
      (Theory3.transCongrRight K0 (Theory2.symm K0 wrA1)
        (Theory3.transAssoc K0 wrA1 A2c αassocRest))
      (Theory3.trans K0
        (Theory3.symm K0
          (Theory3.transAssoc K0 (Theory2.symm K0 wrA1) wrA1
            (Theory2.trans K0 A2c αassocRest)))
        (Theory3.trans K0
          (Theory3.transCongrLeft K0 (Theory3.transLeftCancel K0 wrA1)
            (Theory2.trans K0 A2c αassocRest))
          (Theory3.transReflLeft K0 (Theory2.trans K0 A2c αassocRest))))
  have h2b :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.symm K0 A2c)
          (Theory2.trans K0
            (Theory2.symm K0 wrA1)
            (Theory2.trans K0
              (Theory2.trans K0 wrA1 A2c)
              αassocRest)))
        (Theory2.trans K0 (Theory2.symm K0 A2c)
          (Theory2.trans K0 A2c αassocRest)) :=
    Theory3.transCongrRight K0 (Theory2.symm K0 A2c) h2b_inner
  have h2c :
      Theory3 K0
        (Theory2.trans K0 (Theory2.symm K0 A2c)
          (Theory2.trans K0 A2c αassocRest))
        αassocRest := by
    exact Theory3.trans K0
      (Theory3.symm K0
        (Theory3.transAssoc K0 (Theory2.symm K0 A2c) A2c αassocRest))
      (Theory3.trans K0
        (Theory3.transCongrLeft K0 (Theory3.transLeftCancel K0 A2c)
          αassocRest)
        (Theory3.transReflLeft K0 αassocRest))
  exact Theory3.trans K0 h0
    (Theory3.trans K0 h1
      (Theory3.trans K0 h2a
        (Theory3.trans K0 h2b h2c)))

/-- Strict-model forward step-head bridge for the structural associator shell. -/
noncomputable def reductionSeq_comp_associator_stepHead_strict_in_Theory3
    (K : StrictExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep L M) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.step s rest) q r)
      (Theory2.whiskerLeft K.toExtensionalKanComplex
        (betaEtaStep_in_Theory1 K.toExtensionalKanComplex L M s)
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex rest q r)) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStep_in_Theory1 K0 L M s
  let sourceRest := reductionSeq_associator_source_in_Theory2 K0 rest q r
  let assocRest := reductionSeq_associator_in_Theory2 K0 rest q r
  let targetRest := reductionSeq_associator_target_in_Theory2 K0 rest q r
  let shellRest := reductionSeq_associator_shell_in_Theory2 K0 rest q r
  let αsource := Theory2.whiskerLeft K0 α sourceRest
  let αassoc := Theory2.whiskerLeft K0 α assocRest
  let αtarget := Theory2.whiskerLeft K0 α targetRest
  let assocStep := reductionSeq_associator_in_Theory2 K0 (ReductionSeq.step s rest) q r
  let targetStep := reductionSeq_associator_target_in_Theory2 K0 (ReductionSeq.step s rest) q r
  let A2c := Theory2.associator K0 α
    (Theory1.comp K0 (reductionSeq_in_Theory1 K0 rest) (reductionSeq_in_Theory1 K0 q))
    (reductionSeq_in_Theory1 K0 r)
  let wrsA1 := Theory2.whiskerRight K0
    (Theory2.symm K0
      (Theory2.associator K0 α
        (reductionSeq_in_Theory1 K0 rest)
        (reductionSeq_in_Theory1 K0 q)))
    (reductionSeq_in_Theory1 K0 r)
  let middlePrefix := Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1
  let A3 := Theory2.associator K0 α
    (reductionSeq_in_Theory1 K0 rest)
    (Theory1.comp K0 (reductionSeq_in_Theory1 K0 q) (reductionSeq_in_Theory1 K0 r))
  have hMid0 :
      Theory3 K0
        (Theory2.trans K0 assocStep targetStep)
        (Theory2.trans K0 assocStep (Theory2.trans K0 A3 αtarget)) :=
    Theory3.transCongrRight K0 assocStep (reductionSeq_associator_target_step_in_Theory3 K0 s rest q r)
  have hMid1 :
      Theory3 K0
        (Theory2.trans K0 assocStep (Theory2.trans K0 A3 αtarget))
        (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget) :=
    Theory3.symm K0 (Theory3.transAssoc K0 assocStep A3 αtarget)
  have hMid2 :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget)) :=
    Theory3.transCongrRight K0 middlePrefix (Theory3.trans K0 hMid0 hMid1)
  have hMid3 :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget))
        (Theory2.trans K0 (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep A3)) αtarget) :=
    Theory3.symm K0 (Theory3.transAssoc K0 middlePrefix (Theory2.trans K0 assocStep A3) αtarget)
  have hMid4 :
      Theory3 K0
        (Theory2.trans K0 (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep A3)) αtarget)
        (Theory2.trans K0 αassoc αtarget) :=
    Theory3.transCongrLeft K0 (reductionSeq_associator_middle_step_strict_in_Theory3 K s rest q r) αtarget
  have hMid :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 αassoc αtarget) :=
    Theory3.trans K0 hMid2 (Theory3.trans K0 hMid3 hMid4)
  have h0 :
      Theory3 K0
        (reductionSeq_associator_shell_in_Theory2 K0 (ReductionSeq.step s rest) q r)
        (Theory2.trans K0 (Theory2.trans K0 αsource middlePrefix) (Theory2.trans K0 assocStep targetStep)) :=
    Theory3.transCongrLeft K0 (reductionSeq_associator_source_step_strict_in_Theory3 K s rest q r)
      (Theory2.trans K0 assocStep targetStep)
  have h1 :
      Theory3 K0
        (Theory2.trans K0 (Theory2.trans K0 αsource middlePrefix) (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 αsource (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))) :=
    Theory3.transAssoc K0 αsource middlePrefix (Theory2.trans K0 assocStep targetStep)
  have h2 :
      Theory3 K0
        (Theory2.trans K0 αsource (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep)))
        (Theory2.trans K0 αsource (Theory2.trans K0 αassoc αtarget)) :=
    Theory3.transCongrRight K0 αsource hMid
  have h3 :
      Theory3 K0
        (Theory2.trans K0 αsource (Theory2.trans K0 αassoc αtarget))
        (Theory2.trans K0 αsource
          (Theory2.whiskerLeft K0 α (Theory2.trans K0 assocRest targetRest))) :=
    Theory3.transCongrRight K0 αsource
      (Theory3.symm K0 (Theory3.whiskerLeftTrans K0 α assocRest targetRest))
  have h4 :
      Theory3 K0
        (Theory2.trans K0 αsource
          (Theory2.whiskerLeft K0 α (Theory2.trans K0 assocRest targetRest)))
        (Theory2.whiskerLeft K0 α shellRest) :=
    Theory3.symm K0
      (Theory3.whiskerLeftTrans K0 α sourceRest (Theory2.trans K0 assocRest targetRest))
  exact Theory3.trans K0 h0
    (Theory3.trans K0 h1
      (Theory3.trans K0 h2
        (Theory3.trans K0 h3 h4)))

/-- Strict-model source-side normalization for the structural associator shell
when the left explicit path begins with an inverse βη step. -/
noncomputable def reductionSeq_associator_source_stepInv_strict_in_Theory3
    (K : StrictExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_source_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.stepInv s rest) q r)
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.whiskerLeft K.toExtensionalKanComplex
          (betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s)
          (reductionSeq_associator_source_in_Theory2 K.toExtensionalKanComplex
            rest q r))
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.symm K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex
              (betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s)
              (Theory1.comp K.toExtensionalKanComplex
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex q))
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))
          (Theory2.whiskerRight K.toExtensionalKanComplex
            (Theory2.symm K.toExtensionalKanComplex
              (Theory2.associator K.toExtensionalKanComplex
                (betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)))
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStepInv_in_Theory1 K0 L M s
  let β := reductionSeq_in_Theory1 K0 rest
  let γ := reductionSeq_in_Theory1 K0 q
  let δ := reductionSeq_in_Theory1 K0 r
  let βγs := reductionSeq_in_Theory1 K0 (ReductionSeq.concat rest q)
  let c1 := reductionSeq_comp_in_Theory2 K0 rest q
  let c2 := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.concat rest q) r
  let c1s := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.stepInv s rest) q
  let c2s := reductionSeq_comp_in_Theory2 K0 (ReductionSeq.concat (ReductionSeq.stepInv s rest) q) r
  let A1 := Theory2.associator K0 α β γ
  let A2 := Theory2.associator K0 α βγs δ
  let A2c := Theory2.associator K0 α (Theory1.comp K0 β γ) δ
  let sourceRest := reductionSeq_associator_source_in_Theory2 K0 rest q r
  let wrsc1 := Theory2.whiskerRight K0 (Theory2.symm K0 c1) δ
  let αwrsc1 := Theory2.whiskerLeft K0 α wrsc1
  let wrsA1 := Theory2.whiskerRight K0 (Theory2.symm K0 A1) δ
  have hSymmC2s :
      Theory3 K0
        (Theory2.symm K0 c2s)
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          (Theory2.symm K0 A2)) := by
    exact Theory3.trans K0
      (by
        simpa [c2s, A2, c2, α, βγs, δ, reductionSeq_comp_in_Theory2, ReductionSeq.concat,
          reductionSeq_in_Theory1] using
          (Theory3.symmTrans K0 A2 (Theory2.whiskerLeft K0 α c2)))
      (Theory3.transCongrLeft K0
        (Theory3.invWhiskerLeft K0 α c2)
        (Theory2.symm K0 A2))
  have hWrsC1_left :
      Theory3 K0
        (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
        (Theory2.trans K0 A2
          (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c))) := by
    have hWLWR :
        Theory3 K0
          (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)
          (Theory2.trans K0 A2c
            (Theory2.trans K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
              (Theory2.symm K0 A2))) := by
      simpa [A2c, A2, α, β, γ, δ, c1, reductionSeq_in_Theory1] using
        (Theory3.strictWhiskerLeftWhiskerRight K α c1 δ)
    have hSymm0 :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
          (Theory2.symm K0
            (Theory2.trans K0 A2c
              (Theory2.trans K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
                (Theory2.symm K0 A2)))) :=
      Theory3.symmCongr K0 hWLWR
    have hSymm1 :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.trans K0 A2c
              (Theory2.trans K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
                (Theory2.symm K0 A2))))
          (Theory2.trans K0
            (Theory2.symm K0
              (Theory2.trans K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
                (Theory2.symm K0 A2)))
            (Theory2.symm K0 A2c)) :=
      Theory3.symmTrans K0 A2c
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
          (Theory2.symm K0 A2))
    have hSymm2 :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.trans K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
              (Theory2.symm K0 A2)))
          (Theory2.trans K0
            (Theory2.symm K0 (Theory2.symm K0 A2))
            (Theory2.symm K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))) :=
      Theory3.symmTrans K0
        (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ))
        (Theory2.symm K0 A2)
    have hA2ss :
        Theory3 K0
          (Theory2.symm K0 (Theory2.symm K0 A2))
          A2 :=
      Theory3.symmSymm K0 A2
    have hLeftSymm :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
          (Theory2.whiskerLeft K0 α
            (Theory2.symm K0 (Theory2.whiskerRight K0 c1 δ))) :=
      Theory3.invWhiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)
    have hRightSymm :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 c1 δ))
          wrsc1 :=
      Theory3.invWhiskerRight K0 c1 δ
    have hInner :
        Theory3 K0
          (Theory2.trans K0
            (Theory2.symm K0
              (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
            (Theory2.symm K0 A2c))
          (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c)) := by
      exact Theory3.trans K0
        (Theory3.transCongrLeft K0 hLeftSymm (Theory2.symm K0 A2c))
        (Theory3.transCongrLeft K0
          (Theory3.whiskerLeftCongr K0 α hRightSymm)
          (Theory2.symm K0 A2c))
    exact Theory3.trans K0 hSymm0
      (Theory3.trans K0 hSymm1
        (Theory3.trans K0
          (Theory3.transCongrLeft K0 hSymm2 (Theory2.symm K0 A2c))
          (Theory3.trans K0
            (Theory3.transAssoc K0
              (Theory2.symm K0 (Theory2.symm K0 A2))
              (Theory2.symm K0
                (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
              (Theory2.symm K0 A2c))
            (Theory3.trans K0
              (Theory3.transCongrLeft K0 hA2ss
                (Theory2.trans K0
                  (Theory2.symm K0
                    (Theory2.whiskerLeft K0 α (Theory2.whiskerRight K0 c1 δ)))
                  (Theory2.symm K0 A2c)))
              (Theory3.transCongrRight K0 A2 hInner)))))
  have hWrsC1 :
      Theory3 K0
        (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)
        (Theory2.trans K0 A2
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))) := by
    have h0 :
        Theory3 K0
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)
          (Theory2.symm K0 (Theory2.whiskerRight K0 c1s δ)) :=
      Theory3.whiskerRightSymm K0 c1s δ
    have h1 :
        Theory3 K0
          (Theory2.whiskerRight K0 c1s δ)
          (Theory2.trans K0
            (Theory2.whiskerRight K0 A1 δ)
            (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)) := by
      simpa [c1s, A1, c1, α, β, γ, reductionSeq_comp_in_Theory2, reductionSeq_in_Theory1] using
        (Theory3.whiskerRightTrans K0 A1 (Theory2.whiskerLeft K0 α c1) δ)
    have h2 :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 c1s δ))
          (Theory2.symm K0
            (Theory2.trans K0
              (Theory2.whiskerRight K0 A1 δ)
              (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))) :=
      Theory3.symmCongr K0 h1
    have h3 :
        Theory3 K0
          (Theory2.symm K0
            (Theory2.trans K0
              (Theory2.whiskerRight K0 A1 δ)
              (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)))
          (Theory2.trans K0
            (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))) :=
      Theory3.symmTrans K0
        (Theory2.whiskerRight K0 A1 δ)
        (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ)
    have h4 :
        Theory3 K0
          (Theory2.trans K0
            (Theory2.symm K0 (Theory2.whiskerRight K0 (Theory2.whiskerLeft K0 α c1) δ))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ)))
          (Theory2.trans K0
            (Theory2.trans K0 A2
              (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c)))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))) :=
      Theory3.transCongrLeft K0 hWrsC1_left (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))
    have h5 :
        Theory3 K0
          (Theory2.trans K0
            (Theory2.trans K0 A2
              (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c)))
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ)))
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c)
                (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))))) := by
      exact Theory3.trans K0
        (Theory3.transAssoc K0 A2
          (Theory2.trans K0 αwrsc1 (Theory2.symm K0 A2c))
          (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ)))
        (Theory3.transCongrRight K0 A2
          (Theory3.transAssoc K0 αwrsc1 (Theory2.symm K0 A2c)
            (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))))
    have h6 :
        Theory3 K0
          (Theory2.symm K0 (Theory2.whiskerRight K0 A1 δ))
          wrsA1 :=
      Theory3.invWhiskerRight K0 A1 δ
    exact Theory3.trans K0 h0
      (Theory3.trans K0 h2
        (Theory3.trans K0 h3
          (Theory3.trans K0 h4
            (Theory3.trans K0 h5
              (Theory3.transCongrRight K0 A2
                (Theory3.transCongrRight K0 αwrsc1
                  (Theory3.transCongrRight K0 (Theory2.symm K0 A2c) h6)))))))
  have hS0 :
      Theory3 K0
        (Theory2.trans K0 (Theory2.symm K0 c2s)
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ))
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)) :=
    Theory3.transCongrLeft K0 hSymmC2s (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ)
  have hS1 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.whiskerRight K0 (Theory2.symm K0 c1s) δ))
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))) :=
    Theory3.transCongrRight K0
      (Theory2.trans K0
        (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
        (Theory2.symm K0 A2))
      hWrsC1
  have hCancelA2 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.symm K0 A2)
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
        (Theory2.trans K0 αwrsc1
          (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)) := by
    exact Theory3.trans K0
      (Theory3.symm K0
        (Theory3.transAssoc K0 (Theory2.symm K0 A2) A2
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
      (Theory3.trans K0
        (Theory3.transCongrLeft K0 (Theory3.transLeftCancel K0 A2)
          (Theory2.trans K0 αwrsc1 (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))
        (Theory3.transReflLeft K0
          (Theory2.trans K0 αwrsc1 (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
  have hS2 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0
            (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
            (Theory2.symm K0 A2))
          (Theory2.trans K0 A2
            (Theory2.trans K0 αwrsc1
              (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))) := by
    exact Theory3.trans K0
      (Theory3.transAssoc K0 (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
        (Theory2.symm K0 A2)
        (Theory2.trans K0 A2
          (Theory2.trans K0 αwrsc1 (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))))
      (Theory3.transCongrRight K0 (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2)) hCancelA2)
  have hCombineSrc :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          αwrsc1)
        (Theory2.whiskerLeft K0 α sourceRest) := by
    simpa [sourceRest, reductionSeq_associator_source_in_Theory2, wrsc1, c2, c1] using
      (Theory3.symm K0 (Theory3.whiskerLeftTrans K0 α (Theory2.symm K0 c2) wrsc1))
  have hS3 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2))
          (Theory2.trans K0 αwrsc1
            (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))
        (Theory2.trans K0
          (Theory2.whiskerLeft K0 α sourceRest)
          (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)) := by
    exact Theory3.trans K0
      (Theory3.symm K0
        (Theory3.transAssoc K0
          (Theory2.whiskerLeft K0 α (Theory2.symm K0 c2)) αwrsc1
          (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1)))
      (Theory3.transCongrLeft K0 hCombineSrc
        (Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1))
  simpa [reductionSeq_associator_source_in_Theory2, c1s, c2s, sourceRest, wrsc1, αwrsc1, wrsA1,
    A1, A2, A2c, α, β, γ, δ, βγs, c1, c2, reductionSeq_comp_in_Theory2,
    reductionSeq_in_Theory1, ReductionSeq.concat] using
    (Theory3.trans K0 hS0 (Theory3.trans K0 hS1 (Theory3.trans K0 hS2 hS3)))

/-- Strict-model middle contraction for the inverse associator step-head
bridge. -/
noncomputable def reductionSeq_associator_middle_stepInv_strict_in_Theory3
    (K : StrictExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.symm K.toExtensionalKanComplex
            (Theory2.associator K.toExtensionalKanComplex
              (betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s)
              (Theory1.comp K.toExtensionalKanComplex
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex q))
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))
          (Theory2.whiskerRight K.toExtensionalKanComplex
            (Theory2.symm K.toExtensionalKanComplex
              (Theory2.associator K.toExtensionalKanComplex
                (betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
                (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)))
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))
        (Theory2.trans K.toExtensionalKanComplex
          (reductionSeq_associator_in_Theory2 K.toExtensionalKanComplex
            (ReductionSeq.stepInv s rest) q r)
          (Theory2.associator K.toExtensionalKanComplex
            (betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s)
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex rest)
            (Theory1.comp K.toExtensionalKanComplex
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex q)
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex r)))))
      (Theory2.whiskerLeft K.toExtensionalKanComplex
        (betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s)
        (reductionSeq_associator_in_Theory2 K.toExtensionalKanComplex rest q r)) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStepInv_in_Theory1 K0 L M s
  let β := reductionSeq_in_Theory1 K0 rest
  let γ := reductionSeq_in_Theory1 K0 q
  let δ := reductionSeq_in_Theory1 K0 r
  let A1 := Theory2.associator K0 α β γ
  let A2c := Theory2.associator K0 α (Theory1.comp K0 β γ) δ
  let A3 := Theory2.associator K0 α β (Theory1.comp K0 γ δ)
  let assocStep := reductionSeq_associator_in_Theory2 K0 (ReductionSeq.stepInv s rest) q r
  let assocRest := reductionSeq_associator_in_Theory2 K0 rest q r
  let wrA1 := Theory2.whiskerRight K0 A1 δ
  let αassocRest := Theory2.whiskerLeft K0 α assocRest
  have hPent :
      Theory3 K0
        (Theory2.trans K0 assocStep A3)
        (Theory2.trans K0
          (Theory2.trans K0 wrA1 A2c)
          αassocRest) := by
    simpa [assocStep, assocRest, A1, A2c, A3, wrA1, α, β, γ, δ, αassocRest,
      reductionSeq_associator_in_Theory2, reductionSeq_in_Theory1] using
      (Theory3.strictPentagon K α β γ δ)
  have hSymmWr :
      Theory3 K0
        (Theory2.whiskerRight K0 (Theory2.symm K0 A1) δ)
        (Theory2.symm K0 wrA1) :=
    Theory3.whiskerRightSymm K0 A1 δ
  have h0 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.whiskerRight K0 (Theory2.symm K0 A1) δ))
          (Theory2.trans K0 assocStep A3))
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.symm K0 wrA1))
          (Theory2.trans K0 assocStep A3)) :=
    Theory3.transCongrLeft K0
      (Theory3.transCongrRight K0 (Theory2.symm K0 A2c) hSymmWr)
      (Theory2.trans K0 assocStep A3)
  have h1 :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.symm K0 wrA1))
          (Theory2.trans K0 assocStep A3))
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c)
            (Theory2.symm K0 wrA1))
          (Theory2.trans K0
            (Theory2.trans K0 wrA1 A2c)
            αassocRest)) :=
    Theory3.transCongrRight K0
      (Theory2.trans K0 (Theory2.symm K0 A2c)
        (Theory2.symm K0 wrA1))
      hPent
  have h2a :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.trans K0 (Theory2.symm K0 A2c) (Theory2.symm K0 wrA1))
          (Theory2.trans K0
            (Theory2.trans K0 wrA1 A2c)
            αassocRest))
        (Theory2.trans K0
          (Theory2.symm K0 A2c)
          (Theory2.trans K0
            (Theory2.symm K0 wrA1)
            (Theory2.trans K0
              (Theory2.trans K0 wrA1 A2c)
              αassocRest))) :=
    Theory3.transAssoc K0 (Theory2.symm K0 A2c) (Theory2.symm K0 wrA1)
      (Theory2.trans K0 (Theory2.trans K0 wrA1 A2c) αassocRest)
  have h2b_inner :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.symm K0 wrA1)
          (Theory2.trans K0
            (Theory2.trans K0 wrA1 A2c)
            αassocRest))
        (Theory2.trans K0 A2c αassocRest) := by
    exact Theory3.trans K0
      (Theory3.transCongrRight K0 (Theory2.symm K0 wrA1)
        (Theory3.transAssoc K0 wrA1 A2c αassocRest))
      (Theory3.trans K0
        (Theory3.symm K0
          (Theory3.transAssoc K0 (Theory2.symm K0 wrA1) wrA1
            (Theory2.trans K0 A2c αassocRest)))
        (Theory3.trans K0
          (Theory3.transCongrLeft K0 (Theory3.transLeftCancel K0 wrA1)
            (Theory2.trans K0 A2c αassocRest))
          (Theory3.transReflLeft K0 (Theory2.trans K0 A2c αassocRest))))
  have h2b :
      Theory3 K0
        (Theory2.trans K0
          (Theory2.symm K0 A2c)
          (Theory2.trans K0
            (Theory2.symm K0 wrA1)
            (Theory2.trans K0
              (Theory2.trans K0 wrA1 A2c)
              αassocRest)))
        (Theory2.trans K0 (Theory2.symm K0 A2c)
          (Theory2.trans K0 A2c αassocRest)) :=
    Theory3.transCongrRight K0 (Theory2.symm K0 A2c) h2b_inner
  have h2c :
      Theory3 K0
        (Theory2.trans K0 (Theory2.symm K0 A2c)
          (Theory2.trans K0 A2c αassocRest))
        αassocRest := by
    exact Theory3.trans K0
      (Theory3.symm K0
        (Theory3.transAssoc K0 (Theory2.symm K0 A2c) A2c αassocRest))
      (Theory3.trans K0
        (Theory3.transCongrLeft K0 (Theory3.transLeftCancel K0 A2c)
          αassocRest)
        (Theory3.transReflLeft K0 αassocRest))
  exact Theory3.trans K0 h0
    (Theory3.trans K0 h1
      (Theory3.trans K0 h2a
        (Theory3.trans K0 h2b h2c)))

/-- Strict-model inverse step-head bridge for the structural associator shell. -/
noncomputable def reductionSeq_comp_associator_stepInvHead_strict_in_Theory3
    (K : StrictExtensionalKanComplex) {L M N P Q : Term}
    (s : BetaEtaStep M L) (rest : ReductionSeq M N)
    (q : ReductionSeq N P) (r : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
        (ReductionSeq.stepInv s rest) q r)
      (Theory2.whiskerLeft K.toExtensionalKanComplex
        (betaEtaStepInv_in_Theory1 K.toExtensionalKanComplex L M s)
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex rest q r)) := by
  let K0 := K.toExtensionalKanComplex
  let α := betaEtaStepInv_in_Theory1 K0 L M s
  let sourceRest := reductionSeq_associator_source_in_Theory2 K0 rest q r
  let assocRest := reductionSeq_associator_in_Theory2 K0 rest q r
  let targetRest := reductionSeq_associator_target_in_Theory2 K0 rest q r
  let shellRest := reductionSeq_associator_shell_in_Theory2 K0 rest q r
  let αsource := Theory2.whiskerLeft K0 α sourceRest
  let αassoc := Theory2.whiskerLeft K0 α assocRest
  let αtarget := Theory2.whiskerLeft K0 α targetRest
  let assocStep := reductionSeq_associator_in_Theory2 K0 (ReductionSeq.stepInv s rest) q r
  let targetStep := reductionSeq_associator_target_in_Theory2 K0 (ReductionSeq.stepInv s rest) q r
  let A2c := Theory2.associator K0 α
    (Theory1.comp K0 (reductionSeq_in_Theory1 K0 rest) (reductionSeq_in_Theory1 K0 q))
    (reductionSeq_in_Theory1 K0 r)
  let wrsA1 := Theory2.whiskerRight K0
    (Theory2.symm K0
      (Theory2.associator K0 α
        (reductionSeq_in_Theory1 K0 rest)
        (reductionSeq_in_Theory1 K0 q)))
    (reductionSeq_in_Theory1 K0 r)
  let middlePrefix := Theory2.trans K0 (Theory2.symm K0 A2c) wrsA1
  let A3 := Theory2.associator K0 α
    (reductionSeq_in_Theory1 K0 rest)
    (Theory1.comp K0 (reductionSeq_in_Theory1 K0 q) (reductionSeq_in_Theory1 K0 r))
  have hMid0 :
      Theory3 K0
        (Theory2.trans K0 assocStep targetStep)
        (Theory2.trans K0 assocStep (Theory2.trans K0 A3 αtarget)) :=
    Theory3.transCongrRight K0 assocStep (reductionSeq_associator_target_stepInv_in_Theory3 K0 s rest q r)
  have hMid1 :
      Theory3 K0
        (Theory2.trans K0 assocStep (Theory2.trans K0 A3 αtarget))
        (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget) :=
    Theory3.symm K0 (Theory3.transAssoc K0 assocStep A3 αtarget)
  have hMid2 :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget)) :=
    Theory3.transCongrRight K0 middlePrefix (Theory3.trans K0 hMid0 hMid1)
  have hMid3 :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 (Theory2.trans K0 assocStep A3) αtarget))
        (Theory2.trans K0 (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep A3)) αtarget) :=
    Theory3.symm K0 (Theory3.transAssoc K0 middlePrefix (Theory2.trans K0 assocStep A3) αtarget)
  have hMid4 :
      Theory3 K0
        (Theory2.trans K0 (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep A3)) αtarget)
        (Theory2.trans K0 αassoc αtarget) :=
    Theory3.transCongrLeft K0 (reductionSeq_associator_middle_stepInv_strict_in_Theory3 K s rest q r) αtarget
  have hMid :
      Theory3 K0
        (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 αassoc αtarget) :=
    Theory3.trans K0 hMid2 (Theory3.trans K0 hMid3 hMid4)
  have h0 :
      Theory3 K0
        (reductionSeq_associator_shell_in_Theory2 K0 (ReductionSeq.stepInv s rest) q r)
        (Theory2.trans K0 (Theory2.trans K0 αsource middlePrefix) (Theory2.trans K0 assocStep targetStep)) :=
    Theory3.transCongrLeft K0 (reductionSeq_associator_source_stepInv_strict_in_Theory3 K s rest q r)
      (Theory2.trans K0 assocStep targetStep)
  have h1 :
      Theory3 K0
        (Theory2.trans K0 (Theory2.trans K0 αsource middlePrefix) (Theory2.trans K0 assocStep targetStep))
        (Theory2.trans K0 αsource (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep))) :=
    Theory3.transAssoc K0 αsource middlePrefix (Theory2.trans K0 assocStep targetStep)
  have h2 :
      Theory3 K0
        (Theory2.trans K0 αsource (Theory2.trans K0 middlePrefix (Theory2.trans K0 assocStep targetStep)))
        (Theory2.trans K0 αsource (Theory2.trans K0 αassoc αtarget)) :=
    Theory3.transCongrRight K0 αsource hMid
  have h3 :
      Theory3 K0
        (Theory2.trans K0 αsource (Theory2.trans K0 αassoc αtarget))
        (Theory2.trans K0 αsource
          (Theory2.whiskerLeft K0 α (Theory2.trans K0 assocRest targetRest))) :=
    Theory3.transCongrRight K0 αsource
      (Theory3.symm K0 (Theory3.whiskerLeftTrans K0 α assocRest targetRest))
  have h4 :
      Theory3 K0
        (Theory2.trans K0 αsource
          (Theory2.whiskerLeft K0 α (Theory2.trans K0 assocRest targetRest)))
        (Theory2.whiskerLeft K0 α shellRest) :=
    Theory3.symm K0
      (Theory3.whiskerLeftTrans K0 α sourceRest (Theory2.trans K0 assocRest targetRest))
  exact Theory3.trans K0 h0
    (Theory3.trans K0 h1
      (Theory3.trans K0 h2
        (Theory3.trans K0 h3 h4)))

/-- In a strict extensional Kan complex, the recursive associator comparison
factors through the coherent extension derived axiom-free from strict filler
uniqueness. The direct strict step-head bridges remain available separately
below. -/
noncomputable def reductionSeq_comp_associator_strict_in_Theory3
    (K : StrictExtensionalKanComplex)
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K.toExtensionalKanComplex
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex p q r)
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (ReductionSeq.concat_assoc p q r))) :=
  reductionSeq_comp_associator_in_Theory3
    K.toCoherentExtensionalKanComplex p q r

/-- In a strict extensional Kan model, the interpreted equality-generated
associator 2-cell agrees with the structural associator shell. -/
noncomputable def homotopy2_associator_strict_bridge_in_Theory3
    (K : StrictExtensionalKanComplex)
    {L M N P : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) (r : ReductionSeq N P) :
    Theory3 K.toExtensionalKanComplex
      (homotopy2_in_Theory2 K.toExtensionalKanComplex
        (HigherTerms.associator p q r))
      (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex p q r) := by
  let K0 := K.toExtensionalKanComplex
  have hInterp :
      homotopy2_in_Theory2 K0 (HigherTerms.associator p q r) =
        Theory2.ofEq K0
          (congrArg (fun u => reductionSeq_in_Theory1 K0 u)
            (ReductionSeq.concat_assoc p q r)) :=
    homotopy2_in_Theory2_ofEq K0 (ReductionSeq.concat_assoc p q r)
  exact hInterp ▸
    Theory3.symm K0 (reductionSeq_comp_associator_strict_in_Theory3 K p q r)

/-- Left whiskering preserves the strict associator bridge. This packages the
strict shell comparison in the form needed by later pentagon-side endpoint
bridges. -/
noncomputable def homotopy2_whiskerLeft_associator_strict_bridge_in_Theory3
    (K : StrictExtensionalKanComplex)
    {A B C D E : Term}
    (p : ReductionSeq A B)
    (q : ReductionSeq B C) (r : ReductionSeq C D) (s : ReductionSeq D E) :
    Theory3 K.toExtensionalKanComplex
      (homotopy2_in_Theory2 K.toExtensionalKanComplex
        (HigherTerms.whiskerLeft p (HigherTerms.associator q r s)))
      (reductionSeq_whiskerLeft_in_Theory2 K.toExtensionalKanComplex p
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex q r s)) := by
  exact homotopy2_whiskerLeft_associator_bridge_in_Theory3_of_associatorBridge
    K.toExtensionalKanComplex
    (homotopy2_associator_strict_bridge_in_Theory3 K) p q r s

/-- In a strict extensional Kan model, the source 2-cell of the primitive
triangle 3-cell bridges to the corresponding structural shell. -/
noncomputable def homotopy2_triangle_source_strict_bridge_in_Theory3
    (K : StrictExtensionalKanComplex)
    {L M N : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) :
    Theory3 K.toExtensionalKanComplex
      (homotopy2_in_Theory2 K.toExtensionalKanComplex
        (Homotopy2.trans
          (HigherTerms.associator p (ReductionSeq.refl M) q)
          (HigherTerms.whiskerLeft p (HigherTerms.leftUnitor q))))
      (Theory2.trans K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          p (ReductionSeq.refl M) q)
        (reductionSeq_whiskerLeft_in_Theory2 K.toExtensionalKanComplex p
          (reductionSeq_leftUnitor_shell_in_Theory2 K.toExtensionalKanComplex q))) := by
  let K0 := K.toExtensionalKanComplex
  have hAssoc :
      Theory3 K0
        (homotopy2_in_Theory2 K0
          (HigherTerms.associator p (ReductionSeq.refl M) q))
        (reductionSeq_associator_shell_in_Theory2 K0 p (ReductionSeq.refl M) q) :=
    homotopy2_associator_strict_bridge_in_Theory3 K p (ReductionSeq.refl M) q
  have hLeft :
      Theory3 K0
        (homotopy2_in_Theory2 K0
          (HigherTerms.whiskerLeft p (HigherTerms.leftUnitor q)))
        (reductionSeq_whiskerLeft_in_Theory2 K0 p
          (reductionSeq_leftUnitor_shell_in_Theory2 K0 q)) := by
    change Theory3 K0
      (reductionSeq_whiskerLeft_in_Theory2 K0 p
        (homotopy2_in_Theory2 K0 (HigherTerms.leftUnitor q)))
      (reductionSeq_whiskerLeft_in_Theory2 K0 p
        (reductionSeq_leftUnitor_shell_in_Theory2 K0 q))
    exact reductionSeq_whiskerLeftCongr_in_Theory3 K0 p
      (homotopy2_leftUnitor_bridge_in_Theory3 K0 q)
  change Theory3 K0
    (Theory2.trans K0
      (homotopy2_in_Theory2 K0
        (HigherTerms.associator p (ReductionSeq.refl M) q))
      (homotopy2_in_Theory2 K0
        (HigherTerms.whiskerLeft p (HigherTerms.leftUnitor q))))
    (Theory2.trans K0
      (reductionSeq_associator_shell_in_Theory2 K0 p (ReductionSeq.refl M) q)
      (reductionSeq_whiskerLeft_in_Theory2 K0 p
        (reductionSeq_leftUnitor_shell_in_Theory2 K0 q)))
  exact Theory3.trans K0
    (Theory3.transCongrRight K0
      (homotopy2_in_Theory2 K0
        (HigherTerms.associator p (ReductionSeq.refl M) q))
      hLeft)
    (Theory3.transCongrLeft K0 hAssoc
      (reductionSeq_whiskerLeft_in_Theory2 K0 p
        (reductionSeq_leftUnitor_shell_in_Theory2 K0 q)))

/-- In a strict extensional Kan model, the target 2-cell of the primitive
triangle 3-cell already collapses to the equality-generated 2-cell on the
concatenated explicit paths. -/
noncomputable def homotopy2_triangle_target_strict_bridge_in_Theory3
    (K : StrictExtensionalKanComplex)
    {L M N : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N) :
    Theory3 K.toExtensionalKanComplex
      (homotopy2_in_Theory2 K.toExtensionalKanComplex
        (HigherTerms.whiskerRight (HigherTerms.rightUnitor p) q))
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun r => reductionSeq_in_Theory1 K.toExtensionalKanComplex r)
          (congrArg (fun r => ReductionSeq.concat r q)
            (ReductionSeq.concat_refl_right p)))) :=
  homotopy2_triangle_target_ofEq_toOfEq_in_Theory3 K.toExtensionalKanComplex p q

/-- In a strict extensional Kan model, the source 2-cell of the primitive
pentagon 3-cell bridges to the corresponding structural associator shells. -/
noncomputable def homotopy2_pentagon_source_strict_bridge_in_Theory3
    (K : StrictExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (homotopy2_in_Theory2 K.toExtensionalKanComplex
        (Homotopy2.trans
          (HigherTerms.associator (ReductionSeq.concat p q) r s)
          (HigherTerms.associator p q (ReductionSeq.concat r s))))
      (Theory2.trans K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          (ReductionSeq.concat p q) r s)
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          p q (ReductionSeq.concat r s))) := by
  exact homotopy2_pentagon_source_bridge_in_Theory3_of_associatorBridge
    K.toExtensionalKanComplex
    (homotopy2_associator_strict_bridge_in_Theory3 K) p q r s

/-- In a strict extensional Kan model, the target 2-cell of the primitive
pentagon 3-cell bridges to the mixed shell whose first factor is the
equality-generated normalization of the right-whiskered associator and whose
remaining factors are the structural associator shells. -/
noncomputable def homotopy2_pentagon_target_strict_bridge_in_Theory3
    (K : StrictExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (homotopy2_in_Theory2 K.toExtensionalKanComplex
        (Homotopy2.trans
          (Homotopy2.trans
            (HigherTerms.whiskerRight (HigherTerms.associator p q r) s)
            (HigherTerms.associator p (ReductionSeq.concat q r) s))
          (HigherTerms.whiskerLeft p (HigherTerms.associator q r s))))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.ofEq K.toExtensionalKanComplex
            (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
              (congrArg (fun u => ReductionSeq.concat u s)
                (ReductionSeq.concat_assoc p q r))))
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            p (ReductionSeq.concat q r) s))
        (reductionSeq_whiskerLeft_in_Theory2 K.toExtensionalKanComplex p
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            q r s))) := by
  exact homotopy2_pentagon_target_bridge_in_Theory3_of_associatorBridge
    K.toExtensionalKanComplex
    (homotopy2_associator_strict_bridge_in_Theory3 K) p q r s

/-- In a strict extensional Kan model, the full explicit pentagon shell bridges to
the mixed structural target shell determined by the strict associator bridge. -/
noncomputable def homotopy2_pentagon_shell_strict_bridge_in_Theory3
    (K : StrictExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          (ReductionSeq.concat p q) r s)
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          p q (ReductionSeq.concat r s)))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (Theory2.ofEq K.toExtensionalKanComplex
            (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
              (congrArg (fun u => ReductionSeq.concat u s)
                (ReductionSeq.concat_assoc p q r))))
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            p (ReductionSeq.concat q r) s))
        (reductionSeq_whiskerLeft_in_Theory2 K.toExtensionalKanComplex p
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            q r s))) := by
  exact homotopy2_pentagon_shell_bridge_in_Theory3_of_associatorBridge
    K.toExtensionalKanComplex
    (homotopy2_associator_strict_bridge_in_Theory3 K) p q r s

/-- In a strict extensional Kan model, any associator-specific right-whisker
triangle comparison upgrades the remaining equality-generated pentagon target
factor to the structural right-whisker shell. -/
noncomputable def
    homotopy2_pentagon_rightWhiskeredAssociator_shell_strict_bridge_in_Theory3_ofTriangleComparisonPath3
    (K : StrictExtensionalKanComplex) {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q)
    (triangleComparison :
      Theory3 K.toExtensionalKanComplex
        (fun ρ =>
          K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.trianglePath2
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightTriangle
              ((homotopy2_in_Theory2 K.toExtensionalKanComplex
                (HigherTerms.associator p q r)) ρ)
              ((reductionSeq_in_Theory1 K.toExtensionalKanComplex s) ρ))
            (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightTriangle
              ((reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
                p q r) ρ)
              ((reductionSeq_in_Theory1 K.toExtensionalKanComplex s) ρ)))
        (Theory2.refl K.toExtensionalKanComplex
          (Theory1.comp K.toExtensionalKanComplex
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex
              (ReductionSeq.concat (ReductionSeq.concat p q) r))
            (reductionSeq_in_Theory1 K.toExtensionalKanComplex s)))) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (congrArg (fun u => ReductionSeq.concat u s)
            (ReductionSeq.concat_assoc p q r))))
      (reductionSeq_whiskerRight_in_Theory2 K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          p q r) s) := by
  exact homotopy2_pentagon_rightWhiskeredAssociator_shell_bridge_in_Theory3_ofTriangleComparisonPath3
    K.toExtensionalKanComplex p q r s triangleComparison

/-- In a strict extensional Kan model, the associator-specific right-whisker
triangle comparison is automatic because the induced semantic 2-cell already has
fixed boundary and hence coincides with the corresponding reflexive 2-cell. -/
noncomputable def
    homotopy2_associator_rightWhisker_triangleComparison_strict_in_Theory3
    (K : StrictExtensionalKanComplex) {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (fun ρ =>
        K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.trianglePath2
          (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightTriangle
            ((homotopy2_in_Theory2 K.toExtensionalKanComplex
              (HigherTerms.associator p q r)) ρ)
            ((reductionSeq_in_Theory1 K.toExtensionalKanComplex s) ρ))
          (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightTriangle
            ((reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
              p q r) ρ)
            ((reductionSeq_in_Theory1 K.toExtensionalKanComplex s) ρ)))
      (Theory2.refl K.toExtensionalKanComplex
        (Theory1.comp K.toExtensionalKanComplex
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex
            (ReductionSeq.concat (ReductionSeq.concat p q) r))
          (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))) :=
  Theory3.ofEq K.toExtensionalKanComplex
    (K.theory2_eq _ _)

/-- In a strict extensional Kan model, the remaining equality-generated pentagon
target factor already upgrades to the structural right-whisker shell. -/
noncomputable def homotopy2_pentagon_rightWhiskeredAssociator_shell_strict_bridge_in_Theory3
    (K : StrictExtensionalKanComplex) {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.ofEq K.toExtensionalKanComplex
        (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
          (congrArg (fun u => ReductionSeq.concat u s)
            (ReductionSeq.concat_assoc p q r))))
      (reductionSeq_whiskerRight_in_Theory2 K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          p q r) s) := by
  exact
    homotopy2_pentagon_rightWhiskeredAssociator_shell_strict_bridge_in_Theory3_ofTriangleComparisonPath3
      K p q r s
      (homotopy2_associator_rightWhisker_triangleComparison_strict_in_Theory3
        K p q r s)

/-- Strict-model specialization of the abstract structural pentagon shell upgrade:
any strict right-whisker bridge for associator shells upgrades the mixed target
shell to the fully structural target shell. -/
noncomputable def
    homotopy2_pentagon_structural_shell_strict_bridge_in_Theory3_of_associatorRightWhiskerBridges
    (K : StrictExtensionalKanComplex)
    (hRightBridge :
      {L M N P Q : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
        (r : ReductionSeq N P) → (s : ReductionSeq P Q) →
        Theory3 K.toExtensionalKanComplex
          (Theory2.ofEq K.toExtensionalKanComplex
            (congrArg (fun u => reductionSeq_in_Theory1 K.toExtensionalKanComplex u)
              (congrArg (fun u => ReductionSeq.concat u s)
                (ReductionSeq.concat_assoc p q r))))
          (reductionSeq_whiskerRight_in_Theory2 K.toExtensionalKanComplex
            (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
              p q r) s))
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          (ReductionSeq.concat p q) r s)
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          p q (ReductionSeq.concat r s)))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (reductionSeq_whiskerRight_in_Theory2 K.toExtensionalKanComplex
            (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
              p q r) s)
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            p (ReductionSeq.concat q r) s))
        (reductionSeq_whiskerLeft_in_Theory2 K.toExtensionalKanComplex p
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            q r s))) := by
  exact homotopy2_pentagon_structural_shell_bridge_in_Theory3_of_associatorRightWhiskerBridges
    K.toExtensionalKanComplex
    (homotopy2_associator_strict_bridge_in_Theory3 K)
    hRightBridge p q r s

/-- Strict-model specialization of the sharpened pentagon frontier: an
associator-specific right-whisker triangle-comparison family is enough to
upgrade the explicit pentagon shell all the way to the fully structural target
shell. -/
noncomputable def
    homotopy2_pentagon_structural_shell_strict_bridge_in_Theory3_of_associatorBridgeOfTriangleComparisonPath3
    (K : StrictExtensionalKanComplex)
    (hAssocTriangle :
      {L M N P Q : Term} → (p : ReductionSeq L M) → (q : ReductionSeq M N) →
        (r : ReductionSeq N P) → (s : ReductionSeq P Q) →
        Theory3 K.toExtensionalKanComplex
          (fun ρ =>
            K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.trianglePath2
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightTriangle
                ((homotopy2_in_Theory2 K.toExtensionalKanComplex
                  (HigherTerms.associator p q r)) ρ)
                ((reductionSeq_in_Theory1 K.toExtensionalKanComplex s) ρ))
              (K.toExtensionalKanComplex.toReflexiveKanComplex.toKanComplex.whiskerRightTriangle
                ((reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
                  p q r) ρ)
                ((reductionSeq_in_Theory1 K.toExtensionalKanComplex s) ρ)))
          (Theory2.refl K.toExtensionalKanComplex
            (Theory1.comp K.toExtensionalKanComplex
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex
                (ReductionSeq.concat (ReductionSeq.concat p q) r))
              (reductionSeq_in_Theory1 K.toExtensionalKanComplex s))))
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          (ReductionSeq.concat p q) r s)
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          p q (ReductionSeq.concat r s)))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (reductionSeq_whiskerRight_in_Theory2 K.toExtensionalKanComplex
            (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
              p q r) s)
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            p (ReductionSeq.concat q r) s))
        (reductionSeq_whiskerLeft_in_Theory2 K.toExtensionalKanComplex p
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            q r s))) := by
  exact homotopy2_pentagon_structural_shell_strict_bridge_in_Theory3_of_associatorRightWhiskerBridges
    K
    (fun p q r s =>
      homotopy2_pentagon_rightWhiskeredAssociator_shell_strict_bridge_in_Theory3_ofTriangleComparisonPath3
        K p q r s (hAssocTriangle p q r s))
    p q r s

/-- In a strict extensional Kan model, the full explicit pentagon shell already
bridges to the fully structural target shell. -/
noncomputable def homotopy2_pentagon_structural_shell_strict_bridge_in_Theory3
    (K : StrictExtensionalKanComplex)
    {L M N P Q : Term}
    (p : ReductionSeq L M) (q : ReductionSeq M N)
    (r : ReductionSeq N P) (s : ReductionSeq P Q) :
    Theory3 K.toExtensionalKanComplex
      (Theory2.trans K.toExtensionalKanComplex
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          (ReductionSeq.concat p q) r s)
        (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
          p q (ReductionSeq.concat r s)))
      (Theory2.trans K.toExtensionalKanComplex
        (Theory2.trans K.toExtensionalKanComplex
          (reductionSeq_whiskerRight_in_Theory2 K.toExtensionalKanComplex
            (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
              p q r) s)
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            p (ReductionSeq.concat q r) s))
        (reductionSeq_whiskerLeft_in_Theory2 K.toExtensionalKanComplex p
          (reductionSeq_associator_shell_in_Theory2 K.toExtensionalKanComplex
            q r s))) := by
  exact
    homotopy2_pentagon_structural_shell_strict_bridge_in_Theory3_of_associatorBridgeOfTriangleComparisonPath3
      K
      (fun p q r s =>
        homotopy2_associator_rightWhisker_triangleComparison_strict_in_Theory3
          K p q r s)
      p q r s


end HigherLambdaModel.Lambda.ExtensionalKan
