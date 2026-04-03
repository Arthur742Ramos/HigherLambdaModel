/-!
# Omega-Groupoid Interfaces

This file collects generic low-dimensional interfaces for the higher groupoid
data used across the repository.

The current codebase only has a fully explicit syntactic realization through
3-cells. The structures below are therefore intentionally phrased as a
low-dimensional core: source and target are encoded by the dependent typing of
`Hom`, `Hom2`, and `Hom3`, while the coherence fields package the operations
and witnesses already used by the lambda-calculus layer.
-/

namespace HigherLambdaModel.Simplicial

universe u v w z

/-- A globular tower of higher cells with explicit boundary maps. -/
structure GlobularTower where
  Cell : Nat → Sort u
  source : {n : Nat} → Cell (n + 1) → Cell n
  target : {n : Nat} → Cell (n + 1) → Cell n
  globular_src : {n : Nat} → (x : Cell (n + 2)) →
    source (source x) = source (target x)
  globular_tgt : {n : Nat} → (x : Cell (n + 2)) →
    target (source x) = target (target x)

/-- Low-dimensional groupoid data with dependent source and target. -/
structure OmegaGroupoidData where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (M : Obj) → Hom M M
  comp : {M N P : Obj} → Hom M N → Hom N P → Hom M P
  inv : {M N : Obj} → Hom M N → Hom N M
  Hom2 : {M N : Obj} → Hom M N → Hom M N → Type w
  refl2 : {M N : Obj} → (p : Hom M N) → Hom2 p p

/-- A weak omega-groupoid core packaged through 3-cells.

The interface is intentionally generic: it does not prescribe how higher cells
are implemented, only which operations and coherence witnesses are available. -/
structure OmegaGroupoid extends OmegaGroupoidData where
  Hom3 : {M N : Obj} → {p q : Hom M N} → Hom2 p q → Hom2 p q → Type z
  symm2 : {M N : Obj} → {p q : Hom M N} → Hom2 p q → Hom2 q p
  trans2 : {M N : Obj} → {p q r : Hom M N} → Hom2 p q → Hom2 q r → Hom2 p r
  whiskerLeft : {M N P : Obj} → (r : Hom M N) → {p q : Hom N P} →
    Hom2 p q → Hom2 (comp r p) (comp r q)
  whiskerRight : {M N P : Obj} → {p q : Hom M N} → Hom2 p q → (s : Hom N P) →
    Hom2 (comp p s) (comp q s)
  hcomp : {M N P : Obj} → {p p' : Hom M N} → {q q' : Hom N P} →
    Hom2 p p' → Hom2 q q' → Hom2 (comp p q) (comp p' q')
  associator : {M N P Q : Obj} → (p : Hom M N) → (q : Hom N P) → (r : Hom P Q) →
    Hom2 (comp (comp p q) r) (comp p (comp q r))
  leftUnitor : {M N : Obj} → (p : Hom M N) → Hom2 (comp (id M) p) p
  rightUnitor : {M N : Obj} → (p : Hom M N) → Hom2 (comp p (id N)) p
  inv_right : {M N : Obj} → (p : Hom M N) → Hom2 (comp p (inv p)) (id M)
  inv_left : {M N : Obj} → (p : Hom M N) → Hom2 (comp (inv p) p) (id N)
  hom3_refl : {M N : Obj} → {p q : Hom M N} → (α : Hom2 p q) → Hom3 α α
  pentagon_coh : {M N P Q R : Obj} → (p : Hom M N) → (q : Hom N P) →
    (r : Hom P Q) → (s : Hom Q R) →
    Hom3
      (trans2 (associator (comp p q) r s) (associator p q (comp r s)))
      (trans2
        (trans2 (whiskerRight (associator p q r) s)
          (associator p (comp q r) s))
        (whiskerLeft p (associator q r s)))
  triangle_coh : {M N P : Obj} → (p : Hom M N) → (q : Hom N P) →
    Hom3
      (trans2 (associator p (id N) q) (whiskerLeft p (leftUnitor q)))
      (whiskerRight (rightUnitor p) q)
  interchange_coh : {M N P : Obj} → {p p' : Hom M N} → {q q' : Hom N P} →
    (α : Hom2 p p') → (β : Hom2 q q') →
    Hom3 (hcomp α β)
      (trans2 (whiskerRight α q) (whiskerLeft p' β))

/-- A reflexive low-dimensional globular tower. -/
structure ReflexiveGlobularTower where
  Cell0 : Type u
  Cell1 : Cell0 → Cell0 → Type v
  Cell2 : {M N : Cell0} → Cell1 M N → Cell1 M N → Sort w
  Cell3 : {M N : Cell0} → {p q : Cell1 M N} → Cell2 p q → Cell2 p q → Sort z
  cell2_refl : ∀ {M N : Cell0} (p : Cell1 M N), Cell2 p p
  cell3_refl : ∀ {M N : Cell0} {p q : Cell1 M N}
      (α : Cell2 p q), Cell3 α α

namespace OmegaGroupoid

/-- Every omega-groupoid determines a reflexive low-dimensional globular tower. -/
def toReflexiveGlobularTower (G : OmegaGroupoid) : ReflexiveGlobularTower where
  Cell0 := G.Obj
  Cell1 := G.Hom
  Cell2 := G.Hom2
  Cell3 := G.Hom3
  cell2_refl := G.refl2
  cell3_refl := G.hom3_refl

end OmegaGroupoid

end HigherLambdaModel.Simplicial
