/-!
# Omega-Groupoid Interfaces

This file collects generic low-dimensional interfaces for the higher groupoid
data used across the repository.

The current codebase only has a fully explicit syntactic realization through
3-cells, with the next two layers obtained reflexively from the recursive
higher-derivation tower. The structures below are therefore intentionally
phrased as a low-dimensional core: source and target are encoded by the
dependent typing of `Hom`, `Hom2`, `Hom3`, `Hom4`, and `Hom5`, while the
coherence fields package the operations and witnesses already used by the
lambda-calculus layer.
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

/-- A weak omega-groupoid core packaged through 5-cells.

The interface is intentionally generic: it does not prescribe how higher cells
are implemented, only which operations and coherence witnesses are available. -/
structure OmegaGroupoid extends OmegaGroupoidData where
  Hom3 : {M N : Obj} → {p q : Hom M N} → Hom2 p q → Hom2 p q → Type z
  Hom4 : {M N : Obj} → {p q : Hom M N} → {α β : Hom2 p q} →
    Hom3 α β → Hom3 α β → Type z
  Hom5 : {M N : Obj} → {p q : Hom M N} → {α β : Hom2 p q} → {η θ : Hom3 α β} →
    Hom4 η θ → Hom4 η θ → Type z
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
  hom4_refl : {M N : Obj} → {p q : Hom M N} → {α β : Hom2 p q} →
    (η : Hom3 α β) → Hom4 η η
  hom5_refl : {M N : Obj} → {p q : Hom M N} → {α β : Hom2 p q} → {η θ : Hom3 α β} →
    (ω : Hom4 η θ) → Hom5 ω ω
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
  Cell4 : {M N : Cell0} → {p q : Cell1 M N} → {α β : Cell2 p q} →
    Cell3 α β → Cell3 α β → Sort z
  Cell5 : {M N : Cell0} → {p q : Cell1 M N} → {α β : Cell2 p q} →
    {η θ : Cell3 α β} → Cell4 η θ → Cell4 η θ → Sort z
  cell2_refl : ∀ {M N : Cell0} (p : Cell1 M N), Cell2 p p
  cell3_refl : ∀ {M N : Cell0} {p q : Cell1 M N}
      (α : Cell2 p q), Cell3 α α
  cell4_refl : ∀ {M N : Cell0} {p q : Cell1 M N} {α β : Cell2 p q}
      (η : Cell3 α β), Cell4 η η
  cell5_refl : ∀ {M N : Cell0} {p q : Cell1 M N} {α β : Cell2 p q}
      {η θ : Cell3 α β} (ω : Cell4 η θ), Cell5 ω ω

namespace OmegaGroupoid

/-- Every omega-groupoid determines a reflexive globular tower through 5-cells. -/
def toReflexiveGlobularTower (G : OmegaGroupoid) : ReflexiveGlobularTower where
  Cell0 := G.Obj
  Cell1 := G.Hom
  Cell2 := G.Hom2
  Cell3 := G.Hom3
  Cell4 := G.Hom4
  Cell5 := G.Hom5
  cell2_refl := G.refl2
  cell3_refl := G.hom3_refl
  cell4_refl := G.hom4_refl
  cell5_refl := G.hom5_refl

/-- The pentagon coherence 3-cell carries a reflexive 4-cell. -/
def pentagon4 (G : OmegaGroupoid) {M N P Q R : G.Obj}
    (p : G.Hom M N) (q : G.Hom N P) (r : G.Hom P Q) (s : G.Hom Q R) :
    G.Hom4 (G.pentagon_coh p q r s) (G.pentagon_coh p q r s) :=
  G.hom4_refl (G.pentagon_coh p q r s)

/-- The reflexive pentagon 4-cell carries a reflexive 5-cell. -/
def pentagon5 (G : OmegaGroupoid) {M N P Q R : G.Obj}
    (p : G.Hom M N) (q : G.Hom N P) (r : G.Hom P Q) (s : G.Hom Q R) :
    G.Hom5 (G.pentagon4 p q r s) (G.pentagon4 p q r s) :=
  G.hom5_refl (G.pentagon4 p q r s)

/-- The interchange hexagon 3-cell carries a reflexive 4-cell. -/
def hexagon4 (G : OmegaGroupoid) {M N P : G.Obj}
    {p p' : G.Hom M N} {q q' : G.Hom N P}
    (α : G.Hom2 p p') (β : G.Hom2 q q') :
    G.Hom4 (G.interchange_coh α β) (G.interchange_coh α β) :=
  G.hom4_refl (G.interchange_coh α β)

/-- The reflexive interchange hexagon 4-cell carries a reflexive 5-cell. -/
def hexagon5 (G : OmegaGroupoid) {M N P : G.Obj}
    {p p' : G.Hom M N} {q q' : G.Hom N P}
    (α : G.Hom2 p p') (β : G.Hom2 q q') :
    G.Hom5 (G.hexagon4 α β) (G.hexagon4 α β) :=
  G.hom5_refl (G.hexagon4 α β)

end OmegaGroupoid

end HigherLambdaModel.Simplicial
