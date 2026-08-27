import Mathlib.Data.Nat.Basic

/-!
# Advertised proposition-level result

This is the deliberately small statement surface for the Palomar entry.  It
keeps the mathematical objects visible: de Bruijn lambda terms, beta/eta
conversion, and the reflexive/extensional Kan-complex interface used to
interpret them.  The full higher-cell and `K∞` development remains in the
repository's ordinary library modules.
-/

namespace HigherLambdaModel.Palomar

/-! ## Untyped lambda terms -/

/-- Untyped lambda terms, represented with de Bruijn variable indices. -/
inductive Term : Type where
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving Repr, DecidableEq, Inhabited

namespace Term

/-- Shift every free variable at or above cutoff `c` by the integer `d`. -/
def shift (d : Int) (c : Nat) : Term → Term
  | var n => if n < c then var n else var (Int.toNat (n + d))
  | app M N => app (shift d c M) (shift d c N)
  | lam M => lam (shift d (c + 1) M)

/-- Shift a term by one at the outermost binder depth. -/
abbrev shift1 : Term → Term := shift 1 0

/-- Capture-avoiding substitution of `N` for variable `j` in a term. -/
def subst (j : Nat) (N : Term) : Term → Term
  | var n =>
      if n = j then N
      else if n > j then var (n - 1)
      else var n
  | app M₁ M₂ => app (subst j N M₁) (subst j N M₂)
  | lam M => lam (subst (j + 1) (shift1 N) M)

/-- Capture-avoiding substitution for the outermost variable. -/
abbrev subst0 (N : Term) (M : Term) : Term := subst 0 N M

/-- Whether a de Bruijn variable occurs free at the requested outer index. -/
def hasFreeVar (n : Nat) : Term → Bool
  | var m => m = n
  | app M N => hasFreeVar n M || hasFreeVar n N
  | lam M => hasFreeVar (n + 1) M

end Term

/-! ## Beta/eta conversion -/

/-- One compatible beta-reduction step. -/
inductive BetaStep : Term → Term → Prop where
  | beta : ∀ M N, BetaStep (Term.app (Term.lam M) N) (Term.subst0 N M)
  | appL : ∀ {M M' N}, BetaStep M M' → BetaStep (Term.app M N) (Term.app M' N)
  | appR : ∀ {M N N'}, BetaStep N N' → BetaStep (Term.app M N) (Term.app M N')
  | lam : ∀ {M M'}, BetaStep M M' → BetaStep (Term.lam M) (Term.lam M')

/-- One compatible eta-reduction step, subject to the usual freshness condition. -/
inductive EtaStep : Term → Term → Prop where
  | eta : ∀ M, ¬Term.hasFreeVar 0 M = true →
      EtaStep (Term.lam (Term.app M (Term.var 0))) (Term.shift (-1) 0 M)
  | appL : ∀ {M M' N}, EtaStep M M' → EtaStep (Term.app M N) (Term.app M' N)
  | appR : ∀ {M N N'}, EtaStep N N' → EtaStep (Term.app M N) (Term.app M N')
  | lam : ∀ {M M'}, EtaStep M M' → EtaStep (Term.lam M) (Term.lam M')

/-- A single step of the union of beta and eta reduction. -/
inductive BetaEtaStep : Term → Term → Prop where
  | beta : ∀ {M N}, BetaStep M N → BetaEtaStep M N
  | eta : ∀ {M N}, EtaStep M N → BetaEtaStep M N

/-- The reflexive, symmetric, transitive closure of beta-eta steps. -/
inductive BetaEtaConv : Term → Term → Prop where
  | refl : ∀ M, BetaEtaConv M M
  | step : ∀ {M N P}, BetaEtaStep M N → BetaEtaConv N P → BetaEtaConv M P
  | stepInv : ∀ {M N P}, BetaEtaStep N M → BetaEtaConv N P → BetaEtaConv M P

/-- The ordinary untyped beta-eta theory on de Bruijn terms. -/
def TH_lambda_eq (M N : Term) : Prop := BetaEtaConv M N

/-! ## Extensional Kan-complex semantics -/

/-- A simplicial set interface with its face, degeneracy, and simplicial laws. -/
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
      i ≤ n + 1 → face (n + 1) i (degen (n + 1) i σ) = σ
  face_degen_succ : ∀ (n : Nat) (σ : Simplex (n + 1)) {i : Nat},
      i ≤ n + 1 → face (n + 1) (i + 1) (degen (n + 1) i σ) = σ
  face_degen_gt : ∀ (n : Nat) (σ : Simplex (n + 1)) {i j : Nat},
      j + 1 < i → i ≤ n + 2 →
      face (n + 1) i (degen (n + 1) j σ) = degen n j (face n (i - 1) σ)
  degen_degen : ∀ (n : Nat) (σ : Simplex n) {i j : Nat},
      i ≤ j → j ≤ n →
      degen (n + 1) (j + 1) (degen n i σ) = degen (n + 1) i (degen n j σ)

/-- The vertices (0-simplices) of a simplicial set. -/
abbrev SimplicialSet.Obj (S : SimplicialSet) : Type := S.Simplex 0

/-- The compatible faces of an `n`-simplex with one missing facet. -/
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

/-- A simplicial set in which every horn has a chosen filler. -/
structure KanComplex extends SimplicialSet where
  fill : ∀ {n missing : Nat}, Horn toSimplicialSet n missing → Simplex (n + 1)
  fill_spec : ∀ {n missing : Nat} (Λ : Horn toSimplicialSet n missing)
      {i : Nat} (_hi : i ≤ n + 1) (hmi : i ≠ missing),
      face n i (fill Λ) = Λ.facet i hmi

/-- The function space used to interpret application in a model. -/
def FunctorSpace (K : KanComplex) : Type := K.Obj → K.Obj

/-- A Kan complex equipped with retraction data for its function space. -/
structure ReflexiveKanComplex extends KanComplex where
  F : toKanComplex.Obj → FunctorSpace toKanComplex
  G : FunctorSpace toKanComplex → toKanComplex.Obj
  eta : ∀ (f : FunctorSpace toKanComplex) (x : toKanComplex.Obj), F (G f) x = f x

/-- A reflexive Kan complex whose function-space retraction is extensional. -/
structure ExtensionalKanComplex extends ReflexiveKanComplex where
  epsilon : ∀ (x : toReflexiveKanComplex.Obj), x = G (F x)

/-- An environment assigning a model object to every free variable index. -/
def Valuation (K : ReflexiveKanComplex) := Nat → K.Obj

/-- Update an environment at the outermost variable index. -/
def Valuation.update {K : ReflexiveKanComplex} (ρ : Valuation K) (v : K.Obj) : Valuation K :=
  fun n => if n = 0 then v else ρ (n - 1)

/-- Interpret a de Bruijn lambda term in the function-space model. -/
noncomputable def interpret (K : ReflexiveKanComplex) (ρ : Valuation K) : Term → K.Obj
  | Term.var n => ρ n
  | Term.app M N => K.F (interpret K ρ M) (interpret K ρ N)
  | Term.lam M => K.G (fun f => interpret K (fun n => if n = 0 then f else ρ (n - 1)) M)

/-- Equality of two terms under every valuation in a reflexive model. -/
def TheoryEq (K : ExtensionalKanComplex) (M N : Term) : Prop :=
  ∀ (ρ : Valuation K.toReflexiveKanComplex),
    interpret K.toReflexiveKanComplex ρ M = interpret K.toReflexiveKanComplex ρ N

/-- Equality in every extensional Kan-complex model. -/
def HoTFT_eq (M N : Term) : Prop :=
  ∀ (K : ExtensionalKanComplex), TheoryEq K M N

/-! The proof is intentionally left open here; Comparator checks the solution. -/

/-- Every beta/eta conversion is valid in every extensional Kan-complex model. -/
theorem main_result (M N : Term) (h : TH_lambda_eq M N) :
    HoTFT_eq M N := by
  sorry

end HigherLambdaModel.Palomar
