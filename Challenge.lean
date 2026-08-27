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

inductive Term : Type where
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving Repr, DecidableEq, Inhabited

namespace Term

def shift (d : Int) (c : Nat) : Term → Term
  | var n => if n < c then var n else var (Int.toNat (n + d))
  | app M N => app (shift d c M) (shift d c N)
  | lam M => lam (shift d (c + 1) M)

abbrev shift1 : Term → Term := shift 1 0

def subst (j : Nat) (N : Term) : Term → Term
  | var n =>
      if n = j then N
      else if n > j then var (n - 1)
      else var n
  | app M₁ M₂ => app (subst j N M₁) (subst j N M₂)
  | lam M => lam (subst (j + 1) (shift1 N) M)

abbrev subst0 (N : Term) (M : Term) : Term := subst 0 N M

def hasFreeVar (n : Nat) : Term → Bool
  | var m => m = n
  | app M N => hasFreeVar n M || hasFreeVar n N
  | lam M => hasFreeVar (n + 1) M

end Term

/-! ## Beta/eta conversion -/

inductive BetaStep : Term → Term → Prop where
  | beta : ∀ M N, BetaStep (Term.app (Term.lam M) N) (Term.subst0 N M)
  | appL : ∀ {M M' N}, BetaStep M M' → BetaStep (Term.app M N) (Term.app M' N)
  | appR : ∀ {M N N'}, BetaStep N N' → BetaStep (Term.app M N) (Term.app M N')
  | lam : ∀ {M M'}, BetaStep M M' → BetaStep (Term.lam M) (Term.lam M')

inductive EtaStep : Term → Term → Prop where
  | eta : ∀ M, ¬Term.hasFreeVar 0 M = true →
      EtaStep (Term.lam (Term.app M (Term.var 0))) (Term.shift (-1) 0 M)
  | appL : ∀ {M M' N}, EtaStep M M' → EtaStep (Term.app M N) (Term.app M' N)
  | appR : ∀ {M N N'}, EtaStep N N' → EtaStep (Term.app M N) (Term.app M N')
  | lam : ∀ {M M'}, EtaStep M M' → EtaStep (Term.lam M) (Term.lam M')

inductive BetaEtaStep : Term → Term → Prop where
  | beta : ∀ {M N}, BetaStep M N → BetaEtaStep M N
  | eta : ∀ {M N}, EtaStep M N → BetaEtaStep M N

inductive BetaEtaConv : Term → Term → Prop where
  | refl : ∀ M, BetaEtaConv M M
  | step : ∀ {M N P}, BetaEtaStep M N → BetaEtaConv N P → BetaEtaConv M P
  | stepInv : ∀ {M N P}, BetaEtaStep N M → BetaEtaConv N P → BetaEtaConv M P

def TH_lambda_eq (M N : Term) : Prop := BetaEtaConv M N

/-! ## Extensional Kan-complex semantics -/

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

abbrev SimplicialSet.Obj (S : SimplicialSet) : Type := S.Simplex 0

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

structure KanComplex extends SimplicialSet where
  fill : ∀ {n missing : Nat}, Horn toSimplicialSet n missing → Simplex (n + 1)
  fill_spec : ∀ {n missing : Nat} (Λ : Horn toSimplicialSet n missing)
      {i : Nat} (_hi : i ≤ n + 1) (hmi : i ≠ missing),
      face n i (fill Λ) = Λ.facet i hmi

def FunctorSpace (K : KanComplex) : Type := K.Obj → K.Obj

structure ReflexiveKanComplex extends KanComplex where
  F : toKanComplex.Obj → FunctorSpace toKanComplex
  G : FunctorSpace toKanComplex → toKanComplex.Obj
  eta : ∀ (f : FunctorSpace toKanComplex) (x : toKanComplex.Obj), F (G f) x = f x

structure ExtensionalKanComplex extends ReflexiveKanComplex where
  epsilon : ∀ (x : toReflexiveKanComplex.Obj), x = G (F x)

def Valuation (K : ReflexiveKanComplex) := Nat → K.Obj

def Valuation.update {K : ReflexiveKanComplex} (ρ : Valuation K) (v : K.Obj) : Valuation K :=
  fun n => if n = 0 then v else ρ (n - 1)

noncomputable def interpret (K : ReflexiveKanComplex) (ρ : Valuation K) : Term → K.Obj
  | Term.var n => ρ n
  | Term.app M N => K.F (interpret K ρ M) (interpret K ρ N)
  | Term.lam M => K.G (fun f => interpret K (fun n => if n = 0 then f else ρ (n - 1)) M)

def TheoryEq (K : ExtensionalKanComplex) (M N : Term) : Prop :=
  ∀ (ρ : Valuation K.toReflexiveKanComplex),
    interpret K.toReflexiveKanComplex ρ M = interpret K.toReflexiveKanComplex ρ N

def HoTFT_eq (M N : Term) : Prop :=
  ∀ (K : ExtensionalKanComplex), TheoryEq K M N

/-! The proof is intentionally left open here; Comparator checks the solution. -/

/-- Every beta/eta conversion is valid in every extensional Kan-complex model. -/
theorem main_result (M N : Term) (h : TH_lambda_eq M N) :
    HoTFT_eq M N := by
  sorry

end HigherLambdaModel.Palomar
