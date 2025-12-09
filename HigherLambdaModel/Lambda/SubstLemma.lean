/-
# Substitution Lemma for Interpretation

This module proves the key substitution lemma:
  ⟦M[N]⟧ρ = ⟦M⟧(ρ[⟦N⟧ρ/0])

The proof requires careful tracking of de Bruijn indices.
-/

import HigherLambdaModel.Lambda.Reduction

namespace HigherLambdaModel.Lambda.SubstLemma

open Term

/-! ## Kan Complex Structure (copied from ExtensionalKan for self-containment) -/

structure KanComplex where
  Simplex : Nat → Type
  Obj : Type := Simplex 0
  face : {n : Nat} → Fin (n + 2) → Simplex (n + 1) → Simplex n
  degen : {n : Nat} → Fin (n + 1) → Simplex n → Simplex (n + 1)
  PathSpace : Obj → Obj → Type
  pathSpace_isSimplex : ∀ a b, PathSpace a b = Simplex 1
  kanFilling : True

def FunctorSpace (K : KanComplex) : Type := K.Obj → K.Obj

structure ReflexiveKanComplex extends KanComplex where
  F : Obj → FunctorSpace toKanComplex
  G : FunctorSpace toKanComplex → Obj
  eta : ∀ (f : FunctorSpace toKanComplex) (x : Obj), F (G f) x = f x

def ReflexiveKanComplex.app (K : ReflexiveKanComplex) (a b : K.Obj) : K.Obj :=
  K.F a b

def Valuation (K : ReflexiveKanComplex) := Nat → K.Obj

noncomputable def interpret (K : ReflexiveKanComplex) (ρ : Valuation K) : Term → K.Obj
  | Term.var n => ρ n
  | Term.app M N => K.app (interpret K ρ M) (interpret K ρ N)
  | Term.lam M => K.G (fun f => interpret K (fun n => if n = 0 then f else ρ (n - 1)) M)

def Valuation.update {K : ReflexiveKanComplex} (ρ : Valuation K) (v : K.Obj) : Valuation K :=
  fun n => if n = 0 then v else ρ (n - 1)

/-! ## Key Shift Lemma -/

/-- Helper: (n : Nat) + (1 : Int) converted back to Nat equals n + 1 -/
theorem nat_add_one_toNat (n : Nat) : (↑n + (1 : Int)).toNat = n + 1 := by
  have h : (↑n : Int) + 1 = ↑(n + 1) := by omega
  rw [h]
  exact Int.toNat_natCast (n + 1)

/-- General shift lemma: shifting and adjusting valuation preserves interpretation -/
theorem interpret_shift_aux (K : ReflexiveKanComplex) (M : Term) :
    ∀ (ρ₁ ρ₂ : Valuation K) (c : Nat),
    (∀ n, n < c → ρ₁ n = ρ₂ n) →
    (∀ n, n ≥ c → ρ₁ (n + 1) = ρ₂ n) →
    interpret K ρ₁ (Term.shift 1 c M) = interpret K ρ₂ M := by
  induction M with
  | var n =>
    intro ρ₁ ρ₂ c h_lt h_ge
    simp only [Term.shift, interpret]
    split
    · -- n < c
      rename_i h
      exact h_lt n h
    · -- n ≥ c
      rename_i h_nlt
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
    · -- h_lt for c+1
      intro n hn
      cases n with
      | zero => rfl
      | succ n =>
        simp only [Nat.succ_sub_one]
        have : n < c := by omega
        exact h_lt n this
    · -- h_ge for c+1
      intro n hn
      cases n with
      | zero => omega
      | succ n =>
        simp only [Nat.succ_sub_one]
        have : n ≥ c := by omega
        exact h_ge n this

/-- Shifting by 1 at cutoff 0 with extended valuation -/
theorem interpret_shift1 (K : ReflexiveKanComplex) (N : Term) (ρ : Valuation K) (f : K.Obj) :
    interpret K (fun n => if n = 0 then f else ρ (n - 1)) (Term.shift1 N) =
    interpret K ρ N := by
  apply interpret_shift_aux
  · -- h_lt: for n < 0, impossible
    intro n hn
    omega
  · -- h_ge: for n ≥ 0
    intro n _
    cases n with
    | zero => rfl
    | succ n =>
      have h1 : n + 1 + 1 ≠ 0 := by omega
      have h2 : n + 1 + 1 - 1 = n + 1 := by omega
      simp only [h1, ↓reduceIte, h2]

/-! ## The Main Substitution Lemma -/

/-- Generalized substitution lemma -/
theorem interpret_subst_aux (K : ReflexiveKanComplex) (M : Term) :
    ∀ (N : Term) (ρ : Valuation K) (j : Nat),
    interpret K ρ (Term.subst j N M) =
    interpret K (fun n => if n = j then interpret K ρ N
                          else if n > j then ρ (n - 1)
                          else ρ n) M := by
  induction M with
  | var n =>
    intro N ρ j
    simp only [Term.subst, interpret]
    -- After simp, we need to handle three cases based on the split in subst
    split
    · -- n = j: goal is interpret K ρ N = interpret K ρ N
      rfl
    · split
      · -- n > j: goal is interpret K ρ (var (n - 1)) = ρ (n - 1)
        simp only [interpret]
      · -- n < j: goal is interpret K ρ (var n) = ρ n
        simp only [interpret]
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
      -- LHS: if 0 = j+1 then ... else if 0 > j+1 then ... else ρ' 0
      -- Since 0 ≠ j+1 and 0 ≯ j+1, we get ρ' 0 = g
      have h1 : ¬(0 = j + 1) := by omega
      have h2 : ¬(0 > j + 1) := by omega
      simp only [if_neg h1, if_neg h2]
      -- ρ' 0 = (if 0 = 0 then g else ...) = g
      rfl
    | succ n =>
      simp only [Nat.succ_sub_one]
      split
      · -- n + 1 = j + 1, i.e., n = j
        rename_i heq
        have hneq : n = j := by omega
        simp only [hneq, ↓reduceIte]
        -- Need: interpret K ρ' (shift1 N) = interpret K ρ N
        exact interpret_shift1 K N ρ g
      · split
        · -- n + 1 > j + 1, i.e., n > j
          rename_i hne hgt
          have hgt' : n > j := by omega
          have hne' : n ≠ j := by omega
          simp only [if_neg hne', if_pos hgt']
          -- Need: ρ' n = ρ (n - 1)
          -- ρ' n = if n = 0 then g else ρ (n - 1)
          have hn0 : n ≠ 0 := by omega
          show (if n = 0 then g else ρ (n - 1)) = ρ (n - 1)
          simp only [if_neg hn0]
        · -- n + 1 ≤ j + 1, i.e., n ≤ j, and n + 1 ≠ j + 1, so n < j
          rename_i hne hng
          have hlt : n < j := by omega
          have hne' : n ≠ j := by omega
          have hng' : ¬(n > j) := by omega
          simp only [if_neg hne', if_neg hng']
          -- Need: ρ' (n + 1) = ρ n
          -- ρ' (n + 1) = if n+1 = 0 then g else ρ ((n+1) - 1) = ρ n
          have hn0 : n + 1 ≠ 0 := by omega
          show (if n + 1 = 0 then g else ρ (n + 1 - 1)) = ρ n
          simp only [if_neg hn0, Nat.add_sub_cancel]

/-- The main substitution lemma -/
theorem interpret_subst (K : ReflexiveKanComplex) (M N : Term) (ρ : Valuation K) :
    interpret K ρ (M[N]) = interpret K (ρ.update (interpret K ρ N)) M := by
  simp only [Term.subst0]
  rw [interpret_subst_aux K M N ρ 0]
  congr 1
  funext n
  simp only [Valuation.update]
  cases n with
  | zero =>
    -- Goal: (if 0 = 0 then v else if 0 > 0 then ... else ρ 0) = (if 0 = 0 then v else ...)
    simp only [↓reduceIte]
  | succ n =>
    have h1 : n + 1 ≠ 0 := by omega
    have h2 : n + 1 > 0 := by omega
    have h3 : n + 1 - 1 = n := by omega
    simp only [if_neg h1, if_pos h2, h3]

end HigherLambdaModel.Lambda.SubstLemma
