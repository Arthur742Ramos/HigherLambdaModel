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

structure KanComplex.PathSpace (K : KanComplex) (a b : K.Obj) where
  simplex : K.Simplex 1
  source : K.face 0 1 simplex = a
  target : K.face 0 0 simplex = b

def KanComplex.reflPath (K : KanComplex) (a : K.Obj) : K.PathSpace a a where
  simplex := K.degen 0 0 a
  source := K.face_degen0_succ a
  target := K.face_degen0_eq a

structure KanComplex.Path2 (K : KanComplex) {a b : K.Obj}
    (p q : K.PathSpace a b) where
  simplex : K.Simplex 2
  face0 : K.face 1 0 simplex = (K.reflPath b).simplex
  face1 : K.face 1 1 simplex = q.simplex
  face2 : K.face 1 2 simplex = p.simplex

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

def KanComplex.compPath (K : KanComplex) {a b c : K.Obj}
    (p : K.PathSpace a b) (q : K.PathSpace b c) : K.PathSpace a c := by
  let Λ : Horn K.toSimplicialSet 1 1 :=
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
  refine
    { simplex := K.face 1 1 (K.fill Λ)
      source := ?_
      target := ?_ }
  · have h2 : K.face 1 2 (K.fill Λ) = p.simplex :=
      K.fill_spec Λ (i := 2) (by omega) (by omega)
    calc
      K.face 0 1 (K.face 1 1 (K.fill Λ))
          = K.face 0 1 (K.face 1 2 (K.fill Λ)) := by
              symm
              simpa using (K.face_face 0 (K.fill Λ) (i := 1) (j := 1) (by omega) (by omega))
      _ = K.face 0 1 p.simplex := by rw [h2]
      _ = a := p.source
  · have h0 : K.face 1 0 (K.fill Λ) = q.simplex :=
      K.fill_spec Λ (i := 0) (by omega) (by omega)
    calc
      K.face 0 0 (K.face 1 1 (K.fill Λ))
          = K.face 0 0 (K.face 1 0 (K.fill Λ)) := by
              simpa using (K.face_face 0 (K.fill Λ) (i := 0) (j := 0) (by omega) (by omega))
      _ = K.face 0 0 q.simplex := by rw [h0]
      _ = c := q.target

def FunctorSpace (K : KanComplex) : Type := K.Obj → K.Obj

structure ReflexiveKanComplex extends KanComplex where
  F : toKanComplex.Obj → FunctorSpace toKanComplex
  G : FunctorSpace toKanComplex → toKanComplex.Obj
  eta : ∀ (f : FunctorSpace toKanComplex) (x : toKanComplex.Obj), F (G f) x = f x

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
