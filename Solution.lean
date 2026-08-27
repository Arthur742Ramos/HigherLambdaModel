import Mathlib.Data.Nat.Basic

namespace HigherLambdaModel.Palomar

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

private theorem surface_nat_add_one_toNat (n : Nat) :
    (↑n + (1 : Int)).toNat = n + 1 := by
  have h : (↑n : Int) + 1 = ↑(n + 1) := by omega
  rw [h]
  exact Int.toNat_natCast (n + 1)

private theorem surface_shift_aux (K : ReflexiveKanComplex) (M : Term) :
    ∀ (ρ₁ ρ₂ : Valuation K) (c : Nat),
    (∀ n, n < c → ρ₁ n = ρ₂ n) →
    (∀ n, n ≥ c → ρ₁ (n + 1) = ρ₂ n) →
    interpret K ρ₁ (Term.shift 1 c M) = interpret K ρ₂ M := by
  induction M with
  | var n =>
    intro ρ₁ ρ₂ c h_lt h_ge
    simp only [Term.shift, interpret]
    split
    · rename_i h
      exact h_lt n h
    · rename_i h_nlt
      have h : n ≥ c := Nat.le_of_not_lt h_nlt
      simp only [surface_nat_add_one_toNat, interpret]
      exact h_ge n h
  | app M₁ M₂ ih₁ ih₂ =>
    intro ρ₁ ρ₂ c h_lt h_ge
    simp only [Term.shift, interpret]
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
      | succ n => exact h_lt n (by omega)
    · intro n hn
      cases n with
      | zero => omega
      | succ n => exact h_ge n (by omega)

private theorem surface_shift1 (K : ReflexiveKanComplex) (N : Term) (ρ : Valuation K) (f : K.Obj) :
    interpret K (fun n => if n = 0 then f else ρ (n - 1)) (Term.shift1 N) =
      interpret K ρ N := by
  apply surface_shift_aux
  · intro n hn
    omega
  · intro n _
    cases n with
    | zero => rfl
    | succ n =>
      have h1 : n + 1 + 1 ≠ 0 := by omega
      have h2 : n + 1 + 1 - 1 = n + 1 := by omega
      simp only [h1, ↓reduceIte, h2]

private theorem surface_subst_aux (K : ReflexiveKanComplex) (M : Term) :
    ∀ (N : Term) (ρ : Valuation K) (j : Nat),
    interpret K ρ (Term.subst j N M) =
      interpret K (fun n => if n = j then interpret K ρ N
        else if n > j then ρ (n - 1) else ρ n) M := by
  induction M with
  | var n =>
    intro N ρ j
    simp only [Term.subst, interpret]
    split
    · rfl
    · split <;> simp only [interpret]
  | app M₁ M₂ ih₁ ih₂ =>
    intro N ρ j
    simp only [Term.subst, interpret]
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
        exact surface_shift1 K N ρ g
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

private theorem surface_subst (K : ReflexiveKanComplex) (M N : Term) (ρ : Valuation K) :
    interpret K ρ (Term.subst0 N M) =
      interpret K (Valuation.update ρ (interpret K ρ N)) M := by
  simp only [Term.subst0]
  rw [surface_subst_aux K M N ρ 0]
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

private theorem surface_nat_sub_one_toNat (n : Nat) (h : n ≥ 1) :
    (↑n + (-1 : Int)).toNat = n - 1 := by
  have h' : (↑n : Int) + (-1) = ↑(n - 1) := by omega
  rw [h']
  exact Int.toNat_natCast (n - 1)

private theorem surface_unshift_aux (K : ReflexiveKanComplex) (M : Term) :
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
    · have hne : n ≠ c := by
        intro heq
        simp only [heq, decide_true, Bool.true_eq_false] at hfv
      have hn_gt : n > c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hn) (Ne.symm hne)
      simp only [hn, ↓reduceIte]
      have hn_ge1 : n ≥ 1 := by omega
      simp only [surface_nat_sub_one_toNat n hn_ge1, interpret]
      exact h_gt n hn_gt
  | app M₁ M₂ ih₁ ih₂ =>
    intro ρ₁ ρ₂ c h_lt h_gt hfv
    simp only [Term.hasFreeVar, Bool.or_eq_false_iff] at hfv
    simp only [Term.shift, interpret]
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
    · intro n hn
      cases n with
      | zero => rfl
      | succ n =>
        simp only [Nat.succ_sub_one, ρ₁', ρ₂']
        exact h_lt n (by omega)
    · intro n hn
      cases n with
      | zero => omega
      | succ n =>
        have hn' : n > c := by omega
        have hn0 : n ≠ 0 := by omega
        simp only [Nat.succ_sub_one, ρ₁', ρ₂', hn0, ↓reduceIte]
        exact h_gt n hn'
    · exact hfv

private theorem surface_unshift (K : ReflexiveKanComplex) (M : Term)
    (ρ : Valuation K) (f : K.Obj) (h : Term.hasFreeVar 0 M = false) :
    interpret K (fun n => if n = 0 then f else ρ (n - 1)) M =
      interpret K ρ (Term.shift (-1) 0 M) := by
  apply surface_unshift_aux
  · intro n hn
    omega
  · intro n hn
    have h1 : n ≠ 0 := by omega
    simp only [h1, ↓reduceIte]
  · exact h

private theorem beta_sound (K : ExtensionalKanComplex) {M N : Term}
    (h : BetaStep M N) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M = interpret K.toReflexiveKanComplex ρ N := by
  induction h generalizing ρ with
  | beta M N =>
    simp only [interpret]
    rw [surface_subst]
    exact (K.toReflexiveKanComplex.eta
      (fun f => interpret K.toReflexiveKanComplex
        (Valuation.update ρ f) M) (interpret K.toReflexiveKanComplex ρ N))
  | appL h ih =>
    simp only [interpret]
    rw [ih]
  | appR h ih =>
    simp only [interpret]
    rw [ih]
  | lam h ih =>
    simp only [interpret]
    congr 1
    funext f
    exact ih (Valuation.update ρ f)

private theorem eta_sound (K : ExtensionalKanComplex) {M N : Term}
    (h : EtaStep M N) (ρ : Valuation K.toReflexiveKanComplex) :
    interpret K.toReflexiveKanComplex ρ M = interpret K.toReflexiveKanComplex ρ N := by
  induction h generalizing ρ with
  | eta M hfv =>
    simp only [interpret]
    have hfv' : Term.hasFreeVar 0 M = false := by
      cases h : Term.hasFreeVar 0 M with
      | false => rfl
      | true => exact False.elim (hfv h)
    have key : ∀ f, interpret K.toReflexiveKanComplex
        (fun n => if n = 0 then f else ρ (n - 1)) M =
        interpret K.toReflexiveKanComplex ρ (Term.shift (-1) 0 M) :=
      fun f => surface_unshift K.toReflexiveKanComplex M ρ f hfv'
    simp only [key]
    exact (K.epsilon (interpret K.toReflexiveKanComplex ρ
      (Term.shift (-1) 0 M))).symm
  | appL h ih =>
    simp only [interpret]
    rw [ih]
  | appR h ih =>
    simp only [interpret]
    rw [ih]
  | lam h ih =>
    simp only [interpret]
    congr 1
    funext f
    exact ih (Valuation.update ρ f)

/-- Every beta/eta conversion is valid in every extensional Kan-complex model. -/
theorem main_result (M N : Term) (h : TH_lambda_eq M N) :
    HoTFT_eq M N := by
  intro K
  change BetaEtaConv M N at h
  have sound : ∀ {M N : Term}, BetaEtaConv M N →
      ∀ (ρ : Valuation K.toReflexiveKanComplex),
        interpret K.toReflexiveKanComplex ρ M =
          interpret K.toReflexiveKanComplex ρ N := by
    intro M N h
    induction h with
    | refl M =>
      intro ρ
      rfl
    | step h _ ih =>
      intro ρ
      cases h with
      | beta h => exact (beta_sound K h ρ).trans (ih ρ)
      | eta h => exact (eta_sound K h ρ).trans (ih ρ)
    | stepInv h _ ih =>
      intro ρ
      cases h with
      | beta h => exact (beta_sound K h ρ).symm.trans (ih ρ)
      | eta h => exact (eta_sound K h ρ).symm.trans (ih ρ)
  exact sound h

end HigherLambdaModel.Palomar
