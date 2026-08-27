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

/-! ## Restricted exponential semantics

The semantic morphisms are a chosen exponential object, not the full
set-theoretic endomap space.  Bodies are specifications supplied to the
restricted abstraction operation; only term-generated bodies need be exact. -/

structure Body (α : Type) where
  run : α → α

structure ReflexiveKanComplex extends KanComplex where
  Morphism : Type
  eval : Morphism → toKanComplex.Obj → toKanComplex.Obj
  reify : toKanComplex.Obj → Morphism
  reflect : Morphism → toKanComplex.Obj
  abstract : Body toKanComplex.Obj → Morphism
  reify_reflect_eval :
    ∀ (m : Morphism) (x : toKanComplex.Obj),
      eval (reify (reflect m)) x = eval m x

noncomputable def interpret (K : ReflexiveKanComplex) (ρ : Nat → K.Obj) : Term → K.Obj
  | Term.var n => ρ n
  | Term.app M N =>
      K.eval (K.reify (interpret K ρ M)) (interpret K ρ N)
  | Term.lam M =>
      K.reflect (K.abstract
        { run := fun f => interpret K (fun n => if n = 0 then f else ρ (n - 1)) M })

private theorem body_ext {α : Type} {b c : Body α}
    (h : ∀ x, b.run x = c.run x) : b = c := by
  cases b with
  | mk b =>
    cases c with
    | mk c =>
      congr 1
      exact funext h

structure ExtensionalKanComplex extends ReflexiveKanComplex where
  reflect_reify : ∀ (x : toReflexiveKanComplex.Obj),
    toReflexiveKanComplex.reflect (toReflexiveKanComplex.reify x) = x
  morphism_extensional :
    ∀ (m n : toReflexiveKanComplex.Morphism),
      (∀ x, toReflexiveKanComplex.eval m x =
        toReflexiveKanComplex.eval n x) →
      toReflexiveKanComplex.reflect m =
        toReflexiveKanComplex.reflect n

structure CertifiedExtensionalKanComplex extends ExtensionalKanComplex where
  abstract_eval :
    ∀ (ρ : Nat → toReflexiveKanComplex.Obj) (M : Term)
      (x : toReflexiveKanComplex.Obj),
      toReflexiveKanComplex.eval
          (toReflexiveKanComplex.abstract
            { run := fun f =>
                interpret toReflexiveKanComplex
                  (fun n => if n = 0 then f else ρ (n - 1)) M }) x =
        interpret toReflexiveKanComplex
          (fun n => if n = 0 then x else ρ (n - 1)) M

abbrev CertifiedExtensionalKanComplex.reflexive
    (K : CertifiedExtensionalKanComplex) : ReflexiveKanComplex :=
  K.toExtensionalKanComplex.toReflexiveKanComplex

def Valuation (K : ReflexiveKanComplex) := Nat → K.Obj

def Valuation.update {K : ReflexiveKanComplex} (ρ : Valuation K) (v : K.Obj) : Valuation K :=
  fun n => if n = 0 then v else ρ (n - 1)

def TheoryEq (K : CertifiedExtensionalKanComplex) (M N : Term) : Prop :=
  ∀ (ρ : Valuation K.toExtensionalKanComplex.toReflexiveKanComplex),
    interpret K.toExtensionalKanComplex.toReflexiveKanComplex ρ M =
      interpret K.toExtensionalKanComplex.toReflexiveKanComplex ρ N

def HoTFT_eq (M N : Term) : Prop :=
  ∀ (K : CertifiedExtensionalKanComplex), TheoryEq K M N

/-! ### Concrete nontrivial restricted carrier -/

def boolSimplicialSet : SimplicialSet where
  Simplex := fun _ => Bool
  face := fun _ _ b => b
  degen := fun _ _ b => b
  face_degen0_eq := by intro σ; rfl
  face_degen0_succ := by intro σ; rfl
  face_face := by intro n σ i j hij hj; rfl
  face_degen_lt := by intro n σ i j hij hj; rfl
  face_degen_eq := by intro n σ i hi; rfl
  face_degen_succ := by intro n σ i hi; rfl
  face_degen_gt := by intro n σ i j hji hi; rfl
  degen_degen := by intro n σ i j hij hj; rfl

private def boolHornPivot {n i : Nat} (_hi : i ≤ n + 1) : Nat :=
  if i = 0 then 1 else 0

private theorem boolHornPivot_ne {n i : Nat} (hi : i ≤ n + 1) :
    boolHornPivot hi ≠ i := by
  by_cases h : i = 0
  · subst h
    simp [boolHornPivot]
  · simp [boolHornPivot, h]
    intro h0
    exact h h0.symm

private theorem boolHornPivot_le {n i : Nat} (hi : i ≤ n + 1) :
    boolHornPivot hi ≤ n + 1 := by
  by_cases h : i = 0
  · subst h
    simp [boolHornPivot]
  · simp [boolHornPivot, h]

private theorem boolHornFacetsEq
    {n i : Nat} (Λ : Horn boolSimplicialSet n i)
    {j k : Nat} (hj : j ≤ n + 1) (hk : k ≤ n + 1)
    (hji : j ≠ i) (hki : k ≠ i) :
    Λ.facet j hji = Λ.facet k hki := by
  cases n with
  | zero =>
      have hi := Λ.missing_le
      have hi' : i = 0 ∨ i = 1 := by omega
      have hj' : j = 0 ∨ j = 1 := by omega
      have hk' : k = 0 ∨ k = 1 := by omega
      rcases hi' with rfl | rfl <;>
        rcases hj' with rfl | rfl <;>
          rcases hk' with rfl | rfl <;>
            first
            | rfl
            | exact False.elim (hji rfl)
            | exact False.elim (hki rfl)
  | succ m =>
      by_cases hjk : j = k
      · subst hjk
        rfl
      · cases Nat.lt_or_gt_of_ne hjk with
        | inl hjkLt =>
            simpa [boolSimplicialSet] using
              (Λ.compatibility hj hk hji hki hjkLt).symm
        | inr hkjLt =>
            simpa [boolSimplicialSet] using
              Λ.compatibility hk hj hki hji hkjLt

def boolKanComplex : KanComplex where
  toSimplicialSet := boolSimplicialSet
  fill := fun {n} {missing} Λ =>
    Λ.facet (boolHornPivot Λ.missing_le) (boolHornPivot_ne Λ.missing_le)
  fill_spec := by
    intro n missing Λ i hi hmi
    exact boolHornFacetsEq Λ (boolHornPivot_le Λ.missing_le) hi
      (boolHornPivot_ne Λ.missing_le) hmi

def boolRestrictedModel : ReflexiveKanComplex where
  toKanComplex := boolKanComplex
  Morphism := boolKanComplex.Obj
  eval := fun m _ => m
  reify := fun x => x
  reflect := fun m => m
  abstract := fun b => b.run false
  reify_reflect_eval := by intro m x; rfl

def boolExtensionalCandidate : ExtensionalKanComplex where
  toReflexiveKanComplex := boolRestrictedModel
  reflect_reify := by intro x; rfl
  morphism_extensional := by
    intro m n h
    exact h false

theorem boolExtensionalCandidate_nontrivial :
    ∃ x y : boolExtensionalCandidate.toReflexiveKanComplex.Obj, x ≠ y := by
  refine ⟨false, true, ?_⟩
  intro h
  cases h

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
    apply congrArg K.reflect
    apply congrArg K.abstract
    apply body_ext
    intro f
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
    apply congrArg K.reflect
    apply congrArg K.abstract
    apply body_ext
    intro g
    let ρ' := fun n => if n = 0 then g else ρ (n - 1)
    change interpret K ρ' (Term.subst (j + 1) (Term.shift1 N) M) =
      interpret K
        (fun n => if n = 0 then g
          else if n - 1 = j then interpret K ρ N
          else if n - 1 > j then ρ (n - 1 - 1) else ρ (n - 1)) M
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
    apply congrArg K.reflect
    apply congrArg K.abstract
    apply body_ext
    intro g
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

private theorem beta_sound (K : CertifiedExtensionalKanComplex) {M N : Term}
    (h : BetaStep M N) (ρ : Valuation K.reflexive) :
    interpret K.reflexive ρ M = interpret K.reflexive ρ N := by
  induction h generalizing ρ with
  | beta M N =>
    simp only [interpret]
    rw [K.reflexive.reify_reflect_eval]
    calc
      K.reflexive.eval (K.reflexive.abstract
          { run := fun f =>
              interpret K.reflexive
                (fun n => if n = 0 then f else ρ (n - 1)) M })
          (interpret K.reflexive ρ N) =
          interpret K.reflexive
            (fun n => if n = 0 then interpret K.reflexive ρ N
              else ρ (n - 1)) M :=
        K.abstract_eval ρ M (interpret K.reflexive ρ N)
      _ = interpret K.reflexive ρ (Term.subst0 N M) := by
        symm
        exact surface_subst K.reflexive M N ρ
  | appL h ih =>
    simp only [interpret]
    rw [ih]
  | appR h ih =>
    simp only [interpret]
    rw [ih]
  | lam h ih =>
    simp only [interpret]
    apply congrArg K.reflexive.reflect
    apply congrArg K.reflexive.abstract
    apply body_ext
    intro f
    exact ih (Valuation.update ρ f)

private theorem eta_sound (K : CertifiedExtensionalKanComplex) {M N : Term}
    (h : EtaStep M N) (ρ : Valuation K.reflexive) :
    interpret K.reflexive ρ M = interpret K.reflexive ρ N := by
  induction h generalizing ρ with
  | eta M hfv =>
    simp only [interpret]
    have hfv' : Term.hasFreeVar 0 M = false := by
      cases h : Term.hasFreeVar 0 M with
      | false => rfl
      | true => exact False.elim (hfv h)
    rw [← K.toExtensionalKanComplex.reflect_reify
      (interpret K.reflexive ρ (Term.shift (-1) 0 M))]
    apply K.toExtensionalKanComplex.morphism_extensional
    intro f
    calc
      K.reflexive.eval (K.reflexive.abstract
          { run := fun g =>
              interpret K.reflexive
                (fun n => if n = 0 then g else ρ (n - 1))
                (Term.app M (Term.var 0)) }) f =
          interpret K.reflexive
            (fun n => if n = 0 then f else ρ (n - 1))
              (Term.app M (Term.var 0)) :=
        K.abstract_eval ρ (Term.app M (Term.var 0)) f
      _ = K.reflexive.eval (K.reflexive.reify
            (interpret K.reflexive
              (fun n => if n = 0 then f else ρ (n - 1)) M)) f := by
        rfl
      _ = K.reflexive.eval (K.reflexive.reify
            (interpret K.reflexive
              ρ (Term.shift (-1) 0 M))) f := by
        rw [surface_unshift K.reflexive M ρ f hfv']
  | appL h ih =>
    simp only [interpret]
    rw [ih]
  | appR h ih =>
    simp only [interpret]
    rw [ih]
  | lam h ih =>
    simp only [interpret]
    apply congrArg K.reflexive.reflect
    apply congrArg K.reflexive.abstract
    apply body_ext
    intro f
    exact ih (Valuation.update ρ f)

/-- Every beta/eta conversion is valid in every certified extensional
restricted-exponential model. -/
theorem main_result (M N : Term) (h : TH_lambda_eq M N) :
    HoTFT_eq M N := by
  intro K
  change BetaEtaConv M N at h
  have sound : ∀ {M N : Term}, BetaEtaConv M N →
      ∀ (ρ : Valuation K.reflexive),
        interpret K.reflexive ρ M =
          interpret K.reflexive ρ N := by
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
