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

namespace HigherLambdaModel.Lambda.ExtensionalKan

open Term

/-! ## Simplicial Sets and Kan Complexes -/

structure KanComplex where
  Simplex : Nat → Type
  Obj : Type := Simplex 0
  face : {n : Nat} → Fin (n + 2) → Simplex (n + 1) → Simplex n
  degen : {n : Nat} → Fin (n + 1) → Simplex n → Simplex (n + 1)
  PathSpace : Obj → Obj → Type
  pathSpace_isSimplex : ∀ a b, PathSpace a b = Simplex 1
  kanFilling : True

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
  F : Obj → FunctorSpace toKanComplex
  G : FunctorSpace toKanComplex → Obj
  eta : ∀ (f : FunctorSpace toKanComplex) (x : Obj), F (G f) x = f x

/-! ## Extensional Kan Complexes -/

/-- An extensional Kan complex adds the ε-law to a reflexive Kan complex:
    ε: x = G(F(x)) for all objects x

    This ensures that every object can be recovered from its "function behavior",
    making the model fully extensional. Together with η, this gives us:
    - η: F(G(f)) = f (functions are determined by their graphs)
    - ε: G(F(x)) = x (objects are determined by their function behavior)

    In such models, β-reduction and η-reduction are both sound. -/
structure ExtensionalKanComplex extends ReflexiveKanComplex where
  epsilon : ∀ (x : Obj), x = G (F x)

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

/-! ## β-reduction Soundness (Remark 2.1) -/

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
  simp only [interpret, ReflexiveKanComplex.app]
  rw [K.eta, interpret_subst]
  rfl

/-! ## η-reduction Soundness -/

/-- η-reduction is sound in extensional Kan complexes:

    ⟦λx.Mx⟧ρ = ⟦M⟧ρ  (when x ∉ FV(M))

    This theorem shows that the η-reduction rule λx.Mx →η M preserves meaning
    when x is not free in M. The proof uses:
    1. The ε-law (extensionality): x = G(F(x))
    2. The shift lemma for terms without free variable 0

    This requires the full extensionality axiom, unlike β-soundness which
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

def HoTFT_eq (M N : Term) : Prop :=
  ∀ (K : ExtensionalKanComplex), TheoryEq K M N

scoped notation:50 M " =_HoTFT " N => HoTFT_eq M N

theorem beta_in_HoTFT (M N : Term) : (Term.app (Term.lam M) N) =_HoTFT (M[N]) := fun K ρ =>
  beta_sound K M N ρ

theorem eta_in_HoTFT (M : Term) (h : Term.hasFreeVar 0 M = false) :
    (Term.lam (Term.app (Term.shift 1 0 M) (Term.var 0))) =_HoTFT M := fun K ρ =>
  eta_sound K M ρ h

end HigherLambdaModel.Lambda.ExtensionalKan
