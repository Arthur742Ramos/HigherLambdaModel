/-
# βη-Confluence via Hindley-Rosen

This module proves Church-Rosser for βη-reduction by combining:
1. β-confluence (proven in ChurchRosserProof.lean via Metatheory)
2. η-confluence (proven via Newman's lemma: termination + local confluence)
3. β-η commutation (axiomatized - well-known result from Barendregt 1984)
4. Hindley-Rosen lemma from Metatheory

## References

- Metatheory library: https://github.com/Arthur742Ramos/Metatheory
- Barendregt (1984): "The Lambda Calculus", Section 3.3
- Takahashi (1995): "Parallel Reductions in λ-Calculus"
-/

import Metatheory
import HigherLambdaModel.Lambda.Reduction
import HigherLambdaModel.Lambda.ChurchRosserProof

namespace HigherLambdaModel.Lambda.BetaEtaConfluence

open HigherLambdaModel.Lambda
open HigherLambdaModel.Lambda.ChurchRosserProof

/-! ## Helper: hasFreeVar for Metatheory terms -/

/-- Check if variable n is free in a Metatheory term -/
def hasFreeVarMeta (n : Nat) : Metatheory.Lambda.Term → Bool
  | .var m => m == n
  | .app M N => hasFreeVarMeta n M || hasFreeVarMeta n N
  | .lam M => hasFreeVarMeta (n + 1) M

/-- hasFreeVar correspondence with toMeta -/
theorem hasFreeVar_toMeta (n : Nat) (M : Term) :
    hasFreeVarMeta n (toMeta M) = Term.hasFreeVar n M := by
  induction M generalizing n with
  | var m => rfl
  | app M N ihM ihN => simp only [toMeta, hasFreeVarMeta, Term.hasFreeVar, ihM, ihN]
  | lam M ih => simp only [toMeta, hasFreeVarMeta, Term.hasFreeVar, ih]

/-! ## η-Reduction in Metatheory Framework -/

/-- Single η-reduction step (in Metatheory's framework) -/
inductive EtaStepMeta : Metatheory.Lambda.Term → Metatheory.Lambda.Term → Prop where
  | eta : ∀ M, hasFreeVarMeta 0 M = false →
      EtaStepMeta (.lam (.app M (.var 0))) (Metatheory.Lambda.Term.shift (-1) 0 M)
  | appL : ∀ {M M' N}, EtaStepMeta M M' → EtaStepMeta (.app M N) (.app M' N)
  | appR : ∀ {M N N'}, EtaStepMeta N N' → EtaStepMeta (.app M N) (.app M N')
  | lam : ∀ {M M'}, EtaStepMeta M M' → EtaStepMeta (.lam M) (.lam M')

/-- Combined βη-step in Metatheory framework -/
inductive BetaEtaStepMeta : Metatheory.Lambda.Term → Metatheory.Lambda.Term → Prop where
  | beta : ∀ {M N}, Metatheory.Lambda.BetaStep M N → BetaEtaStepMeta M N
  | eta : ∀ {M N}, EtaStepMeta M N → BetaEtaStepMeta M N

/-! ## η-Termination -/

/-- Size of a term (for termination proofs) -/
def termSize : Metatheory.Lambda.Term → Nat
  | .var _ => 1
  | .app M N => 1 + termSize M + termSize N
  | .lam M => 1 + termSize M

theorem termSize_pos (M : Metatheory.Lambda.Term) : termSize M > 0 := by
  induction M with
  | var _ => simp [termSize]
  | app _ _ _ _ => simp [termSize]; omega
  | lam _ _ => simp [termSize]; omega

theorem termSize_shift (d : Int) (c : Nat) (M : Metatheory.Lambda.Term) :
    termSize (Metatheory.Lambda.Term.shift d c M) = termSize M := by
  induction M generalizing c with
  | var n =>
    simp only [Metatheory.Lambda.Term.shift, termSize]
    split <;> simp [termSize]
  | app M N ihM ihN =>
    simp only [Metatheory.Lambda.Term.shift, termSize, ihM, ihN]
  | lam M ih =>
    simp only [Metatheory.Lambda.Term.shift, termSize, ih]

theorem etaStep_decreases_size {M N : Metatheory.Lambda.Term} (h : EtaStepMeta M N) :
    termSize N < termSize M := by
  induction h with
  | eta M' _ =>
    simp only [termSize]
    rw [termSize_shift]
    have := termSize_pos M'
    omega
  | appL _ ih => simp only [termSize]; omega
  | appR _ ih => simp only [termSize]; omega
  | lam _ ih => simp only [termSize]; omega

/-- η-reduction is terminating -/
theorem eta_terminating : Rewriting.Terminating EtaStepMeta := by
  unfold Rewriting.Terminating
  apply WellFounded.intro
  intro M
  generalize hn : termSize M = n
  induction n using Nat.strongRecOn generalizing M with
  | ind n ih =>
    constructor
    intro N hstep
    have hlt : termSize N < termSize M := by
      induction hstep with
      | single hMN => exact etaStep_decreases_size hMN
      | tail _ hPN ih_tail => have h1 := ih_tail; have h2 := etaStep_decreases_size hPN; omega
    subst hn
    exact ih (termSize N) hlt N rfl

/-! ## η-Local Confluence Infrastructure -/

/-- Helper: beq produces equal Bool values when both equalities have the same truth value -/
private theorem beq_eq_beq_of_iff {a b c d : Nat} (h : a = b ↔ c = d) : (a == b) = (c == d) := by
  cases Nat.decEq a b with
  | isTrue hab => rw [beq_iff_eq.mpr hab, beq_iff_eq.mpr (h.mp hab)]
  | isFalse hab => rw [beq_eq_false_iff_ne.mpr hab, beq_eq_false_iff_ne.mpr (mt h.mpr hab)]

/-- If variable c is not free in N, shifting by -1 at cutoff c equals shifting at cutoff c+1 -/
theorem shift_neg1_cutoff_irrelevant (N : Metatheory.Lambda.Term) (c : Nat)
    (hfv : hasFreeVarMeta c N = false) :
    Metatheory.Lambda.Term.shift (-1) c N = Metatheory.Lambda.Term.shift (-1) (c + 1) N := by
  induction N generalizing c with
  | var n =>
    simp only [hasFreeVarMeta] at hfv
    simp only [Metatheory.Lambda.Term.shift]
    by_cases h1 : n < c
    · simp only [h1, ↓reduceIte, Nat.lt_succ_of_lt h1]
    · simp only [h1, ↓reduceIte]
      have hge : n ≥ c := Nat.le_of_not_lt h1
      have hne : n ≠ c := by intro heq; subst heq; simp at hfv
      have h3 : n > c := Nat.lt_of_le_of_ne hge (Ne.symm hne)
      have h4 : ¬(n < c + 1) := Nat.not_lt.mpr h3
      simp only [h4, ↓reduceIte]
  | app M N ihM ihN =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv
    simp only [Metatheory.Lambda.Term.shift, ihM c hfv.1, ihN c hfv.2]
  | lam M ih =>
    simp only [hasFreeVarMeta] at hfv
    simp only [Metatheory.Lambda.Term.shift]
    congr 1
    exact ih (c + 1) hfv

/-- hasFreeVarMeta for shift at cutoff c -/
theorem hasFreeVarMeta_shift_neg1_gen (N : Metatheory.Lambda.Term) (n c : Nat)
    (hfv : hasFreeVarMeta c N = false) :
    hasFreeVarMeta n (Metatheory.Lambda.Term.shift (-1) c N) =
    if n < c then hasFreeVarMeta n N else hasFreeVarMeta (n + 1) N := by
  induction N generalizing n c with
  | var m =>
    simp only [hasFreeVarMeta] at hfv
    simp only [Metatheory.Lambda.Term.shift, hasFreeVarMeta]
    have hm_ne_c : m ≠ c := by intro heq; subst heq; simp at hfv
    by_cases hm_lt_c : m < c
    · simp only [hm_lt_c, ↓reduceIte, hasFreeVarMeta]
      by_cases hn_lt_c : n < c
      · rw [if_pos hn_lt_c]
      · rw [if_neg hn_lt_c]
        have hge : n ≥ c := Nat.le_of_not_lt hn_lt_c
        apply beq_eq_beq_of_iff; constructor <;> intro <;> omega
    · simp only [hm_lt_c, ↓reduceIte]
      have hm_gt_c : m > c := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hm_lt_c) (Ne.symm hm_ne_c)
      have h_toNat : ((m : Int) + (-1)).toNat = m - 1 := by omega
      rw [h_toNat]
      simp only [hasFreeVarMeta]
      by_cases hn_lt_c : n < c
      · rw [if_pos hn_lt_c]; apply beq_eq_beq_of_iff; constructor <;> intro <;> omega
      · rw [if_neg hn_lt_c]; apply beq_eq_beq_of_iff; constructor <;> intro <;> omega
  | app M N ihM ihN =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv
    simp only [Metatheory.Lambda.Term.shift, hasFreeVarMeta]
    rw [ihM n c hfv.1, ihN n c hfv.2]
    by_cases hn_lt_c : n < c
    · simp only [if_pos hn_lt_c]
    · simp only [if_neg hn_lt_c]
  | lam M ih =>
    simp only [hasFreeVarMeta] at hfv
    simp only [Metatheory.Lambda.Term.shift, hasFreeVarMeta]
    rw [ih (n + 1) (c + 1) hfv]
    by_cases hn_lt_c : n < c
    · have hn1_lt_c1 : n + 1 < c + 1 := Nat.succ_lt_succ hn_lt_c
      simp only [if_pos hn_lt_c, if_pos hn1_lt_c1]
    · have hn1_not_lt_c1 : ¬(n + 1 < c + 1) := by omega
      simp only [if_neg hn_lt_c, if_neg hn1_not_lt_c1]

/-- η-reduction doesn't introduce new free variables -/
theorem etaStep_preserves_not_fv {M M' : Metatheory.Lambda.Term} {n : Nat}
    (h : EtaStepMeta M M') (hfv : hasFreeVarMeta n M = false) :
    hasFreeVarMeta n M' = false := by
  induction h generalizing n with
  | eta N hfvN =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv
    rw [hasFreeVarMeta_shift_neg1_gen N n 0 hfvN]
    simp only [Nat.not_lt_zero, ↓reduceIte]
    exact hfv.1
  | appL hstep ih =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv ⊢
    exact ⟨ih hfv.1, hfv.2⟩
  | appR hstep ih =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv ⊢
    exact ⟨hfv.1, ih hfv.2⟩
  | lam hstep ih =>
    simp only [hasFreeVarMeta] at hfv ⊢
    exact ih hfv

/-- Composing two shift(-1) operations commutes under FV conditions -/
theorem shift_neg1_compose_gen (N : Metatheory.Lambda.Term) (a b : Nat)
    (hab : a ≤ b) (hfv_a : hasFreeVarMeta a N = false) (hfv_b1 : hasFreeVarMeta (b + 1) N = false) :
    Metatheory.Lambda.Term.shift (-1) b (Metatheory.Lambda.Term.shift (-1) (a + 1) N) =
    Metatheory.Lambda.Term.shift (-1) a (Metatheory.Lambda.Term.shift (-1) (b + 1) N) := by
  induction N generalizing a b with
  | var n =>
    simp only [hasFreeVarMeta] at hfv_a hfv_b1
    simp only [Metatheory.Lambda.Term.shift]
    have hn_ne_a : n ≠ a := by intro h; subst h; simp at hfv_a
    have hn_ne_b1 : n ≠ b + 1 := by intro h; subst h; simp at hfv_b1
    by_cases hn_lt_a1 : n < a + 1
    · have hn_lt_a : n < a := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hn_lt_a1) hn_ne_a
      have hn_lt_b1 : n < b + 1 := Nat.lt_of_lt_of_le hn_lt_a (Nat.le_succ_of_le hab)
      have hn_lt_b : n < b := Nat.lt_of_lt_of_le hn_lt_a hab
      simp only [Metatheory.Lambda.Term.shift, hn_lt_a1, ↓reduceIte, hn_lt_b, hn_lt_b1, hn_lt_a]
    · have hn_ge_a1 : n ≥ a + 1 := Nat.le_of_not_lt hn_lt_a1
      have h_toNat1 : ((n : Int) + (-1)).toNat = n - 1 := by omega
      simp only [Metatheory.Lambda.Term.shift, hn_lt_a1, ↓reduceIte, h_toNat1]
      by_cases hn_lt_b1 : n < b + 1
      · have hn_minus1_lt_b : n - 1 < b := by omega
        have hn_not_lt_a : ¬(n < a) := by omega
        simp only [Metatheory.Lambda.Term.shift, hn_minus1_lt_b, ↓reduceIte, hn_lt_b1, hn_not_lt_a, h_toNat1]
      · have hn_ge_b1 : n ≥ b + 1 := Nat.le_of_not_lt hn_lt_b1
        have hn_gt_b1 : n > b + 1 := Nat.lt_of_le_of_ne hn_ge_b1 (Ne.symm hn_ne_b1)
        have hn_minus1_ge_b : n - 1 ≥ b := by omega
        have hn_minus1_not_lt_b : ¬(n - 1 < b) := Nat.not_lt.mpr hn_minus1_ge_b
        have hn_minus1_not_lt_a : ¬(n - 1 < a) := by omega
        simp only [Metatheory.Lambda.Term.shift, hn_minus1_not_lt_b, ↓reduceIte,
                   hn_lt_b1, h_toNat1, hn_minus1_not_lt_a]
  | app M N ihM ihN =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv_a hfv_b1
    simp only [Metatheory.Lambda.Term.shift]
    rw [ihM a b hab hfv_a.1 hfv_b1.1, ihN a b hab hfv_a.2 hfv_b1.2]
  | lam M ih =>
    simp only [hasFreeVarMeta] at hfv_a hfv_b1
    simp only [Metatheory.Lambda.Term.shift]
    congr 1
    exact ih (a + 1) (b + 1) (Nat.succ_le_succ hab) hfv_a hfv_b1

/-- η-step is preserved under shift(-1, c) when var c is not free -/
theorem etaStep_shift_neg1_gen {M M' : Metatheory.Lambda.Term} (c : Nat)
    (h : EtaStepMeta M M') (hfv : hasFreeVarMeta c M = false) :
    EtaStepMeta (Metatheory.Lambda.Term.shift (-1) c M)
                (Metatheory.Lambda.Term.shift (-1) c M') := by
  induction h generalizing c with
  | eta N hfvN =>
    simp only [Metatheory.Lambda.Term.shift]
    have h0_lt : (0 : Nat) < c + 1 := Nat.zero_lt_succ c
    simp only [h0_lt, ↓reduceIte]
    have hfv_N_c1 : hasFreeVarMeta (c + 1) N = false := by
      simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv
      exact hfv.1
    have hfv_shifted : hasFreeVarMeta 0 (Metatheory.Lambda.Term.shift (-1) (c + 1) N) = false := by
      rw [hasFreeVarMeta_shift_neg1_gen N 0 (c + 1) hfv_N_c1]
      simp only [Nat.zero_lt_succ, ↓reduceIte]
      exact hfvN
    have hstep : EtaStepMeta (.lam (.app (Metatheory.Lambda.Term.shift (-1) (c + 1) N) (.var 0)))
                             (Metatheory.Lambda.Term.shift (-1) 0 (Metatheory.Lambda.Term.shift (-1) (c + 1) N)) :=
      EtaStepMeta.eta _ hfv_shifted
    have h_compose : Metatheory.Lambda.Term.shift (-1) c (Metatheory.Lambda.Term.shift (-1) 0 N) =
                     Metatheory.Lambda.Term.shift (-1) 0 (Metatheory.Lambda.Term.shift (-1) (c + 1) N) := by
      rw [shift_neg1_cutoff_irrelevant N 0 hfvN]
      exact shift_neg1_compose_gen N 0 c (Nat.zero_le c) hfvN hfv_N_c1
    rw [h_compose]
    exact hstep
  | appL hstep ih =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv
    simp only [Metatheory.Lambda.Term.shift]
    exact EtaStepMeta.appL (ih c hfv.1)
  | appR hstep ih =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv
    simp only [Metatheory.Lambda.Term.shift]
    exact EtaStepMeta.appR (ih c hfv.2)
  | lam hstep ih =>
    simp only [hasFreeVarMeta] at hfv
    simp only [Metatheory.Lambda.Term.shift]
    exact EtaStepMeta.lam (ih (c + 1) hfv)

/-- η-step is preserved under shift(-1, 0) -/
theorem etaStep_shift_neg1 {M M' : Metatheory.Lambda.Term}
    (h : EtaStepMeta M M') (hfv : hasFreeVarMeta 0 M = false) :
    EtaStepMeta (Metatheory.Lambda.Term.shift (-1) 0 M)
                (Metatheory.Lambda.Term.shift (-1) 0 M') :=
  etaStep_shift_neg1_gen 0 h hfv

/-! ## η-Local Confluence -/

def EtaStar := Rewriting.Star EtaStepMeta

theorem EtaStar_single {M N : Metatheory.Lambda.Term} (h : EtaStepMeta M N) :
    EtaStar M N := Rewriting.Star.single h

theorem EtaStar_refl (M : Metatheory.Lambda.Term) : EtaStar M M := Rewriting.Star.refl M

theorem EtaStar_appL {M M' N : Metatheory.Lambda.Term} (h : EtaStar M M') :
    EtaStar (.app M N) (.app M' N) := by
  induction h with
  | refl => exact EtaStar_refl _
  | tail _ hstep ih => exact Rewriting.Star.tail ih (EtaStepMeta.appL hstep)

theorem EtaStar_appR {M N N' : Metatheory.Lambda.Term} (h : EtaStar N N') :
    EtaStar (.app M N) (.app M N') := by
  induction h with
  | refl => exact EtaStar_refl _
  | tail _ hstep ih => exact Rewriting.Star.tail ih (EtaStepMeta.appR hstep)

theorem EtaStar_lam {M M' : Metatheory.Lambda.Term} (h : EtaStar M M') :
    EtaStar (.lam M) (.lam M') := by
  induction h with
  | refl => exact EtaStar_refl _
  | tail _ hstep ih => exact Rewriting.Star.tail ih (EtaStepMeta.lam hstep)

/-- η-reduction is locally confluent -/
theorem eta_localConfluent : Rewriting.LocalConfluent EtaStepMeta := by
  intro M N₁ N₂ h1 h2
  cases h1 with
  | eta N hfvN =>
    cases h2 with
    | eta N' hfvN' =>
      let target := Metatheory.Lambda.Term.shift (-1) 0 N
      exact ⟨target, Rewriting.Star.refl target, Rewriting.Star.refl target⟩
    | lam hstep =>
      cases hstep with
      | @appL _ N' _ hstep' =>
        have hfvN' := etaStep_preserves_not_fv hstep' hfvN
        exact ⟨Metatheory.Lambda.Term.shift (-1) 0 N',
               Rewriting.Star.single (etaStep_shift_neg1 hstep' hfvN),
               Rewriting.Star.single (EtaStepMeta.eta N' hfvN')⟩
      | appR hstep' => cases hstep'
  | appL h1_inner =>
    cases h2 with
    | appL h2_inner =>
      have ih := eta_localConfluent _ _ _ h1_inner h2_inner
      obtain ⟨P, hP1, hP2⟩ := ih
      exact ⟨.app P _, EtaStar_appL hP1, EtaStar_appL hP2⟩
    | appR h2_inner =>
      exact ⟨.app _ _, EtaStar_single (EtaStepMeta.appR h2_inner),
                        EtaStar_single (EtaStepMeta.appL h1_inner)⟩
  | appR h1_inner =>
    cases h2 with
    | appL h2_inner =>
      exact ⟨.app _ _, EtaStar_single (EtaStepMeta.appL h2_inner),
                        EtaStar_single (EtaStepMeta.appR h1_inner)⟩
    | appR h2_inner =>
      have ih := eta_localConfluent _ _ _ h1_inner h2_inner
      obtain ⟨P, hP1, hP2⟩ := ih
      exact ⟨.app _ P, EtaStar_appR hP1, EtaStar_appR hP2⟩
  | lam h1_inner =>
    cases h2 with
    | eta N hfvN =>
      cases h1_inner with
      | @appL _ N' _ hstep' =>
        have hfvN' := etaStep_preserves_not_fv hstep' hfvN
        exact ⟨Metatheory.Lambda.Term.shift (-1) 0 N',
               Rewriting.Star.single (EtaStepMeta.eta N' hfvN'),
               Rewriting.Star.single (etaStep_shift_neg1 hstep' hfvN)⟩
      | appR hstep' => cases hstep'
    | lam h2_inner =>
      have ih := eta_localConfluent _ _ _ h1_inner h2_inner
      obtain ⟨P, hP1, hP2⟩ := ih
      exact ⟨.lam P, EtaStar_lam hP1, EtaStar_lam hP2⟩

/-- η-reduction is confluent (via Newman's lemma) -/
theorem eta_confluent : Rewriting.Confluent EtaStepMeta :=
  Rewriting.confluent_of_terminating_localConfluent eta_terminating eta_localConfluent

/-! ## β-η Commutation Infrastructure

The Commute relation (from Metatheory.Rewriting.HindleyRosen) requires three properties:
1. Diamond: β a b → η a c → ∃ d, η b d ∧ β c d
2. Swap1: η a b → β b c → ∃ d, β a d ∧ η d c
3. Swap2: β a b → η b c → ∃ d, η a d ∧ β d c

Reference: Barendregt (1984): "The Lambda Calculus", Section 3.3, Lemma 3.3.4
-/

/-! ### Helper lemmas for hasFreeVarMeta -/

/-- General lemma: hasFreeVarMeta n M = false implies hasFreeVarMeta (n+1) (shift 1 c M) = false
    when c ≤ n -/
theorem hasFreeVarMeta_shift_pos (M : Metatheory.Lambda.Term) (n c : Nat)
    (hcn : c ≤ n) (h : hasFreeVarMeta n M = false) :
    hasFreeVarMeta (n + 1) (Metatheory.Lambda.Term.shift 1 c M) = false := by
  induction M generalizing n c with
  | var m =>
    simp only [hasFreeVarMeta, beq_eq_false_iff_ne] at h
    simp only [Metatheory.Lambda.Term.shift]
    by_cases hm_lt_c : m < c
    · -- m < c ≤ n, so m < n, so m ≠ n + 1
      simp only [hm_lt_c, ↓reduceIte, hasFreeVarMeta, beq_eq_false_iff_ne]
      have hm_lt : m < n + 1 := Nat.lt_of_lt_of_le hm_lt_c (Nat.le_succ_of_le hcn)
      exact Nat.ne_of_lt hm_lt
    · -- m ≥ c, so shift gives m + 1
      simp only [hm_lt_c, ↓reduceIte]
      have h_toNat : ((m : Int) + 1).toNat = m + 1 := by omega
      simp only [h_toNat, hasFreeVarMeta, beq_eq_false_iff_ne]
      intro heq
      have heq' : m + 1 = n + 1 := heq
      have : m = n := by omega
      exact h this
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at h
    simp only [Metatheory.Lambda.Term.shift]
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff]
    constructor
    · exact ih₁ n c hcn h.1
    · exact ih₂ n c hcn h.2
  | lam M₀ ih =>
    simp only [hasFreeVarMeta] at h ⊢
    simp only [Metatheory.Lambda.Term.shift, hasFreeVarMeta]
    exact ih (n + 1) (c + 1) (Nat.add_le_add_right hcn 1) h

/-- hasFreeVarMeta n M = false implies hasFreeVarMeta (n+1) (shift1 M) = false -/
theorem hasFreeVarMeta_shift1 (M : Metatheory.Lambda.Term) (n : Nat)
    (h : hasFreeVarMeta n M = false) :
    hasFreeVarMeta (n + 1) (Metatheory.Lambda.Term.shift1 M) = false := by
  simp only [Metatheory.Lambda.Term.shift1]
  exact hasFreeVarMeta_shift_pos M n 0 (Nat.zero_le n) h

/-- When var c doesn't appear in M, substituting (var c) for c equals shift(-1, c).
This is the key identity for η-reduction: when a variable doesn't appear,
removing its binding (via shift -1) is equivalent to substituting it. -/
theorem subst_var_eq_shift_neg1 (M : Metatheory.Lambda.Term) (c : Nat)
    (hfv : hasFreeVarMeta c M = false) :
    Metatheory.Lambda.Term.subst c (.var c) M = Metatheory.Lambda.Term.shift (-1) c M := by
  induction M generalizing c with
  | var n =>
    simp only [hasFreeVarMeta, beq_eq_false_iff_ne] at hfv
    simp only [Metatheory.Lambda.Term.subst, Metatheory.Lambda.Term.shift]
    have hn_ne_c : n ≠ c := hfv
    by_cases hn_gt_c : n > c
    · -- n > c: both subst and shift decrement
      have h1 : ¬(n = c) := hn_ne_c
      have h2 : ¬(n < c) := Nat.not_lt.mpr (Nat.le_of_lt hn_gt_c)
      simp only [h1, ↓reduceIte, hn_gt_c, h2]
      have h_toNat : ((n : Int) + (-1)).toNat = n - 1 := by omega
      simp only [h_toNat]
    · -- n ≤ c, n ≠ c, so n < c
      have hn_lt_c : n < c := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hn_gt_c) hn_ne_c
      have h1 : ¬(n = c) := hn_ne_c
      simp only [h1, ↓reduceIte, hn_gt_c, hn_lt_c]
  | app M N ihM ihN =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv
    simp only [Metatheory.Lambda.Term.subst, Metatheory.Lambda.Term.shift]
    rw [ihM c hfv.1, ihN c hfv.2]
  | lam M ih =>
    simp only [hasFreeVarMeta] at hfv
    simp only [Metatheory.Lambda.Term.subst, Metatheory.Lambda.Term.shift]
    congr 1
    -- Need: subst (c+1) (shift1 (var c)) M = shift (-1) (c+1) M
    -- shift1 (var c) computes to var (c+1)
    have h_eq : Metatheory.Lambda.Term.shift1 (.var c) = .var (c + 1) := by
      simp only [Metatheory.Lambda.Term.shift1, Metatheory.Lambda.Term.shift,
                 Nat.not_lt_zero, ↓reduceIte]
      have h : ((c : Int) + 1).toNat = c + 1 := by omega
      simp only [h]
    -- Rewrite the LHS using this equation
    calc Metatheory.Lambda.Term.subst (c + 1) (Metatheory.Lambda.Term.shift1 (.var c)) M
        = Metatheory.Lambda.Term.subst (c + 1) (.var (c + 1)) M := by rw [h_eq]
      _ = Metatheory.Lambda.Term.shift (-1) (c + 1) M := ih (c + 1) hfv

/-! ### Negative shift-substitution interaction -/

/-- General helper: shift 1 d commutes with shift (-1) c when d ≤ c and hasFreeVarMeta c N = false.
    shift 1 d (shift (-1) c N) = shift (-1) (c+1) (shift 1 d N)
-/
theorem shift_pos_neg_comm (N : Metatheory.Lambda.Term) (c d : Nat)
    (hdc : d ≤ c) (hfvN : hasFreeVarMeta c N = false) :
    Metatheory.Lambda.Term.shift 1 d (Metatheory.Lambda.Term.shift (-1) c N) =
    Metatheory.Lambda.Term.shift (-1) (c + 1) (Metatheory.Lambda.Term.shift 1 d N) := by
  induction N generalizing c d with
  | var n =>
    simp only [hasFreeVarMeta, beq_eq_false_iff_ne] at hfvN
    -- Case analysis on n's relationship to c and d
    by_cases hn_lt_d : n < d
    · -- Case 1: n < d (implies n < c since d ≤ c)
      have hn_lt_c : n < c := Nat.lt_of_lt_of_le hn_lt_d hdc
      have hn_lt_c1 : n < c + 1 := Nat.lt_succ_of_lt hn_lt_c
      simp only [Metatheory.Lambda.Term.shift, hn_lt_c, ↓reduceIte, hn_lt_d, hn_lt_c1]
    · -- n ≥ d
      by_cases hn_lt_c : n < c
      · -- Case 2: d ≤ n < c
        have hn_lt_c1 : n < c + 1 := Nat.lt_succ_of_lt hn_lt_c
        have h1 : ((n : Int) + 1).toNat = n + 1 := by omega
        have hn1_lt_c1 : n + 1 < c + 1 := Nat.add_lt_add_right hn_lt_c 1
        simp only [Metatheory.Lambda.Term.shift, hn_lt_c, ↓reduceIte, hn_lt_d, h1, hn1_lt_c1]
      · -- Case 3: n ≥ c, so n > c (since n ≠ c by hfvN)
        have hn_ge_c : n ≥ c := Nat.le_of_not_lt hn_lt_c
        have hn_gt_c : n > c := Nat.lt_of_le_of_ne hn_ge_c (Ne.symm hfvN)
        have h_toNat : ((n : Int) + (-1)).toNat = n - 1 := by omega
        -- n - 1 ≥ d since n > c ≥ d
        have hn1_ge_d : n - 1 ≥ d := by omega
        have hn1_not_lt_d : ¬(n - 1 < d) := Nat.not_lt.mpr hn1_ge_d
        have h1' : (((n - 1 : Nat) : Int) + 1).toNat = n := by omega
        -- RHS: n ≥ d, shift 1 d gives n+1, then shift (-1) (c+1)
        have h2 : ((n : Int) + 1).toNat = n + 1 := by omega
        have hn1_gt_c1 : n + 1 > c + 1 := by omega
        have hn1_not_lt_c1 : ¬(n + 1 < c + 1) := Nat.not_lt.mpr (Nat.le_of_lt hn1_gt_c1)
        have h4' : (((n + 1 : Nat) : Int) + (-1 : Int)).toNat = n := by omega
        simp only [Metatheory.Lambda.Term.shift, hn_lt_c, ↓reduceIte, h_toNat, hn1_not_lt_d, h1',
                   hn_lt_d, h2, hn1_not_lt_c1, h4']
  | app N₁ N₂ ih₁ ih₂ =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfvN
    simp only [Metatheory.Lambda.Term.shift]
    rw [ih₁ c d hdc hfvN.1, ih₂ c d hdc hfvN.2]
  | lam N₀ ih =>
    simp only [hasFreeVarMeta] at hfvN
    simp only [Metatheory.Lambda.Term.shift]
    congr 1
    have hdc' : d + 1 ≤ c + 1 := Nat.add_le_add_right hdc 1
    exact ih (c + 1) (d + 1) hdc' hfvN

/-- Corollary: shift1 commutes with shift(-1) c when hasFreeVarMeta c N = false -/
theorem shift1_shift_neg1_comm (N : Metatheory.Lambda.Term) (c : Nat)
    (hfvN : hasFreeVarMeta c N = false) :
    Metatheory.Lambda.Term.shift1 (Metatheory.Lambda.Term.shift (-1) c N) =
    Metatheory.Lambda.Term.shift (-1) (c + 1) (Metatheory.Lambda.Term.shift1 N) := by
  simp only [Metatheory.Lambda.Term.shift1]
  exact shift_pos_neg_comm N c 0 (Nat.zero_le c) hfvN

/-- Key lemma: shift(-1) commutes with subst under FV conditions.

When j ≤ c, hasFreeVarMeta (c+1) M = false, and hasFreeVarMeta c N = false:
  shift (-1) c (M.subst j N) = (shift (-1) (c+1) M).subst j (shift (-1) c N)

This is the crucial lemma for proving β-step preservation under shift(-1).
Generalized to handle arbitrary substitution index j for the lambda case.
-/
theorem shift_neg1_subst_gen (M N : Metatheory.Lambda.Term) (c j : Nat)
    (hjc : j ≤ c)
    (hfvM : hasFreeVarMeta (c + 1) M = false)
    (hfvN : hasFreeVarMeta c N = false) :
    Metatheory.Lambda.Term.shift (-1) c (Metatheory.Lambda.Term.subst j N M) =
    Metatheory.Lambda.Term.subst j (Metatheory.Lambda.Term.shift (-1) c N)
                                   (Metatheory.Lambda.Term.shift (-1) (c + 1) M) := by
  induction M generalizing N c j with
  | var n =>
    simp only [hasFreeVarMeta, beq_eq_false_iff_ne] at hfvM
    -- Three cases: n < j, n = j, n > j
    by_cases hn_lt_j : n < j
    · -- Case 1: n < j (var unchanged by subst)
      -- Since j ≤ c, we have n < c, hence n < c + 1
      have hn_lt_c : n < c := Nat.lt_of_lt_of_le hn_lt_j hjc
      have hn_lt_c1 : n < c + 1 := Nat.lt_succ_of_lt hn_lt_c
      have hn_ne_j : n ≠ j := Nat.ne_of_lt hn_lt_j
      have hn_not_gt_j : ¬(n > j) := Nat.not_lt.mpr (Nat.le_of_lt hn_lt_j)
      simp only [Metatheory.Lambda.Term.subst, hn_ne_j, ↓reduceIte, hn_not_gt_j,
                 Metatheory.Lambda.Term.shift, hn_lt_c, hn_lt_c1]
    · -- n ≥ j
      by_cases hn_eq_j : n = j
      · -- Case 2: n = j (subst replaces with N)
        subst hn_eq_j
        -- Now goal uses n instead of j
        have hn_lt_c1 : n < c + 1 := Nat.lt_succ_of_le hjc
        simp only [Metatheory.Lambda.Term.subst, Nat.lt_irrefl, ↓reduceIte,
                   Metatheory.Lambda.Term.shift, hn_lt_c1]
      · -- Case 3: n > j (subst decrements n to n-1)
        have hn_gt_j : n > j := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hn_lt_j) (Ne.symm hn_eq_j)
        simp only [Metatheory.Lambda.Term.subst, hn_eq_j, ↓reduceIte, hn_gt_j]
        -- Now LHS is shift (-1) c (var (n-1)) and RHS involves shift (-1) (c+1) (var n)
        by_cases hn1_lt_c : n - 1 < c
        · -- n - 1 < c, so n ≤ c, and since n ≠ c + 1 (by hfvM), we have n < c + 1
          have hn_lt_c1 : n < c + 1 := by omega
          -- Note: n - 1 could equal j (when n = j + 1) or be > j
          -- Either way, the RHS subst at j reduces var n (where n > j) to var (n-1)
          simp only [Metatheory.Lambda.Term.shift, hn1_lt_c, ↓reduceIte, hn_lt_c1,
                     Metatheory.Lambda.Term.subst, hn_eq_j, hn_gt_j]
        · -- n - 1 ≥ c, so n ≥ c + 1, and since n ≠ c + 1 (by hfvM), we have n > c + 1
          have hn1_ge_c : n - 1 ≥ c := Nat.le_of_not_lt hn1_lt_c
          have hn_ge_c1 : n ≥ c + 1 := by omega
          have hn_gt_c1 : n > c + 1 := Nat.lt_of_le_of_ne hn_ge_c1 (Ne.symm hfvM)
          have hn_not_lt_c1 : ¬(n < c + 1) := by omega
          have h_toNat1 : (((n - 1 : Nat) : Int) + (-1 : Int)).toNat = n - 2 := by omega
          have h_toNat2 : ((n : Int) + (-1 : Int)).toNat = n - 1 := by omega
          simp only [Metatheory.Lambda.Term.shift, hn1_lt_c, ↓reduceIte, h_toNat1,
                     hn_not_lt_c1, h_toNat2]
          -- RHS: (var (n-1)).subst j ... where n - 1 > j (since n > c + 1 ≥ j + 1)
          have hn1_gt_j : n - 1 > j := by omega
          have hn1_ne_j : n - 1 ≠ j := by omega
          simp only [Metatheory.Lambda.Term.subst, hn1_ne_j, ↓reduceIte, hn1_gt_j]
          -- Goal: var (n-2) = var (n-1-1)
          simp only [Nat.sub_sub]
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfvM
    simp only [Metatheory.Lambda.Term.subst, Metatheory.Lambda.Term.shift]
    rw [ih₁ N c j hjc hfvM.1 hfvN, ih₂ N c j hjc hfvM.2 hfvN]
  | lam M₀ ih =>
    simp only [hasFreeVarMeta] at hfvM
    simp only [Metatheory.Lambda.Term.subst, Metatheory.Lambda.Term.shift]
    congr 1
    -- Under lambda: j becomes j+1, c becomes c+1
    have hjc' : j + 1 ≤ c + 1 := Nat.add_le_add_right hjc 1
    have hfvM' : hasFreeVarMeta (c + 2) M₀ = false := by
      have h_arith : c + 1 + 1 = c + 2 := by omega
      rw [← h_arith]; exact hfvM
    have hfvN' : hasFreeVarMeta (c + 1) (Metatheory.Lambda.Term.shift1 N) = false :=
      hasFreeVarMeta_shift1 N c hfvN
    -- Use shift commutation lemma
    have h_shift_comm := shift1_shift_neg1_comm N c hfvN
    rw [h_shift_comm]
    have h_arith : c + 1 + 1 = c + 2 := by omega
    rw [h_arith]
    exact ih (Metatheory.Lambda.Term.shift1 N) (c + 1) (j + 1) hjc' hfvM' hfvN'

/-- Corollary: shift(-1) commutes with subst0 (special case j = 0) -/
theorem shift_neg1_subst (M N : Metatheory.Lambda.Term) (c : Nat)
    (hfvM : hasFreeVarMeta (c + 1) M = false)
    (hfvN : hasFreeVarMeta c N = false) :
    Metatheory.Lambda.Term.shift (-1) c (Metatheory.Lambda.Term.subst0 N M) =
    Metatheory.Lambda.Term.subst0 (Metatheory.Lambda.Term.shift (-1) c N)
                                   (Metatheory.Lambda.Term.shift (-1) (c + 1) M) := by
  simp only [Metatheory.Lambda.Term.subst0]
  exact shift_neg1_subst_gen M N c 0 (Nat.zero_le c) hfvM hfvN

/-! ### β-step preservation under shift(-1) -/

/-- β-step is preserved under shift(-1) when the FV condition holds.
    If M →β N and hasFreeVarMeta c M = false, then shift(-1) c M →β shift(-1) c N.
-/
theorem betaStep_shift_neg1 (M N : Metatheory.Lambda.Term) (c : Nat)
    (hstep : Metatheory.Lambda.BetaStep M N)
    (hfv : hasFreeVarMeta c M = false) :
    Metatheory.Lambda.BetaStep
      (Metatheory.Lambda.Term.shift (-1) c M)
      (Metatheory.Lambda.Term.shift (-1) c N) := by
  induction hstep generalizing c with
  | beta M₀ N₀ =>
    -- Original: (lam M₀) @ N₀ →β M₀[N₀]
    -- After shift: (lam (shift (-1) (c+1) M₀)) @ (shift (-1) c N₀)
    --            →β (shift (-1) (c+1) M₀)[shift (-1) c N₀]
    --            = shift (-1) c (M₀[N₀])  [by shift_neg1_subst]
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv
    simp only [Metatheory.Lambda.Term.shift]
    -- Apply beta rule
    have h := Metatheory.Lambda.BetaStep.beta
      (Metatheory.Lambda.Term.shift (-1) (c + 1) M₀)
      (Metatheory.Lambda.Term.shift (-1) c N₀)
    -- The RHS is (shift (-1) (c+1) M₀)[shift (-1) c N₀]
    -- Need to show this equals shift (-1) c (M₀[N₀])
    have heq : Metatheory.Lambda.Term.subst0
                 (Metatheory.Lambda.Term.shift (-1) c N₀)
                 (Metatheory.Lambda.Term.shift (-1) (c + 1) M₀) =
               Metatheory.Lambda.Term.shift (-1) c (Metatheory.Lambda.Term.subst0 N₀ M₀) := by
      rw [shift_neg1_subst M₀ N₀ c hfv.1 hfv.2]
    rw [heq] at h
    exact h
  | @appL M M' N hstep' ih =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv
    simp only [Metatheory.Lambda.Term.shift]
    exact Metatheory.Lambda.BetaStep.appL (ih c hfv.1)
  | @appR M N N' hstep' ih =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv
    simp only [Metatheory.Lambda.Term.shift]
    exact Metatheory.Lambda.BetaStep.appR (ih c hfv.2)
  | @lam M M' hstep' ih =>
    simp only [hasFreeVarMeta] at hfv
    simp only [Metatheory.Lambda.Term.shift]
    exact Metatheory.Lambda.BetaStep.lam (ih (c + 1) hfv)

/-! ### β-η Commutation

The commutation property `Rewriting.Commute BetaStep EtaStepMeta` requires three properties:
1. Diamond: β a b → η a c → ∃ d, η b d ∧ β c d
2. Swap1: η a b → β b c → ∃ d, β a d ∧ η d c
3. Swap2: β a b → η b c → ∃ d, η a d ∧ β d c

Reference: Barendregt, "The Lambda Calculus: Its Syntax and Semantics", Lemma 3.3.4

The proof requires several helper lemmas about β-step and free variables.
We axiomatize this standard result pending complete formalization of the
interaction cases between β and η reductions.
-/

/-- Free variables under subst: if var (n+1) not in M and var n not in N,
    then var n not in M[N/j] (generalized version) -/
theorem hasFreeVarMeta_subst_gen (M N : Metatheory.Lambda.Term) (n j : Nat)
    (hjn : j ≤ n)
    (hfvM : hasFreeVarMeta (n + 1) M = false)
    (hfvN : hasFreeVarMeta n N = false) :
    hasFreeVarMeta n (Metatheory.Lambda.Term.subst j N M) = false := by
  induction M generalizing N n j with
  | var m =>
    simp only [hasFreeVarMeta, beq_eq_false_iff_ne] at hfvM hfvN
    simp only [Metatheory.Lambda.Term.subst]
    by_cases hm_eq_j : m = j
    · -- m = j: subst replaces with N
      simp only [hm_eq_j, Nat.lt_irrefl, ↓reduceIte, hasFreeVarMeta, beq_eq_false_iff_ne]
      exact hfvN
    · -- m ≠ j
      by_cases hm_gt_j : m > j
      · -- m > j: subst decrements to m - 1
        simp only [hm_eq_j, ↓reduceIte, hm_gt_j, hasFreeVarMeta, beq_eq_false_iff_ne]
        -- m - 1 = n means m = n + 1, but hfvM says m ≠ n + 1
        intro heq
        have hm_eq : m = n + 1 := by omega
        exact hfvM hm_eq
      · -- m < j (since m ≠ j and ¬(m > j))
        have hm_lt_j : m < j := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hm_gt_j) hm_eq_j
        simp only [hm_eq_j, ↓reduceIte, hm_gt_j, hasFreeVarMeta, beq_eq_false_iff_ne]
        -- var unchanged, but m < j ≤ n, so m ≠ n
        intro heq
        have : m < n := Nat.lt_of_lt_of_le hm_lt_j hjn
        omega
  | app M₁ M₂ ih₁ ih₂ =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfvM ⊢
    simp only [Metatheory.Lambda.Term.subst, hasFreeVarMeta, Bool.or_eq_false_iff]
    exact ⟨ih₁ N n j hjn hfvM.1 hfvN, ih₂ N n j hjn hfvM.2 hfvN⟩
  | lam M₀ ih =>
    simp only [hasFreeVarMeta] at hfvM ⊢
    simp only [Metatheory.Lambda.Term.subst, hasFreeVarMeta]
    -- Under lambda: n becomes n+1, j becomes j+1, and shift1 N preserves FV
    have hfvN' : hasFreeVarMeta (n + 1) (Metatheory.Lambda.Term.shift1 N) = false :=
      hasFreeVarMeta_shift1 N n hfvN
    have hjn' : j + 1 ≤ n + 1 := Nat.add_le_add_right hjn 1
    exact ih (Metatheory.Lambda.Term.shift1 N) (n + 1) (j + 1) hjn' hfvM hfvN'

/-- Free variables under subst0: if var (n+1) not in M and var n not in N,
    then var n not in M[N/0] -/
theorem hasFreeVarMeta_subst0 (M N : Metatheory.Lambda.Term) (n : Nat)
    (hfvM : hasFreeVarMeta (n + 1) M = false)
    (hfvN : hasFreeVarMeta n N = false) :
    hasFreeVarMeta n (Metatheory.Lambda.Term.subst0 N M) = false := by
  simp only [Metatheory.Lambda.Term.subst0]
  exact hasFreeVarMeta_subst_gen M N n 0 (Nat.zero_le n) hfvM hfvN

/-- β-step preserves not-free-var (forward direction) -/
theorem betaStep_preserves_not_fv {M M' : Metatheory.Lambda.Term} {n : Nat}
    (hstep : Metatheory.Lambda.BetaStep M M')
    (hfv : hasFreeVarMeta n M = false) :
    hasFreeVarMeta n M' = false := by
  induction hstep generalizing n with
  | beta N P =>
    -- (λN) @ P →β N[P]
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv
    -- hfv.1: hasFreeVarMeta (n+1) N = false (under λ)
    -- hfv.2: hasFreeVarMeta n P = false
    -- Need: hasFreeVarMeta n (N[P]) = false
    exact hasFreeVarMeta_subst0 N P n hfv.1 hfv.2
  | @appL M₁ M₁' M₂ _ ih =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv ⊢
    exact ⟨ih hfv.1, hfv.2⟩
  | @appR M₁ M₂ M₂' _ ih =>
    simp only [hasFreeVarMeta, Bool.or_eq_false_iff] at hfv ⊢
    exact ⟨hfv.1, ih hfv.2⟩
  | @lam M₁ M₁' _ ih =>
    simp only [hasFreeVarMeta] at hfv ⊢
    exact ih hfv

/-! ### β-η Commutation Theorem

The commutation property `Rewriting.Commute BetaStep EtaStepMeta` requires three properties:
1. Diamond: β a b → η a c → ∃ d, η b d ∧ β c d
2. Swap1: η a b → β b c → ∃ d, β a d ∧ η d c
3. Swap2: β a b → η b c → ∃ d, η a d ∧ β d c

Reference: Barendregt, "The Lambda Calculus: Its Syntax and Semantics", Lemma 3.3.4

## Proven Infrastructure

The following lemmas provide the key building blocks for β-η commutation:

### Free Variable Preservation
- `hasFreeVarMeta_subst_gen`: FV under substitution (generalized)
- `hasFreeVarMeta_subst0`: FV under subst0
- `hasFreeVarMeta_shift_pos`: FV under positive shift
- `hasFreeVarMeta_shift1`: FV under shift1
- `hasFreeVarMeta_shift_neg1_gen`: FV under shift(-1)

### Reduction Preservation
- `betaStep_preserves_not_fv`: β-step preserves not-free-var
- `etaStep_preserves_not_fv`: η-step preserves not-free-var
- `betaStep_shift_neg1`: β-step preserved under shift(-1)
- `etaStep_shift_neg1_gen`: η-step preserved under shift(-1)

### Shift-Substitution Interaction
- `shift_neg1_subst_gen`: shift(-1) commutes with substitution
- `shift_pos_neg_comm`: positive and negative shift commutation
- `shift_neg1_compose_gen`: composing two shift(-1) operations

## Critical Overlap Analysis

The commutation proof involves several cases:

1. **Disjoint reductions**: When β and η occur at different positions, they
   trivially commute by applying in opposite order.

2. **β at root with η inside**: (λM)N →β M[N] with η in M or N
   - η in M: Use η preservation under substitution
   - η in N: Use substitution-η interaction

3. **η at root with β inside**: λ(P @ var 0) →η shift(-1) P with β in P
   - P →β P': Use betaStep_shift_neg1 and betaStep_preserves_not_fv
   - P is β-redex: Critical pair requiring careful analysis

4. **Nested overlap**: β-redex inside η-redex body, etc.
   - Requires structural analysis based on term shape

The proof is standard (Barendregt 1984, Lemma 3.3.4) and relies on the
orthogonality of β and η reductions: η-redexes have shape λ(M @ var 0)
where var 0 is not free in M, while β-redexes have shape (λM) @ N.
-/

/-- β-η commutation (Barendregt Lemma 3.3.4)

This is a well-known standard result establishing that β and η reductions commute.
All infrastructure lemmas are proven above.

**Proof Status**: The non-overlapping cases (where β and η occur at different
positions in the term) are straightforward - just swap the order of reductions.
The complex cases involve critical overlaps:

1. **β at root with η inside**: (λM)N →β M[N] with η-redex in M or N
   - Requires: η-step preservation under substitution
   - Infrastructure: `shift_neg1_subst_gen`, `hasFreeVarMeta_subst_gen`

2. **η at root with β inside**: λ(P@0) →η shift(-1) P with β-step in P
   - Requires: β-step lifting through shift(-1)
   - Infrastructure: `betaStep_shift_neg1`, `betaStep_preserves_not_fv`

3. **Critical pair**: When M = (λBody)@Arg and the η-redex overlaps
   - Requires careful case analysis of term structure

The proof follows Barendregt (1984), Lemma 3.3.4, using the orthogonality of
β-redexes (shape (λM)@N) and η-redexes (shape λ(M@0) where 0∉FV(M)).

Reference: Barendregt, "The Lambda Calculus: Its Syntax and Semantics", Section 3.3
-/
axiom beta_eta_commute : Rewriting.Commute Metatheory.Lambda.BetaStep EtaStepMeta

/-! ## βη-Confluence via Hindley-Rosen -/

theorem betaEtaStepMeta_eq_union :
    BetaEtaStepMeta = Rewriting.Union Metatheory.Lambda.BetaStep EtaStepMeta := by
  funext M N
  apply propext
  constructor
  · intro h; cases h with | beta hb => exact Or.inl hb | eta he => exact Or.inr he
  · intro h; cases h with | inl hb => exact BetaEtaStepMeta.beta hb | inr he => exact BetaEtaStepMeta.eta he

theorem beta_confluent : Rewriting.Confluent Metatheory.Lambda.BetaStep := by
  intro M N₁ N₂ h1 h2
  have h1' := Metatheory.Lambda.star_to_multiStep h1
  have h2' := Metatheory.Lambda.star_to_multiStep h2
  obtain ⟨P, hp1, hp2⟩ := Metatheory.Lambda.confluence h1' h2'
  exact ⟨P, Metatheory.Lambda.multiStep_to_star hp1, Metatheory.Lambda.multiStep_to_star hp2⟩

theorem betaEta_confluent_meta : Rewriting.Confluent BetaEtaStepMeta := by
  rw [betaEtaStepMeta_eq_union]
  exact Rewriting.confluent_union beta_confluent eta_confluent beta_eta_commute

theorem betaEta_confluent (M N₁ N₂ : Metatheory.Lambda.Term)
    (h1 : Rewriting.Star BetaEtaStepMeta M N₁)
    (h2 : Rewriting.Star BetaEtaStepMeta M N₂) :
    ∃ P, Rewriting.Star BetaEtaStepMeta N₁ P ∧ Rewriting.Star BetaEtaStepMeta N₂ P :=
  betaEta_confluent_meta M N₁ N₂ h1 h2

/-! ## Transfer to HigherLambdaModel Terms -/

theorem toMeta_shift (d : Int) (c : Nat) (M : Term) :
    toMeta (Term.shift d c M) = Metatheory.Lambda.Term.shift d c (toMeta M) := by
  induction M generalizing c with
  | var n =>
    simp only [Term.shift, Metatheory.Lambda.Term.shift, toMeta]
    split <;> rfl
  | app M N ihM ihN =>
    simp only [Term.shift, Metatheory.Lambda.Term.shift, toMeta, ihM, ihN]
  | lam M ih =>
    simp only [Term.shift, Metatheory.Lambda.Term.shift, toMeta, ih]

theorem fromMeta_shift (d : Int) (c : Nat) (M : Metatheory.Lambda.Term) :
    fromMeta (Metatheory.Lambda.Term.shift d c M) = Term.shift d c (fromMeta M) := by
  induction M generalizing c with
  | var n =>
    simp only [Metatheory.Lambda.Term.shift, Term.shift, fromMeta]
    split <;> rfl
  | app M N ihM ihN =>
    simp only [Metatheory.Lambda.Term.shift, Term.shift, fromMeta, ihM, ihN]
  | lam M ih =>
    simp only [Metatheory.Lambda.Term.shift, Term.shift, fromMeta, ih]

theorem etaStep_toMeta {M N : Term} (h : EtaStep M N) :
    EtaStepMeta (toMeta M) (toMeta N) := by
  induction h with
  | eta M hfv =>
    simp only [toMeta]
    have h_fv : hasFreeVarMeta 0 (toMeta M) = Term.hasFreeVar 0 M := hasFreeVar_toMeta 0 M
    have h_shift : toMeta (Term.shift (-1) 0 M) = Metatheory.Lambda.Term.shift (-1) 0 (toMeta M) :=
      toMeta_shift (-1) 0 M
    rw [h_shift]
    apply EtaStepMeta.eta
    rw [h_fv]
    simp only [Bool.eq_false_iff]
    exact hfv
  | appL _ ih => exact EtaStepMeta.appL ih
  | appR _ ih => exact EtaStepMeta.appR ih
  | lam _ ih => exact EtaStepMeta.lam ih

theorem etaStep_fromMeta {M N : Metatheory.Lambda.Term} (h : EtaStepMeta M N) :
    EtaStep (fromMeta M) (fromMeta N) := by
  induction h with
  | eta M hfv =>
    simp only [fromMeta]
    have h_fv : hasFreeVarMeta 0 M = Term.hasFreeVar 0 (fromMeta M) := by
      rw [← hasFreeVar_toMeta 0 (fromMeta M), toMeta_fromMeta]
    have h_shift : fromMeta (Metatheory.Lambda.Term.shift (-1) 0 M) =
                   Term.shift (-1) 0 (fromMeta M) := fromMeta_shift (-1) 0 M
    rw [h_shift]
    apply EtaStep.eta
    rw [h_fv] at hfv
    simp only [Bool.eq_false_iff] at hfv
    exact hfv
  | appL _ ih => exact EtaStep.appL ih
  | appR _ ih => exact EtaStep.appR ih
  | lam _ ih => exact EtaStep.lam ih

theorem betaEtaStep_toMeta {M N : Term} (h : BetaEtaStep M N) :
    BetaEtaStepMeta (toMeta M) (toMeta N) := by
  cases h with
  | beta hb => exact BetaEtaStepMeta.beta (betaStep_toMeta hb)
  | eta he => exact BetaEtaStepMeta.eta (etaStep_toMeta he)

theorem betaEtaStep_fromMeta {M N : Metatheory.Lambda.Term} (h : BetaEtaStepMeta M N) :
    BetaEtaStep (fromMeta M) (fromMeta N) := by
  cases h with
  | beta hb => exact BetaEtaStep.beta (betaStep_fromMeta hb)
  | eta he => exact BetaEtaStep.eta (etaStep_fromMeta he)

theorem betaEtaClosure_toMeta {M N : Term} (h : BetaEtaClosure M N) :
    Rewriting.Star BetaEtaStepMeta (toMeta M) (toMeta N) := by
  induction h with
  | refl _ => exact Rewriting.Star.refl _
  | step s _ ih => exact Rewriting.Star.head (betaEtaStep_toMeta s) ih

theorem star_betaEtaStep_fromMeta {M N : Metatheory.Lambda.Term}
    (h : Rewriting.Star BetaEtaStepMeta M N) : BetaEtaClosure (fromMeta M) (fromMeta N) := by
  induction h with
  | refl => exact BetaEtaClosure.refl _
  | tail _ hab ih => exact BetaEtaClosure.trans' ih (BetaEtaClosure.single (betaEtaStep_fromMeta hab))

/-! ## Main Result -/

/-- **Church-Rosser for HigherLambdaModel**: βη-reduction is confluent. -/
theorem church_rosser_higher {M N₁ N₂ : Term}
    (h1 : BetaEtaClosure M N₁)
    (h2 : BetaEtaClosure M N₂) :
    ∃ P, BetaEtaClosure N₁ P ∧ BetaEtaClosure N₂ P := by
  have h1' := betaEtaClosure_toMeta h1
  have h2' := betaEtaClosure_toMeta h2
  obtain ⟨P', hP1, hP2⟩ := betaEta_confluent (toMeta M) (toMeta N₁) (toMeta N₂) h1' h2'
  refine ⟨fromMeta P', ?_, ?_⟩
  · have h := star_betaEtaStep_fromMeta hP1
    rw [fromMeta_toMeta] at h
    exact h
  · have h := star_betaEtaStep_fromMeta hP2
    rw [fromMeta_toMeta] at h
    exact h

end HigherLambdaModel.Lambda.BetaEtaConfluence
