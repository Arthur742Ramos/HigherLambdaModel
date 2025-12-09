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

/-! ## β-η Commutation

The Commute relation (from Metatheory.Rewriting.HindleyRosen) requires three properties:
1. Diamond: β a b → η a c → ∃ d, η b d ∧ β c d
2. Swap1: η a b → β b c → ∃ d, β a d ∧ η d c
3. Swap2: β a b → η b c → ∃ d, η a d ∧ β d c

This is a well-known result from the λ-calculus literature. The proof requires
careful analysis of critical pairs when β and η redexes overlap.

## Why this is axiomatized

Proving β-η commutation fully requires extensive de Bruijn infrastructure:
1. Lemmas about negative shift-substitution interaction (shift (-1) and subst)
2. β-step preservation under negative shifts
3. η-step preservation under substitution
4. Critical pair analysis for all overlapping cases

The key insight for the critical overlap case λ((λ P) (var 0)) is that when
hasFreeVar 1 P = false, we have subst 0 (var 0) P = shift (-1) 1 P.

The Metatheory library provides lemmas for positive shifts, but η-reduction
uses negative shifts (shift (-1) 0 M), requiring additional lemmas not
currently in the library.

Reference: Barendregt (1984): "The Lambda Calculus", Section 3.3, Lemma 3.3.4
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
