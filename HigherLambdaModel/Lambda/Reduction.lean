/-
# β-Reduction and η-Reduction

This module defines the fundamental reduction relations on λ-terms:
- β-reduction: (λx.M)N →β M[N/x]
- η-reduction: λx.Mx →η M (when x ∉ FV(M))

## Key Definitions

- `BetaStep` : Single-step β-reduction
- `EtaStep` : Single-step η-reduction
- `BetaEtaStep` : Combined βη-reduction step
- `BetaEtaClosure` : Reflexive-transitive closure (reduction sequence)
- `BetaEtaConv` : Symmetric-transitive closure (conversion/equivalence)

## Mathematical Background

In the paper "The Theory of an Arbitrary Higher λ-Model" (arXiv:2111.07092),
these reductions form the 1-cells of the higher λ-model structure.
The key insight is that in homotopic λ-models (extensional Kan complexes),
multiple distinct reduction paths between the same terms can exist,
and these paths themselves form higher structure.

## References

- de Queiroz & Martínez-Rivillas, "The Theory of an Arbitrary Higher λ-Model"
- Barendregt, "The Lambda Calculus: Its Syntax and Semantics"
-/

import HigherLambdaModel.Lambda.Term

namespace HigherLambdaModel.Lambda

open Term

/-! ## Single-Step Reductions -/

/-- A single β-reduction step: (λM)N →β M[N].
    We track both the source and target to form explicit "arrows". -/
inductive BetaStep : Term → Term → Prop where
  /-- β-redex at the root: (λM)N →β M[N/x] -/
  | beta : ∀ M N, BetaStep (app (lam M) N) (M[N])
  /-- β-reduction in the function part of an application -/
  | appL : ∀ {M M' N}, BetaStep M M' → BetaStep (app M N) (app M' N)
  /-- β-reduction in the argument part of an application -/
  | appR : ∀ {M N N'}, BetaStep N N' → BetaStep (app M N) (app M N')
  /-- β-reduction under a λ-abstraction -/
  | lam : ∀ {M M'}, BetaStep M M' → BetaStep (Term.lam M) (Term.lam M')

/-- A single η-reduction step: λx.Mx →η M when x ∉ FV(M).
    Formulated using de Bruijn: (lam (M · var 0)) →η M when 0 ∉ FV(M). -/
inductive EtaStep : Term → Term → Prop where
  /-- η-redex at the root -/
  | eta : ∀ M, ¬hasFreeVar 0 M = true → EtaStep (Term.lam (app M (var 0))) (shift (-1) 0 M)
  /-- η-reduction in the function part of an application -/
  | appL : ∀ {M M' N}, EtaStep M M' → EtaStep (app M N) (app M' N)
  /-- η-reduction in the argument part of an application -/
  | appR : ∀ {M N N'}, EtaStep N N' → EtaStep (app M N) (app M N')
  /-- η-reduction under a λ-abstraction -/
  | lam : ∀ {M M'}, EtaStep M M' → EtaStep (Term.lam M) (Term.lam M')

/-- Combined βη-reduction: either a β-step or an η-step -/
inductive BetaEtaStep : Term → Term → Prop where
  | beta : ∀ {M N}, BetaStep M N → BetaEtaStep M N
  | eta : ∀ {M N}, EtaStep M N → BetaEtaStep M N

/-! ## Reduction Closures -/

/-- Reflexive-transitive closure of βη-reduction.
    This represents a reduction sequence M →* N. -/
inductive BetaEtaClosure : Term → Term → Prop where
  | refl : ∀ M, BetaEtaClosure M M
  | step : ∀ {M N P}, BetaEtaStep M N → BetaEtaClosure N P → BetaEtaClosure M P

/-- βη-conversion (equivalence): symmetric-transitive closure.
    M =βη N means M and N are convertible. -/
inductive BetaEtaConv : Term → Term → Prop where
  | refl : ∀ M, BetaEtaConv M M
  | step : ∀ {M N P}, BetaEtaStep M N → BetaEtaConv N P → BetaEtaConv M P
  | stepInv : ∀ {M N P}, BetaEtaStep N M → BetaEtaConv N P → BetaEtaConv M P

namespace BetaStep

/-- β-reduction is deterministic at each redex position -/
theorem beta_det_root (M N : Term) :
    BetaStep (app (Term.lam M) N) (M[N]) := beta M N

end BetaStep

namespace BetaEtaClosure

/-- Single step is a reduction -/
theorem single {M N : Term} (h : BetaEtaStep M N) : BetaEtaClosure M N :=
  step h (refl N)

/-- Transitivity of reduction -/
theorem trans' {M N P : Term} (h1 : BetaEtaClosure M N) (h2 : BetaEtaClosure N P) :
    BetaEtaClosure M P := by
  induction h1 with
  | refl _ => exact h2
  | step s _ ih => exact step s (ih h2)

/-- Reduction is preserved under application (left) -/
theorem appL' {M M' N : Term} (h : BetaEtaClosure M M') :
    BetaEtaClosure (app M N) (app M' N) := by
  induction h with
  | refl _ => exact refl _
  | step s _ ih =>
    apply step
    · cases s with
      | beta hb => exact BetaEtaStep.beta (BetaStep.appL hb)
      | eta he => exact BetaEtaStep.eta (EtaStep.appL he)
    · exact ih

/-- Reduction is preserved under application (right) -/
theorem appR' {M N N' : Term} (h : BetaEtaClosure N N') :
    BetaEtaClosure (app M N) (app M N') := by
  induction h with
  | refl _ => exact refl _
  | step s _ ih =>
    apply step
    · cases s with
      | beta hb => exact BetaEtaStep.beta (BetaStep.appR hb)
      | eta he => exact BetaEtaStep.eta (EtaStep.appR he)
    · exact ih

/-- Reduction is preserved under λ-abstraction -/
theorem lam' {M M' : Term} (h : BetaEtaClosure M M') :
    BetaEtaClosure (Term.lam M) (Term.lam M') := by
  induction h with
  | refl _ => exact refl _
  | step s _ ih =>
    apply step
    · cases s with
      | beta hb => exact BetaEtaStep.beta (BetaStep.lam hb)
      | eta he => exact BetaEtaStep.eta (EtaStep.lam he)
    · exact ih

/-- Combined congruence for application -/
theorem app' {M M' N N' : Term}
    (hM : BetaEtaClosure M M') (hN : BetaEtaClosure N N') :
    BetaEtaClosure (app M N) (app M' N') :=
  trans' (appL' hM) (appR' hN)

end BetaEtaClosure

namespace BetaEtaConv

/-- βη-conversion includes reduction -/
theorem of_closure {M N : Term} (h : BetaEtaClosure M N) : BetaEtaConv M N := by
  induction h with
  | refl _ => exact refl _
  | step s _ ih => exact step s ih

/-- Transitivity of βη-conversion -/
theorem trans' {M N P : Term} (h1 : BetaEtaConv M N) (h2 : BetaEtaConv N P) :
    BetaEtaConv M P := by
  induction h1 generalizing P with
  | refl _ => exact h2
  | step s _ ih => exact step s (ih h2)
  | stepInv s _ ih => exact stepInv s (ih h2)

/-- Symmetry of βη-conversion -/
theorem symm' {M N : Term} (h : BetaEtaConv M N) : BetaEtaConv N M := by
  induction h with
  | refl _ => exact refl _
  | step s _ ih => exact trans' ih (stepInv s (refl _))
  | stepInv s _ ih => exact trans' ih (step s (refl _))

/-- Conversion is preserved under application (left) -/
theorem appL' {M M' N : Term} (h : BetaEtaConv M M') :
    BetaEtaConv (app M N) (app M' N) := by
  induction h with
  | refl _ => exact refl _
  | step s _ ih =>
    apply step
    · cases s with
      | beta hb => exact BetaEtaStep.beta (BetaStep.appL hb)
      | eta he => exact BetaEtaStep.eta (EtaStep.appL he)
    · exact ih
  | stepInv s _ ih =>
    apply stepInv
    · cases s with
      | beta hb => exact BetaEtaStep.beta (BetaStep.appL hb)
      | eta he => exact BetaEtaStep.eta (EtaStep.appL he)
    · exact ih

/-- Conversion is preserved under application (right) -/
theorem appR' {M N N' : Term} (h : BetaEtaConv N N') :
    BetaEtaConv (app M N) (app M N') := by
  induction h with
  | refl _ => exact refl _
  | step s _ ih =>
    apply step
    · cases s with
      | beta hb => exact BetaEtaStep.beta (BetaStep.appR hb)
      | eta he => exact BetaEtaStep.eta (EtaStep.appR he)
    · exact ih
  | stepInv s _ ih =>
    apply stepInv
    · cases s with
      | beta hb => exact BetaEtaStep.beta (BetaStep.appR hb)
      | eta he => exact BetaEtaStep.eta (EtaStep.appR he)
    · exact ih

/-- Conversion is preserved under λ-abstraction -/
theorem lam' {M M' : Term} (h : BetaEtaConv M M') :
    BetaEtaConv (Term.lam M) (Term.lam M') := by
  induction h with
  | refl _ => exact refl _
  | step s _ ih =>
    apply step
    · cases s with
      | beta hb => exact BetaEtaStep.beta (BetaStep.lam hb)
      | eta he => exact BetaEtaStep.eta (EtaStep.lam he)
    · exact ih
  | stepInv s _ ih =>
    apply stepInv
    · cases s with
      | beta hb => exact BetaEtaStep.beta (BetaStep.lam hb)
      | eta he => exact BetaEtaStep.eta (EtaStep.lam he)
    · exact ih

/-- Combined congruence for application -/
theorem app' {M M' N N' : Term}
    (hM : BetaEtaConv M M') (hN : BetaEtaConv N N') :
    BetaEtaConv (app M N) (app M' N') :=
  trans' (appL' hM) (appR' hN)

end BetaEtaConv

/-! ## Notation for Reductions -/

/-- Notation for single-step βη-reduction -/
scoped infix:50 " →βη " => BetaEtaStep

/-- Notation for multi-step βη-reduction -/
scoped infix:50 " →*βη " => BetaEtaClosure

/-- Notation for βη-conversion -/
scoped infix:50 " =βη " => BetaEtaConv

/-! ## Key Examples -/

/-- (λx.x)M →β M : The identity combinator applied to any term reduces to that term. -/
example (M : Term) : (Term.I @ M) →*βη M :=
  BetaEtaClosure.single (BetaEtaStep.beta (BetaStep.beta (var 0) M))

/-- Reflexivity: any term reduces to itself in zero steps. -/
example (M : Term) : M →*βη M :=
  BetaEtaClosure.refl M

/-- β-reduction under application: if M →β M' then MN →β M'N -/
example (M M' N : Term) (h : BetaStep M M') : (M @ N) →*βη (M' @ N) :=
  BetaEtaClosure.single (BetaEtaStep.beta (BetaStep.appL h))

/-- β-reduction under lambda: if M →β M' then λx.M →β λx.M' -/
example (M M' : Term) (h : BetaStep M M') : (Term.lam M) →*βη (Term.lam M') :=
  BetaEtaClosure.single (BetaEtaStep.beta (BetaStep.lam h))

end HigherLambdaModel.Lambda
