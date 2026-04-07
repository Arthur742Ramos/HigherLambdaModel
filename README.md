# Higher Lambda Model

<div align="center">

**A Lean 4 formalization of higher-dimensional structure in the untyped lambda calculus**

[![Lean 4](https://img.shields.io/badge/Lean-4.24.0-blue?logo=lean)](https://lean-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](./LICENSE)
[![arXiv](https://img.shields.io/badge/arXiv-2111.07092-b31b1b.svg)](https://arxiv.org/abs/2111.07092)

*Formalizing "The Theory of an Arbitrary Higher λ-Model" and "The K∞ Homotopy λ-Model"*

</div>

---

## Overview

This repository formalizes the higher-conversion viewpoint on the untyped
lambda calculus together with the concrete `K∞` model developed by
Martínez-Rivillas and de Queiroz.

At the proposition level, the current top-line theorem is:

**`TH_λ= ⊆ HoTFT`**

Every classical `βη`-equality provable in the lambda calculus is valid in all
extensional Kan-complex models formalized here. On top of that proposition-level
result, the repository now contains:

- an explicit tower of higher conversions and higher terms,
- a canonical omega-groupoid/coherence API shared across the codebase,
- a generic admissible-model coherence package,
- a concrete admissible `K∞` instance,
- and a small suite of concrete higher-conversion examples.

The exact paper-level coverage is tracked in
[`docs/theorem_index.md`](./docs/theorem_index.md). Completed execution work is
tracked in [`docs/closure_backlog.md`](./docs/closure_backlog.md).

## Repository Snapshot

Current snapshot, excluding `.lake`:

- `31` Lean files
- `13,492` lines of Lean
- `309` named `theorem` / `lemma` declarations
- `1` remaining local `axiom` (the bare semantic pentagon back-loop contraction in `ExtensionalKan.lean`) and no `sorry` / `admit` declarations
- all closure backlog issues `0` through `8` completed

## Key Results Formalized

| Result | Lean file(s) | Status |
| --- | --- | --- |
| Extensional Kan-complex semantics and substitution-compatible interpretation | `HigherLambdaModel/Lambda/ExtensionalKan.lean` | `done` |
| β- and η-soundness | `HigherLambdaModel/Lambda/ExtensionalKan.lean` | `done` |
| Classical theory embeds into HoTFT: `TH_λ= ⊆ HoTFT` | `HigherLambdaModel/Lambda/NTerms.lean` | `done` |
| Higher terms embed into higher conversions: `Πₙ ⊆ Σₙ` | `HigherLambdaModel/Lambda/NTerms.lean` | `done` |
| Canonical omega-groupoid API and generic coherence packaging | `HigherLambdaModel/Simplicial/OmegaGroupoid.lean`, `HigherLambdaModel/Lambda/Coherence.lean`, `HigherLambdaModel/Lambda/TruncationCore.lean`, `HigherLambdaModel/Lambda/Truncation.lean` | `done` |
| Concrete admissible `K∞` instance | `HigherLambdaModel/KInfinity/Properties.lean` | `done` |
| Non-trivial example suite | `HigherLambdaModel/KInfinity/Examples.lean` | `done` |
| Paper-level exactness for the continuous `K∞ ≃ [K∞ → K∞]` story | `docs/theorem_index.md` | `done` |

## Project Structure

```text
HigherLambdaModel/
|-- Domain/
|   |-- CHPO.lean              # Complete homotopy partial orders and projective limits
|   +-- ScottDomain.lean       # Homotopy Scott domains and exponential constructions
|-- Lambda/
|   |-- Term.lean              # De Bruijn lambda terms, shifting, substitution
|   |-- Reduction.lean         # β/η reduction, conversion, and explicit paths
|   |-- HigherTerms.lean       # Constructive higher-cell tower
|   |-- ExtensionalKan.lean    # Kan-complex semantics and HoTFT layers
|   |-- NTerms.lean            # n-terms, n-conversions, and TH_λ= ⊆ HoTFT
|   |-- Coherence.lean         # Canonical omega-groupoid structure on λ-terms
|   |-- TruncationCore.lean    # Generic coherence packaging and realized towers
|   |-- Truncation.lean        # 0-truncation back to ordinary βη-theory
|   |-- ChurchRosserProof.lean # Church-Rosser transfer from Metatheory
|   +-- BetaEtaConfluence.lean # Constructive common-extension compatibility layer
|-- Simplicial/
|   |-- Basic.lean             # Simplicial infrastructure
|   |-- Limits.lean            # Categorical/simplicial limit helpers
|   |-- InfinityCategory.lean  # Infinity-categorical packaging
|   +-- OmegaGroupoid.lean     # Shared omega-groupoid API
|-- KInfinity/
|   |-- NonTrivial.lean        # Section 4 non-triviality interfaces and N⁺
|   |-- Construction.lean      # The K₀, K₁, ... tower and h-projection pairs
|   |-- Properties.lean        # Proposition-level `K∞` consequences
|   +-- Examples.lean          # Concrete higher-conversion example suite
|-- docs/
|   |-- theorem_index.md       # Paper-to-Lean claim matrix
|   +-- closure_backlog.md     # Completed closure roadmap
|-- paper/
|   +-- K_infinity_homotopy_lambda_model.pdf
+-- lakefile.toml
```

## Building

### Prerequisites

- [Lean 4](https://lean-lang.org/) `v4.24.0`
- [Lake](https://github.com/leanprover/lean4/tree/master/src/lake) (bundled with Lean)

### Build

```bash
git clone https://github.com/Arthur742Ramos/HigherLambdaModel.git
cd HigherLambdaModel
lake build
```

### Dependencies

Lake fetches:

- [ComputationalPathsLean](https://github.com/Arthur742Ramos/ComputationalPathsLean)
- [Metatheory](https://github.com/Arthur742Ramos/Metatheory)

The remaining external proof-theoretic dependency of note is `Metatheory`,
which supplies the Church-Rosser transfer used in
`HigherLambdaModel/Lambda/ChurchRosserProof.lean`.

## Concrete Example Suite

`HigherLambdaModel/KInfinity/Examples.lean` packages concrete witnesses rather
than just abstract interfaces. The current examples include:

- a confluence diamond on the duplicated-identity term: `duplicatedIdentity_diamond`,
- explicit associator and triangle witnesses: `duplicatedIdentity_associator`,
  `duplicatedIdentity_triangle`,
- a proof that two parallel 2-cells are not definitionally equal:
  `duplicatedIdentity_parallel_2cells_ne`,
- compatibility with ordinary proposition-level theory:
  `churchOne_truncates_to_TH`,
- and the `K∞` point-separation witness:
  `beta_eta_points_distinct_in_KInfinity`.

## Closure Status

The closure backlog in [`docs/closure_backlog.md`](./docs/closure_backlog.md)
is complete. That means the repository now has:

- a shared omega-groupoid API,
- explicit higher-conversion algebra on lambda terms,
- a generic coherence theorem,
- a concrete `K∞` admissible-model instance,
- and an example suite exercising the infrastructure.

In particular, the current `K∞` Example 4.2 development now separates the
chosen β-side and η-side points not only through the explicit 1/2/3/4/5-cell
omega-groupoid core, but through every dimension of the current recursively
completed all-dimensional `kInfinityTower` whenever the 0-boundary is that same
β/η pair.

It does **not** mean that every statement in the source papers is formalized
verbatim. The remaining paper-level partials and missing claims are deliberate,
documented, and visible in [`docs/theorem_index.md`](./docs/theorem_index.md).

The Section 4 closure story is now materially stronger than the earlier roadmap
checkpoints:

- Proposition 4.1 is fully internalized: `kInfinity_algebraic`,
  `kInfinity_boundedComplete`, and `kInfinityScottDomain` close the exact `K∞`
  Homotopy Scott Domain statement.
- Example 4.2 is also closed at the current chosen-point /
  interpreted-witness level. The repository has the continuous λ-term
  interpreter over CHPO products and continuous exponentials, the public
  substitution and arbitrary one-step βη soundness theorems, the proof-relevant
  one-step and explicit 1-term witness layers, and the paper-facing β₁ / η₁
  witness packages `betaEtaPaper_beta1Witness_interpretation` /
  `betaEtaPaper_eta1Witness_interpretation`. Those explicit 1-term witness
  packages now arise from the generic Prop-level classification-based map
  `example42NTerm1Witness_interpretation` on arbitrary
  `NTerm1Witness betaEtaPaperSource betaEtaPaperTarget`, rather than routing
  through the bespoke two-tag `Example42DirectWitness` selector, and they
  inherit the full existing no 1/2/3/4/5/recursive-higher-cell separation
  suite.

The remaining paper-level gaps are now:

- a direct semantic interpretation of the full primitive `Homotopy3Deriv`
  language rather than only the current structural fragment (the structural
  fragment now reaches reflexivity, equality, symmetry, transitivity,
  reflexive left/right whiskering, left/right-whisker transitivity,
  left/right-whisker symmetry, inverse left/right-whisker symmetry, and
  interchange; outside that structural fragment, standalone primitive semantic
  theorems already cover triangle, pentagon, and the second interchange form.
  Interpreted syntactic right whiskers now also bridge back to the legacy
  structural shell, so the live `ExtensionalKan.lean` file now also proves the
  self-comparison contraction `triangleSelfReflPath3`; for a bare generic
  `KanComplex`, the remaining pentagon frontier is the smaller local front-face
  axiom `pentagonInnerRightFrontReflPath3`, while the new strict
  filler-uniqueness layer (`StrictKanComplex`, `StrictExtensionalKanComplex`,
  `Theory3.strictWhiskerLeftWhiskerRight`, `Theory3.strictPentagon`) now
  discharges both the WLWR front-loop obstruction and the pentagon axiom-free;
  the explicit-path strict wrappers
  `homotopy2_strictWhiskerLeftWhiskerRight_in_Theory3` and
  `reductionSeq_strictPentagon_in_Theory3` expose those proofs without forcing
  a return to the raw semantic level. The recursive associator bookkeeping is
  now packaged on both the semantic and
  HoTFT sides by `reductionSeq_comp_associator_in_Theory3_of_heads` and
  `reductionSeq_comp_associator_in_HoTFT3_of_heads`. In strict models, the
  local forward and inverse step-head bridges are now also proven directly via
  `reductionSeq_comp_associator_stepHead_strict_in_Theory3`,
  `reductionSeq_comp_associator_stepInvHead_strict_in_Theory3`, and the
  resulting recursive strict theorem
  `reductionSeq_comp_associator_strict_in_Theory3`. So the live `Homotopy3`
  gap is now the unsupported coherence fragment outside `StructuralHomotopy3`,
  concretely the final direct endpoint-language bridge from full primitive
  syntax back to the structural `HoTFT3` interface),
- and a stronger all-dimensional constructive omega-groupoid story beyond the
  current explicit 5-cell core plus recursive identity tower.

## Theory Summary

The main proposition-level interfaces remain:

```lean
def TheoryEq (K : ExtensionalKanComplex) (M N : Term) : Prop :=
  forall rho, interpret K rho M = interpret K rho N

def HoTFT_eq (M N : Term) : Prop :=
  forall K : ExtensionalKanComplex, TheoryEq K M N

def TH_lambda_eq (M N : Term) : Prop :=
  BetaEtaConv M N

theorem TH_lambda_eq_subset_HoTFT (M N : Term) (h : M =_TH N) :
    M =_HoTFT N
```

The generic coherence layer additionally packages the explicit higher
conversion tower through the shared simplicial interface, proves that
0-truncation recovers ordinary `TH_λ=`, and now compares that explicit tower
with the shared recursive-identity omega tower used by both the constructive
λ-term model and the concrete `K∞` model.

## References

### Primary Sources

- Martínez-Rivillas, A. and de Queiroz, R. (2021). *The Theory of an Arbitrary Higher λ-Model*. [arXiv:2111.07092](https://arxiv.org/abs/2111.07092)
- Martínez-Rivillas, A. and de Queiroz, R. *The K∞ Homotopy λ-Model*. Local copy in [`paper/K_infinity_homotopy_lambda_model.pdf`](./paper/K_infinity_homotopy_lambda_model.pdf)

### Background

- Barendregt, H. P. (1984). *The Lambda Calculus: Its Syntax and Semantics*. North-Holland.
- Hofmann, M. and Streicher, T. (1998). "The groupoid interpretation of type theory". *Twenty-five years of constructive type theory*.
- Lumsdaine, P. L. (2009). "Weak omega-categories from intensional type theory". *TLCA*.
- Univalent Foundations Program (2013). *Homotopy Type Theory*. Institute for Advanced Study.

## Contributing

Contributions are welcome. The highest-signal directions are:

- strengthening the remaining `partial` and `missing` rows in `docs/theorem_index.md`,
- internalizing more of the confluence story now imported from `Metatheory`,
- extending the direct semantic treatment of higher 3-cells,
- and pushing the `K∞` layer from chosen-data shadows to exact paper statements.

## License

[MIT License](./LICENSE)

## Acknowledgments

This formalization is based on the work of Martínez-Rivillas and de Queiroz.
Thanks to Arthur Ramos for the supporting Lean infrastructure libraries.

---

<div align="center">

*All declarations included in this repository are mechanically verified by Lean 4; paper-level coverage gaps are tracked explicitly in `docs/theorem_index.md`.*

</div>
