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

The main paper-level gaps still tracked there are:

Proposition 4.1 is now fully internalized: `kInfinity_algebraic`,
`kInfinity_boundedComplete`, and `kInfinityScottDomain` close the exact `K∞`
Homotopy Scott Domain statement, so the remaining paper-facing obstructions are
now semantic rather than domain-theoretic.

- the full interpreted beta/eta separation statement of Example 4.2
  (the repository now packages the strongest honest current endpoint as
  `proposition_4_4_example_4_2`, combining the completed non-trivial homotopy
  λ-model witness with the full β/η point-separation suite through the explicit
  1/2/3/4/5-cell hierarchy and the recursively completed all-dimensional tower;
  the repo now also has a well-scoped λ-term semantics over CHPO product
  contexts and continuous exponentials, together with public substitution and
  arbitrary one-step βη soundness theorems
  `interpretContinuous_subst`, `interpretContinuous_subst0`,
  `beta_sound_continuous`, `betaStep_sound_continuous`,
  `eta_sound_continuous`, `etaStep_sound_continuous`,
  `betaEtaStep_sound_continuous`, and the bridge lemma
  `interpretContinuous_lam_reflect_apply`; it fixes the paper's concrete
  witness terms `(λz.xz) y` and `xy` in `KInfinity/Examples.lean`, proves the
  object-level equalities
  `betaEtaPaperFunction_interpretContinuous` and
  `betaEtaPaperSource_interpretContinuous` via those generic theorems, packages
  the explicit β₁/η₁ witness maps themselves as
  `betaEtaPaper_beta1_continuousWitness` and
  `betaEtaPaper_eta1_continuousWitness`, and now also packages them with the
  chosen separated `K∞` points as
  `betaEtaPaper_beta1_interpretation` / `betaEtaPaper_eta1_interpretation`;
  those chosen-data packages now inherit the full existing separation suite
  through no 1/2/3/4/5-cell and no recursive higher cell via
  `betaEtaPaper_witness_interpretations_no_path`,
  `betaEtaPaper_witness_interpretations_no_2cell`,
  `betaEtaPaper_witness_interpretations_no_3cell`,
  `betaEtaPaper_witness_interpretations_no_4cell`,
  `betaEtaPaper_witness_interpretations_no_5cell`, and
  `betaEtaPaper_witness_interpretations_no_recursive_higher_cell`; the repo now
  also makes the proof-relevance issue explicit through
  `Example42DirectWitness` and `betaEtaPaper_beta1_eq_eta1`, showing that the
  ordinary `NTerm1.redex` layer already identifies the direct β₁ and η₁
  witnesses because `BetaEtaStep` is proposition-valued. So what still remains
  is not the chosen-data identification itself, but a proof-relevant semantic
  derivation that these representatives are the canonical images of the paper
  witnesses rather than an explicit packaging choice),
- a direct semantic interpretation of the full primitive `Homotopy3Deriv`
  language rather than only the current structural fragment (the structural
  fragment now reaches reflexivity, equality, symmetry, transitivity,
  reflexive left/right whiskering, left-whisker transitivity, left-whisker
  symmetry, and interchange; outside that structural fragment, the direct
  primitive coverage now also includes triangle, right-whisker transitivity,
  forward and inverse right-whisker symmetry, and the second interchange
  form, so the remaining gap has narrowed to pentagon),
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
