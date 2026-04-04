# Higher Lambda Model Closure Backlog

This document turned the omega-groupoid closure roadmap into an execution queue
for this repository.

The broken iCloud-backed Desktop checkout is no longer the working baseline.
Active work now happens in `/Users/arthur/LocalRepos/HigherLambdaModel`, where
Git and Lean both work normally.

All backlog issues `0` through `8` are now complete. Remaining paper-level
`partial` and `missing` claims are tracked in `docs/theorem_index.md` rather
than in this execution queue.

## Definition of done

We treat the omega-groupoid closure effort as complete when the repository
contains a machine-checked end-to-end theorem stack with the following shape:

1. A generic higher lambda-model interface with explicit higher-conversion operations.
2. A canonical simplicial or infinity-categorical realization of those higher conversions as an omega/infinity-groupoid.
3. A generic coherence theorem connecting the lambda side to the simplicial or infinity-categorical side.
4. A concrete proof that `K_\infty` satisfies the generic hypotheses.
5. Concrete examples witnessing non-trivial and non-equivalent higher conversions.
6. A paper-to-Lean theorem index showing which manuscript claims are formalized and where.

## Issue 0: Materialize the repository locally

Status: done

Problem:
The original checkout under Desktop was iCloud-managed and contained many
`dataless` files, including `.git/HEAD`, source files, and paper assets. That
made Git, Lean, and direct source inspection unreliable.

Resolution:

- A fresh clone was created at `/Users/arthur/LocalRepos/HigherLambdaModel`.
- `git remote -v` resolves to `https://github.com/Arthur742Ramos/HigherLambdaModel.git`.
- `find . -flags +dataless -type f` reports no dataless files in the fresh clone.
- `scripts/check_repo_readiness.sh /Users/arthur/LocalRepos/HigherLambdaModel` passes.
- `lake build` now runs to completion in the active clone.

Acceptance criteria:

1. Key repository files are no longer marked `dataless`.
2. `git rev-parse --show-toplevel` succeeds.
3. `head -n 20 README.md` succeeds.
4. `lake build` runs to completion or fails with an ordinary Lean error rather than a filesystem timeout.

Follow-up:

1. Keep all further work in `/Users/arthur/LocalRepos/HigherLambdaModel`.
2. Do not resume editing the broken Desktop checkout.

Support tooling:

- `/Users/arthur/LocalRepos/HigherLambdaModel/scripts/check_repo_readiness.sh`
  This script reports dataless counts, key file flags, basic read checks, Git readiness, and Lean availability.

## Issue 1: Build and dependency stabilization

Status: done

Goal:
Get a deterministic baseline build and isolate theorem gaps from environment failures.

Likely files:

- `/Users/arthur/LocalRepos/HigherLambdaModel/lakefile.toml`
- `/Users/arthur/LocalRepos/HigherLambdaModel/lake-manifest.json`
- `/Users/arthur/LocalRepos/HigherLambdaModel/lean-toolchain`
- `/Users/arthur/LocalRepos/HigherLambdaModel/.github/workflows/lean_action_ci.yml`

Acceptance criteria:

1. `lake build` succeeds locally.
2. CI uses the same Lean toolchain as local development.
3. Any dependency fetches are reproducible.

Current state:

- `lake build` succeeds in `/Users/arthur/LocalRepos/HigherLambdaModel`.
- The active toolchain is `leanprover/lean4:v4.24.0`.
- The current baseline commit is `0adb404`, synced with `origin/master`.

## Issue 2: Paper-to-Lean claim matrix

Status: done

Goal:
Create a single source of truth mapping paper claims to Lean declarations and formalization status.

Deliverable:

- `/Users/arthur/LocalRepos/HigherLambdaModel/docs/theorem_index.md`

Acceptance criteria:

1. Every major theorem or construction claimed in the papers has one row.
2. Each row lists source paper section, Lean file, declaration name, and status.
3. Unformalized claims are explicitly marked `missing` or `partial`.

Completed work:

- `docs/theorem_index.md` now indexes the main claims from both papers.
- The index distinguishes `done`, `partial`, and `missing` claims.
- The document makes the remaining paper-level gaps explicit instead of implying closure beyond the Lean code.

## Issue 3: Canonical omega/infinity-groupoid API

Status: done

Completion commit:

- `f507738` (`Extend omega-groupoid to 5-cells with pentagon/hexagon coherences (Issue 3)`)

Goal:
Make the simplicial or infinity-categorical layer expose one canonical interface for the higher-categorical structure used by the lambda development.

Likely files:

- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/Simplicial/OmegaGroupoid.lean`
- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/Simplicial.lean`
- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/Lambda/HigherTerms.lean`
- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/Lambda/Coherence.lean`

Acceptance criteria:

1. There is one exported interface for source, target, identity, composition, and higher coherence data.
2. The lambda-side modules depend on that interface rather than ad hoc local lemmas.
3. The API is sufficient to state the generic coherence theorem.

Completed work:

- Added `HigherLambdaModel/Simplicial/OmegaGroupoid.lean` as the shared low-dimensional omega-groupoid interface.
- Rebased `LambdaOmegaGroupoidData` and `LambdaOmegaGroupoid` onto that shared interface.
- Added `GlobularTower` and `ReflexiveGlobularTower` to the shared simplicial layer.
- Extended the canonical interface through 5-cells and added the packaged pentagon and interchange reflexive lifts.
- `lake build` continued to succeed after the extraction.

## Issue 4: Higher-conversion algebra on lambda terms

Status: done

Completion commit:

- `2be4305` (`Close whiskerRightRefl → HoTFT3 bridge (Issue 4 COMPLETE)`)

Goal:
Ensure the lambda layer contains explicit operations and laws for higher conversions, not just syntax and isolated reduction facts.

Likely files:

- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/Lambda/Term.lean`
- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/Lambda/HigherTerms.lean`
- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/Lambda/Reduction.lean`
- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/Lambda/SubstLemma.lean`
- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/Lambda/NTerms.lean`
- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/Lambda/Higher.lean`

Acceptance criteria:

1. Higher conversions have explicit boundary maps.
2. Composition or pasting is defined where needed.
3. Identities and inverse or equivalence data are represented.
4. Substitution is compatible with the higher structure.

Completed work:

- Added recursive boundary operators `HigherTerms.Cell.source` and `HigherTerms.Cell.target` for the higher-cell tower.
- Proved generic globularity of the recursive tower via `HigherTerms.Cell.globular_source` and `HigherTerms.Cell.globular_target`.
- Exported the recursive boundaries publicly as `NConversion.source` and `NConversion.target`, while preserving the low-dimensional aliases.
- Rebased `LambdaTower` on the shared `Simplicial.GlobularTower` interface.
- Added boundary-aware semantic triangle and tetrahedron interfaces (`TheoryTriangle`, `TheoryTetrahedron`, `HoTFTTriangle`, `HoTFTTetrahedron`).
- Added semantic tetrahedron witnesses for associators, unitors, whiskering, and reflexive composites.
- Added comparison/filler constructions (`KanComplex.tetrahedronPath3`, `KanComplex.tetrahedronComparisonTetrahedron`) and lifted them to the semantic and HoTFT layers.
- Normalized both `whiskerLeftRefl` and `whiskerRightRefl` all the way into the restricted `Theory3` / `HoTFT3` interface.

## Issue 5: Generic coherence theorem

Status: done

Completion commit:

- `bedcc24` (`Issue 5: Generic Coherence Theorem`)

Goal:
Formalize the central theorem that higher conversions in an admissible higher lambda-model form the intended omega/infinity-groupoid structure.

Likely files:

- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/Lambda/Coherence.lean`
- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/Lambda/ExtensionalKan.lean`
- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/Lambda/TruncationCore.lean`
- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/Lambda/Truncation.lean`

Acceptance criteria:

1. The theorem is stated generically over the intended class of higher lambda-models.
2. The proof imports the canonical simplicial or infinity-groupoid API rather than duplicating structure.
3. Lower-dimensional truncations recover the ordinary conversion theory already formalized elsewhere in the repo.

Completed work:

- Added `AdmissibleHigherLambdaModel` as the generic interface tying a globular tower to the canonical omega-groupoid API.
- Added `HigherConversionCoherence`, `higherConversionCoherenceData`, and `higherConversions_form_omegaGroupoid`.
- Specialized the generic theorem to the explicit lambda tower via `lambdaAdmissibleHigherLambdaModel`, `lambdaHigherConversionCoherence`, and `lambda_higher_conversions_form_omegaGroupoid`.
- Added the truncation recovery theorem `lambda_generic_coherence_0_truncation`, showing that 0-truncation of the generic coherence package recovers ordinary `TH_λ=`.

## Issue 6: `K_\infty` as the principal instance

Status: done

Completion commit:

- `ae10629` (`Issue 6: K∞ as principal instance of AdmissibleHigherLambdaModel`)

Goal:
Show that the concrete `K_\infty` model satisfies the generic hypotheses and inherits the full theorem stack.

Likely files:

- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/KInfinity/Construction.lean`
- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/KInfinity/Properties.lean`
- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/KInfinity/NonTrivial.lean`
- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/KInfinity.lean`

Acceptance criteria:

1. `K_\infty` is exposed as an instance of the generic interface.
2. Non-trivial higher conversions are derived through the generic theorems where possible.
3. Model-specific lemmas are minimized and isolated.

Completed work:

- Added `kInfinityOmegaGroupoid` as the canonical identity-type omega-groupoid on the carrier of `KInfinityCHPO`.
- Added the packed all-dimensional tower `kInfinityTower`.
- Added `kInfinityAdmissibleHigherLambdaModel`, `kInfinityHigherConversionCoherence`, and `kInfinity_higher_conversions_form_omegaGroupoid`.
- Added the recovered realized tower `reflexiveKInfinityTower` together with the definitional identification lemma.
- Added specialized `KInfinityPath`, `KInfinityPath2`, `kInfinityPentagon4`, `kInfinityPentagon5`, `kInfinityHexagon4`, and `kInfinityHexagon5` interfaces for concrete higher cells in the model.

## Issue 7: Non-trivial example suite

Status: done

Completion commit:

- `08f6155` (`Issue 7: Non-trivial example suite`)

Goal:
Turn the theory into executable evidence by proving a small set of named examples.

Suggested deliverable:

- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/KInfinity/Examples.lean`

Acceptance criteria:

1. At least three examples of distinct higher conversions are formalized.
2. At least one example proves non-equivalence of higher conversions.
3. At least one example shows compatibility with truncation to the ordinary theory.

Completed work:

- Added `HigherLambdaModel/KInfinity/Examples.lean` and exported it from `HigherLambdaModel/KInfinity.lean`.
- Formalized a concrete confluence diamond on the duplicated-identity term via `duplicatedIdentity_diamond`.
- Added explicit associator and triangle witnesses via `duplicatedIdentity_associator` and `duplicatedIdentity_triangle`.
- Proved non-definitional inequality between parallel 2-cells via `duplicatedIdentity_parallel_2cells_ne`.
- Proved truncation compatibility via `churchOne_truncates_to_TH` and `duplicatedIdentity_path_truncations_agree`.
- Re-exported the `K∞` separation example as `beta_eta_points_distinct_in_KInfinity`.

## Issue 8: Publishable theorem index and manuscript sync

Status: done

Goal:
Make the manuscript precise about what is formalized and what remains future work.

Likely files:

- `/Users/arthur/LocalRepos/HigherLambdaModel/docs/theorem_index.md`
- `/Users/arthur/LocalRepos/HigherLambdaModel/docs/closure_backlog.md`
- `/Users/arthur/LocalRepos/HigherLambdaModel/README.md`
- `/Users/arthur/LocalRepos/HigherLambdaModel/paper/K_infinity_homotopy_lambda_model.pdf`

Acceptance criteria:

1. The manuscript cites theorem names or file locations for formalized claims.
2. Any remaining conjectural statements are explicitly labeled.
3. The paper no longer implies closure beyond what the Lean code proves.

Completed work:

- Rewrote `docs/theorem_index.md` so each major paper claim has an explicit row with source section, Lean file, declaration name, and status.
- Kept all unformalized claims visible and labeled `partial` or `missing`.
- Updated `README.md` to reflect the current repository counts and to distinguish completed backlog work from remaining paper-level gaps.
- Corrected this backlog so it matches the actual repository assets. The checkout contains `paper/K_infinity_homotopy_lambda_model.pdf`; there is no local `paper/manuscript.tex`.

## Execution order

1. Issue 0: materialize the repository locally.
2. Issue 1: stabilize build and CI.
3. Issue 2: create the paper-to-Lean claim matrix.
4. Issue 3: unify the canonical omega/infinity-groupoid API.
5. Issue 4: complete the higher-conversion algebra.
6. Issue 5: prove the generic coherence theorem.
7. Issue 6: instantiate the theorem stack for `K_\infty`.
8. Issue 7: add the non-trivial example suite.
9. Issue 8: publish the theorem index and sync the public docs to the Lean state.
