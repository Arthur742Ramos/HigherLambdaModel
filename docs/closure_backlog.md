# Higher Lambda Model Closure Backlog

This document turns the omega-groupoid closure roadmap into an execution queue for this repository.

The broken iCloud-backed Desktop checkout is no longer the working baseline.
Active work now happens in `/Users/arthur/LocalRepos/HigherLambdaModel`, where
Git and Lean both work normally. Issues 0 and 1 are complete, issue 2 is
complete via `docs/theorem_index.md`, and issue 3 is now in progress.

## Definition of done

We will treat the omega-groupoid structure as "closed" only when the repository contains a machine-checked end-to-end theorem stack with the following shape:

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
- The document makes the main closure gaps explicit, including the full weak omega-groupoid claim, the missing `K_infinity equiv [K_infinity -> K_infinity]` equivalence, and the restricted 3-cell semantics.

## Issue 3: Canonical omega/infinity-groupoid API

Status: in progress

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

Progress so far:

- Added `HigherLambdaModel/Simplicial/OmegaGroupoid.lean` as the shared low-dimensional omega-groupoid interface.
- Rebased `LambdaOmegaGroupoidData` and `LambdaOmegaGroupoid` onto that shared interface.
- Added a generic `GlobularTower` and `ReflexiveGlobularTower` interface to the shared simplicial layer.
- `lake build` still succeeds after the extraction.

## Issue 4: Higher-conversion algebra on lambda terms

Status: in progress

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

Progress so far:

- Added recursive boundary operators `HigherTerms.Cell.source` and `HigherTerms.Cell.target` for the entire higher-cell tower.
- Proved generic globularity of the recursive tower via `HigherTerms.Cell.globular_source` and `HigherTerms.Cell.globular_target`.
- Exported these publicly as `NConversion.source` and `NConversion.target`, while preserving the old low-dimensional aliases `source0`, `source1`, `target0`, and `target1`.
- Added generic tower-level globularity lemmas `NConversion.globular_src` and `NConversion.globular_tgt`.
- Added new 3-dimensional globularity lemmas `globular_src_3` and `globular_tgt_3`.
- Rebased `LambdaTower` onto the generic `Simplicial.GlobularTower` interface.
- Rebased the legacy `Higher.lean` facade onto the canonical `lambdaOmegaGroupoid` interface instead of duplicating operations directly.
- Added boundary-aware semantic 3-simplex wrappers in `ExtensionalKan.lean` for the associator, left and right whiskering, and left and right unitors.
- Lifted those wrappers to the HoTFT layer, so the missing 3-cell constructors now have explicit modelwise tetrahedron targets even though they are not yet normalized into the restricted `Theory3` / `HoTFT3` interface.
- Added named boundary-aware semantic triangle and tetrahedron interfaces (`TheoryTriangle`, `TheoryTetrahedron`, `HoTFTTriangle`, `HoTFTTetrahedron`) so those 3-simplex witnesses are part of the public semantic API rather than ad hoc raw `K.Tetrahedron` values.
- Exported λ-side subset statements into that boundary-aware layer for interpreted associators, left and right unitors, and left and right whiskering of arbitrary explicit 2-cells.
- Added degenerate tetrahedron constructors for reflexive 2-cells on arbitrary semantic triangles, exposing the reflexive composite side of the boundary-aware 3-cell layer.
- Isolated `whiskerLeftRefl` at the HoTFT boundary-aware level as a pair of named tetrahedra with identical outer boundary: one for the whiskered reflexive 2-cell and one for the reflexive semantic composite. The remaining gap there is now a comparison between those two tetrahedra rather than the absence of semantic witnesses.
- Added a reusable horn-filling construction `KanComplex.tetrahedronPath3` for comparing compatible tetrahedra and lifting the result back to a semantic 3-cell via `TheoryTetrahedron.path3` and `HoTFTTetrahedron.path3`.
- Used that new comparison layer to normalize `whiskerLeftRefl` all the way into the existing `HoTFT3` interface via `homotopy2_whiskerLeftRefl_in_HoTFT3` and `Homotopy2_whiskerLeftRefl_subset_HoTFT3`.
- Added a more general boundary-aware 4-simplex comparison `KanComplex.tetrahedronComparisonTetrahedron` with semantic and HoTFT lifts (`TheoryTetrahedron.comparison`, `HoTFTTetrahedron.comparison`) for tetrahedra that still differ on one outer face.
- Applied that broader comparison to `whiskerRightRefl`, producing an explicit intermediate HoTFT tetrahedron witness `Homotopy2_whiskerRightRefl_subset_HoTFTTetrahedron` whose only remaining gap is final normalization into `HoTFT3`.

## Issue 5: Generic coherence theorem

Status: pending

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

## Issue 6: `K_\infty` as the principal instance

Status: pending

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

## Issue 7: Non-trivial example suite

Status: pending

Goal:
Turn the theory into executable evidence by proving a small set of named examples.

Suggested deliverable:

- `/Users/arthur/LocalRepos/HigherLambdaModel/HigherLambdaModel/KInfinity/Examples.lean`

Acceptance criteria:

1. At least three examples of distinct higher conversions are formalized.
2. At least one example proves non-equivalence of higher conversions.
3. At least one example shows compatibility with truncation to the ordinary theory.

## Issue 8: Publishable theorem index and manuscript sync

Status: pending

Goal:
Make the manuscript precise about what is formalized and what remains future work.

Likely files:

- `/Users/arthur/LocalRepos/HigherLambdaModel/paper/manuscript.tex`
- `/Users/arthur/LocalRepos/HigherLambdaModel/docs/theorem_index.md`

Acceptance criteria:

1. The manuscript cites theorem names or file locations for formalized claims.
2. Any remaining conjectural statements are explicitly labeled.
3. The paper no longer implies closure beyond what the Lean code proves.

## Execution order

1. Issue 0: materialize the repository locally.
2. Issue 1: stabilize build and CI.
3. Issue 2: create the paper-to-Lean claim matrix.
4. Issue 3: unify the canonical omega/infinity-groupoid API.
5. Issue 4: complete the higher-conversion algebra.
6. Issue 5: prove the generic coherence theorem.
7. Issue 6: instantiate the theorem stack for `K_\infty`.
8. Issue 7: formalize the non-trivial examples.
9. Issue 8: sync the manuscript with the formalization status.

## Immediate next action

Use the new intermediate `whiskerRightRefl` tetrahedron to design the final
normalization step into `HoTFT3`. The next proof cannot be a generic
contraction of an arbitrary loop-shaped `Path2 p p` to `reflPath2 p`, because
that is not available in a general Kan complex. The remaining gap is therefore
the specific normalization of the `whiskerRightRefl` tetrahedron using the
existing whiskering, composition, and unitor data already formalized here.

Separately, `whiskerLeftRefl` is now normalized at the direct semantic / HoTFT
layer, but it is not yet folded into the restricted `StructuralHomotopy3`
fragment. The missing bridge there is between structural whiskering along an
explicit reduction sequence (`reductionSeq_whiskerLeft_*`) and direct semantic
whiskering by the whole interpreted path.
