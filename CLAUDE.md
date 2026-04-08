# Claude Code Instructions for HigherLambdaModel

## Project Overview

This is a Lean 4 formalization of "The Theory of an Arbitrary Higher λ-Model" (arXiv:2111.07092). It formalizes extensional Kan complexes, higher βη-conversions, and the relationship between classical λ-theory and homotopic λ-models.

## CRITICAL: No Sorrys Allowed

**`sorry` is NEVER acceptable in this codebase.** Every theorem must be fully proven.

If a proof is difficult:
1. Break it into smaller lemmas
2. Use helper functions or auxiliary definitions
3. Simplify the statement if the current formulation is unprovable
4. If truly impossible, restructure the approach - but NEVER leave a sorry

When you encounter a sorry:
- Treat it as a blocking bug that must be fixed immediately
- Use subagents to parallelize proving independent cases
- Consider whether axioms are needed (and document why)

## Build Commands

```bash
lake build          # Build the project
lake clean          # Clean build artifacts
```

## Manager Pattern for Substantial Tasks

When given a substantial task with multiple independent parts, act as a **manager**:

### 1. Plan First
- Analyze the task and break it into independent subtasks
- Identify dependencies between subtasks
- Create a todo list with `TodoWrite`

### 2. Delegate to Subagents
For independent tasks, spawn subagents in parallel using the `Task` tool:

```
# Good: Launch multiple independent tasks in parallel
Task(subagent_type="Explore", prompt="Find all uses of BetaStep in the codebase")
Task(subagent_type="Explore", prompt="Find all uses of EtaStep in the codebase")

# Good: Use Plan agent for complex implementation planning
Task(subagent_type="Plan", prompt="Design the implementation for proving interpret_subst")
```

### 3. When to Use Subagents
- **Explore agent**: Codebase searches, understanding code structure
- **Plan agent**: Designing implementation strategies
- **general-purpose agent**: Complex multi-step tasks, writing code

### 4. When NOT to Use Subagents
- Simple single-file edits
- Sequential tasks with heavy dependencies
- Quick lookups (use Glob/Grep directly)

## Code Style

### Lean 4 Conventions
- Prefer `theorem` for Prop-valued results, `def` for data
- Use docstrings (`/-- ... -/`) for public definitions
- Group related definitions with `/-! ## Section Name -/`

### This Project's Patterns
- De Bruijn indices for λ-terms (no named variables)
- `Term.var n`, `Term.app M N`, `Term.lam M`
- Notation: `M @ N` for application, `ƛ M` for lambda, `M[N]` for substitution
- Reduction: `→βη` (single step), `→*βη` (multi-step), `=βη` (conversion)

## Key Files

| File | Purpose |
|------|---------|
| `Lambda/Term.lean` | λ-term syntax, substitution, shifting |
| `Lambda/Reduction.lean` | β/η-reduction relations |
| `Lambda/HigherTerms.lean` | Explicit reduction sequences, homotopies |
| `Lambda/ExtensionalKan.lean` | Extensional Kan complexes, interpretation |
| `Lambda/NTerms.lean` | n-conversions, n-terms, main theorems |
| `Lambda/SubstLemma.lean` | Substitution lemma for interpretation |
| `Lambda/BetaEtaConfluence.lean` | Confluence via Hindley-Rosen |
| `Lambda/TruncationCore.lean` | h-levels and truncation |
| `Lambda/Coherence.lean` | Higher coherence laws |

## Current State

### Completed (All Core Theorems Proven)
- Basic λ-calculus infrastructure (terms, substitution, shifting)
- Extensional Kan complex definitions
- **β-soundness theorem** (fully proven)
- **η-soundness theorem** (fully proven)
- **interpret_subst lemma** (fully proven)
- n-term/n-conversion tower
- **TH_λ= ⊆ HoTFT** main theorem (fully proven)
- β-confluence via Metatheory library
- βη-confluence via Hindley-Rosen lemma

### Axioms Used (Well-Justified)
| Axiom | Justification |
|-------|---------------|
| `church_rosser` | Standard result (provable via Metatheory isomorphism) |
| `ReductionSeq.inv` | Follows from Church-Rosser |
| `eta_diamond` | Eta has no critical pairs |
| `beta_eta_commute` | Standard commutation lemma |
| `CoherentExtensionalKanComplex.wlwrPath3` | WLWR interchange coherence (wr(wl(α)(η),δ) ~ assoc;wl(wr(η,δ));symm(assoc)); follows from Mac Lane coherence in a bicategory but axiomatized for extensional Kan complexes; automatically satisfied by all strict models |

### Potential Future Work
1. **Eliminate axioms**: Create term isomorphism with Metatheory to remove `church_rosser` axiom
2. **Extensions**: Typed lambda calculi, more examples
3. **Connections**: Link to other HoTT formalizations

## Example: Delegating Proof Work

For proving a lemma with multiple cases:

```markdown
I'll act as manager and delegate the cases:

1. Spawn agent for var case: "Prove interpret_subst for Term.var"
2. Spawn agent for app case: "Prove interpret_subst for Term.app"
3. Spawn agent for lam case: "Prove interpret_subst for Term.lam"

Then integrate results into the main proof.
```

## References

- Paper: https://arxiv.org/abs/2111.07092
- ComputationalPathsLean: https://github.com/Arthur742Ramos/ComputationalPathsLean
- Metatheory: https://github.com/Arthur742Ramos/Metatheory
- This project: https://github.com/Arthur742Ramos/HigherLambdaModel
