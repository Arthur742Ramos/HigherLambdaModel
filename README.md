# Higher Lambda Model

<div align="center">

**A Lean 4 formalization of higher-dimensional structure in the untyped lambda calculus**

[![Lean 4](https://img.shields.io/badge/Lean-4.24.0-blue?logo=lean)](https://lean-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](./LICENSE)
[![arXiv](https://img.shields.io/badge/arXiv-2111.07092-b31b1b.svg)](https://arxiv.org/abs/2111.07092)

*Formalizing "The Theory of an Arbitrary Higher Lambda-Model" by Martinez-Rivillas and de Queiroz*

</div>

---

## Overview

This project reveals a surprising truth: **the untyped lambda calculus has hidden homotopic structure**.

In classical lambda calculus, two terms are beta-eta equivalent if *some* reduction path connects them. But this view discards important structure: there may be **many different paths** between terms, and these paths themselves can be related by **homotopies**.

```
         M                    The space of reductions
        /|\                   forms a weak omega-groupoid:
       / | \
      /  |  \                 - 0-cells: Lambda terms
     p   q   r                - 1-cells: Reduction sequences
      \  |  /                 - 2-cells: Homotopies between paths
       \ | /                  - n-cells (n >= 3): Trivial (extensionality)
        \|/
         N
```

**Main Theorem (TH_lambda = HoTFT):** Every equation provable in classical lambda calculus is valid in all homotopic lambda-models (extensional Kan complexes).

## Key Results Formalized

| Result | File | Description |
|--------|------|-------------|
| **Beta-Soundness** | `ExtensionalKan.lean` | `(lambda M) N = M[N]` in all models |
| **Eta-Soundness** | `ExtensionalKan.lean` | `lambda x. M x = M` when `x not in FV(M)` |
| **TH_lambda subset HoTFT** | `NTerms.lean` | Classical lambda-theory embeds in HoTFT |
| **Pi_n -> Sigma_n** | `NTerms.lean` | n-terms embed into n-conversions |
| **BetaEta Compatibility** | `BetaEtaConfluence.lean` | Constructive common-extension layer for parallel paths |

## The Tower of n-Conversions

The formalization captures the full hierarchy of higher conversions:

```lean
def NConversion : Nat -> Sort _
  | 0 => Term
  | 1 => Σ (M N : Term), ReductionSeq M N
  | 2 => Σ (M N : Term) (p q : ReductionSeq M N), Homotopy2 p q
  | 3 => Σ (M N : Term) (p q : ReductionSeq M N) (α β : Homotopy2 p q), Homotopy3 α β
  | n + 4 => PSigma (fun x : NConversion (n + 3) =>
      PSigma (fun y : NConversion (n + 3) => x = y))
```

Low dimensions are carried by explicit constructive witnesses. Above dimension 3,
the tower continues internally via Lean identity types instead of collapsing to a
dummy terminal object.

## Project Structure

```
HigherLambdaModel/
|-- Lambda/
|   |-- Term.lean              # De Bruijn lambda-terms, substitution
|   |-- Reduction.lean         # Beta/eta reduction, conversion
|   |-- HigherTerms.lean       # Explicit paths, homotopies, omega-groupoid
|   |-- ExtensionalKan.lean    # Kan complexes, interpretation, soundness
|   |-- NTerms.lean            # n-terms, n-conversions, main theorems
|   |-- SubstLemma.lean        # Substitution lemma for interpretation
|   |-- TruncationCore.lean    # h-levels and truncation
|   |-- BetaEtaConfluence.lean # Confluence via Metatheory
|   +-- Coherence.lean         # Higher coherence laws
+-- lakefile.toml              # Build configuration
```

**4,290+ lines** of verified Lean 4 code with **no sorrys**.

## Mathematical Background

### Extensional Kan Complexes

An **extensional Kan complex** is a model of lambda calculus where:

```lean
structure ExtensionalKanComplex extends ReflexiveKanComplex where
  -- Every object equals G(F(x)) - full extensionality
  epsilon : forall x, x = G (F x)
```

Here `F : K -> [K -> K]` extracts a function from an object, and `G : [K -> K] -> K` abstracts a function into an object. The eta law `F(G(f)) = f` plus extensionality `x = G(F(x))` ensures that objects *are* their functional behavior.

### Interpretation

Lambda terms are interpreted in any extensional Kan complex:

```lean
noncomputable def interpret (K : ReflexiveKanComplex)
    (rho : Nat -> K.Obj) : Term -> K.Obj
  | var n => rho n
  | app M N => K.app (interpret K rho M) (interpret K rho N)
  | lam M => K.G (fun f => interpret K (rho[f/0]) M)
```

The **soundness theorems** prove this interpretation respects beta and eta:

- **Beta**: `interpret K rho ((lam M) @ N) = interpret K rho (M[N])`
- **Eta**: `interpret K rho (lam (M @ var 0)) = interpret K rho M` (when 0 not free in M)

## Installation

### Prerequisites

- [Lean 4](https://lean-lang.org/) (v4.24.0 or compatible)
- [Lake](https://github.com/leanprover/lean4/tree/master/src/lake) (included with Lean)

### Building

```bash
git clone https://github.com/Arthur742Ramos/HigherLambdaModel.git
cd HigherLambdaModel
lake build
```

### Dependencies

Automatically fetched by Lake:

- [ComputationalPathsLean](https://github.com/Arthur742Ramos/ComputationalPathsLean) - Related path-theoretic infrastructure (not used directly by the current higher-cell core)
- [Metatheory](https://github.com/Arthur742Ramos/Metatheory) - External Church-Rosser/confluence development

## Examples

The formalization includes the standard lambda calculus combinators:

```lean
-- Identity: lambda x. x
def I : Term := lam (var 0)

-- K combinator: lambda x. lambda y. x
def K : Term := lam (lam (var 1))

-- S combinator: lambda x. lambda y. lambda z. x z (y z)
def S : Term := lam (lam (lam (app (app (var 2) (var 0)) (app (var 1) (var 0)))))

-- Fixed-point combinator Y
def Y : Term :=
  lam (app (lam (app (var 1) (app (var 0) (var 0))))
           (lam (app (var 1) (app (var 0) (var 0)))))

-- Church numerals, booleans, pairs...
def church (n : Nat) : Term := ...
def tru : Term := K
def fls : Term := lam (lam (var 0))
```

## Formalization Status

### Fully Proven

- [x] Core lambda calculus (terms, substitution, shifting)
- [x] Beta and eta reduction relations
- [x] Extensional Kan complex definitions
- [x] Interpretation and substitution lemma
- [x] Beta-soundness and eta-soundness
- [x] Single-step soundness with congruence
- [x] Main theorem: TH_lambda subset HoTFT
- [x] n-terms and n-conversions tower
- [x] Beta-confluence (via Metatheory library)
- [x] Constructive higher-cell/coherence layer for explicit βη paths

### Current Proof Status

The repository currently has no local `axiom`, `sorry`, or `admit` declarations
in its `.lean` sources. The remaining external proof-theoretic dependency of note
is `Metatheory`, which is used for the Church-Rosser transfer in
`ChurchRosserProof.lean`.

## Theory Summary

### Definition 2.9: Theory of a Kan Complex

```lean
def TheoryEq (K : ExtensionalKanComplex) (M N : Term) : Prop :=
  forall rho, interpret K rho M = interpret K rho N
```

### Definition 2.10: Homotopy Type-Free Theory

```lean
def HoTFT_eq (M N : Term) : Prop :=
  forall K : ExtensionalKanComplex, TheoryEq K M N
```

### Definition 3.2: Classical Lambda Theory

```lean
def TH_lambda_eq (M N : Term) : Prop :=
  BetaEtaConv M N
```

### Main Theorem

```lean
theorem TH_lambda_eq_subset_HoTFT (M N : Term) (h : M =betaeta N) :
    M =_HoTFT N
```

**Significance:** Classical lambda calculus faithfully embeds into homotopic models. The higher structure is a *conservative extension*.

## References

### Primary Source

> Martinez-Rivillas, A. and de Queiroz, R. (2021). *The Theory of an Arbitrary Higher Lambda-Model*. [arXiv:2111.07092](https://arxiv.org/abs/2111.07092)

### Background

- Barendregt, H. P. (1984). *The Lambda Calculus: Its Syntax and Semantics*. North-Holland.
- Hofmann, M. and Streicher, T. (1998). "The groupoid interpretation of type theory". *Twenty-five years of constructive type theory*.
- Lumsdaine, P. L. (2009). "Weak omega-categories from intensional type theory". *TLCA*.
- Univalent Foundations Program (2013). *Homotopy Type Theory*. Institute for Advanced Study.

### Related Formalizations

- [ComputationalPathsLean](https://github.com/Arthur742Ramos/ComputationalPathsLean) - Related computational-path infrastructure
- [Metatheory](https://github.com/Arthur742Ramos/Metatheory) - Rewriting theory and Church-Rosser

## Contributing

Contributions welcome! Particularly:

- Internalizing more of the confluence development currently imported from Metatheory
- Refining the higher-cell tower above dimension 3
- Adding more examples and applications
- Extending to typed lambda calculi
- Connecting to other formalizations of HoTT

## License

[MIT License](./LICENSE) - see LICENSE file for details.

## Acknowledgments

This formalization is based on the theoretical work of Martinez-Rivillas and de Queiroz. Thanks to Arthur Ramos for the Metatheory and related Lean infrastructure libraries.

---

<div align="center">

*All theorems mechanically verified by the Lean 4 proof assistant.*

</div>
