# Higher Lambda Model Theorem Index

This document is the repository's paper-to-Lean claim matrix for the current
`master` branch. Every major theorem or construction from the two source papers
appears below with a Lean location, a representative declaration name, and an
explicit status.

Unformalized claims are kept visible and marked `partial` or `missing` rather
than omitted.

Status legend:

- `done`: a direct Lean declaration matching the claim exists and the current
  repository builds.
- `partial`: the repository contains a weaker, chosen-data, low-dimensional, or
  otherwise incomplete shadow of the paper claim.
- `missing`: no corresponding declaration was found in the current repository.

## Theory paper: `The Theory of an Arbitrary Higher λ-Model`

| Claim | Source paper section | Lean file | Declaration(s) | Status | Notes |
| --- | --- | --- | --- | --- | --- |
| Reflexive/extensional Kan complexes and interpretation of λ-terms | §2, Defs. 2.7, 2.9, 2.10 | `HigherLambdaModel/Lambda/ExtensionalKan.lean` | `ReflexiveKanComplex`, `ExtensionalKanComplex`, `interpret`, `interpret_subst` | `done` | The semantic model and substitution-compatible interpretation are formalized directly. |
| β- and η-soundness of the interpretation | §2, semantic soundness development | `HigherLambdaModel/Lambda/ExtensionalKan.lean` | `beta_sound`, `eta_sound`, `betaStep_sound`, `etaStep_sound`, `betaEtaStep_sound`, `reductionSeq_sound` | `done` | The repository proves soundness both for primitive steps and explicit conversion paths. |
| Theory of an extensional Kan complex and HoTFT | §2, Defs. 2.9 and 2.10 | `HigherLambdaModel/Lambda/ExtensionalKan.lean` | `TheoryEq`, `HoTFT_eq`, `HoTFT1`, `HoTFT2`, `HoTFT3`, `HoTFT4` | `done` | Both the proposition-level theory and the proof-relevant HoTFT layers are present. |
| Tower of n-conversions `Σₙ` with explicit boundaries and globularity | §3, Def. 3.1 | `HigherLambdaModel/Lambda/NTerms.lean`, `HigherLambdaModel/Lambda/HigherTerms.lean` | `NConversion`, `NConversion.source`, `NConversion.target`, `NConversion.globular_src`, `NConversion.globular_tgt`, `lambdaTower` | `done` | The higher-conversion tower is constructive through the explicit low dimensions and recursive above them. |
| Classical λ-theory `TH_λ=` | §3, Def. 3.2 | `HigherLambdaModel/Lambda/NTerms.lean` | `TH_lambda_eq` | `done` | Classical βη-convertibility is formalized exactly as the paper's proposition-level theory. |
| n-terms `Πₙ`, higher λ-abstraction, and the primitive `β₁` / `η₁` terms | §3, Def. 3.3 and Prop. 3.2 | `HigherLambdaModel/Lambda/NTerms.lean` | `NTerm1`, `NTerm`, `higherLam1`, `beta1Term`, `eta1Term` | `done` | The computational witnesses for higher conversions are internalized directly. |
| Embedding `Πₙ ⊆ Σₙ` | §3, Prop. 3.4 | `HigherLambdaModel/Lambda/NTerms.lean` | `NTerm.toNConversion`, `pi_subset_sigma` | `done` | Every packaged n-term is sent to the corresponding n-conversion. |
| Classical theory embeds into HoTFT: `TH_λ= ⊆ HoTFT` | §3, corollary after Prop. 3.4 | `HigherLambdaModel/Lambda/NTerms.lean` | `TH_lambda_eq_subset_HoTFT`, `TH_lambda_eq_subset_HoTFT1` | `done` | This is the repository's main proposition-level theorem for the theory paper. |
| Semantic HoTFT 2-cells for explicit syntactic 2-cells | §3, higher semantic interpretation | `HigherLambdaModel/Lambda/ExtensionalKan.lean`, `HigherLambdaModel/Lambda/NTerms.lean` | `homotopy2_in_HoTFT2`, `Homotopy2_subset_HoTFT2` | `done` | Arbitrary explicit syntactic 2-cells are interpreted proof-relevantly. |
| Semantic HoTFT 3-cells for explicit syntactic 3-cells | §3, higher semantic interpretation | `HigherLambdaModel/Lambda/HigherTerms.lean`, `HigherLambdaModel/Lambda/ExtensionalKan.lean`, `HigherLambdaModel/Lambda/NTerms.lean` | `StructuralHomotopy3`, `structuralHomotopy3_in_HoTFT3`, `StructuralHomotopy3_subset_HoTFT3`, `homotopy2_whiskerLeftRefl_in_HoTFT3`, `homotopy2_whiskerRightRefl_in_HoTFT3` | `partial` | The structural 3-cell fragment and the direct reflexive whiskering laws are interpreted all the way into `HoTFT3`, but the full primitive `Homotopy3Deriv` language is not yet given a direct semantic interpretation. |
| Weak ω-groupoid/coherence package on higher λ-conversions | §3, weak ω-groupoid presentation of higher conversions | `HigherLambdaModel/Simplicial/OmegaGroupoid.lean`, `HigherLambdaModel/Lambda/Coherence.lean`, `HigherLambdaModel/Lambda/TruncationCore.lean`, `HigherLambdaModel/Lambda/Truncation.lean` | `OmegaGroupoid`, `lambdaOmegaGroupoid`, `pentagon`, `triangle`, `interchange`, `AdmissibleHigherLambdaModel`, `higherConversions_form_omegaGroupoid`, `lambdaAdmissibleHigherLambdaModel`, `lambda_higher_conversions_form_omegaGroupoid`, `lambda_generic_coherence_0_truncation` | `partial` | The canonical API, generic coherence packaging, and 0-truncation recovery theorem are formalized. The current repository still packages the ω-groupoid through explicit coherence up to 5-cells plus recursive identity types above that level, rather than a standalone all-dimensional constructive calculus. |

## `K∞` paper: `The K∞ Homotopy λ-Model`

| Claim | Source paper section | Lean file | Declaration(s) | Status | Notes |
| --- | --- | --- | --- | --- | --- |
| Projective-limit infrastructure and the inverse-limit presentation of `K∞` | §3, Def. 3.10 and §4, Rem. 4.2 | `HigherLambdaModel/Domain/CHPO.lean`, `HigherLambdaModel/KInfinity/Construction.lean` | `Projective.System`, `Projective.Thread`, `Projective.KInfinity`, `system`, `KInfinityCHPO`, `projectToLevel`, `projectContinuous` | `done` | The inverse-limit c.h.p.o. used for `K∞` is formalized directly in the repository. |
| Homotopy Scott domains and self-exponential closure | §3, Def. 3.12 and Prop. 3.14 | `HigherLambdaModel/Domain/ScottDomain.lean`, `HigherLambdaModel/KInfinity/Properties.lean` | `HomotopyScottDomain`, `boundedComplete_exponential`, `exponentialScottDomainOfFiniteStepBasis`, `selfExponentialScottDomainOfFiniteStepBasis`, `stage_boundedComplete` | `partial` | The bounded-complete part is formalized generically and the chosen-data interface for Proposition 3.14 is present, but the full finite-step-basis hypothesis needed to recover the paper statement for every stage is not yet internalized for the concrete `Kₙ` tower. |
| Non-trivial Kan complexes and the sphere-summand model `N` | §4, Defs. 4.1, 4.2 and Ex. 4.1 | `HigherLambdaModel/KInfinity/NonTrivial.lean` | `HomotopyGroupKanComplex`, `IsNonTrivialKanComplex`, `SpherePoint`, `sphereHomotopyGroup`, `N`, `N_isNonTrivial` | `done` | The chosen-data non-triviality interface and the `N = ⨿ₙ Sⁿ` witness are fully formalized. |
| The flat c.h.p.o. `N⁺` | §4, Def. 4.3 | `HigherLambdaModel/KInfinity/NonTrivial.lean` | `NPlus`, `NPlusScottDomain`, `bottom0` | `done` | The base object `K₀ = N⁺` is implemented concretely. |
| Interface for non-trivial homotopy λ-models | §4, Def. 4.4 | `HigherLambdaModel/KInfinity/NonTrivial.lean` | `ReflexiveCHPO`, `NonTrivialHomotopyLambdaModel` | `done` | The repository contains the exact packaging interface used to state the paper's notion. |
| Sequence `K₀, K₁, ...` | §4, Def. 4.5 | `HigherLambdaModel/KInfinity/Construction.lean` | `K`, `K0`, `bottomAt` | `done` | The recursive tower `K₀ = N⁺`, `Kₙ₊₁ = [Kₙ → Kₙ]` is formalized directly. |
| Initial h-projection pair `(f₀⁺, f₀⁻)` | §4, Def. 4.6 | `HigherLambdaModel/KInfinity/Construction.lean` | `f0Plus`, `f0Minus`, `initialPair` | `done` | The initial projection pair is implemented exactly as an explicit continuous-map package. |
| Recursive h-projection pairs `(fₙ⁺, fₙ⁻)` | §4, Def. 4.7 | `HigherLambdaModel/KInfinity/Construction.lean` | `pair`, `fPlus`, `fMinus`, `fMinus_comp_fPlus`, `fPlus_fMinus_le` | `done` | The recursive projection-pair construction is fully formalized. |
| `K∞` as the repository's canonical admissible higher λ-model | §4, homotopy-λ-model packaging of `K∞` | `HigherLambdaModel/KInfinity/Properties.lean` | `kInfinityOmegaGroupoid`, `kInfinityTower`, `kInfinityAdmissibleHigherLambdaModel`, `kInfinityHigherConversionCoherence`, `kInfinity_higher_conversions_form_omegaGroupoid` | `done` | This is the repository's generic-coherence packaging of the concrete model. It is stronger than a bare construction of the tower, but it is not itself the paper's missing `K∞ ≃ [K∞ → K∞]` witness. |
| Proposition 4.1: `K∞` is a Homotopy Scott Domain | §4, Prop. 4.1 | `HigherLambdaModel/KInfinity/Properties.lean` | `stage_scottDomain_zero`, `stage_boundedComplete`, `Proposition41Witness`, `proposition_4_1` | `partial` | Lean records the stagewise bounded-complete data, coordinate projections, and a concrete compact approximation interface. The exact paper statement that `KInfinityCHPO` itself is a Homotopy Scott Domain is not yet proved verbatim. |
| Remark 4.2: fixed-point equivalence `K∞ ≃ [K∞ → K∞]` | §4, Rem. 4.2 | `HigherLambdaModel/KInfinity/NonTrivial.lean`, `HigherLambdaModel/KInfinity/Properties.lean` | `ReflexiveCHPO`, `kInfinityAdmissibleHigherLambdaModel` | `missing` | The interface and generic admissible-model packaging exist, but there is no explicit `ReflexiveCHPO KInfinityCHPO` instance and no declarations for the paper's equivalence maps `h` and `k`. |
| Proposition 4.2: `x ≃ supₙ f_{n,∞}(xₙ)` | §4, Prop. 4.2 | `HigherLambdaModel/KInfinity/Properties.lean` | `proposition_4_2_approximation`, `proposition_4_2` | `partial` | The current formalization proves the exactness of a chosen level-0 approximation, not the full paper-level homotopy-equivalence statement. |
| Proposition 4.3: formulas for the equivalences `h` and `k` | §4, Prop. 4.3 | `HigherLambdaModel/KInfinity/Properties.lean` | `kBase`, `proposition_4_3` | `partial` | Only the base-coordinate shadow is formalized; the actual maps `h : [K∞ → K∞] → K∞` and `k : K∞ → [K∞ → K∞]` are absent. |
| Remark 4.3: application in `K∞` | §4, Rem. 4.3 | `HigherLambdaModel/KInfinity/Properties.lean` | `application`, `remark_4_3` | `partial` | Application is defined only through the same base-coordinate shadow used for Proposition 4.3. |
| Proposition 4.4: `K∞` is a non-trivial homotopy λ-model | §4, Prop. 4.4 | `HigherLambdaModel/KInfinity/Properties.lean` | `KInfinityKanComplex`, `proposition_4_4` | `partial` | The non-trivial Kan-complex half is proved. The full paper statement is still blocked by the missing reflexive c.h.p.o. equivalence of Remark 4.2 / Definition 4.4. |
| Example 4.2: interpreted β- and η-contractions are non-equivalent in `K∞` | §4, Ex. 4.2 | `HigherLambdaModel/KInfinity/Properties.lean` | `s1Left`, `s1Right`, `interp1Eta`, `interp1Beta`, `example_4_2` | `partial` | Lean currently proves the separation of the chosen β-side and η-side points. The full interpreted β/η contraction argument and the resulting HoTFT-level non-2-conversion statement are not yet formalized. |

## Remaining Paper-Level Gaps

1. Extend the semantic 3-cell interpretation from the current structural
   fragment to the full primitive syntactic 3-cell language.
2. Replace the present low-dimensional ω-groupoid package with a direct
   all-dimensional constructive formalization, if the stronger paper reading is
   desired.
3. Construct the missing fixed-point equivalence `K∞ ≃ [K∞ → K∞]` and package
   it as `ReflexiveCHPO KInfinityCHPO`.
4. Upgrade the chosen-data shadows of Proposition 4.1, Proposition 4.2,
   Proposition 4.3, and Remark 4.3 to statements matching the paper text
   verbatim.
5. Strengthen Proposition 4.4 and Example 4.2 from their current chosen-data
   forms to the exact paper statements.
