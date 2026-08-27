# Palomar verification project

This directory is the self-contained Lean project used for the Palomar
submission. It mirrors the compact proposition-level Challenge/Solution
surface at the repository root while keeping the registry replay independent
of the repository's larger development dependencies. The surface uses a
chosen restricted exponential of semantic morphisms; it does not identify that
exponential with the full set-theoretic endomap space. `ExtensionalKanComplex`
records the carrier/exponential interface, while
`CertifiedExtensionalKanComplex` separately certifies representation of the
term-generated bodies used by the beta/eta interpretation. The checked-in
`boolExtensionalCandidate_nontrivial` theorem witnesses two distinct vertices
of the restricted carrier interface. The directory pins its own Lean toolchain
so it remains self-contained if the main development moves to a different
toolchain later.

Submit this project with:

- Project directory: `palomar`
- Comparator configuration: `comparator.json`
- Formalization metadata: the repository-root `formalization.yaml`

The root files remain the canonical development surface for local CI; these
files provide the reproducible, minimal verification boundary described in
`formalization.yaml`.
