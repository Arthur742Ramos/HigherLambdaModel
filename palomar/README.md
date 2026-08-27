# Palomar verification project

This directory is the self-contained Lean project used for the Palomar
submission. It mirrors the compact proposition-level Challenge/Solution
surface at the repository root while keeping the registry replay independent
of the repository's larger development dependencies.

Submit this project with:

- Project directory: `palomar`
- Comparator configuration: `comparator.json`
- Formalization metadata: the repository-root `formalization.yaml`

The root files remain the canonical development surface for local CI; these
files provide the reproducible, minimal verification boundary described in
`formalization.yaml`.
