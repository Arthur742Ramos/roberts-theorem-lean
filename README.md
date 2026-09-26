# Roberts' Theorem in Lean 4

A Lean 4 / Mathlib formalization of **Roberts' theorem (1979)**:
on an unrestricted domain of valuations with three or more alternatives,
every dominant-strategy implementable social choice function is an
**affine maximizer**.

This is the capstone of a mechanism-design formalization program alongside
the VCG mechanism and the Green–Laffont characterization:
it says that affine maximizers are essentially all that dominant-strategy
implementation can achieve.

## Status

Work in progress. Milestones:

- M0: repository scaffold
- M1: core definitions (valuations, mechanisms, DSIC, affine maximizers)
- M2: taxation principle
- M3: affine prices and Roberts' theorem
- M4: Palomar Challenge/Solution packaging
- M5: Palomar submission

## Toolchain

Lean / Mathlib `v4.35.0-rc2`.
