# Roberts' Theorem in Lean 4

A Lean 4 / Mathlib formalization of **Roberts' theorem (1979)**:
on an unrestricted domain of valuations with three or more alternatives,
every onto dominant-strategy incentive compatible choice function is an
**affine maximizer**.

## Theorem

`Roberts.roberts_theorem`: For finite nonempty agent and alternative types
`N` and `A` with decidable equality and `3 ≤ Fintype.card A`, every mechanism
`M : Mechanism N A` with `IsDSIC M` and `Function.Surjective M.choiceFn`
satisfies `IsAffineMaximizer M.choiceFn`, where the latter asserts the
existence of nonnegative weights (not all zero) and alternative offsets such
that the choice function always selects an affine-score maximizer.

## Proof structure

The proof follows the modular route:

1. **Taxation principle** (`Roberts/Taxation.lean`): DSIC implies weak
   monotonicity (W-MON).
2. **S-MON reduction** (`Roberts/SMon.lean`): tie-breaking a W-MON choice
   function yields a strongly monotone (S-MON) rule. The key tie-set
   transport lemma is proved via an asymmetric simultaneous-bump
   construction (Lavi–Mu'alem–Nisan 2003).
3. **No-veto power** (`Roberts/NoVeto.lean`): S-MON + onto gives no-veto
   power for all-but-one agents.
4. **Two-agent case** (`Roberts/TwoAgent.lean`): affine price representation.
5. **Induction** (`Roberts/Induction.lean`): the n ≥ 3 step assembles global
   weights and offsets from fixed-report slices (Lemmas 9 and 10).

## Status

Complete. Zero `sorry`, zero custom axioms. The full development builds
with `lake build` (1527 jobs) and `Roberts.roberts_theorem` depends only on
the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Palomar packaging

`Challenge.lean` states the comparator definitions and theorem;
`Solution.lean` imports the verified library. `comparator.json` lists the
comparator names and permitted axioms. Run `scripts/verify-palomar.sh` for
the local declaration, build, axiom, sorry, comparator, and whitespace
checks.

## Toolchain

Lean / Mathlib `v4.35.0-rc2`.
