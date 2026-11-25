# erdos-1026-lean

A Lean 4 proof of `erdos_1026.variants.lower_bound` (Erdős Problem 1026) from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/ErdosProblems/1026.lean`): the constant 1/√2 is admissible.

The proof shows more. Every sequence of n ≥ 1 distinct positive reals has a monotone subsequence
with sum at least (∑ xᵢ)/√n, so every c ≤ 1 is admissible. The argument is the weighted
Erdős–Szekeres square-packing argument plus Cauchy–Schwarz.

Definitions and the statement are copied verbatim from formal-conjectures; Mathlib is pinned to
the same commit (`0df444a`, Lean v4.33.1). `lake build` checks everything; the theorem depends only
on `propext`, `Classical.choice` and `Quot.sound`.

The proof was written with AI assistance (Claude).
