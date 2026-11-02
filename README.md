# fibonacci-3-accessibility-lean

A Lean 4 formalization of the main result of
**"The Fibonacci numbers are not 3-accessible"** by William J. Wesley
([arXiv:2609.33744v1](https://arxiv.org/abs/2609.33744)), relying only on the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`).

> **Attribution.** The mathematics is the work of the paper's author. This repository is an independent
> formalization, not affiliated with or endorsed by the author. The Lean proofs were written by AI coding agents
> (DeepSeek models in an agent harness) under the direction of the repository owner (LUOLINGc325), as part of an
> experiment on AI-driven formalization; the definitions and theorem statements were fixed by the owner beforehand.

## What is formalized

All definitions are in [`FibAccess/Defs.lean`](FibAccess/Defs.lean) and the three theorems in
[`spec/STATEMENT.lean`](spec/STATEMENT.lean).

- `F = {fₙ : n ≥ 1} = {1, 2, 3, 5, 8, …}`.
- `IsDiffSeq D k x`: `x 0 < x 1 < ⋯ < x (k-1)` are positive integers with consecutive differences in `D`.
- `Mono c k x`: the first `k` terms of `x` have the same colour under `c`.
- `Accessible D r`: every `r`-colouring of the positive integers contains arbitrarily long monochromatic
  `D`-diffsequences (colourings are given on `ℕ`; the colour of `0` is never used).

```lean
theorem main : ¬ Accessible F 3                                                   -- doa(F) = 2 (upper bound)
theorem theorem1 : ∃ c : ℕ → Fin 3, ∀ x : ℕ → ℕ, IsDiffSeq F 19 x → ¬ Mono c 19 x  -- Theorem 1
theorem main_nonvacuous : Accessible F 1                                          -- sanity check
```

The proof follows the paper: `α = 184 + 8φ`, `ρ(n) = ⌊αn⌋ mod 232`, the difference set `S` (Lemma 2/3), and a
finite check on the Cayley digraph of `ℤ/232`, done in the kernel with a height certificate that strictly decreases
along same-colour edges.

## Note on the colouring

The paper's proof ends with: the longest paths in `G[C₁]`, `G[C₂]`, `G[C₃]` have 19, 18 and 14 vertices, "so the
longest possible length of a monochromatic diffsequence is at most 19". This bounds monochromatic sequences by 19
terms, i.e. it excludes 20-term sequences, while Theorem 1 states that 19-term sequences are excluded.
The formalization uses the paper's colouring with the single residue `68` moved from `C₁` to `C₃`; the longest
paths then have 18, 18 and 14 vertices, so Theorem 1 holds exactly as stated (see
[`FibAccess/Data.lean`](FibAccess/Data.lean)). `doa(F) = 2` is unaffected either way.
(A direct search over `[1, 400000]` with the paper's original colouring found no monochromatic `F`-diffsequence
longer than 14 terms, so the gap concerns the stated argument, not necessarily the paper's colouring.)

## Verification

The [build workflow](.github/workflows/build.yml) builds everything from a clean checkout (Mathlib from its official
cache), fails on any `sorry` warning or forbidden token (`sorry`, `admit`, `native_decide`, `implemented_by`,
`extern`, `skipKernelTC`, `axiom`), checks the exact types of the three theorems
([`scripts/CheckStatement.lean`](scripts/CheckStatement.lean)) and that they depend only on `propext`,
`Classical.choice` and `Quot.sound`.

```sh
lake exe cache get
lake build
lake env lean scripts/CheckStatement.lean
```

Toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0` (`56a005855ea17e0b0958f73ec801ae140b0a1679`).

## License

Apache-2.0, see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
