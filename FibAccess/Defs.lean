import Mathlib

/-!
# Definitions for arXiv:2609.33744

W. J. Wesley, "The Fibonacci numbers are not 3-accessible" (Introduction and Section 2 of the paper).
-/

namespace FibAccess

/-- The Fibonacci numbers `F = {f_n : n ≥ 1} = {1, 2, 3, 5, 8, …}` (paper §2: `f₀ = 0`, `f₁ = 1`). -/
def F : Set ℕ := {d | ∃ n, 1 ≤ n ∧ Nat.fib n = d}

/-- `x 0 < x 1 < ⋯ < x (k - 1)` are positive integers whose consecutive differences lie in `D`:
a `k`-term `D`-diffsequence in `ℤ⁺`. Terms with index `≥ k` are ignored. -/
def IsDiffSeq (D : Set ℕ) (k : ℕ) (x : ℕ → ℕ) : Prop :=
  (∀ i, i < k → 0 < x i) ∧ ∀ i, i + 1 < k → x i < x (i + 1) ∧ x (i + 1) - x i ∈ D

/-- The first `k` terms of `x` all receive the colour of `x 0`. -/
def Mono {r : ℕ} (c : ℕ → Fin r) (k : ℕ) (x : ℕ → ℕ) : Prop :=
  ∀ i, i < k → c (x i) = c (x 0)

/-- `D` is `r`-accessible: every `r`-colouring of `ℤ⁺` contains arbitrarily long monochromatic
`D`-diffsequences. Colourings are given on `ℕ`; the colour of `0` is never used. -/
def Accessible (D : Set ℕ) (r : ℕ) : Prop :=
  ∀ c : ℕ → Fin r, ∀ k : ℕ, ∃ x : ℕ → ℕ, IsDiffSeq D k x ∧ Mono c k x

end FibAccess
