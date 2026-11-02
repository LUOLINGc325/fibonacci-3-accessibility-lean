import FibAccess

/-!
# Endpoint statements for arXiv:2609.33744

W. J. Wesley, "The Fibonacci numbers are not 3-accessible". Definitions: `FibAccess/Defs.lean`.
The proofs are assembled from the modules under `FibAccess/`.
-/

namespace FibAccess

/-- Main result (abstract; Theorem 1, "In particular"): the Fibonacci numbers are not 3-accessible. -/
theorem main : ¬ Accessible F 3 :=
  main_aux

/-- Theorem 1: there is a 3-colouring of `ℤ⁺` with no monochromatic 19-term `F`-diffsequence. -/
theorem theorem1 : ∃ c : ℕ → Fin 3, ∀ x : ℕ → ℕ, IsDiffSeq F 19 x → ¬ Mono c 19 x :=
  theorem1_aux

/-- Non-vacuity: the notions are not degenerate, since `F` is 1-accessible. -/
theorem main_nonvacuous : Accessible F 1 :=
  main_nonvacuous_aux

end FibAccess
