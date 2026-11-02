import STATEMENT

-- The endpoints have exactly these types (definitions in `FibAccess/Defs.lean`).
example : ¬ FibAccess.Accessible FibAccess.F 3 := FibAccess.main
example : ∃ c : ℕ → Fin 3, ∀ x : ℕ → ℕ, FibAccess.IsDiffSeq FibAccess.F 19 x → ¬ FibAccess.Mono c 19 x :=
  FibAccess.theorem1
example : FibAccess.Accessible FibAccess.F 1 := FibAccess.main_nonvacuous

#print axioms FibAccess.main
#print axioms FibAccess.theorem1
#print axioms FibAccess.main_nonvacuous
