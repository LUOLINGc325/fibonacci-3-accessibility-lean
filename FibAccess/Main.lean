import FibAccess.Step

/-!
# The main combinatorial argument

Any `F`-diffsequence `x` with all terms of one colour yields a directed walk of
length `19` in the Cayley graph of `ℤ/232` with steps in `S` (Lemma 2 of the
paper).  The colouring `colourOf` and height `rk` from `FibAccess/Data.lean`
make every monochromatic step strictly increase the height, while the height is
at most `18`; this rules out a walk with `19` vertices.
-/

namespace FibAccess

/-- The colouring of `ℕ` induced by `rho`. -/
noncomputable def c (n : ℕ) : Fin 3 := colourOf (rho n)

lemma rho_lt (n : ℕ) : rho n < 232 := Nat.mod_lt _ (by norm_num)

theorem theorem1_aux :
    ∃ c : ℕ → Fin 3, ∀ x : ℕ → ℕ, IsDiffSeq F 19 x → ¬ Mono c 19 x := by
  refine ⟨c, ?_⟩
  intro x hseq hmono
  -- Each consecutive pair of terms gives a step in `S`.
  have hstep : ∀ i, i < 18 → ∃ s ∈ S, rho (x (i + 1)) = (rho (x i) + s) % 232 := by
    intro i hi
    have hlt : i + 1 < 19 := by omega
    have hd := hseq.2 i hlt
    have hsum : x i + (x (i + 1) - x i) = x (i + 1) := by omega
    obtain ⟨s, hs, hrel⟩ := rho_step (x i) (x (i + 1) - x i) hd.2
    exact ⟨s, hs, by simpa [hsum] using hrel⟩
  -- The height strictly increases along each monochromatic step.
  have hrstep : ∀ i, i < 18 → rk (rho (x i)) < rk (rho (x (i + 1))) := by
    intro i hi
    obtain ⟨s, hs, hrel⟩ := hstep i hi
    have hsL : s ∈ Slist := (mem_S_iff s).mp hs
    obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hsL
    let si : Fin 25 := ⟨idx, by simpa [Slist_length] using hidx⟩
    have hget' : Slist.get si = s := by
      simp only [si]
      exact hget
    let a : Fin 232 := ⟨rho (x i), rho_lt (x i)⟩
    have hval : (substep a si).val = rho (x (i + 1)) := by
      show (rho (x i) + Slist.get si) % 232 = rho (x (i + 1))
      rw [hget']
      exact hrel.symm
    have hc0 : c (x i) = c (x 0) := hmono i (by omega)
    have hc1 : c (x (i + 1)) = c (x 0) := hmono (i + 1) (by omega)
    have hceq : colourOf (rho (x (i + 1))) = colourOf (rho (x i)) := by
      have h : c (x (i + 1)) = c (x i) := by rw [hc1, hc0]
      exact h
    have hcol : colourOf (substep a si) = colourOf a := by
      rw [hval]
      exact hceq
    have hr := rank_edge a si hcol
    simpa [a, hval] using hr
  -- Hence the height increases by at least one along the whole walk.
  have hchain : ∀ i, i ≤ 18 → rk (rho (x 0)) + i ≤ rk (rho (x i)) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have hj18 : j < 18 := by omega
      have h1 := ih (by omega)
      have h2 := hrstep j hj18
      show rk (rho (x 0)) + (j + 1) ≤ rk (rho (x (j + 1)))
      omega
  have h18 := hchain 18 (by norm_num)
  have hle : rk (rho (x 18)) ≤ 18 := rk_le ⟨rho (x 18), rho_lt (x 18)⟩
  have hpos : 1 ≤ rk (rho (x 0)) := rk_pos ⟨rho (x 0), rho_lt (x 0)⟩
  omega

theorem main_aux : ¬ Accessible F 3 := by
  intro hacc
  obtain ⟨c, hc⟩ := theorem1_aux
  obtain ⟨x, hx, hm⟩ := hacc c 19
  exact hc x hx hm

theorem main_nonvacuous_aux : Accessible F 1 := by
  intro c k
  refine ⟨fun i => i + 1, ?_, ?_⟩
  · constructor
    · intro i _
      change 0 < i + 1
      omega
    · intro i _
      constructor
      · change i + 1 < i + 1 + 1
        omega
      · have hd : i + 1 + 1 - (i + 1) = 1 := by omega
        rw [hd]
        exact ⟨1, by norm_num, Nat.fib_one⟩
  · intro i _
    exact Subsingleton.elim _ _

end FibAccess
