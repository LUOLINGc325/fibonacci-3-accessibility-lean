import FibAccess.Data

open Real
open scoped goldenRatio

noncomputable section

namespace FibAccess

def alpha : ℝ := 184 + 8 * φ

def aa (n : ℕ) : ℕ := 184 * Nat.fib n + 8 * Nat.fib (n + 1)
def A (n : ℕ) : ℕ := aa n % 232

def rho (n : ℕ) : ℕ := (⌊alpha * n⌋).toNat % 232

lemma alpha_mul_fib (n : ℕ) :
    alpha * (Nat.fib n : ℝ) =
      184 * (Nat.fib n : ℝ) + 8 * (Nat.fib (n + 1) : ℝ) - 8 * ψ ^ n := by
  have h := Real.fib_succ_sub_goldenRatio_mul_fib n
  unfold alpha
  linear_combination (-8 : ℝ) * h

lemma abs_psi_lt_one : |ψ| < 1 := by
  have h1 : -1 < ψ := Real.neg_one_lt_goldenConj
  have h2 : ψ < 0 := Real.goldenConj_neg
  rw [abs_of_neg h2]
  linarith

lemma abs_psi_lt_ratio : |ψ| < (13 : ℝ) / 20 := by
  have h2 : ψ < 0 := Real.goldenConj_neg
  rw [abs_of_neg h2]
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  unfold Real.goldenConj
  nlinarith

lemma abs_eight_psi_pow_lt_one {n : ℕ} (hn : 5 ≤ n) : |8 * ψ ^ n| < 1 := by
  have habs_le : |ψ| ^ n ≤ |ψ| ^ 5 :=
    pow_le_pow_of_le_one (abs_nonneg ψ) (le_of_lt abs_psi_lt_one) hn
  have hn5 : |ψ| ^ n < (13 / 20 : ℝ) ^ 5 :=
    lt_of_le_of_lt habs_le (pow_lt_pow_left₀ abs_psi_lt_ratio (abs_nonneg _) (by norm_num))
  rw [abs_mul, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 8)]
  have : 8 * |ψ| ^ n ≤ 8 * ((13 : ℝ) / 20) ^ 5 := by nlinarith
  have hnum : 8 * ((13 : ℝ) / 20) ^ 5 < 1 := by norm_num
  linarith

/-! ### alpha bounds -/

lemma alpha_gt : (196.8 : ℝ) < alpha := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  unfold alpha Real.goldenRatio
  nlinarith

lemma alpha_lt : alpha < 197 := by
  have hs : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  unfold alpha Real.goldenRatio
  nlinarith

lemma alpha_pos : 0 < alpha := lt_trans (by norm_num) alpha_gt

lemma floor_alpha_one : ⌊alpha * (1 : ℝ)⌋ = 196 := by
  rw [Int.floor_eq_iff]
  constructor <;> push_cast <;> linarith [alpha_gt, alpha_lt]

lemma floor_alpha_two : ⌊alpha * (2 : ℝ)⌋ = 393 := by
  rw [Int.floor_eq_iff]
  constructor <;> push_cast <;> linarith [alpha_gt, alpha_lt]

lemma floor_alpha_three : ⌊alpha * (3 : ℝ)⌋ = 590 := by
  rw [Int.floor_eq_iff]
  constructor <;> push_cast <;> linarith [alpha_gt, alpha_lt]

/-! ### modular membership helpers -/

lemma O_sub_S {x : ℕ} (h : x ∈ O) : x ∈ S := by
  simp only [O, Finset.mem_insert, Finset.mem_singleton] at h
  rw [mem_S_iff]
  simp only [Slist, List.mem_cons, List.not_mem_nil, or_false]
  omega

lemma Om1_sub_S {a : ℕ} (ha1 : 1 ≤ a) (h : a % 232 ∈ O) : (a - 1) % 232 ∈ S := by
  simp only [O, Finset.mem_insert, Finset.mem_singleton] at h
  rw [mem_S_iff]
  simp only [Slist, List.mem_cons, List.not_mem_nil, or_false]
  omega

lemma Op1_sub_S {a : ℕ} (h : a % 232 ∈ O) : (a + 1) % 232 ∈ S := by
  simp only [O, Finset.mem_insert, Finset.mem_singleton] at h
  rw [mem_S_iff]
  simp only [Slist, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-! ### orbit -/

lemma aa_rec (n : ℕ) : aa (n + 2) = aa n + aa (n + 1) := by
  unfold aa
  have h2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
  have h3 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := by
    have := Nat.fib_add_two (n := n + 1)
    simpa [show n + 1 + 2 = n + 3 by omega] using this
  simp only [h2, h3]
  omega

lemma A_rec (n : ℕ) : A (n + 2) = (A n + A (n + 1)) % 232 := by
  unfold A
  rw [aa_rec, Nat.add_mod]

lemma A_period : ∀ n, A (n + 7) = A n := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero => unfold A aa; norm_num [Nat.fib]
  | one => unfold A aa; norm_num [Nat.fib]
  | more n ih1 ih2 =>
    have h := A_rec (n + 7)
    have h2 := A_rec n
    rw [show n + 2 + 7 = n + 7 + 2 by omega, h, h2,
        show n + 7 + 1 = n + 1 + 7 by omega, ih1, ih2]

lemma A_mod7 (n : ℕ) : A n = A (n % 7) := by
  have hperiod : ∀ m k, A (m + 7 * k) = A m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, A_period]
      exact ih
  conv_lhs => rw [← Nat.mod_add_div n 7]
  exact hperiod _ _

lemma A_mem (n : ℕ) : A n ∈ O := by
  rw [A_mod7]
  have hlt : n % 7 < 7 := Nat.mod_lt _ (by norm_num)
  interval_cases h : n % 7 <;> decide

/-! ### floor of alpha * fib n -/

lemma one_le_aa {n : ℕ} (hn : 1 ≤ n) : 1 ≤ aa n := by
  unfold aa
  have h : 0 < Nat.fib n := by rw [Nat.fib_pos]; omega
  omega

lemma floor_fib_ge5 {n : ℕ} (hn : 5 ≤ n) :
    ⌊alpha * (Nat.fib n : ℝ)⌋ = (aa n : ℤ) ∨
    ⌊alpha * (Nat.fib n : ℝ)⌋ = (aa n : ℤ) - 1 := by
  have h := alpha_mul_fib n
  have ht : |8 * ψ ^ n| < 1 := abs_eight_psi_pow_lt_one hn
  have ht1 : 8 * ψ ^ n < 1 := (abs_lt.mp ht).2
  have ht2 : -1 < 8 * ψ ^ n := (abs_lt.mp ht).1
  have hcast : ((aa n : ℕ) : ℝ) = 184 * (Nat.fib n : ℝ) + 8 * (Nat.fib (n + 1) : ℝ) := by
    unfold aa; push_cast; ring
  have hval : alpha * (Nat.fib n : ℝ) = (aa n : ℝ) - 8 * ψ ^ n := by
    rw [h, hcast]
  by_cases hlt : alpha * (Nat.fib n : ℝ) < (aa n : ℝ)
  · right
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩ <;> push_cast <;> linarith
  · left
    push Not at hlt
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · push_cast; exact hlt
    · push_cast; linarith


/-! ### small n floors -/

lemma floor_fib_one : ⌊alpha * (Nat.fib 1 : ℝ)⌋ = 196 := by
  simpa using floor_alpha_one

lemma floor_fib_two : ⌊alpha * (Nat.fib 2 : ℝ)⌋ = 196 := by
  simpa using floor_alpha_one

lemma floor_fib_three : ⌊alpha * (Nat.fib 3 : ℝ)⌋ = 393 := by
  have h : (Nat.fib 3 : ℝ) = 2 := by norm_num [Nat.fib]
  rw [h]; exact floor_alpha_two

lemma floor_fib_four : ⌊alpha * (Nat.fib 4 : ℝ)⌋ = 590 := by
  have h : (Nat.fib 4 : ℝ) = 3 := by norm_num [Nat.fib]
  rw [h]; exact floor_alpha_three

lemma floor_fib_small_mem {n : ℕ} (hn1 : 1 ≤ n) (hn4 : n ≤ 4) :
    (⌊alpha * (Nat.fib n : ℝ)⌋).toNat % 232 ∈ S ∧
    ((⌊alpha * (Nat.fib n : ℝ)⌋).toNat + 1) % 232 ∈ S := by
  interval_cases n
  · rw [floor_fib_one]; decide
  · rw [floor_fib_two]; decide
  · rw [floor_fib_three]; decide
  · rw [floor_fib_four]; decide

lemma floor_value_mem {f : ℕ} (hf : f ∈ F) :
    (⌊alpha * (f : ℝ)⌋).toNat % 232 ∈ S ∧
    ((⌊alpha * (f : ℝ)⌋).toNat + 1) % 232 ∈ S := by
  unfold F at hf
  obtain ⟨n, hn1, rfl⟩ := hf
  by_cases h5 : 5 ≤ n
  · have hb := floor_fib_ge5 h5
    have ha1 : 1 ≤ aa n := one_le_aa (by omega)
    have hO : aa n % 232 ∈ O := A_mem n
    rcases hb with hb | hb
    · rw [hb]
      constructor
      · simpa using O_sub_S hO
      · simpa using Op1_sub_S hO
    · rw [hb]
      have htn : (((aa n : ℤ) - 1).toNat) = aa n - 1 := by
        change (((aa n : ℤ) - ((1 : ℕ) : ℤ)).toNat) = aa n - 1
        rw [Int.toNat_sub']; simp
      constructor
      · rw [htn]; exact Om1_sub_S ha1 hO
      · rw [htn]
        have hpred : aa n - 1 + 1 = aa n := by omega
        rw [hpred]; exact O_sub_S hO
  · exact floor_fib_small_mem hn1 (by omega)

/-! ### floor step -/

lemma floor_step (x f : ℕ) :
    ⌊alpha * ((x + f : ℕ) : ℝ)⌋ = ⌊alpha * (x : ℝ)⌋ + ⌊alpha * (f : ℝ)⌋ ∨
    ⌊alpha * ((x + f : ℕ) : ℝ)⌋ = ⌊alpha * (x : ℝ)⌋ + ⌊alpha * (f : ℝ)⌋ + 1 := by
  have hx0 : (0 : ℝ) ≤ alpha * (x : ℝ) - ((⌊alpha * (x : ℝ)⌋ : ℤ) : ℝ) := by
    have := Int.floor_le (alpha * (x : ℝ)); linarith
  have hx1 : alpha * (x : ℝ) - ((⌊alpha * (x : ℝ)⌋ : ℤ) : ℝ) < 1 := by
    have := Int.lt_floor_add_one (alpha * (x : ℝ)); linarith
  have hf0 : (0 : ℝ) ≤ alpha * (f : ℝ) - ((⌊alpha * (f : ℝ)⌋ : ℤ) : ℝ) := by
    have := Int.floor_le (alpha * (f : ℝ)); linarith
  have hf1 : alpha * (f : ℝ) - ((⌊alpha * (f : ℝ)⌋ : ℤ) : ℝ) < 1 := by
    have := Int.lt_floor_add_one (alpha * (f : ℝ)); linarith
  have hsum : alpha * ((x + f : ℕ) : ℝ) =
      (((⌊alpha * (x : ℝ)⌋ + ⌊alpha * (f : ℝ)⌋ : ℤ)) : ℝ) +
        ((alpha * (x : ℝ) - ((⌊alpha * (x : ℝ)⌋ : ℤ) : ℝ)) +
         (alpha * (f : ℝ) - ((⌊alpha * (f : ℝ)⌋ : ℤ) : ℝ))) := by
    push_cast; ring
  by_cases hlt : (alpha * (x : ℝ) - ((⌊alpha * (x : ℝ)⌋ : ℤ) : ℝ)) +
      (alpha * (f : ℝ) - ((⌊alpha * (f : ℝ)⌋ : ℤ) : ℝ)) < 1
  · left
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · rw [hsum]; push_cast; linarith
    · rw [hsum]; push_cast; linarith
  · right
    push Not at hlt
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · rw [hsum]; push_cast; linarith
    · rw [hsum]; push_cast; linarith

lemma rho_step (x f : ℕ) (hf : f ∈ F) :
    ∃ s ∈ S, rho (x + f) = (rho x + s) % 232 := by
  have hmem := floor_value_mem hf
  have hfpos : 0 < f := by
    unfold F at hf
    obtain ⟨n, hn1, rfl⟩ := hf
    rw [Nat.fib_pos]; omega
  have hA0 : (0 : ℤ) ≤ ⌊alpha * (x : ℝ)⌋ :=
    Int.floor_nonneg.mpr (mul_nonneg alpha_pos.le (by positivity))
  have hB0 : (0 : ℤ) ≤ ⌊alpha * (f : ℝ)⌋ :=
    Int.floor_nonneg.mpr (mul_pos alpha_pos (by exact_mod_cast hfpos)).le
  have hs := floor_step x f
  rcases hs with hs | hs
  · refine ⟨⌊alpha * (f : ℝ)⌋.toNat % 232, hmem.1, ?_⟩
    rw [rho, hs]
    have hto : (⌊alpha * (x : ℝ)⌋ + ⌊alpha * (f : ℝ)⌋).toNat =
        (⌊alpha * (x : ℝ)⌋).toNat + (⌊alpha * (f : ℝ)⌋).toNat :=
      Int.toNat_add hA0 hB0
    rw [hto, Nat.add_mod]
    simp only [rho]
  · refine ⟨((⌊alpha * (f : ℝ)⌋).toNat + 1) % 232, hmem.2, ?_⟩
    rw [rho, hs]
    have hto : (⌊alpha * (x : ℝ)⌋ + ⌊alpha * (f : ℝ)⌋ + 1).toNat =
        (⌊alpha * (x : ℝ)⌋).toNat + ((⌊alpha * (f : ℝ)⌋).toNat + 1) := by
      have hb0 : (0 : ℤ) ≤ ⌊alpha * (f : ℝ)⌋ + 1 := by linarith
      calc (⌊alpha * (x : ℝ)⌋ + ⌊alpha * (f : ℝ)⌋ + 1).toNat
          = ((⌊alpha * (x : ℝ)⌋ + ⌊alpha * (f : ℝ)⌋) + (1 : ℕ)).toNat := by norm_num
        _ = (⌊alpha * (x : ℝ)⌋ + ⌊alpha * (f : ℝ)⌋).toNat + 1 :=
            Int.toNat_add_nat (by linarith) 1
        _ = (⌊alpha * (x : ℝ)⌋).toNat + (⌊alpha * (f : ℝ)⌋).toNat + 1 := by
            rw [Int.toNat_add hA0 hB0]
        _ = (⌊alpha * (x : ℝ)⌋).toNat + ((⌊alpha * (f : ℝ)⌋).toNat + 1) := by omega
    rw [hto, Nat.add_mod]
    simp only [rho]


end FibAccess
