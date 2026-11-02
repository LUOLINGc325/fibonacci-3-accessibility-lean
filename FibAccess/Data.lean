import FibAccess.Defs

/-!
# Data for the 3-colouring of `ℤ/232`

Definitions live in `FibAccess/Defs.lean`.  This file contains the concrete
finite data used by the proof: the set `S` of possible residues of
`⌊α(x+f)⌋ - ⌊αx⌋`, the colouring of `ℤ/232`, and a decreasing-height certificate
showing that each colour class is acyclic with longest directed path at most 18.
-/

namespace FibAccess

/-- The set `S` from the paper (Lemma 2). -/
def Slist : List ℕ :=
  [7, 8, 9, 55, 56, 57, 126, 127, 128, 129, 159, 160, 161, 162, 183, 184, 185,
   191, 192, 193, 196, 197, 199, 200, 201]

/-- `S` as a finite set. -/
def S : Finset ℕ := Slist.toFinset

lemma Slist_length : Slist.length = 25 := by decide

lemma mem_S_iff (s : ℕ) : s ∈ S ↔ s ∈ Slist := by simp [S]

/-- The orbit `O` of `n ↦ 184 f_n + 8 f_{n+1}` modulo 232. -/
def O : Finset ℕ := {8, 56, 128, 160, 184, 192, 200}

/-- Colour class 1 (the paper's `C₁`, with `68` moved to `C₃`). -/
def inC1 (r : ℕ) : Prop :=
  r ≤ 24 ∨ (87 ≤ r ∧ r ≤ 98) ∨ r = 125 ∨ r = 126 ∨ (148 ≤ r ∧ r ≤ 155) ∨
  (187 ≤ r ∧ r ≤ 196) ∨ (200 ≤ r ∧ r ≤ 217) ∨ r = 231

/-- Colour class 2 (the paper's `C₂`). -/
def inC2 (r : ℕ) : Prop :=
  (41 ≤ r ∧ r ≤ 55) ∨ (117 ≤ r ∧ r ≤ 124) ∨ (127 ≤ r ∧ r ≤ 143) ∨
  (156 ≤ r ∧ r ≤ 186) ∨ (218 ≤ r ∧ r ≤ 224)

instance (r : ℕ) : Decidable (inC1 r) := by unfold inC1; infer_instance
instance (r : ℕ) : Decidable (inC2 r) := by unfold inC2; infer_instance

/-- The 3-colouring `C` of `ℤ/232`; everything outside `C₁ ∪ C₂` is colour 2. -/
def colourOf (r : ℕ) : Fin 3 :=
  if inC1 r then 0 else if inC2 r then 1 else 2

/-- A height function on `ℤ/232`; on each colour class it is the length of the
longest directed path ending at the vertex. -/
def rkList : List ℕ :=
[
  1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 8, 8,
  8, 8, 8, 8, 8, 11, 11, 11, 15, 8, 8, 8, 9, 9, 9, 10,
  10, 10, 11, 11, 11, 12, 12, 12, 11, 4, 4, 4, 8, 8, 8, 8,
  11, 11, 11, 11, 11, 11, 14, 14, 3, 4, 4, 4, 4, 4, 5, 6,
  6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 7, 7, 8, 8, 8,
  9, 9, 9, 10, 10, 10, 11, 7, 5, 7, 7, 7, 7, 7, 10, 10,
  10, 14, 14, 2, 2, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 4,
  5, 5, 5, 5, 5, 7, 7, 7, 7, 10, 10, 10, 10, 6, 6, 13,
  13, 13, 13, 16, 16, 16, 16, 16, 16, 18, 18, 18, 17, 17, 17, 17,
  1, 1, 1, 1, 12, 12, 16, 16, 16, 16, 15, 15, 1, 1, 1, 1,
  1, 1, 1, 2, 2, 2, 2, 5, 5, 5, 9, 9, 9, 9, 12, 12,
  12, 12, 12, 12, 15, 15, 15, 15, 15, 14, 17, 2, 2, 3, 3, 3,
  3, 4, 4, 5, 5, 14, 14, 14, 9, 9, 9, 13, 13, 17, 17, 17,
  17, 17, 17, 16, 18, 18, 18, 18, 18, 18, 3, 3, 3, 3, 6, 6,
  6, 12, 12, 12, 13, 13, 13, 1
]

def rk (r : ℕ) : ℕ := rkList.getD r 0

/-- The successor of a residue by an element of `S`. -/
def substep (a : Fin 232) (s : Fin 25) : Fin 232 :=
  ⟨(a.val + Slist.get s) % 232, Nat.mod_lt _ (by norm_num)⟩

set_option maxRecDepth 1000000 in
/-- The height is at most 18 at every residue. -/
lemma rk_le (a : Fin 232) : rk a.val ≤ 18 := by
  revert a; decide

set_option maxRecDepth 1000000 in
/-- The height is at least 1 at every residue. -/
lemma rk_pos (a : Fin 232) : 1 ≤ rk a.val := by
  revert a; decide

set_option maxRecDepth 1000000 in
/-- Height strictly increases along every monochromatic edge of the Cayley graph. -/
lemma rank_edge (a : Fin 232) (s : Fin 25) :
    colourOf (substep a s) = colourOf a → rk a.val < rk (substep a s).val := by
  revert a s; decide

end FibAccess
