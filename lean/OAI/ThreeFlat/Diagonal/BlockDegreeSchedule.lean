import OAI.ThreeFlat.Diagonal.ShrinkIteration

namespace OAI
/-! # Fixing the degrees and lane budget for a compressor block

The base degree and the refresh loss are fixed before the number of
shrink steps. All later degrees can be taken from the same loop-free
expander family, including the last one used by refresh.
-/

namespace ThreeFlat.Diagonal

open scoped BigOperators Classical

/-- At this degree the floor loss in each of the four retained edge types
is at most one of the permitted 1024 parts of the new slot mass. -/
def shrinkThreshold (d : ℕ) := 1024 * (2^(2*d+1)*d*d)

def degreeIndex (q h : ℕ) : ℕ → ℕ
  | 0 => h+2
  | j+1 => shrinkThreshold (2*q^(degreeIndex q h j))

def blockDegree (q h j : ℕ) := 2*q^(degreeIndex q h j)

theorem degree_dyadic {q : ℕ} (dq : ∃ e : ℕ,q=2^e) (h j : ℕ) : ∃ a : ℕ, blockDegree q h j = 2^a := by
  obtain ⟨e,rfl⟩ := dq
  refine ⟨1+e*degreeIndex (2^e) h j,?_⟩
  simp [blockDegree, pow_add,pow_mul]

theorem degree_start {q : ℕ} (hq : 2 ≤ q) (h : ℕ) : h+2 ≤ blockDegree q h 0 := by
  have a := @Nat.lt_two_pow_self (h+2)
  have b := Nat.pow_le_pow_left hq (h+2)
  change h+2 ≤ 2*q^(h+2)
  omega

theorem degree_scale_le {q : ℕ} (hq : 2 ≤ q) (h i : ℕ) :
    ((2^(2*blockDegree q h i+1)*blockDegree q h i*blockDegree q h i : ℕ):ℝ)/blockDegree q h (i+1) ≤ 1/1024 := by
  let d := blockDegree q h i
  let r := shrinkThreshold d
  have a := @Nat.lt_two_pow_self r
  have b := Nat.pow_le_pow_left hq r
  have hn : 1024*(2^(2*d+1)*d*d) ≤ 2*q^r := by change r ≤ 2*q^r; omega
  change (_:ℝ)/(2*q^r:ℕ) ≤ 1/1024
  have hden : 0 < (2*q^r : ℕ) := by positivity
  rw [div_le_div_iff₀ (Nat.cast_pos.mpr hden) (by norm_num)]
  simpa only [Nat.cast_mul,Nat.cast_ofNat,one_mul,mul_comm,mul_left_comm,mul_assoc] using
    (Nat.cast_le (α := ℝ)).mpr hn

/-- Sufficiently many coordinates for color bits, port number, and tag
selection on a stage. The deliberately large tag field is a fixed
constant determined by the degree. -/
def tagBits (d : ℕ) := 2*d*((d+1)+(d+1)^2)+1

theorem tag_space (d : ℕ) : 2*d*((d+1)+(d+1)^2) < 2^tagBits d :=
  (Nat.lt_succ_self _).trans (@Nat.lt_two_pow_self (tagBits d))

/-- The number of consumed lane coordinates is fixed independently of
network size and of its term choices. -/
def laneCharge (q h s : ℕ) : ℕ :=
  (∑ j : Fin s, ((2*blockDegree q h j.val+1) + Nat.log2 (blockDegree q h j.val) + tagBits (blockDegree q h j.val))) +
    Nat.log2 (blockDegree q h s)

/-- Choose the number of shrink steps after fixing the cost of one refresh. -/
theorem choose_block_length {q h : ℕ} (_hq : 2≤q) (hh : 0<h) {γ : ℝ} (hg : 0 ≤ γ) :
    let d₀ := blockDegree q h 0
    let C := (d₀:ℝ) + 2*(2*γ*d₀/h+1)
    ∃ s : ℕ, 0<s ∧ C*(126/127 : ℝ)^s ≤ 1/4 := by
  apply SlotEnergy.exists_shrink_count
  positivity

end ThreeFlat.Diagonal

end OAI
