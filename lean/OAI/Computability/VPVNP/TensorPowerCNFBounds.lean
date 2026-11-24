import OAI.Computability.VPVNP.TensorPowerCNF
import OAI.Computability.VPVNP.PaddedQuery
import Mathlib.Tactic.Ring

/-! # Input lengths for the tensor-power CNF

For fixed bit width and number of parties, the control-state count and payload
length grow at most exponentially in the number of tensor factors. The exponent
of the local dimension in the compiled input length is absolute.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TensorPowerCNF

/-- Uniform coefficient for the CNF width, literal count and query state count. -/
def sizeCoefficient (b d : ℕ) : ℕ := 4 * d + (2 ^ b) ^ d * (3 * (d * b) + 1) + 2

/-- Coefficient of the bound for the compiled table together with the payload. -/
def lengthCoefficient (b d : ℕ) : ℕ := 4001 * sizeCoefficient b d ^ 6

theorem lengthCoefficient_pos (b d : ℕ) : 0 < lengthCoefficient b d := by
  unfold lengthCoefficient sizeCoefficient
  positivity

private theorem width_bound {d b h u : ℕ} (hh : h ≤ u) (hbits : h * b ≤ u)
    (hpos : 0 < u) :
    d * (h * b) + d * u + h * (2 ^ b) ^ d + 1 ≤ sizeCoefficient b d * u ^ 2 := by
  have hco : 2 * d + (2 ^ b) ^ d + 1 ≤ sizeCoefficient b d := by
    unfold sizeCoefficient
    have := Nat.le_mul_of_pos_right ((2 ^ b) ^ d) (by omega : 0 < 3 * (d * b) + 1)
    omega
  calc
    _ ≤ d * u + d * u + u * (2 ^ b) ^ d + u :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left _ hbits) _)
        (Nat.mul_le_mul_right _ hh)) hpos
    _ = (2 * d + (2 ^ b) ^ d + 1) * u := by ring
    _ ≤ _ := Nat.mul_le_mul hco (by simpa using Nat.pow_le_pow_right hpos (by decide : 1 ≤ 2))

private theorem literal_bound {d b h u : ℕ} (hh : h ≤ u) (hbits : h * b ≤ u)
    (hpos : 0 < u) :
    d * u * (3 * (h * b) + 1) + h * (2 ^ b) ^ d * (3 * (d * b) + 1) + 2 ≤
      sizeCoefficient b d * u ^ 2 := by
  have hup : u ≤ u ^ 2 := by simpa using Nat.pow_le_pow_right hpos (by decide : 1 ≤ 2)
  have hfirst : 3 * (h * b) + 1 ≤ 4 * u := by omega
  calc
    _ ≤ d * u * (4 * u) + u ^ 2 * (2 ^ b) ^ d * (3 * (d * b) + 1) + 2 * (u ^ 2) := by
      apply Nat.add_le_add
      · exact Nat.add_le_add (Nat.mul_le_mul_left _ hfirst)
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (hh.trans hup)))
      · exact Nat.le_mul_of_pos_right _ (Nat.pow_pos hpos)
    _ = _ := by
      unfold sizeCoefficient
      ring

private theorem growth {b : ℕ} (hb : 0 < b) (h : ℕ) :
    h ≤ (2 ^ b) ^ h ∧ h * b ≤ (2 ^ b) ^ h := by
  have hbits : h * b ≤ (2 ^ b) ^ h := by
    rw [← pow_mul, Nat.mul_comm b h]
    exact (h * b).lt_two_pow_self.le
  exact ⟨(Nat.le_mul_of_pos_right _ hb).trans hbits, hbits⟩

private theorem compiledLength_bound {b d h k : ℕ} (φ : HardnessCNF.CNF k)
    (hwidth : k + 1 ≤ sizeCoefficient b d * ((2 ^ b) ^ h) ^ 2)
    (hlits : HardnessCNF.literalCount φ + 2 ≤ sizeCoefficient b d * ((2 ^ b) ^ h) ^ 2) :
    (UniversalMachine.programPrefix
      (QueryMachine.machine (HardnessCNF.query φ) (HardnessCNF.literalCount φ))).length + k ≤
        lengthCoefficient b d * ((2 ^ b) ^ 12) ^ h := by
  let q := QueryMachine.machine (HardnessCNF.query φ) (HardnessCNF.literalCount φ)
  have hstates : q.extra =
      (HardnessCNF.literalCount φ + 1) * Fintype.card (HardnessCNF.State φ) * (k + 1) := by
    simp [q, QueryMachine.machine, TableCompiler.compile, QueryMachine.Control, Nat.mul_assoc]
  have hprefix := UniversalMachine.programPrefix_length_le q
  rw [hstates] at hprefix
  have hcard := HardnessCNF.card_state φ
  have ht : HardnessCNF.literalCount φ + 1 ≤ sizeCoefficient b d * ((2 ^ b) ^ h) ^ 2 := by omega
  have hq : Fintype.card (HardnessCNF.State φ) ≤ sizeCoefficient b d * ((2 ^ b) ^ h) ^ 2 := by omega
  refine (queryInputLength_le hprefix ht hq hwidth).trans_eq ?_
  simp only [lengthCoefficient, mul_pow, ← pow_mul, Nat.mul_assoc]
  rw [Nat.mul_comm h 12]

/-- Bound for the payload width including one unit of control overhead. -/
theorem width_add_one_le (J : Type*) [Fintype J] (b h : ℕ) (hb : 0 < b) :
    width J b h + 1 ≤ sizeCoefficient b (Fintype.card J) * ((2 ^ b) ^ h) ^ 2 := by
  rw [width_eq]
  obtain ⟨hh, hbits⟩ := growth hb h
  exact width_bound hh hbits (by positivity)

/-- The CNF compiler needs one read state per literal and two halting states. -/
theorem literalCount_add_two_le (J : Type*) [Fintype J] (b h : ℕ) (hb : 0 < b) :
    HardnessCNF.literalCount (formula J b h) + 2 ≤
      sizeCoefficient b (Fintype.card J) * ((2 ^ b) ^ h) ^ 2 := by
  rw [literalCount_formula]
  obtain ⟨hh, hbits⟩ := growth hb h
  exact literal_bound hh hbits (by positivity)

/-- The entire table and payload fit at this length, uniformly in the tensor entries. -/
theorem compiledLength_le (J : Type*) [Fintype J] (b h : ℕ) (hb : 0 < b) :
    (UniversalMachine.programPrefix (QueryMachine.machine (HardnessCNF.query (formula J b h))
      (HardnessCNF.literalCount (formula J b h)))).length + width J b h ≤
        lengthCoefficient b (Fintype.card J) * ((2 ^ b) ^ 12) ^ h :=
  compiledLength_bound (formula J b h) (width_add_one_le J b h hb)
    (literalCount_add_two_le J b h hb)

/-- At every sufficiently large source length, the universal polynomial projects
onto the regrouped tensor power. The projection uses the entries of the given
tensor as scalar constants. -/
theorem projection {J R : Type*} [Fintype J] [CommRing R] {b : ℕ}
    (T : (J → Digit b) → R) (hb : 0 < b) (h n : ℕ)
    (hn : lengthCoefficient b (Fintype.card J) * ((2 ^ b) ^ 12) ^ h ≤ n) :
    ∃ φ : Projection R (Fin n × Bool) (J × Word b h),
      φ.hom (MvPolynomial.map (Int.castRingHom R) (P n)) = form T h := by
  rw [← weightedCNF_formula, HardnessCNF.weightedCNF_eq_query]
  exact weightedQuery_projection_at_length _ _ (weights T h) n
    ((compiledLength_le J b h hb).trans hn)

end TensorPowerCNF

end VPVNP
end Computability
end OAI
