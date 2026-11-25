import OAI.Optimization.LinearProgramming.Compression.AffineRows
import OAI.Optimization.LinearProgramming.RAM.Basic
import Mathlib.Data.Nat.Log

/-! Bit lengths of individual products and partial affine sums in a scalar RAM. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open scoped BigOperators

def affineEvalBits (k B : ℕ) : ℕ := 3 + 2 * ((k + 1) + (2 * k + 3) * (B.log2 + 1))

theorem affineEvalBits_mono {k l B : ℕ} (h : k ≤ l) : affineEvalBits k B ≤ affineEvalBits l B := by
  unfold affineEvalBits; gcongr

private theorem log2_le_from_pow {x t : ℕ} (h : x ≤ 2 ^ t) : x.log2 ≤ t := by
  obtain rfl | h0 := eq_or_ne x 0
  · simp
  · exact Nat.le_of_lt_succ <| (Nat.log2_lt h0).mpr <|
      h.trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

theorem ratBits_affine_input (n : ℕ) (q : ℚ) {B : ℕ}
    (h : q.num.natAbs ≤ B ∧ q.den ≤ B) : RAM.ratBits q ≤ affineEvalBits n B := by
  have hn := log2_le_from_pow (h.1.trans B.lt_log2_self.le)
  have hd := log2_le_from_pow (h.2.trans B.lt_log2_self.le)
  calc
    _ ≤ affineEvalBits 0 B := by unfold RAM.ratBits affineEvalBits; omega
    _ ≤ _ := affineEvalBits_mono (Nat.zero_le n)

theorem ratBits_affine_product (a x : ℚ) {B : ℕ}
    (ha : a.num.natAbs ≤ B ∧ a.den ≤ B) (hx : x.num.natAbs ≤ B ∧ x.den ≤ B) :
    RAM.ratBits (a*x) ≤ affineEvalBits 0 B := by
  have hB : B * B ≤ 2 ^ ((B.log2+1) + (B.log2+1)) := by
    rw [pow_add]; exact Nat.mul_le_mul B.lt_log2_self.le B.lt_log2_self.le
  have hn : (a*x).num.natAbs ≤ B * B := by
    rw [Rat.mul_num]
    exact (Int.natAbs_ediv_le_natAbs _ _).trans <| by
      rw [Int.natAbs_mul]; exact Nat.mul_le_mul ha.1 hx.1
  have hd := (Nat.le_of_dvd (Nat.mul_pos a.pos x.pos) (Rat.mul_den_dvd a x)).trans
    (Nat.mul_le_mul ha.2 hx.2)
  have hn' := log2_le_from_pow (hn.trans hB)
  have hd' := log2_le_from_pow (hd.trans hB)
  unfold RAM.ratBits affineEvalBits
  omega

/-- Any set of already processed terms satisfies the same sum-height bound.
Taking a range of indices gives exactly the value of an affine accumulator. -/
theorem ratBits_affine_partial_sum {ι : Type*} (s : Finset ι) (a x : ι → ℚ) (e : ℚ) {B : ℕ}
    (hB : 1 ≤ B) (he : e.num.natAbs ≤ B ∧ e.den ≤ B)
    (ha : ∀ i ∈ s, (a i).num.natAbs ≤ B ∧ (a i).den ≤ B)
    (hx : ∀ i ∈ s, (x i).num.natAbs ≤ B ∧ (x i).den ≤ B) :
    RAM.ratBits (e + ∑ i ∈ s, a i * x i) ≤ affineEvalBits s.card B := by
  classical
  let F : AffineFamily Unit s := ⟨fun _ i => a i, fun _ => e⟩
  have habs (q : ℚ) (h : q.num.natAbs ≤ B) : |q| ≤ (B : ℚ) :=
    (rat_abs_le_num_natAbs _).trans (by exact_mod_cast h)
  obtain ⟨_, hn, hd⟩ := F.evalRat_height (fun i => x i) ()
    (fun j => ⟨habs _ (ha j j.property).1, (ha j j.property).2⟩)
    ⟨habs _ he.1, he.2⟩ (fun j => hx j j.property)
  simp only [AffineFamily.evalRat, F, Fintype.card_coe] at hn hd
  have hsum : (∑ i : s, a i * x i) = ∑ i ∈ s, a i * x i := Finset.sum_coe_sort s (fun i => a i * x i)
  rw [hsum] at hn hd
  let k := s.card
  have hBsq : B ≤ B*B := Nat.le_mul_of_pos_left _ hB
  have hm : k*(B*B)+B ≤ (k+1)*(B*B) := by simpa [add_mul] using Nat.add_le_add_left hBsq (k*(B*B))
  have hden : B*(B*B)^k = B^(2*k+1) := by rw [pow_succ', pow_mul, pow_two]
  have hnum : (k*(B*B)+B) * (B*(B*B)^k) ≤ (k+1)*B^(2*k+3) := by
    calc
      _ ≤ ((k+1)*(B*B)) * (B*(B*B)^k) := Nat.mul_le_mul_right _ hm
      _ = _ := by rw [hden, show 2*k+3 = (2*k+1)+2 by omega, pow_add B (2*k+1) 2, pow_two]; ring
  let E := (k+1) + (2*k+3)*(B.log2+1)
  have hp : (k+1)*B^(2*k+3) ≤ 2^E := by
    calc
      _ ≤ 2^(k+1) * (2^(B.log2+1))^(2*k+3) :=
        Nat.mul_le_mul (k+1).lt_two_pow_self.le (Nat.pow_le_pow_left B.lt_log2_self.le _)
      _ = _ := by rw [← pow_mul, ← pow_add, Nat.mul_comm (B.log2+1)]
  have hpden : B^(2*k+1) ≤ (k+1)*B^(2*k+3) :=
    (Nat.pow_le_pow_right hB (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega))
  have hnum' := log2_le_from_pow ((hn.trans hnum).trans hp)
  have hden' := log2_le_from_pow ((hd.trans_eq hden).trans (hpden.trans hp))
  rw [add_comm e]
  change 3 + _ + _ ≤ 3 + 2 * E
  omega

end Compression
end LinearProgramming
end Optimization
end OAI
