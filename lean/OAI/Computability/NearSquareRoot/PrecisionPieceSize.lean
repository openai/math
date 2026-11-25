import OAI.Computability.NearSquareRoot.PhysicalWalshPieceExecution

/-! # Uniform size bounds for the rounded Walsh-piece trajectory

The degrees and fanout are fixed independently of the address width.
Every selected width up to the address width is admitted, including zero
and the choice in which every address bit is selected.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open Filter Finset PhysicalWalshNode

/-- At most one even piece per pair of selected bits. -/
theorem schedule_length_le_half {A W : ℕ} (ha : 1 < A) (hw : 0 < W) (k s w : ℕ) :
    (schedule A W hw k s w).length ≤ s / 2 := by
  have h := Nat.ofDigits_digits A (s / 2)
  rw [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.sum_ofFn] at h
  change (∑ j : Fin (walshPieceDigits A s).length, (walshPieceDigits A s).get j * A^j.val) = s/2 at h
  rw [← h]
  simp only [schedule, List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def,
    List.length_ofFn, digit_eq_get ha]
  apply Finset.sum_le_sum
  intro j _
  exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by omega))

theorem schedule_length_le {A W : ℕ} (ha : 1 < A) (hw : 0 < W) (k s w : ℕ) :
    (schedule A W hw k s w).length ≤ s :=
  (schedule_length_le_half ha hw k s w).trans (Nat.div_le_self ..)

/-- Every reached level has at most the selected width available for its
binary recursion. -/
theorem level_pow_le {A W : ℕ} (ha : 1 < A) (hw : 0 < W) {k s w : ℕ} {u : Shape}
    (hu : u ∈ schedule A W hw k s w) : 2^u.level ≤ s := by
  obtain ⟨j, t, rfl⟩ := (mem_schedule hw k s w u).mp hu
  have h := offset_add_grow_le t.isLt
  change _ + 2*A^j.val ≤ s at h
  exact (Nat.pow_le_pow_left (show 2 ≤ A from ha) j.val).trans (by omega)

/-- Uniform in the number of selected bits. The possible additional batch
factor is polynomial in the address width, including when there are no
spectator bits to absorb the padding. -/
theorem eventually_extent_le {A W : ℕ} (ha : 1 < A) (hw : 0 < W) :
    ∀ᶠ k : ℕ in atTop, ∀ s ≤ k, extent A W k s ≤ 2^(2*k) := by
  filter_upwards [WalshPadding.eventually_pow_le_two_pow_half W] with k hpoly
  intro s hs
  let q := 2^(k-s)
  let M := W^WalshPadding.depth A s
  have hp : 0 < M := Nat.pow_pos hw
  have hm : M ≤ 2^(k/2) := by
    by_cases h : 2 ≤ s
    · exact ((WalshPadding.batchModulus_le_poly ha h W).trans
        (Nat.pow_le_pow_left (show s/2 ≤ k by omega) W)).trans hpoly
    · simpa [M, WalshPadding.depth, show s/2 = 0 by omega] using (Nat.one_le_two_pow (n := k/2))
  have hceil : q ⌈/⌉ M ≤ q := (ceilDiv_le_iff_le_mul hp).mpr (Nat.le_mul_of_pos_left _ hp)
  calc
    extent A W k s ≤ (M*q)*2^s := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left M hceil)
    _ = M * 2^k := by rw [Nat.mul_assoc]; congr 1; dsimp only [q]; rw [← pow_add, Nat.sub_add_cancel hs]
    _ ≤ 2^k * 2^k := Nat.mul_le_mul_right _ (hm.trans (Nat.pow_le_pow_right (by decide) (k.div_le_self 2)))
    _ = 2^(2*k) := by rw [← pow_add, two_mul]

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
