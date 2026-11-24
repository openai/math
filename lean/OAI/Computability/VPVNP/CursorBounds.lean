import OAI.Computability.VPVNP.CursorRouting
import OAI.Computability.VPVNP.RAMParameters

/-!
# Size of the routed network before compression

In §§11–12 of *VP and VNP differ over every field*, the virtual group uses the least
power-of-two site count that accommodates the pair parser's budget. One circuit of
cursor positions routes each message, with separate fields for each mask. These exact
choices give the position and maximum-width bounds needed in equation (12.1).
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorBounds

open VPVNP.Compression

/-- The live processor address length in Section 9.1. -/
abbrev addressBits := BurstRAM.addressWidth

/-- Live processors indexed by their binary addresses. -/
def processorCount (B n : ℕ) : ℕ := 2 ^ addressBits B n

/-- The least binary virtual address length giving enough bucket slots. -/
def virtualBits (B n : ℕ) : ℕ := BurstRAM.virtualSiteExponent (addressBits B n) n

theorem virtualBits_le_iff (B n d : ℕ) : virtualBits B n ≤ d ↔
    processorCount B n * n * Nat.clog 2 n ≤ 2 ^ d * virtualBucket n := by
  simpa only [virtualBits, processorCount, virtualBucket, BurstRAM.roundedUp_eq, Nat.cast_one,
    Nat.cast_ofNat] using BurstRAM.virtualSiteExponent_le_iff (addressBits B n) n d

/-- Rounding the virtual processor count to a power of two costs at most a factor of two. -/
theorem virtualCount_bound (B n : ℕ) (hn : 2 ≤ n) :
    ((2 ^ virtualBits B n : ℕ) : ℝ) ≤
      2 * (processorCount B n : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) * (Nat.clog 2 n : ℝ) := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hnpos := zero_lt_one.trans_le hn'
  cases hD : virtualBits B n with
  | zero =>
    have hP : 1 ≤ processorCount B n := Nat.one_le_pow _ _ Nat.zero_lt_two
    have hc := Nat.clog_pos Nat.one_lt_two (show 1 < n by omega)
    have hP' : (1 : ℝ) ≤ processorCount B n := by exact_mod_cast hP
    have hc' : (1 : ℝ) ≤ Nat.clog 2 n := by exact_mod_cast hc
    have hn34 := Real.one_le_rpow hn' (by norm_num : (0 : ℝ) ≤ 3 / 4)
    simp only [pow_zero, Nat.cast_one]
    calc
      1 ≤ 2 * (1 : ℝ) * 1 * 1 := by norm_num
      _ ≤ _ := by gcongr
  | succ d =>
    have hlt : 2 ^ d * virtualBucket n < processorCount B n * n * Nat.clog 2 n := by
      apply lt_of_not_ge
      intro h
      have hd := (virtualBits_le_iff B n d).mpr h
      omega
    have hlt' : ((2 ^ d : ℕ) : ℝ) * virtualBucket n <
        (processorCount B n : ℝ) * n * Nat.clog 2 n := by exact_mod_cast hlt
    have hfrac : (n : ℝ) ^ (3 / 4 : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ) = n := by
      rw [← Real.rpow_add hnpos]
      norm_num
    apply le_of_mul_le_mul_right _ (Real.rpow_pos_of_pos hnpos (1 / 4))
    calc
      ((2 ^ (d + 1) : ℕ) : ℝ) * (n : ℝ) ^ (1 / 4 : ℝ)
          ≤ 2 * (((2 ^ d : ℕ) : ℝ) * virtualBucket n) := by
            rw [pow_succ, Nat.cast_mul, Nat.cast_ofNat, mul_comm _ (2 : ℝ), mul_assoc]
            gcongr
            exact (virtualBucket_bounds (by omega : 1 ≤ n)).1
      _ ≤ 2 * ((processorCount B n : ℝ) * n * Nat.clog 2 n) := by gcongr
      _ = 2 * (processorCount B n : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) * (Nat.clog 2 n : ℝ) *
          (n : ℝ) ^ (1 / 4 : ℝ) := by
            conv_lhs => rw [← hfrac]
            ring


/-- The rounded binary logarithm and the paper's real-log convention agree at all lengths. -/
theorem addressBits_eq_ceil (B n : ℕ) :
    addressBits B n = B * ⌈Real.logb 2 n⌉₊ := by
  rw [addressBits, BurstRAM.addressWidth, ← Real.natCeil_logb_natCast 2 n]
  rfl

/-- At most two extra logarithmic terms in the virtual processor address length:
one for the word length `n`, one for its rounded binary logarithm. -/
theorem virtualBits_le (B n : ℕ) : virtualBits B n ≤ (B + 2) * Nat.clog 2 n := by
  let c := Nat.clog 2 n
  have hn : n ≤ 2 ^ c := Nat.le_pow_clog Nat.one_lt_two _
  have hc : c ≤ 2 ^ c := Nat.lt_two_pow_self.le
  unfold virtualBits BurstRAM.virtualSiteExponent
  apply (Nat.sub_le _ _).trans
  apply Nat.clog_le_of_le_pow
  calc
    processorCount B n * n * c ≤ 2 ^ (B * c) * 2 ^ c * 2 ^ c :=
      Nat.mul_le_mul (Nat.mul_le_mul_left (2 ^ (B * c)) hn) hc
    _ = 2 ^ ((B + 2) * c) := by rw [← pow_add, ← pow_add]; ring_nf

/-- At large lengths the virtual group retains at least the live number of address
bits. Thus reserving a fixed number of fresh lane bits per compressor block is possible. -/
theorem addressBits_le_virtualBits (B n : ℕ) (hn : 3 ≤ n) :
    addressBits B n ≤ virtualBits B n := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hcap := (virtualBits_le_iff B n (virtualBits B n)).mp le_rfl
  have hc : 2 ≤ Nat.clog 2 n :=
    (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mpr (show 2 ^ 1 < n by omega)
  have hpow : (n : ℝ) ^ (1 / 4 : ℝ) ≤ n := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hK : virtualBucket n ≤ 2 * n := by
    exact_mod_cast (virtualBucket_bounds (by omega : 1 ≤ n)).2.trans
      (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 2))
  have hKN : virtualBucket n ≤ n * Nat.clog 2 n := by
    calc
      _ ≤ 2 * n := hK
      _ = n * 2 := Nat.mul_comm _ _
      _ ≤ _ := Nat.mul_le_mul_left _ hc
  have hsize : processorCount B n * virtualBucket n ≤ 2 ^ virtualBits B n * virtualBucket n :=
    (Nat.mul_le_mul_left (processorCount B n) hKN).trans (by simpa [mul_assoc] using hcap)
  apply (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp
  exact Nat.le_of_mul_le_mul_right hsize (Nat.two_pow_pos _)

theorem laneBudget (B lanes n : ℕ) (hB : lanes ≤ B) {θ : ℝ} (hθ : θ ≤ 1) (hn : 3 ≤ n) :
    lanes * blockCount θ n ≤ virtualBits B n := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hlog : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg (by norm_num) hn'
  have ht : blockCount θ n ≤ Nat.clog 2 n := by
    rw [blockCount, ← Real.natCeil_logb_natCast 2 n]
    exact (Nat.floor_le_floor (mul_le_of_le_one_left hlog hθ)).trans (Nat.floor_le_ceil _)
  exact (Nat.mul_le_mul hB ht).trans (addressBits_le_virtualBits B n hn)

/-- The virtual word length is inherited from the live RAM. -/
def wordBits (B n : ℕ) : ℕ := (addressBits B n + 10) ^ 4

/-- Count the actual processor-cursor positions in the graph of §12. -/
noncomputable def initialPositions (B n : ℕ) : ℕ :=
  2 ^ virtualBits B n * virtualBits B n

/-- Width of one directed cursor arc, reserving a disjoint payload for each mask system. -/
noncomputable def initialWidth (B n : ℕ) : ℕ :=
  ∑ s : CursorRouting.RAMSystem (virtualBits B n),
    CursorRouting.ramFieldBits (virtualBucket n) (wordBits B n) s

theorem initialPositions_card (B n : ℕ) : initialPositions B n =
    Fintype.card (CursorRouting.Site (virtualBits B n) × Fin (virtualBits B n)) :=
  (CursorRouting.cursorPositions_card _).symm

private theorem arcWidth_le (D H w : ℕ) (hH : 1 ≤ H) :
    (∑ s : CursorRouting.RAMSystem D, CursorRouting.ramFieldBits H w s) ≤
      28 * H * (D + 1) ^ 2 * w := by
  have hD : D ≤ (D + 1) ^ 2 := by nlinarith
  have hL : RAMLayout.layerCount D ≤ (D + 1) ^ 2 := by
    rw [RAMLayout.layerCount, Nat.choose_two_right]
    apply (Nat.div_le_self _ _).trans
    rw [pow_two]
    gcongr
    omega
  rw [CursorRouting.ramArcWidth, RAMLayout.blockBits]
  calc
    _ ≤ (D + 1) ^ 2 * (8 * (H * w)) + (D + 1) ^ 2 * (4 * H * 5 * w) := by
      gcongr
      exact Nat.le_mul_of_pos_left _ hH
    _ = _ := by ring

/-- Pointwise initial-position bound with explicit logarithmic factors. -/
theorem initialPositions_bound (B n : ℕ) (hn : 2 ≤ n) :
    (initialPositions B n : ℝ) ≤
      (2 * ((B : ℝ) + 2)) * (processorCount B n : ℝ) *
        (n : ℝ) ^ (3 / 4 : ℝ) * ((n.log2 : ℝ) + 1) ^ 2 := by
  let c := Nat.clog 2 n
  have hD : (virtualBits B n : ℝ) ≤ ((B : ℝ) + 2) * c := by
    exact_mod_cast virtualBits_le B n
  have hL : (c : ℝ) ≤ (n.log2 : ℝ) + 1 := by exact_mod_cast BurstRAM.clog_le_log2_succ n
  have hR := virtualCount_bound B n hn
  rw [initialPositions, Nat.cast_mul]
  calc
    _ ≤ (2 * (processorCount B n : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) * c) *
        (((B : ℝ) + 2) * c) := mul_le_mul hR hD (by positivity) (by positivity)
    _ ≤ (2 * (processorCount B n : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) * ((n.log2 : ℝ) + 1)) *
        (((B : ℝ) + 2) * ((n.log2 : ℝ) + 1)) := by gcongr
    _ = _ := by ring

/-- Pointwise initial arc-width bound with explicit logarithmic factors. -/
theorem initialWidth_bound (B n : ℕ) (hn : 2 ≤ n) :
    (initialWidth B n : ℝ) ≤
      (56 * ((B : ℝ) + 3) ^ 2 * ((B : ℝ) + 10) ^ 4) *
        (n : ℝ) ^ (1 / 4 : ℝ) * ((n.log2 : ℝ) + 1) ^ 6 := by
  let L := n.log2 + 1
  have hD : virtualBits B n + 1 ≤ (B + 3) * L := by
    have h := (virtualBits_le B n).trans (Nat.mul_le_mul_left _ (BurstRAM.clog_le_log2_succ n))
    dsimp [L]
    nlinarith
  have hw : wordBits B n ≤ ((B + 10) * L) ^ 4 := by
    unfold wordBits addressBits BurstRAM.addressWidth
    apply Nat.pow_le_pow_left
    have h := Nat.mul_le_mul_left B (BurstRAM.clog_le_log2_succ n)
    dsimp [L]
    nlinarith
  have hK : 1 ≤ virtualBucket n := Nat.two_pow_pos _
  have hwidth : initialWidth B n ≤ 28 * virtualBucket n * ((B + 3) * L) ^ 2 *
      ((B + 10) * L) ^ 4 := by
    apply (arcWidth_le _ _ _ hK).trans
    gcongr
  have hwidth' : (initialWidth B n : ℝ) ≤ 28 * (virtualBucket n : ℝ) *
      (((B : ℝ) + 3) * ((n.log2 : ℝ) + 1)) ^ 2 *
      (((B : ℝ) + 10) * ((n.log2 : ℝ) + 1)) ^ 4 := by exact_mod_cast hwidth
  calc
    _ ≤ _ := hwidth'
    _ ≤ 28 * (2 * (n : ℝ) ^ (1 / 4 : ℝ)) *
      (((B : ℝ) + 3) * ((n.log2 : ℝ) + 1)) ^ 2 *
      (((B : ℝ) + 10) * ((n.log2 : ℝ) + 1)) ^ 4 := by
        gcongr
        exact (virtualBucket_bounds (by omega : 1 ≤ n)).2
    _ = _ := by ring

open Filter in
/-- The two pre-compression estimates of §12 hold simultaneously for fixed `B`. -/
theorem initialBounds (B : ℕ) :
    ∃ A W : ℝ, ∃ s t : ℕ, ∀ᶠ n : ℕ in atTop,
      (initialPositions B n : ℝ) ≤ A * (processorCount B n : ℝ) *
        (n : ℝ) ^ (3 / 4 : ℝ) * ((n.log2 : ℝ) + 1) ^ s ∧
      (initialWidth B n : ℝ) ≤ W * (n : ℝ) ^ (1 / 4 : ℝ) * ((n.log2 : ℝ) + 1) ^ t := by
  refine ⟨2 * ((B : ℝ) + 2), 56 * ((B : ℝ) + 3) ^ 2 * ((B : ℝ) + 10) ^ 4,
    2, 6, eventually_atTop.mpr ⟨2, fun n hn => ?_⟩⟩
  exact ⟨initialPositions_bound B n hn, initialWidth_bound B n hn⟩

end CursorBounds

end VPVNP
end Computability
end OAI
