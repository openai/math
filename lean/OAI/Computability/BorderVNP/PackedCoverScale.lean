import OAI.Computability.BorderVNP.CoverDeckTower
import OAI.Computability.BorderVNP.TeamScales

/-!
# Choosing the initial product cover in §7.1

The depth used in a placed pack is one below the congruence level. From
congruence level two onwards, the volume of the product host grows by a fixed
integer factor at each step. Choosing the largest level below the target
volume leaves arbitrarily many levels after all epochs, uniformly in team size.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CoverScale

open Cover Filter TeamScales
open scoped Classical

variable (I : Type*) [Fintype I]

/-- Ratio of consecutive product-cover volumes in the stable range. -/
def factor : ℕ := (7 ^ 3) ^ Fintype.card I

/-- Product tile count at the depth used by a placed pack. -/
noncomputable def sites (depth : ℕ) : ℕ := Fintype.card (I → Deck (depth + 1))

/-- Exact volume at offset `k` from the first stable depth. -/
theorem sites_stable (k : ℕ) : sites I (k + 1) = factor I ^ k * sites I 1 := by
  simp only [sites, Fintype.card_fun, ← Nat.card_eq_fintype_card (α := Deck _), deck_card]
  rw [tileCount_eq k, mul_pow, factor, ← pow_mul (7 ^ 3) k,
    ← pow_mul (7 ^ 3) (Fintype.card I), Nat.mul_comm k (Fintype.card I)]

/-- Every additional stable level contributes exactly one growth factor. -/
theorem sites_add {h : ℕ} (hh : 1 ≤ h) (loss : ℕ) :
    sites I (h + loss) = factor I ^ loss * sites I h := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hh
  calc
    _ = factor I ^ (k + loss) * sites I 1 := by
      rw [show h + loss = (k + loss) + 1 by omega, sites_stable]
    _ = factor I ^ loss * (factor I ^ k * sites I 1) := by rw [pow_add]; ring
    _ = _ := by rw [← sites_stable, show k + 1 = h by omega]

/-- With a nonempty factor set, product-cover volume strictly increases. -/
theorem one_lt_factor [Nonempty I] : 1 < factor I :=
  one_lt_pow₀ (by decide : 1 < (7 ^ 3 : ℕ)) Fintype.card_pos.ne'

/-- Largest stable depth whose tile count is at most the target, provided
the target reaches the first stable level. -/
noncomputable def initialDepth (r n : ℕ) : ℕ :=
  Nat.log (factor I) ⌊(r : ℝ) * (n : ℝ) ^ (9 / 10 : ℝ) / sites I 1⌋₊ + 1

private theorem sites_pos (h : ℕ) : 0 < sites I h := Fintype.card_pos

/-- The rounded cover count lies between the target and the target divided
by one tower step. -/
theorem initial_sites [Nonempty I] {r n : ℕ}
    (h : (sites I 1 : ℝ) ≤ (r : ℝ) * (n : ℝ) ^ (9 / 10 : ℝ)) :
    (r : ℝ) * (n : ℝ) ^ (9 / 10 : ℝ) / factor I < sites I (initialDepth I r n) ∧
    (sites I (initialDepth I r n) : ℝ) ≤ (r : ℝ) * (n : ℝ) ^ (9 / 10 : ℝ) := by
  let x := (r : ℝ) * (n : ℝ) ^ (9 / 10 : ℝ) / sites I 1
  have hb : 0 < (sites I 1 : ℝ) := by exact_mod_cast sites_pos I 1
  have hx : 1 ≤ x := (le_div_iff₀ hb).mpr (by simpa using h)
  have hfloor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  let k := Nat.log (factor I) ⌊x⌋₊
  have hlo : (factor I : ℝ) ^ k ≤ x := by
    have hz := Nat.pow_log_le_self (factor I) (by omega : ⌊x⌋₊ ≠ 0)
    exact (show (factor I : ℝ) ^ k ≤ (⌊x⌋₊ : ℝ) by exact_mod_cast hz).trans
      (Nat.floor_le (zero_le_one.trans hx))
  have hhi : x < (factor I : ℝ) ^ (k + 1) := by
    have hz := Nat.lt_pow_succ_log_self (one_lt_factor I) ⌊x⌋₊
    simpa using (Nat.floor_lt (zero_le_one.trans hx)).mp hz
  change _ < (sites I (k + 1) : ℝ) ∧ (sites I (k + 1) : ℝ) ≤ _
  rw [sites_stable, Nat.cast_mul, Nat.cast_pow]
  refine ⟨(div_lt_iff₀ (by exact_mod_cast (zero_lt_one.trans (one_lt_factor I)))).mpr ?_,
    (le_div_iff₀ hb).mp hlo⟩
  have hhi' := (div_lt_iff₀ hb).mp hhi
  simpa only [pow_succ, mul_right_comm] using hhi'

/-- For any prescribed terminal depth, all sufficiently large processor
lengths admit the same depth formula for every positive team size. The last
inequality controls the final volume after the full epoch loss. -/
theorem eventually_depths [Nonempty I] (loss m : ℕ) {τ α : ℝ} (hτ : 0 ≤ τ)
    (he : τ * Real.logb 2 ((factor I : ℝ) ^ loss) ≤ α / 10)
    (hα : α / 10 < 9 / 10) :
    ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
      let start := initialDepth I r n
      let terminal := start - loss * epochs τ n
      m + 1 ≤ terminal ∧ terminal + loss * epochs τ n = start ∧
      (r : ℝ) * (n : ℝ) ^ (9 / 10 : ℝ) / factor I < sites I start ∧
      (sites I start : ℝ) ≤ (r : ℝ) * (n : ℝ) ^ (9 / 10 : ℝ) ∧
      (r : ℝ) * (n : ℝ) ^ (9 / 10 - α / 10 : ℝ) / factor I < sites I terminal := by
  have hbase : 1 ≤ (factor I : ℝ) := by exact_mod_cast (one_lt_factor I).le
  have hb : 0 < (sites I 1 : ℝ) := by exact_mod_cast sites_pos I 1
  have hg := eventually_rpow_gap hα ((factor I : ℝ) ^ m * sites I 1)
  filter_upwards [hg, eventually_ge_atTop 1] with n hn hn1
  intro r hr start terminal
  have hr1 : 1 ≤ (r : ℝ) := by exact_mod_cast hr
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hn1)
  let L := loss * epochs τ n
  have hL : (factor I : ℝ) ^ L ≤ (n : ℝ) ^ (α / 10) := by
    rw [show L = loss * epochs τ n by rfl, pow_mul]
    exact epoch_growth_le (one_le_pow₀ hbase) hn1 hτ he
  have htarget : (factor I : ℝ) ^ (m + L) * sites I 1 ≤ (r : ℝ) * (n : ℝ) ^ (9 / 10 : ℝ) := by
    calc
      _ = ((factor I : ℝ) ^ m * sites I 1) * (factor I : ℝ) ^ L := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hL (by positivity)
      _ ≤ (n : ℝ) ^ (9 / 10 : ℝ) := hn
      _ ≤ _ := le_mul_of_one_le_left (Real.rpow_nonneg hnpos.le _) hr1
  have hoff : m + L ≤ Nat.log (factor I) ⌊(r : ℝ) * (n : ℝ) ^ (9 / 10 : ℝ) / sites I 1⌋₊ := by
    apply Nat.le_log_of_pow_le (one_lt_factor I)
    apply Nat.le_floor
    simpa only [Nat.cast_pow] using (le_div_iff₀ hb).mpr htarget
  have hstart : m + L + 1 ≤ start := Nat.succ_le_succ hoff
  have ht : m + 1 ≤ terminal := by dsimp only [terminal]; change m + 1 ≤ start - L; omega
  have hsum : terminal + L = start := by dsimp only [terminal]; change start - L + L = start; omega
  have hbottom := (le_mul_of_one_le_left hb.le (one_le_pow₀ hbase (n := m + L))).trans htarget
  obtain ⟨hlo, hhi⟩ := initial_sites I hbottom
  refine ⟨ht, hsum, hlo, hhi, ?_⟩
  have heq : (sites I start : ℝ) = (factor I : ℝ) ^ L * sites I terminal := by
    rw [← hsum, sites_add I (show 1 ≤ terminal by omega), Nat.cast_mul, Nat.cast_pow]
  have hfactor : 0 < (factor I : ℝ) := zero_lt_one.trans_le hbase
  change (r : ℝ) * (n : ℝ) ^ (9 / 10 : ℝ) / factor I < sites I start at hlo
  rw [heq] at hlo
  apply (div_lt_iff₀ hfactor).mpr
  apply lt_of_mul_lt_mul_right (a := (n : ℝ) ^ (α / 10)) _ (Real.rpow_nonneg hnpos.le _)
  calc
    _ = (r : ℝ) * (n : ℝ) ^ (9 / 10 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_add hnpos, sub_add_cancel]
    _ < ((factor I : ℝ) ^ L * sites I terminal) * factor I := (div_lt_iff₀ hfactor).mp hlo
    _ ≤ ((n : ℝ) ^ (α / 10) * sites I terminal) * factor I := by gcongr
    _ = _ := by ring

end Packing.CoverScale

end BorderVNP
end Computability
end OAI
