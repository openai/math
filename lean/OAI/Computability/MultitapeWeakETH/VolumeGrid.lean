import OAI.Computability.MultitapeWeakETH.DyadicBudget

/-! # Turning the grid-index saving into a fixed power saving in the volume -/

namespace OAI.Computability.MultitapeWeakETH.DyadicBudget

open VPVNP Compression Filter

/-- Least grid index whose capacity accommodates the volume. -/
def index (b N : ℕ) := Nat.clog (2^b) N

private theorem base_gt_one {b : ℕ} (hb : 0 < b) : 1 < 2^b := Nat.one_lt_two_pow hb.ne'

theorem grid_cover {b N : ℕ} (hb : 0 < b) (hN : 1 < N) :
    N ≤ 2^(b*index b N) ∧ 2^(b*index b N) ≤ 2^b*N := by
  rw [pow_mul]
  have base := base_gt_one hb
  refine ⟨Nat.le_pow_clog base _,?_⟩
  have hs : 0 < index b N := Nat.clog_pos base hN
  have prev := Nat.pow_pred_clog_lt_self base hN
  change (2^b)^(index b N).pred < N at prev
  conv_lhs => rw [← Nat.succ_pred_eq_of_pos hs,pow_succ]
  exact (Nat.mul_le_mul_right _ prev.le).trans_eq (Nat.mul_comm ..)

/-- Any polynomial in the grid index times 2^((b-1)s) is eventually
absorbed by the same explicit power of the input volume. -/
theorem eventually_grid_saving {b : ℕ} (hb : 1 < b) (A : ℝ) (hA : 0 ≤ A) (d : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      A*((index b N:ℝ)+1)^d*(2:ℝ)^((b-1)*index b N) ≤ (N:ℝ)^(1-1/(2*b:ℝ)) := by
  let e := 1-1/(b:ℝ)
  let c := (2:ℝ)^b
  have bpos : (0:ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb' : (1:ℝ) < b := by exact_mod_cast hb
  have he : 0 ≤ e := by dsimp [e]; apply sub_nonneg.mpr; exact (div_le_one bpos).mpr hb'.le
  have ec : e < 1-1/(2*b:ℝ) := by dsimp [e]; apply sub_lt_sub_left; gcongr; linarith
  have bound := eventually_absorb_polylog (A*2^d*c^e) d ec zero_lt_one
  filter_upwards [bound,eventually_ge_atTop 2] with N bound hN
  let s := index b N
  have hbase : 2 ≤ 2^b := base_gt_one (by omega)
  have hs : s ≤ N.log2+1 :=
    (Nat.clog_anti_left (by decide : 1<2) hbase).trans (BurstRAM.clog_le_log2_succ N)
  have hl : (s:ℝ)+1 ≤ 2*((N.log2:ℝ)+1) := by
    have hc : (s:ℝ) ≤ (N.log2:ℝ)+1 := by exact_mod_cast hs
    linarith [Nat.cast_nonneg (α:=ℝ) N.log2]
  have volume : (2:ℝ)^(b*s) ≤ c*N := by dsimp only [s,c]; exact_mod_cast (grid_cover (b:=b) (by omega) (N:=N) hN).2
  have expo : ((b*s:ℕ):ℝ)*e = ((b-1)*s:ℕ) := by
    rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ b),Nat.cast_one]
    dsimp [e]; field_simp
  have powers : (2:ℝ)^((b-1)*s) = ((2:ℝ)^(b*s))^e := by
    rw [← Real.rpow_natCast (2:ℝ) (b*s),← Real.rpow_mul (by norm_num),expo,Real.rpow_natCast]
  change A*((s:ℝ)+1)^d*(2:ℝ)^((b-1)*s) ≤ _
  rw [powers]
  calc
    _ ≤ A*(2*((N.log2:ℝ)+1))^d*(c*N)^e := by gcongr
    _ = (A*2^d*c^e)*(N:ℝ)^e*((N.log2:ℝ)+1)^d := by
      rw [mul_pow,Real.mul_rpow (by dsimp [c]; positivity) (by positivity)]; ring
    _ ≤ _ := by simpa only [one_mul] using bound

end OAI.Computability.MultitapeWeakETH.DyadicBudget
