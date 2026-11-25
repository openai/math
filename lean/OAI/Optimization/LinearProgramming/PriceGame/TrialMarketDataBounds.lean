import OAI.Optimization.LinearProgramming.PriceGame.TrialExecutionMarketBounds
import OAI.Optimization.LinearProgramming.PriceGame.MomentLocalCost
import OAI.Optimization.LinearProgramming.RAM.Basic
import Mathlib.Data.Nat.Log

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace TrialExecution

open States.Mass Moment Finset

/-- Reduced denominators divide the grid modulus exactly when the scaled value is integral. -/
theorem rat_den_dvd_iff_grid (q : ℚ) (D : ℕ) :
    q.den ∣ D ↔ ∃ z : ℤ, (D : ℚ) * q = z := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨q.num * k, ?_⟩
    have hn := (div_eq_iff (Nat.cast_ne_zero.mpr q.den_ne_zero : (q.den : ℚ) ≠ 0)).mp q.num_div_den
    push_cast
    calc
      _ = (q * (q.den : ℚ)) * k := by ring
      _ = _ := by rw [← hn]
  · rintro ⟨z, hz⟩
    by_cases hd : D = 0
    · simp [hd]
    have hq : q = (z : ℚ) / D := (eq_div_iff (Nat.cast_ne_zero.mpr hd)).mpr (by simpa [mul_comm] using hz)
    rw [hq]
    apply Int.natCast_dvd_natCast.mp
    simpa [Rat.divInt_eq_div] using Rat.den_dvd z (D : ℤ)

/-- A bid reads a tuple coordinate at this level and at most one pivot on a strict ancestor.
No other entry of either the raw assignment or the baseline history is constrained. -/
theorem accepted_bid_bounds {N l : ℕ} (e : Expert N) (history : History N) (i : Vertex N l)
    (hi : e.accepts l i = true) (D : ℕ) {R U : ℚ} (hR : 0 ≤ R) (hU : 0 ≤ U)
    (hraw : ∀ a ∈ e.skeleton.sources, (e.raw a).den ∣ D ∧ |e.raw a| ≤ R)
    (hhist : ∀ j < l, ∀ v, (history j v).den ∣ D ∧ |history j v| ≤ U) :
    (e.intercept history i).den ∣ D ∧ |e.intercept history i| ≤ 2 * R + U := by
  have hl : l = e.skeleton.level := by
    by_contra h
    simp [Expert.accepts, h] at hi
  subst l
  obtain ⟨j, hj⟩ : ∃ j : Fin 64, e.skeleton.tuple j = i := by simpa [Expert.accepts] using hi
  have hsrc : rootVertex N e.skeleton.level i ∈ e.skeleton.sources := by
    refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, mem_univ _, ?_⟩)
    simp only [Skeleton.origin, hj]
  obtain ⟨hrd, hra⟩ := hraw _ hsrc
  have hs : (e.skeleton.shift e.raw history).den ∣ D ∧
      |e.skeleton.shift e.raw history| ≤ R + U := by
    cases hp : e.skeleton.pivot with
    | none => simp [Skeleton.shift, hp, add_nonneg hR hU]
    | some p =>
      have hpivot : rootVertex N p.1 p.2 ∈ e.skeleton.sources := by
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, ?_, rfl⟩)
        simp [hp]
      obtain ⟨hpd, hpa⟩ := hraw _ hpivot
      obtain ⟨hhd, hha⟩ := hhist p.1 p.1.isLt p.2
      have hsd : (e.skeleton.signed (history p.1 p.2)).den ∣ D := by
        unfold Skeleton.signed
        split <;> simpa using hhd
      have hsa : |e.skeleton.signed (history p.1 p.2)| ≤ U := by
        unfold Skeleton.signed
        split <;> simpa using hha
      simp only [Skeleton.shift, hp]
      exact ⟨(Rat.sub_den_dvd_lcm _ _).trans (Nat.lcm_dvd hpd hsd),
        (abs_sub _ _).trans (add_le_add hpa hsa)⟩
  refine ⟨(Rat.sub_den_dvd_lcm _ _).trans (Nat.lcm_dvd hrd hs.1), ?_⟩
  unfold Expert.intercept
  calc
    _ ≤ |e.raw _| + |e.skeleton.shift e.raw history| := abs_sub _ _
    _ ≤ R + (R + U) := add_le_add hra hs.2
    _ = _ := by ring

/-- For actual expert data, the local update obeys the proof's prescribed common unit. -/
theorem probeWeight_den_dvd {N ne l : ℕ} (experts : Fin ne → Expert N)
    (history : History N) (L : Weights ne) (hL : ∀ e, 0 ≤ L e) (η : ℚ)
    (labels : Vertex N l → Bool) (Q : ℕ) (hQ : ∀ e, (L e).den ∣ Q) (e : Fin ne) :
    let A := marketSolverAtCommonWeightUnit experts l history L hL
    (L e * (1 + η * gainQ (fun k i => A.fractions k (some i)) (sides experts)
      (fun i => labelSign (labels i)) e)).den ∣ Q * η.den := by
  let A := marketSolverAtCommonWeightUnit experts l history L hL
  let signed (i : Vertex N l) : ℤ := if (experts e).skeleton.positive = labels i then 1 else -1
  have he (i : Vertex N l) : sides experts e * labelSign (labels i) = (signed i : ℚ) := by
    cases hp : (experts e).skeleton.positive <;> cases hz : labels i <;>
      simp [sides, Market.side, labelSign, signed, hp, hz]
  have hg : gainQ (fun k i => A.fractions k (some i)) (sides experts)
      (fun i => labelSign (labels i)) e = ∑ i, A.fractions e (some i) * (signed i : ℚ) := by
    unfold gainQ
    simp only [mul_assoc, he]
  change (L e * (1 + η * gainQ _ _ _ e)).den ∣ _
  rw [hg]
  exact local_update_den_dvd _ _ _ _ _ (hQ e) fun i =>
    (marketSolverAtCommonWeightUnit_bounds experts l history L hL).1 Q hQ e (some i)

/-- The actual baseline fits both the input price grid and the one-level amplitude recurrence. -/
theorem marketPrice_den_abs {N ne : ℕ} (experts : Fin ne → Expert N) (l : ℕ)
    (history : History N) (L : Weights ne) (hL : ∀ e, 0 ≤ L e) (D R U : ℕ)
    (hraw : ∀ e a, a ∈ (experts e).skeleton.sources →
      ((experts e).raw a).den ∣ D ∧ |(experts e).raw a| ≤ R)
    (hhist : ∀ j < l, ∀ v, (history j v).den ∣ D ∧ |history j v| ≤ U) (i : Vertex N l) :
    let A := marketSolverAtCommonWeightUnit experts l history L hL
    let B := 2 * (ne + N * 2 ^ l + 1) * (2 * R + U)
    (A.prices i).den ∣ D ∧ |A.prices i| ≤ (B : ℚ) := by
  let A := marketSolverAtCommonWeightUnit experts l history L hL
  let B := 2 * (ne + N * 2 ^ l + 1) * (2 * R + U)
  obtain ⟨_, hgrid, hamp⟩ := marketSolverAtCommonWeightUnit_bounds experts l history L hL
  have hb e j (h : (experts e).accepts l j = true) :=
    accepted_bid_bounds (experts e) history j h D (Nat.cast_nonneg R) (Nat.cast_nonneg U)
      (hraw e) hhist
  have hd : (A.prices i).den ∣ D := (rat_den_dvd_iff_grid _ _).mpr <|
    hgrid D (fun e j h => (rat_den_dvd_iff_grid _ _).mp (hb e j h).1) i
  have ha : |A.prices i| ≤ (B : ℚ) := by
    have hc := hamp (2 * (R : ℚ) + U) (by positivity) (fun e j h => (hb e j h).2) i
    dsimp only [B]
    push_cast
    convert hc using 1
    push_cast
    rfl
  exact ⟨hd, ha⟩

/-- Price fields in the designated query use the manuscript's signed numerator and
positive denominator encoding. The bound depends on the supplied grids and magnitudes
of the public raw values and previously visited ancestor levels. -/
theorem marketPrice_ratBits {N ne : ℕ} (experts : Fin ne → Expert N) (l : ℕ)
    (history : History N) (L : Weights ne) (hL : ∀ e, 0 ≤ L e) (D R U : ℕ) (hD : 0 < D)
    (hraw : ∀ e a, a ∈ (experts e).skeleton.sources →
      ((experts e).raw a).den ∣ D ∧ |(experts e).raw a| ≤ R)
    (hhist : ∀ j < l, ∀ v, (history j v).den ∣ D ∧ |history j v| ≤ U) (i : Vertex N l) :
    let A := marketSolverAtCommonWeightUnit experts l history L hL
    let B := 2 * (ne + N * 2 ^ l + 1) * (2 * R + U)
    RAM.ratBits (A.prices i) ≤ 3 + (B * D).log2 + D.log2 := by
  let A := marketSolverAtCommonWeightUnit experts l history L hL
  let B := 2 * (ne + N * 2 ^ l + 1) * (2 * R + U)
  obtain ⟨hd, ha⟩ := marketPrice_den_abs experts l history L hL D R U hraw hhist i
  have hh := rat_num_abs_le_of_den_dvd (A.prices i) B D hD ha hd
  have hden := Nat.le_of_dvd hD hd
  change 3 + (A.prices i).num.natAbs.log2 + (A.prices i).den.log2 ≤ 3 + (B * D).log2 + D.log2
  simp only [Nat.log2_eq_log_two]
  exact Nat.add_le_add (Nat.add_le_add_left (Nat.log_mono_right hh) 3) (Nat.log_mono_right hden)

end TrialExecution
end PriceGame
end LinearProgramming
end Optimization
end OAI
