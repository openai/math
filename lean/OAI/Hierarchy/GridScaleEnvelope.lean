import OAI.Computability.VPVNP.RAMClock
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith

namespace OAI
/-! # A common sublinear dyadic exponent for the collapse envelopes

The exponent is chosen before the tick and its replication factor. It dominates
every fixed power of the word length while taking a vanishing fraction of the
volume exponent. -/

namespace Hierarchy.GridScale
open Filter
open scoped Topology
noncomputable section

/-- This is exactly the pair of numerical envelopes in pointwise collapse. -/
def Envelopes (Q : ℕ → ℕ) (D : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ w : ℕ in atTop,
    (Q w : ℝ) ≤ (2:ℝ)^(ε*w) ∧ (2:ℝ)^((1-ε)*w) ≤ D w

private def Covers (Q : ℕ → ℕ) (D : ℕ → ℝ) (w a : ℕ) : Prop :=
  Q w ≤ 2^a ∧ (2:ℝ)^(w-a) ≤ D w ∧ w.sqrt ≤ a

/-- The least admissible exponent at width `w`. The exceptional initial
widths have no bearing on any of the resulting bounds. -/
def overhead (Q : ℕ → ℕ) (D : ℕ → ℝ) (w : ℕ) : ℕ := by
  classical
  exact if h : ∃ a, Covers Q D w a then Nat.find h else w

private theorem covers_fraction {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D)
    (C : ℕ) (hC : 0<C) : ∀ᶠ w : ℕ in atTop, Covers Q D w (w/C) := by
  have cpos : (0:ℝ)<C := by exact_mod_cast hC
  let ε : ℝ := 1/(2*C)
  have he : 0 < ε := by dsimp [ε]; positivity
  filter_upwards [H ε he, eventually_ge_atTop (C*C)] with w h hw
  have sc : C ≤ w.sqrt := Nat.le_sqrt.mpr hw
  have floor : w.sqrt ≤ w/C := (Nat.le_div_iff_mul_le hC).mpr
    ((Nat.mul_le_mul_left _ sc).trans (Nat.sqrt_le w))
  have one : 1 ≤ w/C := hC.trans_le (sc.trans floor)
  have rem := Nat.mod_lt w hC
  have div := Nat.mod_add_div w C
  have doubled : w ≤ 2*C*(w/C) := by
    nlinarith [Nat.mul_le_mul_left C one]
  have realDouble : (w:ℝ) ≤ 2*(C:ℝ)*(w/C:ℕ) := by exact_mod_cast doubled
  have small : ε*(w:ℝ) ≤ (w/C:ℕ) := by
    change 1/(2*(C:ℝ))*w ≤ _
    rw [one_div, mul_comm, ← div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [realDouble]
  refine ⟨?_, ?_, floor⟩
  · have r : (Q w:ℝ) ≤ (2:ℝ)^(w/C) := by
      rw [← Real.rpow_natCast]
      exact h.1.trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) small)
    exact_mod_cast r
  · rw [← Real.rpow_natCast, Nat.cast_sub (Nat.div_le_self ..)]
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [small] :
      (w:ℝ) - (w/C:ℕ) ≤ (1-ε)*w)).trans h.2

private theorem chosen {Q : ℕ → ℕ} {D : ℕ → ℝ} {w a : ℕ} (h : Covers Q D w a) :
    Covers Q D w (overhead Q D w) ∧ overhead Q D w ≤ a := by
  classical
  have ex : ∃ b, Covers Q D w b := ⟨a,h⟩
  simp only [overhead, dite_eq_left ex]
  exact ⟨Nat.find_spec ex,Nat.find_min' ex h⟩

/-- The chosen exponent majorizes the replication and the deficiency of the gap. -/
theorem bounds {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D) :
    ∀ᶠ w : ℕ in atTop, Q w ≤ 2^(overhead Q D w) ∧
      (2:ℝ)^(w-overhead Q D w) ≤ D w ∧ w.sqrt ≤ overhead Q D w := by
  filter_upwards [covers_fraction H 1 (by decide)] with w h
  exact (chosen h).1

theorem sublinear {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D) (C : ℕ) :
    ∀ᶠ w : ℕ in atTop, C*overhead Q D w ≤ w := by
  filter_upwards [covers_fraction H (C+1) (Nat.succ_pos _)] with w h
  have small := (chosen h).2
  exact (Nat.mul_le_mul (Nat.le_succ _) small).trans (Nat.mul_div_le w (C+1))

theorem grows {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D) :
    Tendsto (overhead Q D) atTop atTop := by
  apply tendsto_atTop.2
  intro N
  filter_upwards [bounds H, eventually_ge_atTop (N*N)] with w h hw
  exact (Nat.le_sqrt.mpr hw).trans h.2.2

/-- Any polynomial in the word length fits in a single overhead factor. -/
theorem polynomial {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D) (C d : ℕ) :
    ∀ᶠ w : ℕ in atTop, C*(w+1)^d ≤ 2^overhead Q D w := by
  obtain ⟨N,limit⟩ := eventually_atTop.mp (Computability.VPVNP.BurstRAM.eventually_polylog_le C (2*d))
  filter_upwards [bounds H, (tendsto_atTop.mp (grows H)) N] with w h hn
  let a := overhead Q D w
  have big : N ≤ 2^a := hn.trans (Nat.lt_two_pow_self.le)
  have p := limit _ big
  rw [Nat.log2_two_pow] at p
  have v : w+1 ≤ (a+1)^2 := (Nat.lt_succ_sqrt' w).trans_le
    (Nat.pow_le_pow_left (Nat.succ_le_succ h.2.2) 2)
  calc
    _ ≤ C*((a+1)^2)^d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left v d)
    _ = C*(a+1)^(2*d) := by rw [pow_mul]
    _ ≤ _ := p


end
end Hierarchy.GridScale

end OAI
