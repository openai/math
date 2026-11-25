import OAI.Computability.BorderVNP.TransmissionStartupArena
import OAI.Computability.BorderVNP.TeamScales

/-! # Word bounds for the physically allocated startup regions -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots.StartupArena

open Filter TeamScales

/-- At the manuscript widths the entire startup uses less than one processor-length
per processor and leaves another full such region below the word modulus. This estimate
is uniform even at the minimum logarithmic word width, with no restriction on the
number of processors. The second, wide boot copy may use one local block per processor. -/
theorem eventually_fits {ξ α : ℝ} (hx : 0 < ξ) (hxa : ξ ≤ α) :
    ∀ᶠ n : ℕ in atTop, ∀ (r teams header copied w : ℕ),
      0 < r → 2 < teams → header ≤ r*TeamScales.link ξ teams n → copied ≤ r*block ξ n →
      logWidth r n ≤ w →
      let arena : StartupArena := ⟨teams,r,TeamScales.literal α n,TeamScales.link ξ teams n,header,copied⟩
      arena.next < r*n ∧ arena.next+r*n < 2^w := by
  have large := eventually_rpow_gap (by linarith : 1-ξ/3 < 1) 20
  filter_upwards [large,eventually_ge_atTop 226] with n room hn
  intro r teams header copied w hr three hc cp wide arena
  have input := input_fields_le (by omega : 1 ≤ n) hx.le hxa teams
  let H := block ξ n
  have small : 20*H ≤ n := by
    have floor : (H : ℝ) ≤ (n : ℝ)^(1-ξ/3) := Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    rw [Real.rpow_one] at room
    exact_mod_cast (show 20*(H:ℝ) ≤ (n:ℝ) by linarith)
  have nativeInput : r*(2*TeamScales.literal α n+(teams-1)*TeamScales.link ξ teams n) ≤ r*(3*H) := Nat.mul_le_mul_left _ input
  have pins : 2*(r*TeamScales.literal α n) ≤ r*(3*H) := by
    rw [←Nat.mul_left_comm]
    apply Nat.mul_le_mul_left
    omega
  have maxLink : TeamScales.link ξ teams n ≤ 3*H := (Nat.le_mul_of_pos_left _ (by omega : 0<teams-1)).trans (by omega)
  have hdr := hc.trans (Nat.mul_le_mul_left r maxLink)
  have blockRoom : 10*H+112 < n := by omega
  have per : r*(10*H+112) < r*n := Nat.mul_lt_mul_of_pos_left blockRoom hr
  have constant : 112 ≤ r*112 := Nat.le_mul_of_pos_left _ hr
  have start : arena.next < r*n := by
    rw [StartupArena.next_eq]
    change r*(2*TeamScales.literal α n+(teams-1)*TeamScales.link ξ teams n)+112+copied+header+2*(r*TeamScales.literal α n) < r*n
    change copied ≤ r*H at cp
    calc
      _ ≤ r*(3*H)+r*112+r*H+r*(3*H)+r*(3*H) := by omega
      _ = r*(10*H+112) := by ring
      _ < r*n := per
  have log : logWidth r n = Nat.clog 2 (2*n*r) := by
    unfold logWidth
    rw [← Real.natCeil_logb_natCast]
    norm_cast
  have fit : 2*n*r ≤ 2^w := (Nat.le_pow_clog (by decide) _).trans
    (Nat.pow_le_pow_right (by decide) (log ▸ wide))
  exact ⟨start, (Nat.add_lt_add_right start (r*n)).trans_le (by rw [show r*n+r*n = 2*n*r by ring]; exact fit)⟩

end TeamContraction.ProcessorSlots.StartupArena

end BorderVNP
end Computability
end OAI
