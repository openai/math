import OAI.Hierarchy.ProbeConfiguredFormat
import OAI.Hierarchy.ProtocolRAMCalendarDeadlineROM

namespace OAI
/-! # Native packet and discrepancy digits at every scheduled temperature -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage PurchaseCT
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)

def basePhase (width : ℕ) :=
  publicPhase (publicStages v.W) v.a v.radius v.W (probeHeat v.W) 1 width v.precision

def digitRadix := v.precision*(publicStages v.W+v.radius+2)+1

theorem quote_digit {s : ℝ} (positive : 0<s) (width kind stock : ℕ) :
    (publicPhase (publicStages v.W) v.a v.radius v.W (probeHeat v.W) s width v.precision).word kind stock<v.digitRadix := by
  let N:=publicStages v.W
  have a : 0<(v.a:ℝ):=by exact_mod_cast v.quadratic_pos
  have bound:=(public_quote_mem (T:=probeHeat v.W) (W:=v.W) a (Nat.cast_nonneg v.radius) positive
    N width v.precision kind stock).2
  have below : (if kind=0 then (N:ℝ) else (v.radius:ℝ)+1)≤(N+v.radius+2:ℕ) := by
    push_cast
    have hn : 0≤(N:ℝ):=Nat.cast_nonneg _
    have hr : 0≤(v.radius:ℝ):=Nat.cast_nonneg _
    split <;> linarith
  have digit:=Nat.floor_le_of_le (n:=v.precision*(N+v.radius+2))
    (by simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left (bound.trans below) (Nat.cast_nonneg v.precision))
  exact Nat.lt_succ_of_le digit

theorem scheduled_digit (width i j a b kind stock : ℕ) (date : i≤v.mesh.inject+v.mesh.cool) :
    (deadline v.mesh v.finish (v.basePhase width) (.outer i a)).word kind stock<v.digitRadix ∧
    (deadline v.mesh v.finish (v.basePhase width) (.inner i a j b)).word kind stock<v.digitRadix := by
  have hot : 0<(v.finish:ℝ):=by exact_mod_cast v.clock.finish_pos
  have times:=v.real_times date
  exact ⟨v.quote_digit (hot.trans_le times.1) width kind stock,
    v.quote_digit ((half_pos hot).trans_le (times.2 j)) width kind stock⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
