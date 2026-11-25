import OAI.Computability.BorderVNP.TeamSiteTimedRowModel
import OAI.Computability.BorderVNP.TeamSiteProcessorRowClock

/-! # Uniform clock for the installed timed endpoint and sorter row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor.Row

open VPVNP RAMTape BurstRAM TeamTapeHandoff Filter
variable {Q Γ : Type} {p r k a m g n d e w : ℕ} {P : TeamOpcode.Program p r k a}
variable {lib : Fin a → Macro Q Γ m g} {mark : Fin a → Γ}

/-- Each real timed endpoint respects the same local logical charge, including
a halted predecessor whose row is empty. -/
theorem charge_le (X : Site P lib mark n d e w) (N : ℕ) {es : List (TeamRAM.Event w)} {out : Frame w r}
    (row : Endpoint X N es out) : TeamTapeHandoff.cost es ≤ X.block.val := by
  change EndpointRow P X.pub _ X.block X.limit X.cap X.frame es out at row
  cases hf : X.frame with
  | accepted elapsed =>
    rw [hf] at row
    obtain ⟨rfl,_,_⟩ := row
    exact Nat.zero_le _
  | live pc regs elapsed =>
    rw [hf] at row
    obtain ⟨safe,pc,z,fin,_,chunk,_⟩ := row
    exact (chunk.clock (X.windowSafe elapsed safe)).1

/-- The actual complete physical row fits the remaining source clock after
the fixed input-measured private timer has been constructed. -/
theorem eventually_budget (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (mark : Fin a → Γ) :
    ∀ᶠ n : ℕ in atTop, ∀ {d e w : ℕ} (X : Site P lib mark n d e w) (dataLength : ℕ),
      X.block.val ≤ n → 2+e+d ≤ n → dataLength ≤ n →
      X.preludeTicks ≤ Processor.Budget.inputCost n w (2^e) dataLength + Processor.Budget.prefixCost r k w X.last →
      ∀ es out, Endpoint X (n^25) es out → budget X (n^25) es ≤ n^36-TeamClocked.prepSteps 25 n := by
  filter_upwards [TimedBudget.eventually_row r k m g (TimedBudget.meterCoefficient m g)] with n bound
  intro d e w X dataLength block dim data pre es out row
  have cost := (charge_le X _ row).trans block
  have step := bound es (X.slots es).length X.last X.hw X.hB dim data cost
  have total := X.cost_le_total dataLength pre (TimedBudget.body m g (TimedBudget.meterCoefficient m g) (n^25) es) es
  change budget X (n^25) es ≤ _ at total
  omega

end TeamSite.TimedProcessor.Row

end BorderVNP
end Computability
end OAI
