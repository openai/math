import OAI.Hierarchy.ProbeFixedCalendarParameters

namespace OAI
/-! # The fixed maximum number of selector bits across the two actual packet menus -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage StripDirectory
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

def payloadSelectorBits (n : ℕ) : ℕ :=
  let menu := payloadMenu F n k v.positive v.radius (Nat.cast_nonneg _) v.toleranceAt
    v.geometry.cutoff.1 v.cost.payload v.cost.payload_nonneg 0
  Finset.univ.sup (fun i : menu.index => (menu.packet i).selectorBits)

def boughtSelectorBits : ℕ :=
  Finset.univ.sup (fun i : v.boughtPackets.index => (v.boughtPackets.packet i).selectorBits)

/-- The private input, stage height and payload width have no effect on this physical encoding bound. -/
def maxBits : ℕ := max (v.payloadSelectorBits (publicStages v.W)) v.boughtSelectorBits

theorem payload_selector_bits (n : ℕ) (hn : n = publicStages v.W) :
    v.payloadSelectorBits n ≤ v.maxBits := hn ▸ le_max_left _ _

theorem purchased_selector_bits : v.boughtSelectorBits ≤ v.maxBits := le_max_right _ _

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
