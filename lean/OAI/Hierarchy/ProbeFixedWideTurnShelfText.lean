import OAI.Hierarchy.ProbeFixedWideTerminal
import OAI.Hierarchy.ProtocolRAMTurnShelfText

namespace OAI
/-! # Instruction, register, and public-word count of the actual terminal chronology -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage ProbeStage.Native
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

theorem wide_turn_shelf_text_exact (h width bits rom work : ℕ) :
    let t:=v.wideTerminal h width bits rom work
    text (ProtocolRAMChronologicalShelf.program (wordBits h (2^v.W) copies)
      t.turns t.sites t.seats t.header t.headerBits t.startColumn t.source t.sourceBits
      t.rom t.romBits t.base t.scratch t.sink t.columns t.heads t.walk)=11098 := by
  intro t
  exact ProtocolRAMTurnText.chrono_text ..

theorem wide_turn_shelf_text : ∃K:ℕ,∀h width bits rom work,
    let t:=v.wideTerminal h width bits rom work
    text (ProtocolRAMChronologicalShelf.program (wordBits h (2^v.W) copies)
      t.turns t.sites t.seats t.header t.headerBits t.startColumn t.source t.sourceBits
      t.rom t.romBits t.base t.scratch t.sink t.columns t.heads t.walk)≤K :=
  ⟨11098,fun h width bits rom work=>(v.wide_turn_shelf_text_exact h width bits rom work).le⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
