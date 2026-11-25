import OAI.Hierarchy.ProtocolRAMFrozenWindowCost
import OAI.Hierarchy.ProtocolRAMTurnRankTextSize

namespace OAI
/-! # Stored instruction and register count of a fixed-format report publisher -/
namespace Hierarchy.ProtocolRAMFrozenWindow
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAM.Calendar ProbeStage.Native TaggedShorterReportedPublish

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

theorem Format.anchor_text (f : Format) (W r : ℕ) (a : Inputs) :
    text (f.anchorPhase W r a) = 188+16*a.owner.work := by
  simp only [Format.anchorPhase,ProtocolRAMPackedAnchorPair.program,ProtocolRAMSupergroupPorts.program,
    text_seq,text_scan,rowText,ProtocolRAMSupergroupPorts.groupExpr,ProtocolRAMSupergroupPorts.baseExpr,Expr.work]
  omega

theorem Format.rank_text (f : Format) (W r : ℕ) (a : Inputs) :
    text (f.rankPhase W r a) = 862 := by
  simp only [Format.rankPhase,ProtocolRAMPackedRanked.program,ProtocolRAMPackedInputs.groupSpread,
    text_seq,ProtocolRAMTurnText.generated,ProtocolRAMTurnText.common_text,text_passes,
    listText,rowText,ProtocolRAMPackedInputs.terms,ProbeStage.Native.columns,
    ProtocolRAMPackedInputs.spreadAddress,ProtocolRAMPackedInputs.triple,ProtocolRAMPackedInputs.weight,
    ProtocolRAMPackedInputs.keyWord,Expr.work,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]; rfl

/-- The owner expression is fixed when the phase is assembled. All capacities affect only the
public bounds and execution time of its loops. -/
theorem Format.phase_text (f : Format) (W r : ℕ) (a : Inputs) :
    text (f.phase W r a) = 5178+16*a.owner.work := by
  let s := f.window
  let A := f.tables r a
  let tape := f.N*f.cap
  have ⟨cl,cr,cs⟩ := clearedProcedure_size W (s.base r) s.maskWords (s.src r) tape f.γ r A
  have ⟨wl,wr,ws⟩ := TaggedShorterSlotWidth.procedure_size W (s.widthBase r) f.groups f.D
    (s.widthSrc r) tape f.γ (r+1) A a.origins
  change text ((f.anchorPhase W r a).seq ((f.rankPhase W r a).seq
    ((clearedProcedure W (s.base r) s.maskWords (s.src r) tape f.γ r A).seq
      (TaggedShorterSlotWidth.procedure W (s.widthBase r) f.groups f.D (s.widthSrc r)
        tape f.γ (r+1) A a.origins)))) = _
  rw [text_seq,text_seq,text_seq,f.anchor_text,f.rank_text]
  simp only [text,cl,cr,cs,wl,wr,ws]
  omega


end Hierarchy.ProtocolRAMFrozenWindow

end OAI
