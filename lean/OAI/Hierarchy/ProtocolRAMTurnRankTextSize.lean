import OAI.Hierarchy.ProtocolRAMTurnText

namespace OAI
/-! # Exact size of the terminal paid-occurrence rank program -/
namespace Hierarchy.ProtocolRAMTurnText
open Computability.VPVNP.BurstRAM PrivateRAM
open Hierarchy.ProtocolRAM Hierarchy.ProtocolRAM.Calendar
open ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure

set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

/-- The four absolute writes emit the original row ID, zero, paid amount, and key.
They compile to fixed register/label/public-slot totals independently of word size. -/
theorem gather_text (w n p src keys : ℕ) (weights ids : Bank) :
    text (ProtocolRAMRankGather.program w n p src keys (ProtocolRAMPackedCommon.inputBanks weights ids)
      ProtocolRAMRankGather.fields)=459 := by
  simp only [ProtocolRAMRankGather.fields,ProtocolRAMRankGather.program,text_seq,generated,text_scan]; rfl

theorem common_text (w n bins p src keys counters dst : ℕ) (weights ids : Bank) :
    text (ProtocolRAMPackedCommon.program w n bins p src keys counters dst (ProtocolRAMPackedCommon.inputBanks weights ids))=519 := by
  simp only [ProtocolRAMPackedCommon.program,text_seq,gather_text,text_scan]; rfl

private theorem key_work (b : RouteSettlement.Banks) (edges : ℕ) :
    (ProtocolRAMTurnPrefix.keyTerm b edges).work=20 := rfl

private theorem weight_work (b : RouteSettlement.Banks) (edges : ℕ) :
    (ProtocolRAMTurnPrefix.widthTerm b edges).work=129 := rfl

theorem rank_text_exact (w lo edges r : ℕ) (b : RouteSettlement.Banks) (paid : Bank) :
    text (ProtocolRAMTurnReplayed.procedure w lo edges r b paid)=1137 := by
  simp only [ProtocolRAMTurnReplayed.procedure,ProtocolRAMTurnPrefix.program,ProtocolRAMTurnPrefix.rankCode,
    text_seq,text_scan,common_text,rowText,key_work,weight_work]

end Hierarchy.ProtocolRAMTurnText

end OAI
