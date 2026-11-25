import OAI.Hierarchy.PairedCursor
import OAI.Hierarchy.TraceNativeScale
import OAI.ThreeFlat.Diagonal.TraceCursorState
import OAI.ThreeFlat.Diagonal.TraceBitSourceOwner
import OAI.ThreeFlat.Diagonal.PhysicalIncidentWidth
import OAI.ThreeFlat.Diagonal.TraceSeedPriceTerm

namespace OAI
/-! # The initial occupied bit count and the work word for each native cursor site -/

noncomputable section
namespace Hierarchy.TraceReceiverSeedWords

open ThreeFlat Diagonal Diagonal.LaneCursor Diagonal.HistoryContraction
open Diagonal.TraceSourceOwner Diagonal.CompressorPacking
open Computability.VPVNP Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open scoped Classical BigOperators

variable {F : Type} [Field F] [Fintype F] {k low W pc regs words S base fuel : ℕ}
  (M : Machine W pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
  (hF : Fintype.card F ≤ 2^W) (st : Word W) (B : PhysicalStage.Block F) (hk : 2≤k+1)

def width (v : PairedCursor.Site (k+1)) :=
  if v.1=0 then (bitIndex hF t.width t.labels base st t.header t.time regs words t.grid v.2).x else 0

private abbrev budgetGrid :=
  TraceStaticRow.gateTable hF t.width t.labels base fuel st regs words ((k+1)+low)

private abbrev budgetShape :=
  TraceSourceOwner.shape W pc regs words S fuel ((k+1)+low) (budgetGrid M t hF st).internal

abbrev budgetState :=
  B.cursorState hk low (1+(((k+1)+low)+((k+1)+low))) (budgetGrid M t hF st).cells

def pairs (v : PairedCursor.Site (k+1)) := (width M t hF st v+1)/2

theorem pairs_le (v : PairedCursor.Site (k+1)) : pairs M t hF st v≤2^low := by
  have span : width M t hF st v ≤ 2*2^low := by
    unfold width
    split
    · rw [TraceSourceOwner.bitIndex_pinCount]
      calc
        _ ≤ pinSpan 1 low := Nat.min_le_left ..
        _ = _ := by simp [pinSpan]
    · omega
  unfold pairs
  omega

def start (v : PairedCursor.Site (k+1)) :=
  1+((budgetState M t hF st B hk).incidentWidth v + if decide (v.1=0) then
    pairs M t hF st v + TraceBitHeader.seedTraceWork low (budgetShape M t hF st).stride (budgetGrid M t hF st).cells B.cursorCopies ((k+1)+low) else 0)

theorem seed_pairs_budget (v : PairedCursor.Site (k+1)) :
    1+(budgetState M t hF st B hk).incidentWidth v+pairs M t hF st v ≤ start M t hF st B hk v := by
  by_cases active : v.1=0
  · simp [start,active]; omega
  · simp [start,active,pairs,width]

end Hierarchy.TraceReceiverSeedWords
end

end OAI
