import OAI.Hierarchy.DescentDatedCaptureMeaning
import OAI.Hierarchy.DescentPrivateNativeDate
import OAI.Hierarchy.DescentTerminalSignedGrainWord

namespace OAI
/-! # Numeric capture flags at the physically issued predecessor donor bank -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM DescentHistoryOrder DescentKernelHistory DescentStageEdgeReceipt DescentPacking
open DescentHostDegree DescentSIMDLookup DescentPackedPrivateSum DescentPackedPrivateAccumulator DescentRawCablePanel
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k i z D wire hist : ℕ}
variable {W : MarkedWorld F d P bits} {source : Reached W G q ε S k i z D wire hist}
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink source he T c n target)
variable {w : ℕ} (port : MeterPort source) (m : Memory w)

local notation "fromOwner" => (originalId ((T.result he).state c).graph.Site) ∘
  rawInput he T c ((BitDescription.scannedRows he T).state c)
local notation "owner" => rawOwner he T c n ((BitDescription.scannedRows he T).state c) (originalId _)
local notation "samples" => DescentRawCablePanel.Live source.placement (BitDescription.scannedRows he T).pick
local notation "width" => DescentRawCablePanel.span (S.groupCount i) k source.placement.cap

local notation "cellBits" => normBits source.placement.cap G.b G.C G.k
local notation "donorCols" => S.groupCount i*2^k*source.placement.cap
local notation "gain" => gainExponent 20 T.Δ
local notation "shelf" => 2^DescentHostDegree.packExponent 20 T.Δ+2
local notation "num" => donorNameBits T.k T.Δ
local notation "ibits" => bundleBits 3 num cellBits
local notation "sM" => port.groupsPerWord*(2^k*source.placement.cap)
local notation "saved" => (DescentPackedDonorSpace.banks port.base port.hosts donorCols sM ibits).source
local notation "issuedSlot" => DescentRawCablePanel.slot source.placement S source.valid
  (source.order.trans Fin.valEmbedding) port.vertex (Equiv.refl _) (BitDescription.scannedRows he T).pick

theorem MeterPort.capture_read (prior : MeterPort.Pins ticket port m) (pos : 0<sM) (packed : ibits*sM≤ w)
    (e : samples) :
    let a:=issuedSlot e
    let idx:=finProdFinEquiv.symm a.2
    let old:=DescentTerminalSignedGrainWord.chip (a:=ibits) saved m a.1 idx.1 pos
    let observation:=report T.k gain shelf (unpackDonor (loc:=3) (a:=num) (c:=cellBits) old) idx.2
    let first:=decide (fromOwner ((rawGraph he T c).src e.val)=fromOwner ((rawGraph he T c).dst e.val))
    let last:=decide (owner ((rawGraph he T c).src e.val)=owner ((rawGraph he T c).dst e.val))
    DepotRAM.Operand.datum true observation=first ∧ DepotRAM.Operand.datum false observation=(!first && last) := by
  dsimp only
  rw [DescentTerminalSignedGrainWord.chip_read saved m
    (fun h j=>packDonor (ticket.measuredDonors port.vertex h j)) prior _ _ pos packed,DescentRawCablePanel.unpack_pack]
  exact ticket.donor_captures port.vertex e

theorem MeterPort.capture_read_hole (prior : MeterPort.Pins ticket port m) (pos : 0<sM) (packed : ibits*sM≤ w)
    (h : Fin port.hosts) (idx : Fin width) (absent : ¬∃e : samples,issuedSlot e=(h,idx)) :
    let ix:=finProdFinEquiv.symm idx
    let old:=DescentTerminalSignedGrainWord.chip (a:=ibits) saved m h ix.1 pos
    let observation:=report T.k gain shelf (unpackDonor (loc:=3) (a:=num) (c:=cellBits) old) ix.2
    DepotRAM.Operand.datum true observation=false ∧ DepotRAM.Operand.datum false observation=false := by
  dsimp only
  rw [DescentTerminalSignedGrainWord.chip_read saved m
    (fun h j=>packDonor (ticket.measuredDonors port.vertex h j)) prior _ _ pos packed,DescentRawCablePanel.unpack_pack]
  exact ticket.donor_captures_hole port.vertex h idx absent

end
end Hierarchy.DescentSixParty.Chronology

end OAI
