import OAI.Hierarchy.DescentChronologicalHeld
import OAI.Hierarchy.DescentPrivateIssued
import OAI.Hierarchy.DescentPackedPrivateAccumulator
import OAI.Hierarchy.DescentRawCablePanel

namespace OAI
/-! # Exact packed-word private accumulator on the chosen chronological branch -/

namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM DescentHistoryOrder DescentKernelHistory DescentStageEdgeReceipt DescentPacking
open DescentSIMDLookup DescentPackedPrivateSum DescentPackedPrivateAccumulator
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k j i z₀ D₀ z D wire hist bw : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist} (path : Path start source)
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink source he T c n target)
variable (L : Layout) (C : Counters)
variable {H r M a : ℕ} (x : Fin H→Fin r→Cell (2+a))

/-- The full host panel is consumed at the packed physical price. Its entries read raw
edge-owner equalities in whole units; the single native scale by the active grain
size converts their sum to exactly the archived bit count. -/
theorem Path.Held.packed_ordinary (m : Memory bw)
    (held : path.Held C.prior m) (room : L.Room bw H r M) (space : C.scaling.Room bw)
    (positive : 0<M) (rows : Layout.count H r M≤L.source.size)
    (width : L.rom.bits=(2+a)*M) (ready : DescentPackedScore.Input (M:=M) L.source L.rom DescentRawCablePanel.score x m)
    (atEnd : C.words=L.starts+Layout.count H r M) (prior : C.prior<L.words)
    (panel : let raw := rawGraph he T c
      let owner := rawOwner he T c n ((BitDescription.scannedRows he T).state c) (originalId _)
      (∑v,∑i,DescentRawCablePanel.score (x v i))*T.z=
        ∑e:raw.Edge,if owner (raw.src e)=owner (raw.dst e) then raw.width e else 0) :
    (program L C bw H r M T.z).Exec m (image L C H r M T.z m) (Layout.billed H r M+C.scaling.steps T.z) ∧
    (path.ordinary ticket).Held C.out (image L C H r M T.z m) := by
  refine ⟨run L C T.z m room space,?_⟩
  have exactCost : (∑v,∑i,DescentRawCablePanel.score (x v i))*T.z=ordinaryFee ticket :=
    panel.trans (ticket.issued.owner_test ((BitDescription.scannedRows he T).state c) (originalId _))
  have readback := DescentPackedPrivateAccumulator.read L C DescentRawCablePanel.score x T.z path.privateCharge m
    room space (DescentRawCablePanel.score_zero a) positive rows width ready atEnd prior held
  change image L C H r M T.z m C.out=((path.privateCharge+ordinaryFee ticket:ℕ):Computability.VPVNP.BurstRAM.Word bw)
  rwa [exactCost] at readback

/-- The word-time bound and the single shared ROM size use this issued record's output width.
The packed score loop reads each word of lanes once. -/
theorem OrdinaryLink.panel_tariff (wide : 2*(2+a)≤bw) :
    (Layout.billed H r (lanes bw (2+a))+C.scaling.steps T.z)*bw≤
      40*(bw+H*bw+4*H*r*(2+a))+(56+4*ProtocolRAMPortScale.bitWidth T.z)*bw ∧
      2^((2+a)*lanes bw (2+a))≤2^(bw/2) :=
  DescentPackedPrivateAccumulator.tariff C bw H r (2+a) T.z (by omega) wide

end
end Hierarchy.DescentSixParty.Chronology

end OAI
