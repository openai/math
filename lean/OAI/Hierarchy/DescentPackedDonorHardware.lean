import OAI.Hierarchy.DescentStaticPortNames
import OAI.Hierarchy.DescentPackedDonorCheap

namespace OAI
/-! # Labels, registers and scratch slots of the complete native donor update -/
namespace Hierarchy.DescentPackedDonorTables
open ProtocolRAM DescentSIMDLookup DescentPackedPrivateAccumulator DescentPackedPrivateSum
open DescentStaticWordColumn
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr

theorem count_hardware (L : Layout) (C : Counters) (H r M w grain : ℕ) :
    names (DescentPackedPrivateAccumulator.program L C w H r M grain)≤199+8*ProtocolRAMPortScale.bitWidth grain := by
  have pref : names (ProtocolRAMEndpointPrefix.exclusive w L.words L.starts (Layout.count H r M))=38 := rfl
  have scalar:=names_scale w C.scaled 1 grain (DescentPrivateEdgeCounter.cell C.words)
  change names (ProtocolRAMStaticPorts.program w C.scaled 1 grain _)≤11+4*(6+1+2*ProtocolRAMPortScale.bitWidth grain) at scalar
  simp only [DescentPackedPrivateAccumulator.program,Layout.program,Counters.add,names_seq,names_scan,pref]
  change ((11+4*12)+38)+(names (ProtocolRAMStaticPorts.program w C.scaled 1 grain _)+(11+4*13))≤_
  omega

theorem full_hardware (bank : Banks) (L : Layout) (C : Counters) (H J M w grain : ℕ)
    {a b : ℕ} (resolver : Cell a→Cell (b*11)) (score : Cell b→ℕ) :
    names ((program bank L.rom.base H J M w resolver score).seq
      ((DescentSIMDLookup.program bank L.source.base H J M w).seq
        (DescentPackedPrivateAccumulator.program L C w H (J*11) (M*11) grain)))≤
      15*(size bank L.rom.base b M+1)+290+8*ProtocolRAMPortScale.bitWidth grain := by
  have acc:=count_hardware L C H (J*11) (M*11) w grain
  simp only [names_seq,program,DescentSIMDLookup.program,names_mount,names_scan,lookup_work]
  omega

end Hierarchy.DescentPackedDonorTables

end OAI
