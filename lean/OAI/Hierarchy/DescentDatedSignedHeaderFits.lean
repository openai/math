import OAI.Hierarchy.DescentDatedSignedSourceRoom
import OAI.Hierarchy.DescentDatedCompactPeerTables

namespace OAI
/-! Address bounds for the original mark, compact neighbor and signed output header. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentSharedCableNames DescentSIMDLookup DescentPackedZip DescentDyadicSpan DescentPackedColony
open DescentParallelBase.ParentFilter DescentOrdinarySignedMeta DescentOrdinaryAtomFieldRAM.ROM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (s : SignedExtent) (I : s.Input) (base : ℕ) {w : ℕ}
local notation "top₀" => s.tailStart base
variable (prior : s.Prior I base w) (room : s.roof base+max s.slab s.oldSlab<2^w)

include room in
private theorem tail_fits : top₀<2^w :=
  (Nat.le_add_right ..).trans_lt (s.clock_room base room 21)

include room in
theorem gathered_fits (z : s.Socket) : (s.gathered base z).Fits w top₀ := by
  have space := tail_fits s base room
  have tables : s.rawStart base≤top₀ := s.cuts_mono base (by decide : (14:Fin 22)≤21)
  apply DescentPacking.PackedMatch.Local.Gather.fits (d:=s.fieldBits) (M:=s.lanes)
  intro f
  have rowFit : (s.rawField base z f).Fits w top₀ :=
    ⟨s.local_slice base z f _ (s.cuts_mono base (by decide : (8:Fin 22)≤21)) space,trivial⟩
  have entry := Fused.TablesROM.layout (D:=s.degree) (Q:=s.lowSites) (K:=s.tickets) (L:=s.cap)
    (b:=s.fieldBits) (M:=s.lanes) (base:=s.shapesStart base)
    (DescentPacking.PackedMatch.Local.Gather.setField (d:=s.fieldBits) (N:=11) f)
    (f.castAdd 2) (Fused.TablesROM.insert_page f) tables space (.lit 0) _ trivial rowFit
  exact ⟨rowFit,entry.shift,entry.apply,entry.shiftBits,entry.applyBits⟩

include room in
private theorem joined_read_fits {n : ℕ} (book : Fin n→Page) (width ptr : ℕ)
    (banks : Fin 2→Fin n) (x y : Expr) (xf : x.Fits w top₀) (yf : y.Fits w top₀)
    (bits : ∀i,(book i).bits≤width) (end₀ : ptr+n*2^width≤top₀) :
    ((joined book width ptr banks).read x y).Fits w top₀ := by
  have page (i : Fin n) := bank_room book width ptr top₀ i (bits i) end₀ (tail_fits s base room)
  exact ⟨page _,yf,page _,xf⟩

include prior room in
theorem flags_fits (z : s.Socket) : (s.flags I base z).Fits w top₀ := by
  apply joined_read_fits s base room
  · exact s.gathered_fits base room z
  · exact ProtocolRAMGeneratedWrite.fits_mono _ (s.cuts_mono base (by decide : (0:Fin 22)≤21)) (prior.mark z)
  · exact RawControls.bitsBound _ _ _
  · exact s.cuts_mono base (by decide : (15:Fin 22)≤21)

include prior room in
theorem signed_header_fits (x : Fin s.blocks) (j : Fin s.candidates) :
    ((s.layout I base).header x j).Fits w top₀ := by
  let z : s.Socket := (x,j)
  have line := s.gathered_fits base room z
  have early := ProtocolRAMGeneratedWrite.fits_mono _ (s.cuts_mono base (by decide : (0:Fin 22)≤21)) (prior.mark z)
  have raw := joined_read_fits s base room (RawControls.pages s.fieldBits s.fieldBits s.lanes)
    (RawControls.width s.fieldBits s.lanes) (s.rawStart base) (Fin.natAdd 2)
    _ _ line early (RawControls.bitsBound _ _ _) (s.cuts_mono base (by decide : (15:Fin 22)≤21))
  have roof : s.roof base<2^w := (Nat.le_add_right ..).trans_lt room
  have peer : (s.peerField I base z).Fits w top₀ := DescentPackedChildNeighbor.SIMD.fitted _ _
    (s.peer_chart_room_of_gathered base roof z line) _
  have tables := DescentOrdinarySignedMeta.pageFits I.newDegree s.fieldBits s.lanes
  have «meta» := s.cuts_mono base (by decide : (16:Fin 22)≤21)
  have pair := joined_read_fits s base room _ _ (s.metaStart base) (Fin.castAdd 2) _ _ peer raw tables «meta»
  exact joined_read_fits s base room _ _ (s.metaStart base) (Fin.natAdd 2) _ _
    (s.flags_fits I base prior room z) pair tables «meta»

include room in
theorem peer_head_fits (good : s.PeerInputs I base w) :
    (s.peerHeadExpr I base).Fits w (s.peerHeadOut base) := by
  let start := s.peerHeadBase base
  let L := s.reach*s.reach
  have eqOut : DescentOrdinaryCompactPeer.ROM.output start s.priorHosts s.hosts L s.lowSites=s.peerHeadOut base := by
    simp only [start,L,DescentOrdinaryCompactPeer.ROM.output,peerHeadOut,peerHeadWords,peerHeadRows,peerKinds,span,Nat.add_assoc]
  have top : s.peerHeadOut base+s.peerHeadRows<2^w :=
    (Nat.add_le_add_left (span_ge s.peerHeadRows) _).trans_lt (tail_fits s base room)
  have early : base≤ start := s.cuts_mono base (by decide : (0:Fin 22)≤19)
  have move (B : Bank) (h : B.Fits w base) : B.Fits w start := ⟨h.1,h.2.1,h.2.2.trans early⟩
  have layout := (DescentOrdinaryCompactPeer.ROM.arranged I.priorRanks I.priorEnds I.newNeighbors start I.hostPitch
    ⟨move _ good.ranks.1,good.ranks.2⟩ ⟨move _ good.ends.1,good.ends.2⟩ ⟨move _ good.neighbors.1,good.neighbors.2⟩
    good.prior good.hosts good.kinds good.targets good.width (eqOut ▸ top)).2
  rw [eqOut] at layout
  exact DescentOrdinaryCompactPeer.fits _ _ I.hostPitch _ layout

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
