import OAI.Hierarchy.DescentScalarVenueReceiver
import OAI.Hierarchy.DescentScalarActorPublisherROM

namespace OAI
/-! # One output raster from the simultaneous route and owner-key banks -/
namespace Hierarchy.DescentScalarVenueMask.Raster
open DescentSIMDLookup DescentPackedZip DescentSharedCableNames DescentPackedColony DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {P r cap raw low k gain slots H G M w : ℕ}
local notation "K"=>1+cap*6
local notation "A"=>DescentPackedActorMask.actors (P*r) cap

structure Shape (P r cap : ℕ) where
  ports : Ports P
  route : Fin r→Fin (1+cap*6)→Bank
  key : Fin r→Fin (1+cap*6)→Bank
  hub : Bank
  ends : Bank

variable (S : Shape P r cap) (k gain slots raw low H G M base : ℕ)
local notation "C"=>Receiver.view S.ports S.route S.key S.hub k gain slots raw low M H G base
local notation "f"=>Receiver.entries k gain slots raw low A
local notation "u"=>Receiver.unit raw low A
local notation "next"=>Receiver.header base raw low M A
local notation "out"=>Headers.post next H G M P
local notation "n"=>H*chunks G M

def output (P r cap raw low H G M base : ℕ):=Headers.post (Receiver.header base raw low M (DescentPackedActorMask.actors (P*r) cap)) H G M P

def code (w : ℕ) :=((Book.install f u M w base).seq (Headers.code S.ports.roster S.ends next H G M P w)).seq (scan w out n ((C).all H))

def result (m : Memory w):=ProtocolRAM.image out n ((C).all H) (Headers.image S.ports.roster S.ends next H G M P (Book.image f u M base m))

def ticks:=((4+10*Receiver.length raw low M A)+Headers.ticks S.ports.roster S.ends next H G M P)+(4+n*(2*((C).all H).work+4))

theorem run (walks : Fin H→Fin P→Option (Fin H)) (t : Fin r→Fin K→Fin H→Fin G→Ticket P raw) (hubs : Fin H→Fin G→Cell 1) (m : Memory w)
    (old : Receiver.Raw S.ports S.route S.key S.hub S.ends base walks t hubs M m) (room : out+n<2^w) :
    let o:=result S k gain slots raw low H G M base m
    (code S k gain slots raw low H G M base w).Exec m o (ticks S k gain slots raw low H G M base) ∧
      (∀p:Row H G M,o (out+(row H G M p).val)=((data (fun h g=>encode (Packed.bits low) A (DescentScalarVenueMask.fields walks t hubs k gain slots low h g)) p).val:Word w)) ∧
      (∀j,j<base ∨ out+n≤j → o j=m j) ∧ CheapCode (code S k gain slots raw low H G M base w):=by
  intro o
  obtain ⟨setup,ready,keep,cheap⟩:=Receiver.mount S.ports S.route S.key S.hub S.ends k gain slots low base walks t hubs m old room
  have rows:=issued C walks t hubs out _ ready
  have check: ((C).all H).Fits w out:=Gather.fits (C).masks ((C).one H) out ready.collectFits _
  have lowBound:base≤out:=by
    dsimp [Headers.post,Headers.rom,Headers.afterHeaders,Headers.start,Receiver.header,DescentPackedChildNeighbor.SIMD.ROM.output]
    repeat first | exact le_rfl | apply Nat.le_add_right_of_le
  refine ⟨setup.then (scan_exec out n ((C).all H) _ check room),fun p=>(ProtocolRAMGeneratedWrite.read_image out n ((C).all H) _ (row H G M p)).trans (rows p),?_,cheap_seq cheap (@scan_cheap _ _ _ _)⟩
  intro a safe
  rcases safe with lo|hi
  · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (lo.trans_le lowBound))).trans (keep _ (.inl lo))
  · exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inr hi)).trans (keep _ (.inr ((Nat.le_add_right ..).trans hi)))

end
end Hierarchy.DescentScalarVenueMask.Raster

end OAI
