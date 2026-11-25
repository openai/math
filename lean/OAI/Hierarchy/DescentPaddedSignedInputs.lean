import OAI.Hierarchy.DescentPaddedFlowChips
import OAI.Hierarchy.DescentPackedMatchSenderPins

namespace OAI
/-! # Decoding directed reset chips from the original packed signed aperture -/
namespace Hierarchy.DescentSixParty.PackedFlow.Padded
open DescentStageEdgeReceipt DescentColonies DescentSIMDLookup DescentSharedCableNames DescentPackedColony
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k age H N D R short M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} (A : GroupStage W G q ε J V k)
    (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S age)
    (groups : J≃Fin R) (hosts : V≃Fin H) (pd : A.degree≤D)
local notation "rank" => groupRank (groups.toEmbedding.trans Fin.valEmbedding) (hosts.toEmbedding.trans Fin.valEmbedding)
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k rank

def widen {a c D cap : ℕ} (degree : a≤D) (capacity : c≤cap) (x : Stage.Live a c) : Stage.Live D cap :=
  ⟨x.neighbor.castLE degree,x.wire.castLE capacity,x.sourceWire.castLE capacity,
   x.within.castLE capacity,x.target,x.markedOut⟩

theorem marked_widen {a c D cap : ℕ} (degree : a≤D) (capacity : c≤cap) (x : Option (Stage.Live a c)) :
    DescentPacking.PackedMatch.Local.Stage.marked short (x.map (widen degree capacity))=
      DescentPacking.PackedMatch.Local.Stage.marked short x := by cases x <;> rfl

def panel (v : Fin N) (g : Fin R) (s : DescentPackedFlowRAM.Slot (2^k) (2*A.cap)) :
    Option (Stage.Live D A.cap) :=
  (DescentPackedFlowPair.Padded.project H v).bind fun t=>
    (Stage.signedPanel A native S ready names ((groups.symm g,hosts.symm t),s.1) s.2).map (widen pd le_rfl)

theorem panel_token (v : Fin N) (g : Fin R) (s : DescentPackedFlowRAM.Slot (2^k) (2*A.cap)) :
    DescentPacking.PackedMatch.Local.Stage.marked short (panel A native S ready groups hosts pd v g s)=
      tokens A native S ready groups hosts short v g s := by
  unfold panel tokens
  cases DescentPackedFlowPair.Padded.project H v with
  | none=>rfl
  | some t=>exact marked_widen ..

theorem read_chips (s : DescentPackedFlowRAM.Slot (2^k) (2*A.cap)) (L : Banks) (out : Bank)
    (fit : Fits L (DescentSignedCableCodec.width D A.cap) short M N R w out.base) (m : Memory w)
    (pins : PinFrame (H:=N) (M:=M) L (DescentPackedMatchSenderPins.table D A.cap short)
      (fun h g=>DescentSignedCableCodec.encode (panel A native S ready groups hosts pd h g s)) m)
    (positive : 0<M) :
    let result:=image out.base (N*chunks R M) (DescentSIMDLookup.lookup L) m
    (DescentSIMDLookup.program L out.base N R M w).Exec m result (4+N*chunks R M*44) ∧
      Reads out (fun (h : Fin N) g=>tokens A native S ready groups hosts short h g s) M result ∧
      CheapCode (DescentSIMDLookup.program L out.base N R M w) := by
  simpa only [panel_token A native S ready groups hosts pd] using
    (DescentPackedMatchSenderPins.mounted L out fit (fun h g=>panel A native S ready groups hosts pd h g s) m pins positive)

end
end Hierarchy.DescentSixParty.PackedFlow.Padded

end OAI
