import OAI.Hierarchy.DescentResetTrunkOriginalHeaders
import OAI.Hierarchy.DescentResetStemCompactRack
import OAI.Hierarchy.DescentResetWindowEmittedSources

namespace OAI
/-! # Identify the native dense reset rack with the actual common hosts -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

open DescentResetFieldAssembler DescentPackedZip DescentSIMDLookup ProtocolRAM DescentSortedRoster DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "radius" => (Z).k-(T).commonDepth
local notation "depth_" => GroupStage.depthBound D n f g
local notation "roster_" => DescentDenseHostOrder.roster (Z).graph radius depth_
local notation "rawWord" => DescentResetFieldAssembler.raw
local notation "used" => Fintype.card B.next.V
local notation "N" H:arg => (H*(roster_).card)
local notation "name_" pad => (Z).rawHostRank T ((vertexCode).trans (Fin.castLEEmb pad))


open DescentResetStemMaskedPorts DescentResetPeerUnionRAM
variable {H H₁ p : ℕ} (previous : Fintype.card input.V≤H)
local notation "vertex" => (vertexCode).trans (Fin.castLEEmb previous)
local notation "rank" => (Z).rawHostRank T vertexCode
local notation "real" => (Z).rawHostRank T vertex
local notation "compressed" => (Z).denseHostRank T vertex

theorem input_rack (j : Fin H₁) :
    (Z).compactRack T vertex j=originalTrunkRack B j :=by
  have same : DescentStageEdgeReceipt.dense (compressed)=denseOrder B :=
    Equiv.ext (fun u=>Fin.ext (dense_physical B previous u))
  simp only [ResetInput.compactRack,originalTrunkRack,same]
  split <;> split <;> first | rfl | contradiction

theorem calibrated_rack (j : Fin H₁) (u : B.next.V)
    (held : originalTrunkRack B j=some u) :
    let live:=((Z).rack_located T vertex j u ((input_rack B previous j).trans held))
    let code : Fin used:=⟨j.val,live⟩
    ((Z).rawAtIndex T vertex code).val=((rank) u).val ∧
    ((Z).parentIndex T vertex code).val=((vertexCode) (position (Z).graph u.val)).val ∧
    priorHub vertex (fun z=>input.placement.hub (B.frame.host.symm z)) ((Z).parentIndex T vertex code)=
      input.placement.hub (B.frame.host.symm (position (Z).graph u.val)) :=by
  intro live code
  obtain ⟨raw,parent,hub⟩:=(Z).rack_registers T vertex (fun z=>input.placement.hub (B.frame.host.symm z)) j u
    ((input_rack B previous j).trans held)
  exact ⟨congrArg Fin.val raw,congrArg Fin.val parent,hub⟩

theorem calibrated_halo (record : B.Recorded p) (near : Fin (N H)→Fin 3→Option (Fin (N H)))
    (u : B.next.V)
    (four : present (selfPeers near) ((real) u)=(insert u ((Z).emittedNear T u)).map (real))
    (absent : (∀j,near ((real) u) j≠some ((real) u)) ↔ u∉(Z).emittedNear T u) :
    (present near ((real) u)).map Fin.valEmbedding=
      (B.next.placement.near u).map ((rank).trans Fin.valEmbedding) :=by
  have bare:=measured_neighbors near (real) ((Z).emittedNear T) u four absent
  rw [bare,rendered_near B record,Finset.map_map]
  rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
