import OAI.Hierarchy.DescentDatedTerrainAnchorRead
import OAI.Hierarchy.DescentDatedOperandPages
import OAI.Hierarchy.DescentDatedOriginSelector

namespace OAI
/-! # The original signed grain found by the retained task’s four physical header pages -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentSixParty DescentStageEdgeReceipt DescentRawCablePanel DescentSharedCableNames
open DescentHostDirectory DescentCableDonorNames DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option quotPrecheck false
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a H Z w M : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (groups : J≃Fin Z) (hosts : V↪Fin H) (win : J×V→Fin (2^k)→Cell a)
    (he : 0≤ε) (hm : 0<M) (profile dest : ℕ) (m : Memory w) (hub : V→Bool) (lay : Bool) (bytes : ℕ)
local notation "rank" => groupRank (groups.toEmbedding.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "near" => hostRotor hosts (DescentGroupPeerOrder.hostRoster A (hosts.trans Fin.valEmbedding))
local notation "fmt" => shapeOf (short:=short) A bytes
local notation "scene" => nativeParts (short:=short) A native S ready rank win groups hosts hm profile dest m near hub lay bytes
local notation "terrain₀" => terrain (short:=short) A native S ready (cableNames k rank) win (rotor A rank)
local notation "real" => spread groups.toEmbedding hosts terrain₀
local notation "matchShape" => shape (2^k) A.degree (2*A.cap) profile
local notation "fieldsAt" => Gather.flat (Gather.descriptorInputs (K:=2^(k+1)) matchShape A.cap real)
local notation "seat" => slot he A groups.toEmbedding hosts hm
open DescentOperandPriorIncidence DescentRawCablePanel.DepotRAM

open DescentTerminalSignedGrainWord DescentTerminalPointerDigits DescentColonies DescentKernelHistory
local notation "names" => cableNames k rank
local notation "board" => Prepare.signed A native S ready groups.toEmbedding hosts
variable (cables : Block k→Fin (2*A.cap)→Bank) (mem : Memory w)
    (prior : ∀x j,DescentPackedColony.Reads (cables x j) (fun h g=>DescentSignedCableCodec.encode (Prepare.signed A native S ready groups.toEmbedding hosts x j h g)) M mem)
    (wide : DescentSignedCableCodec.width A.degree A.cap*M≤w)
    (v : W.graph.Site) (coords : Function.Injective (fun s=>(A.pos s,A.block s)))
local notation "oldHost" => DescentSharedCableNames.Stage.home A v
local notation "previous" => scene (hosts (A.pos v).2) (groups (A.pos v).1)
local notation "oldWords" => fun s=>chip (cables (A.block v) s) mem (hosts (A.pos v).2) (groups (A.pos v).1) hm
local notation "tokenAt" => DescentTerminalPointerDigits.token A native S ready names v
local notation "ports" => A.CellPorts (A.pos v).1 (A.pos v).2 (A.block v)
local notation "recover" => DescentSharedCableNames.Stage.recover A oldHost
local notation "saved" u => DescentSharedCableNames.Stage.live A native S ready names oldHost u

include prior wide in
theorem original_signed_header_panel : Origin.signedWord fmt (A.block v) previous=oldWords := by
  funext t
  change (DescentSIMDLookup.encode _ ((2^k)*(2*A.cap))).symm
    (DescentSIMDLookup.encode _ _ (fun j=>physicalSigned A native S ready rank groups hosts (hosts (A.pos v).2) (groups (A.pos v).1)
      (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)) (finProdFinEquiv (A.block v,t))=_
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  rw [physical_signed_read]
  have original := DescentTerminalSignedGrainWord.chip_read (cables (A.block v) t) mem
    (fun h g => DescentSignedCableCodec.encode (board (A.block v) t h g))
    (prior (A.block v) t) (hosts (A.pos v).2) (groups (A.pos v).1) hm wide
  exact (congrArg DescentSignedCableCodec.encode
    (stored_site A native S ready groups.toEmbedding hosts (A.block v) t (A.pos v))).symm.trans original.symm

include prior wide coords in
theorem native_previous_headers (u : ports) (e : Incident W.graph v) (positive : 0<A.grainCount e.val)
    (atPort : recover u=⟨e.val,⟨0,positive⟩⟩) (peer : Fin A.degree) (serial : Fin A.cap)
    (address : peer.val*A.cap+serial.val=(tokenAt ⟨e,⟨0,positive⟩⟩).1) (outBits : ℕ) :
    let page:=fun f : Fin 4=>DescentDatedOperandPages.law fmt profile outBits
      (DescentDatedOperandPages.header fmt (A.block v) peer serial f).val (DepotRAM.combine fmt previous)
    ∃used : ports,recover used=⟨e.val,⟨0,positive⟩⟩ ∧
      page 0=(DepotRAM.Operand.ticket (saved used).sourceWire 0:Cell outBits) ∧
      page 1=((1+(saved used).neighbor.val:ℕ):Cell outBits) ∧ page 2=((saved used).target.toNat:Cell outBits) ∧
      page 3=((1+(saved used).sourceWire.val:ℕ):Cell outBits) := by
  intro page
  obtain ⟨used,recovered,found⟩:=origin_read A native S ready groups.toEmbedding hosts cables mem prior hm wide
    v coords u e ⟨0,positive⟩ atPort
  have key : (peer.val*A.cap+serial.val,0)=tokenAt ⟨e,⟨0,positive⟩⟩:=Prod.ext address rfl
  have input : ((1+peer.val*A.cap+serial.val:ℕ):Cell (originBits fmt)).val=1+(peer.val*A.cap+serial.val) := by
    have small : 1+peer.val*A.cap+serial.val < 2 ^ originBits fmt := origin_name_fits fmt peer serial
    change (1+peer.val*A.cap+serial.val)%(2^originBits fmt)=_
    rw [Nat.mod_eq_of_lt small,Nat.add_assoc]
  have good : origin (D:=A.degree) (cap:=A.cap) (Origin.signedWord fmt (A.block v) previous)
      (peer.val*A.cap+serial.val,0)=some (saved used) := by
    rw [original_signed_header_panel A native S ready groups hosts win hm profile dest m hub lay bytes cables mem prior wide v,key]
    exact found
  have read:=Origin.readOrigin_real fmt (A.block v) (originBits fmt) outBits 0 previous
    ((1+peer.val*A.cap+serial.val:ℕ):Cell _) (peer.val*A.cap+serial.val) (saved used) input good
  refine ⟨used,recovered,?_⟩
  have header (j : Fin 4) := DescentDatedOperandPages.header_value fmt profile outBits
    (A.block v) peer serial j previous
  exact ⟨(header 0).trans read.1, (header 1).trans read.2.1,
    (header 2).trans read.2.2.1, (header 3).trans read.2.2.2⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
