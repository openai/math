import OAI.Hierarchy.DescentDatedOperandPages
import OAI.Hierarchy.DescentDatedOriginRoom
import OAI.Hierarchy.DescentDonorNativeParts
import OAI.Hierarchy.DescentRetainedPanelSocket

namespace OAI
/-! # Source-preferred signed fields at the original old operand, including a loop -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentSixParty DescentStageEdgeReceipt DescentRawCablePanel DescentSharedCableNames
open DescentHostDirectory DescentCableDonorNames DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a H Z w M : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (groups : J≃Fin Z) (hosts : V↪Fin H) (win : J×V→Fin (2^k)→Cell a)
    (hm : 0<M) (profile dest : ℕ) (m : Memory w) (hub : V→Bool) (lay : Bool) (bytes : ℕ)
local notation "rank" => groupRank (groups.toEmbedding.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "near" => hostRotor hosts (DescentGroupPeerOrder.hostRoster A (hosts.trans Fin.valEmbedding))
local notation "fmt" => shapeOf (short:=short) A bytes
local notation "scene" => nativeParts (short:=short) A native S ready rank win groups hosts hm profile dest m near hub lay bytes
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
local notation "tokenAt" => DescentTerminalPointerDigits.token A native S ready names v
local notation "recover" => DescentSharedCableNames.Stage.recover A oldHost
local notation "saved" => DescentSharedCableNames.Stage.live A native S ready names oldHost

local notation "first_" => DescentTerminalPortChart.first A v


include coords in
theorem preferred_material_headers (edge : Incident W.graph v) (positive : 0<A.grainCount edge.val) (outBits : ℕ) :
    let r:=saved (first_ edge positive)
    let page:=fun f : Fin 4=>DescentDatedOperandPages.law fmt profile outBits
      (DescentDatedOperandPages.header fmt (A.block v) r.neighbor r.wire f).val (DepotRAM.combine fmt previous)
    r.sourceWire=DescentSharedCableNames.Stage.outgoing A native S ready ⟨edge.val,positive⟩ ∧
      r.target=decide (W.graph.src edge.val≠v) ∧
      page 1=((1+r.neighbor.val:ℕ):Cell outBits) ∧ page 2=(r.target.toNat:Cell outBits) ∧
      page 3=((1+r.sourceWire.val:ℕ):Cell outBits) :=by
  intro r page
  let u:=first_ edge positive
  have recovered : recover u=⟨edge.val,⟨0,positive⟩⟩:=by
    dsimp only [u,DescentTerminalPortChart.first];split <;> rfl
  have source : r.sourceWire=DescentSharedCableNames.Stage.outgoing A native S ready ⟨edge.val,positive⟩:=by
    change DescentSharedCableNames.Stage.outgoing A native S ready ⟨(recover u).1,_⟩=_
    exact congrArg (DescentSharedCableNames.Stage.outgoing A native S ready) (Subtype.ext (congrArg Sigma.fst recovered))
  have side : r.target=decide (W.graph.src edge.val≠v):=by
    dsimp only [r,DescentTerminalPortChart.first]
    split <;> rename_i face <;> simp [DescentSharedCableNames.Stage.live,DescentSharedCableNames.Stage.signedBit,face]
  have preferred:=retained_first_origin A native S ready names v coords edge positive
  have words : Origin.signedWord fmt (A.block v) previous=
      fun t=>DescentSignedCableCodec.encode (DescentSharedCableNames.Stage.signedPanel A native S ready names oldHost t):=by
    funext t
    change (DescentSIMDLookup.encode _ ((2^k)*(2*A.cap))).symm
      (DescentSIMDLookup.encode _ _ (fun j=>physicalSigned A native S ready rank groups hosts (hosts (A.pos v).2) (groups (A.pos v).1)
        (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)) (finProdFinEquiv (A.block v,t))=_
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply,physical_signed_read]
    rfl
  let key:=r.neighbor.val*A.cap+r.wire.val
  have label : (key,0)=tokenAt ⟨edge,⟨0,positive⟩⟩:=by
    apply Prod.ext
    · change r.neighbor.val*A.cap+r.wire.val=(finProdFinEquiv (r.neighbor,r.wire)).val
      rw [finProdFinEquiv_apply_val]
      ac_rfl
    · rfl
  have found : origin (D:=A.degree) (cap:=A.cap) (Origin.signedWord fmt (A.block v) previous) (key,0)=some r:=by
    rw [words,label]
    exact preferred
  have input : ((1+r.neighbor.val*A.cap+r.wire.val:ℕ):Cell (originBits fmt)).val=1+key:=by
    have small : 1+r.neighbor.val*A.cap+r.wire.val < 2^originBits fmt := origin_name_fits fmt r.neighbor r.wire
    change (1+r.neighbor.val*A.cap+r.wire.val)%(2^originBits fmt)=_
    rw [Nat.mod_eq_of_lt small,Nat.add_assoc]
  have hit:=Origin.readOrigin_real fmt (A.block v) (originBits fmt) outBits 0 previous
    ((1+r.neighbor.val*A.cap+r.wire.val:ℕ):Cell _) key r input found
  refine ⟨source,side,?_⟩
  have header (j : Fin 4) := DescentDatedOperandPages.header_value fmt profile outBits (A.block v) r.neighbor r.wire j previous
  exact ⟨(header 1).trans hit.2.1,(header 2).trans hit.2.2.1,(header 3).trans hit.2.2.2⟩

include prior wide coords in
omit prior wide in
theorem preferred_previous_headers (edge : Incident W.graph v) (positive : 0<A.grainCount edge.val) (outBits : ℕ) :
    let r:=saved (first_ edge positive)
    let page:=fun f : Fin 4=>DescentDatedOperandPages.law fmt profile outBits
      (DescentDatedOperandPages.header fmt (A.block v) r.neighbor r.wire f).val (DepotRAM.combine fmt previous)
    r.sourceWire=DescentSharedCableNames.Stage.outgoing A native S ready ⟨edge.val,positive⟩ ∧
      r.target=decide (W.graph.src edge.val≠v) ∧
      page 1=((1+r.neighbor.val:ℕ):Cell outBits) ∧ page 2=(r.target.toNat:Cell outBits) ∧
      page 3=((1+r.sourceWire.val:ℕ):Cell outBits) :=by
  exact preferred_material_headers (short:=short) A native S ready groups hosts win hm profile dest m hub lay bytes v coords edge positive outBits

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
