import OAI.Hierarchy.DescentResidentDonorFields

namespace OAI
/-! # The six resident columns at this actual ordinary stage -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentRawCablePanel DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentPackedZip DescentPackedColony
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k t short a H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)
variable (rank : (J×V)↪ℕ) (win : J×V→Fin (2^k)→Cell a)
    (group : J≃Fin G) (hosts : V↪Fin H) (hm : 0<M)
local notation "groups" => group.toEmbedding
local notation "K" => 2^(k+1)
local notation "r" => 2^k
local notation "p" => 2*A.cap
local notation "names" => cableNames k rank
local notation "peers" => rotor A rank
local notation "panel" => terrain (short:=short) A native S ready names win peers
local notation "real" => spread groups hosts panel
variable (profile : ℕ)
local notation "s" => shape r A.degree p profile
local notation "fieldsAt" => Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap real)
variable (dest : ℕ) (issuedMem : Memory w)
variable (roster : Fin H→Fin A.degree→Option (Fin H)) (hub : V→Bool) (lay : Bool)
variable (bytes : ℕ)
local notation "fmt" => shapeOf (short:=short) A bytes
local notation "keysAt" => topologyWords (M:=M) s fieldsAt
local notation "issuedAt" => fun i : Fin ((K*H)*chunks G M)=>SixBirths.cut (SixBirths.width s M) (issuedMem (dest+i.val)).val
local notation "tables" => nativeParts A native S ready rank win group hosts hm profile dest issuedMem roster hub lay bytes

theorem native_parts (v : Fin H) (g : Fin G) :
    DepotRAM.Resident.parts fmt s A.cap profile gadget.C gadget.k A.z hm real lay
      (physicalSigned A native S ready rank group hosts) roster (ordinalChart A roster)
      (hubChart (A:=A) (roster:=roster) (hosts:=hosts) (hub:=hub)) keysAt issuedAt v g=tables v g := rfl

/-- The original terrain and previous signed word shelves and the matcher's
originally emitted topology and six-selector banks furnish all numerical
inputs.  The same computed per-host tables are shared by every group. -/
theorem resident_fields (R : DepotRAM.Resident.Sources fmt K) (mem : Memory w) (base : ℕ)
    (room : DepotRAM.Resident.Fits fmt s R H G M w base)
    (fixed : DepotRAM.Resident.Immutable (H:=H) (G:=G) (M:=M) fmt s R A.cap profile gadget.C gadget.k A.z mem)
    (terrainLease : Source R.terrain (fun h g=>Owners.register lay (real h g)) M mem)
    (ports : ∀i,Source (R.signed i) (fun h g=>physicalSigned A native S ready rank group hosts h g
      (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) M mem)
    (mates : Mounted R.peers roster mem G M)
    (owners : Reads R.owner (ownerWord (short:=short) A native S ready rank win group hosts profile lay) M mem)
    (ordinals : DescentHaloPackedRebase.Reads R.ranks (ordinalChart A roster) M G mem)
    (flags : DescentHaloPackedRebase.Reads R.hubs (hubChart (A:=A) (roster:=roster) (hosts:=hosts) (hub:=hub)) M G mem)
    (priorTopology : ∀i,mem (R.fresh.topology.base+i.val)=((keysAt i).val:Word w))
    (retainedBirths : ∀i : Fin ((K*H)*chunks G M),mem (R.fresh.births.base+i.val)=issuedMem (dest+i.val)) :
    DepotRAM.Loaded fmt (DepotRAM.Resident.fields fmt s R H G M) tables M mem := by
  apply DepotRAM.Resident.loaded fmt s R A.cap profile gadget.C gadget.k A.z hm real lay
    (physicalSigned A native S ready rank group hosts) roster (ordinalChart A roster)
    (hubChart (A:=A) (roster:=roster) (hosts:=hosts) (hub:=hub)) keysAt issuedAt mem base room fixed terrainLease ports mates owners ordinals flags priorTopology
  intro i
  rw [retainedBirths]

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
