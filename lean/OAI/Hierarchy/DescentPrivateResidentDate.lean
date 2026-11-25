import OAI.Hierarchy.DescentPrivateDepotPhase
import OAI.Hierarchy.DescentOrdinaryDonorInputs

namespace OAI
/-! # Source the stage meter directly from the prior physical field banks -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory DescentPackedZip DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
attribute [local irreducible] Stage.nativeParts DescentPacking.PackedMatch.topologyWords
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z D wire hist w short a : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
set_option quotPrecheck false
local notation "A" => prior.placement
local notation "J" => Fin (S.groupCount i)
local notation "native" => prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)
variable {he : 0≤ε} {choice : (prior.placement.stage.result he).Choice}
    {n : Normalize ((prior.placement.stage.result he).state choice)}
variable {z' D' : ℕ} {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he prior.placement.stage choice n next) (port : MeterPort prior)
local notation "H" => port.hosts
local notation "T" => (A).stage
local notation "home" => scanHomeAt he T
local notation "color" => scanColorAt he T
local notation "addr" => nativeAddress he T
local notation "rr" => BitDescription.scannedRows he T
local notation "lay" => bestLayout (branchWidth G (fun _ : (rr).pairs=>(T).z) ((rr).profile choice))
local notation "bytes" => donorNameBits (T).k (T).Δ
local notation "slots" => 2^(packExponent 20 (T).Δ)+2
local notation "grp" => Equiv.refl J
local notation "hosts" => port.vertex
variable (win : Fin (S.groupCount i)×prior.V→Fin (2^k)→Cell a) (hm : 0<port.groupsPerWord)
variable (named : prior.placement.SiteNamed (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)))
    (fit : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val<2^short)
    (winner : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val=
      1+2*heap (nativeAddress he prior.placement.stage (scanHomeAt he prior.placement.stage u)).2+
        (scanColorAt he prior.placement.stage u).toNat)
    (df : prior.placement.degree<2^short)
    (order : ∀e f,(prior.order e).val<(prior.order f).val ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
variable (profile : ℕ)
variable (b : ℕ) (m : Memory w)
    (sumSize : (shape (2^k) prior.placement.degree (2*prior.placement.cap) profile).outputBits*port.groupsPerWord≤w)
    (stored :
      let rankAt:=groupRank (Fin.valEmbedding : Fin (S.groupCount i) ↪ ℕ) (prior.vertex.trans Fin.valEmbedding)
      let shape₀:=shape (2^k) prior.placement.degree (2*prior.placement.cap) profile
      let world:=terrain (short:=short) prior.placement (prior.order.trans Fin.valEmbedding)
        S prior.valid (cableNames k rankAt) win (rotor prior.placement rankAt)
      let partsAt:=spread (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex world
      let inputs:=Gather.flat (Gather.descriptorInputs («K»:=2^(k+1)) shape₀ prior.placement.cap partsAt)
      ∀j,m (b+j.val)=((DescentPacking.PackedMatch.topologyWords («M»:=port.groupsPerWord) shape₀ inputs j).val:Computability.VPVNP.BurstRAM.Word w))
variable (dest : ℕ)
    (roster : Fin port.hosts→Fin prior.placement.degree→Option (Fin port.hosts))
    (mounted : ∀(z : Fin (S.groupCount i)×prior.V) j,roster (port.vertex z.2) j=
      (rotor prior.placement (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)) z j).map
        (fun h=>port.vertex h.2))
local notation "fmt" => Stage.shapeOf (short:=short) A bytes
local notation "measured" => Stage.nativeParts (short:=short) A native S prior.valid rank win grp hosts hm
  profile dest m roster (A).hub lay bytes

variable (birth :
    let stage:=prior.placement.stage
    let actor:=scanHomeAt he stage
    let tint:=scanColorAt he stage
    let flow:=nativeTraffic W.graph W.core actor
    let limit:=prior.placement.cap
    let shape₀:=shape (2^k) prior.placement.degree (2*limit) profile
    let cellAt:=Stage.slot he prior.placement (Equiv.refl (Fin (S.groupCount i))).toEmbedding port.vertex hm
    ∀c : ScanColonies he stage,∀e : Matched flow limit (thinList actor tint c) (thickList actor tint c),
      ∃j : Fin shape₀.pairs,j.val=(pairNumber (DescentPacking.amount (live flow))
        (slabPacking flow limit (thinList actor tint c) (thickList actor tint c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=DescentPacking.PackedMatch.SixBirths.slot (cellAt c).2 j q
        DescentPacking.PackedMatch.SixBirths.atom stage.z (digit (shape₀.digit+1) ip.val (m (dest+(cellAt c).1.val)).val) ip.val=
          some (stage.z,DescentTerminalEpochFlags.encode ((BitDescription.scannedRows he stage).profile choice ⟨c,e⟩),q.val))

local notation "M" => port.groupsPerWord


local notation "K" => 2^(k+1)
local notation "s" => shape (2^k) (A).degree (2*(A).cap) profile
local notation "terrain₀" => terrain (short:=short) A native S prior.valid (cableNames k rank) win (rotor A rank)
local notation "real" => spread (grp).toEmbedding hosts terrain₀
include named fit winner df order sumSize stored mounted birth in
theorem resident_depot_date_board
    (tabs : DepotRAM.Tables6) (R₀ : DepotRAM.Resident.Sources fmt K) (rom : DescentSIMDLookup.Banks)
    (localSpace : DepotRAM.Resident.Fits fmt s R₀ H (S.groupCount i) M w rom.source.base)
    (mountedFields : DepotRAM.Resident.Immutable («H»:=H) (G:=S.groupCount i) («M»:=M) fmt s R₀ (A).cap profile G.C G.k (A).z m)
    (terrainLease : Source R₀.terrain (fun h g=>Owners.register lay (real h g)) M m)
    (ports : ∀i,Source (R₀.signed i) (fun h g=>Stage.physicalSigned A native S prior.valid rank grp hosts h g
      (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) M m)
    (mates : Mounted R₀.peers roster m (S.groupCount i) M)
    (owners : DescentPackedColony.Reads R₀.owner (Stage.ownerWord (short:=short) A native S prior.valid rank win grp hosts profile lay) M m)
    (ordinals : DescentHaloPackedRebase.Reads R₀.ranks (Stage.ordinalChart A roster) M (S.groupCount i) m)
    (flags : DescentHaloPackedRebase.Reads R₀.hubs (Stage.hubChart («A»:=A) (roster:=roster) («hosts»:=hosts) (hub:=(A).hub)) M (S.groupCount i) m)
    (oldAt : R₀.fresh.topology.base=b) (bornAt : R₀.fresh.births.base=dest)
    (fitCode : DepotRAM.FitsInputs fmt tabs (DepotRAM.Resident.fields fmt s R₀ H (S.groupCount i) M) M rom.source.base w)
    (endAt : DescentSIMDLookup.Fits rom (DepotRAM.totalBits fmt) (DepotRAM.outputBits fmt) M H (S.groupCount i) w (port.base+1))
    (static : DepotRAM.Fixed fmt tabs M m)
    (literal : ∀pin : Cell (DepotRAM.totalBits fmt*M) ⊕ Fin (H*chunks (S.groupCount i) M),∀bit : Fin w,
      wordBits w (m (fixedAddr rom pin)) bit=wordBits w (fixedWord (DepotRAM.output fmt (A).cap profile G.b slots) pin) bit)
    (earlier : rom.dictionary.base+rom.dictionary.size≤rom.source.base ∧ rom.mask.base+rom.mask.size≤rom.source.base) :
    let phase:=DepotRAM.phase tabs (DepotRAM.Resident.fields fmt s R₀ H (S.groupCount i) M) rom (port.base+1) H (S.groupCount i) M w
    (phase.Runs m ∧ (∀a,a<rom.source.base→phase.image m a=m a) ∧ MeterPort.Pins ticket port (phase.image m)) ∧
      DescentPackedColony.Reads rom.source (fun h j=>DepotRAM.combine fmt (measured h j)) M (phase.image m) := by
  have loaded:=Stage.resident_fields (short:=short) A native S prior.valid rank win grp hosts hm profile dest m roster (A).hub lay bytes
    R₀ m rom.source.base localSpace mountedFields terrainLease ports mates owners ordinals flags (by rw [oldAt];exact stored)
    (by intro j;rw [bornAt])
  exact depot_date_board ticket port win hm named fit winner df order profile b m sumSize stored dest m roster mounted
    birth tabs _ rom m fitCode endAt static loaded literal earlier

include named fit winner df order sumSize stored mounted birth in
theorem resident_depot_date
    (tabs : DepotRAM.Tables6) (R₀ : DepotRAM.Resident.Sources fmt K) (rom : DescentSIMDLookup.Banks)
    (localSpace : DepotRAM.Resident.Fits fmt s R₀ H (S.groupCount i) M w rom.source.base)
    (mountedFields : DepotRAM.Resident.Immutable («H»:=H) (G:=S.groupCount i) («M»:=M) fmt s R₀ (A).cap profile G.C G.k (A).z m)
    (terrainLease : Source R₀.terrain (fun h g=>Owners.register lay (real h g)) M m)
    (ports : ∀i,Source (R₀.signed i) (fun h g=>Stage.physicalSigned A native S prior.valid rank grp hosts h g
      (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) M m)
    (mates : Mounted R₀.peers roster m (S.groupCount i) M)
    (owners : DescentPackedColony.Reads R₀.owner (Stage.ownerWord (short:=short) A native S prior.valid rank win grp hosts profile lay) M m)
    (ordinals : DescentHaloPackedRebase.Reads R₀.ranks (Stage.ordinalChart A roster) M (S.groupCount i) m)
    (flags : DescentHaloPackedRebase.Reads R₀.hubs (Stage.hubChart («A»:=A) (roster:=roster) («hosts»:=hosts) (hub:=(A).hub)) M (S.groupCount i) m)
    (oldAt : R₀.fresh.topology.base=b) (bornAt : R₀.fresh.births.base=dest)
    (fitCode : DepotRAM.FitsInputs fmt tabs (DepotRAM.Resident.fields fmt s R₀ H (S.groupCount i) M) M rom.source.base w)
    (endAt : DescentSIMDLookup.Fits rom (DepotRAM.totalBits fmt) (DepotRAM.outputBits fmt) M H (S.groupCount i) w (port.base+1))
    (static : DepotRAM.Fixed fmt tabs M m)
    (literal : ∀pin : Cell (DepotRAM.totalBits fmt*M) ⊕ Fin (H*chunks (S.groupCount i) M),∀bit : Fin w,
      wordBits w (m (fixedAddr rom pin)) bit=wordBits w (fixedWord (DepotRAM.output fmt (A).cap profile G.b slots) pin) bit)
    (earlier : rom.dictionary.base+rom.dictionary.size≤rom.source.base ∧ rom.mask.base+rom.mask.size≤rom.source.base) :
    let phase:=DepotRAM.phase tabs (DepotRAM.Resident.fields fmt s R₀ H (S.groupCount i) M) rom (port.base+1) H (S.groupCount i) M w
    phase.Runs m ∧ (∀a,a<rom.source.base→phase.image m a=m a) ∧ MeterPort.Pins ticket port (phase.image m) := by
  exact (resident_depot_date_board ticket port win hm named fit winner df order profile b m sumSize stored dest roster mounted birth
    tabs R₀ rom localSpace mountedFields terrainLease ports mates owners ordinals flags oldAt bornAt
    fitCode endAt static literal earlier).1

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
