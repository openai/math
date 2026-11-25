import OAI.Hierarchy.DescentPrivateResidentDate
import OAI.Hierarchy.DescentDepotResidentRoom

namespace OAI
/-! # Run the immutable table installation, dated geometry, and native ordinary donor gather -/
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
set_option maxHeartbeats 750000
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
local notation "M" => port.groupsPerWord
local notation "K" => 2^(k+1)
local notation "s" => shape (2^k) (A).degree (2*(A).cap) profile
local notation "terrain₀" => terrain (short:=short) A native S prior.valid (cableNames k rank) win (rotor A rank)
local notation "real" => spread (grp).toEmbedding hosts terrain₀
local notation "topology" => Gather.flat (Gather.descriptorInputs («K»:=K) s (A).cap real)
local notation "seat" => Stage.slot he A (grp).toEmbedding hosts hm
local notation "traffic" => nativeTraffic W.graph W.core home
variable (unit base : ℕ) (src top born : Bank) (priorMem : Memory w) (geometry : NativePhase w)
variable (roster : Fin port.hosts→Fin prior.placement.degree→Option (Fin port.hosts))
    (mounted : ∀(z : Fin (S.groupCount i)×prior.V) j,roster (port.vertex z.2) j=
      (rotor prior.placement (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)) z j).map
        (fun h=>port.vertex h.2))
local notation "fmt" => Stage.shapeOf (short:=short) A bytes
local notation "whole" => DepotRAM.Setup.words fmt s K H (S.groupCount i) M unit
local notation "boot" => DepotRAM.Setup.phase fmt s K H (S.groupCount i) M unit base (A).cap profile G.C G.k (A).z G.b slots w
local notation "liveMem" => ((boot).seq geometry).image priorMem
local notation "dest" => born.base
local notation "rom" => DescentSIMDLookup.Book.banks base (DepotRAM.totalBits fmt) H (S.groupCount i) M src
local notation "nextBase" => base+DescentSIMDLookup.Book.words (DepotRAM.totalBits fmt) H (S.groupCount i) M
local notation "tabs" => DepotRAM.Binary.joints fmt M unit nextBase
variable (R : DepotRAM.Resident.Sources
  (Stage.shapeOf (short:=short) prior.placement (donorNameBits prior.placement.stage.k prior.placement.stage.Δ))
  (2^(k+1)))
local notation "R₁" => DepotRAM.Setup.sources fmt s K H (S.groupCount i) M unit base R top born
local notation "f" => DepotRAM.Resident.fields fmt s R₁ H (S.groupCount i) M
local notation "stamped" => DepotRAM.phase tabs f rom (port.base+1) H (S.groupCount i) M w
include named fit winner df order mounted in
theorem installed_depot_date_board (large : 2*DepotRAM.totalBits fmt+1≤unit)
    (space : base+2*(whole+1)≤ src.base)
    (rowsFit : H*chunks (S.groupCount i) M≤ src.size)
    (earlier : src.base+src.size≤port.base+1)
    (extent : port.base+1+H*chunks (S.groupCount i) M<2^w)
    (packed : M*max (DepotRAM.totalBits fmt) (DepotRAM.outputBits fmt)≤w/2)
    (inputs : ∀j,(R.signed j).Fits w src.base) (terrainFit : R.terrain.Fits w src.base)
    (near : Accessible R.peers R.owner H (S.groupCount i) M w src.base)
    (ordFit : DescentHaloPackedRebase.Fits R.ranks H (S.groupCount i) M w src.base)
    (flagFit : DescentHaloPackedRebase.Fits R.hubs H (S.groupCount i) M w src.base)
    (topFit : top.Fits w src.base) (bornFit : born.Fits w src.base)
    (topCount : (K*H)*chunks (S.groupCount i) M≤top.size) (bornCount : (K*H)*chunks (S.groupCount i) M≤born.size)
    (bornWidth : DescentPacking.PackedMatch.SixBirths.width s M≤w) (sumSize : (s).outputBits*M≤w)
    (step : geometry.Runs ((boot).image priorMem))
    (saved : ∀x,x<base+whole→liveMem x=(boot).image priorMem x)
    (stored : ∀j,liveMem (top.base+j.val)=((DescentPacking.PackedMatch.topologyWords («M»:=M) s topology j).val:Computability.VPVNP.BurstRAM.Word w))
    (birth : ∀c : ScanColonies he T,∀e : Matched traffic (A).cap (thinList home color c) (thickList home color c),
      ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live traffic))
        (slabPacking traffic (A).cap (thinList home color c) (thickList home color c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=DescentPacking.PackedMatch.SixBirths.slot (seat c).2 j q
        DescentPacking.PackedMatch.SixBirths.atom (A).stage.z (digit ((s).digit+1) ip.val (liveMem (dest+(seat c).1.val)).val) ip.val=
          some ((A).stage.z,DescentTerminalEpochFlags.encode ((rr).profile choice ⟨c,e⟩),q.val))
    (terrainLease : Source R.terrain (fun h g=>Owners.register lay (real h g)) M liveMem)
    (ports : ∀i,Source (R.signed i) (fun h g=>Stage.physicalSigned A native S prior.valid rank grp hosts h g
      (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) M liveMem)
    (mates : Mounted R.peers roster liveMem (S.groupCount i) M)
    (owners : DescentPackedColony.Reads R.owner (Stage.ownerWord (short:=short) A native S prior.valid rank win grp hosts profile lay) M liveMem)
    (ordinals : DescentHaloPackedRebase.Reads (w:=w) («H»:=port.hosts) R.ranks (Stage.ordinalChart («H»:=port.hosts) A roster) M (S.groupCount i) liveMem)
    (flags : DescentHaloPackedRebase.Reads (w:=w) («H»:=port.hosts) R.hubs (Stage.hubChart («A»:=A) (roster:=roster) («hosts»:=hosts) (hub:=(A).hub)) M (S.groupCount i) liveMem)
    :
    ((((boot).seq geometry).seq stamped).Runs priorMem ∧
      (∀x,x<base→(((boot).seq geometry).seq stamped).image priorMem x=priorMem x) ∧
      MeterPort.Pins ticket port ((((boot).seq geometry).seq stamped).image priorMem)) ∧
      DescentPackedColony.Reads src (fun h g=>DepotRAM.combine fmt (Stage.nativeParts (short:=short) A native S prior.valid rank win grp hosts hm profile dest liveMem roster (A).hub lay bytes h g)) M ((((boot).seq geometry).seq stamped).image priorMem) := by
  have below : src.base<2^w:=by omega
  have enough : base+whole<2^w:=by omega
  obtain ⟨ran,lookup,bin,book⟩:=DepotRAM.Setup.prepared fmt s K H (S.groupCount i) M unit base (A).cap profile
    G.C G.k (A).z G.b slots src top born priorMem large enough geometry step saved
  obtain ⟨shape,reads⟩:=DepotRAM.Setup.room fmt s K H (S.groupCount i) M unit base src.base R top born
    large space below inputs terrainFit near ordFit flagFit topFit bornFit topCount bornCount bornWidth
  have static:=DepotRAM.Setup.immutable fmt s K H (S.groupCount i) M unit base R top born liveMem bin book
  obtain ⟨endFit,dict,mask⟩:=DepotRAM.Setup.lookup_room fmt s K H (S.groupCount i) M unit base src space
    rowsFit earlier extent packed
  obtain ⟨⟨gather,kept,pins⟩,board⟩:=resident_depot_date_board ticket port win hm named fit winner df order profile top.base liveMem sumSize
    stored born.base roster mounted birth tabs R₁ rom shape static terrainLease ports mates owners ordinals flags
    rfl rfl reads endFit bin.1 (fun j bit=>congrArg (fun x=>wordBits w x bit) (lookup j)) ⟨dict,mask⟩
  refine ⟨⟨NativePhase.seq_runs _ _ priorMem ran gather,?_,pins⟩,board⟩
  intro x hx
  have bootKeep:=(DepotRAM.Setup.mount fmt s K H (S.groupCount i) M unit base (A).cap profile G.C G.k (A).z G.b slots
    src top born priorMem large enough).2.2.2.2 x (.inl hx)
  exact (kept x (show x < src.base by omega)).trans ((saved x (by omega)).trans bootKeep)

include named fit winner df order mounted in
theorem installed_depot_date (large : 2*DepotRAM.totalBits fmt+1≤unit)
    (space : base+2*(whole+1)≤ src.base)
    (rowsFit : H*chunks (S.groupCount i) M≤ src.size)
    (earlier : src.base+src.size≤port.base+1)
    (extent : port.base+1+H*chunks (S.groupCount i) M<2^w)
    (packed : M*max (DepotRAM.totalBits fmt) (DepotRAM.outputBits fmt)≤w/2)
    (inputs : ∀j,(R.signed j).Fits w src.base) (terrainFit : R.terrain.Fits w src.base)
    (near : Accessible R.peers R.owner H (S.groupCount i) M w src.base)
    (ordFit : DescentHaloPackedRebase.Fits R.ranks H (S.groupCount i) M w src.base)
    (flagFit : DescentHaloPackedRebase.Fits R.hubs H (S.groupCount i) M w src.base)
    (topFit : top.Fits w src.base) (bornFit : born.Fits w src.base)
    (topCount : (K*H)*chunks (S.groupCount i) M≤top.size) (bornCount : (K*H)*chunks (S.groupCount i) M≤born.size)
    (bornWidth : DescentPacking.PackedMatch.SixBirths.width s M≤w) (sumSize : (s).outputBits*M≤w)
    (step : geometry.Runs ((boot).image priorMem))
    (saved : ∀x,x<base+whole→liveMem x=(boot).image priorMem x)
    (stored : ∀j,liveMem (top.base+j.val)=((DescentPacking.PackedMatch.topologyWords («M»:=M) s topology j).val:Computability.VPVNP.BurstRAM.Word w))
    (birth : ∀c : ScanColonies he T,∀e : Matched traffic (A).cap (thinList home color c) (thickList home color c),
      ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live traffic))
        (slabPacking traffic (A).cap (thinList home color c) (thickList home color c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=DescentPacking.PackedMatch.SixBirths.slot (seat c).2 j q
        DescentPacking.PackedMatch.SixBirths.atom (A).stage.z (digit ((s).digit+1) ip.val (liveMem (dest+(seat c).1.val)).val) ip.val=
          some ((A).stage.z,DescentTerminalEpochFlags.encode ((rr).profile choice ⟨c,e⟩),q.val))
    (terrainLease : Source R.terrain (fun h g=>Owners.register lay (real h g)) M liveMem)
    (ports : ∀i,Source (R.signed i) (fun h g=>Stage.physicalSigned A native S prior.valid rank grp hosts h g
      (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) M liveMem)
    (mates : Mounted R.peers roster liveMem (S.groupCount i) M)
    (owners : DescentPackedColony.Reads R.owner (Stage.ownerWord (short:=short) A native S prior.valid rank win grp hosts profile lay) M liveMem)
    (ordinals : DescentHaloPackedRebase.Reads (w:=w) («H»:=port.hosts) R.ranks (Stage.ordinalChart («H»:=port.hosts) A roster) M (S.groupCount i) liveMem)
    (flags : DescentHaloPackedRebase.Reads (w:=w) («H»:=port.hosts) R.hubs (Stage.hubChart («A»:=A) (roster:=roster) («hosts»:=hosts) (hub:=(A).hub)) M (S.groupCount i) liveMem)
    :
    (((boot).seq geometry).seq stamped).Runs priorMem ∧
      (∀x,x<base→(((boot).seq geometry).seq stamped).image priorMem x=priorMem x) ∧
      MeterPort.Pins ticket port ((((boot).seq geometry).seq stamped).image priorMem) := by
  exact (installed_depot_date_board ticket port win hm named fit winner df order profile unit base src top born priorMem geometry
    roster mounted R large space rowsFit earlier extent packed inputs terrainFit near ordFit flagFit
    topFit bornFit topCount bornCount bornWidth sumSize step saved stored birth terrainLease ports
    mates owners ordinals flags).1


end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
