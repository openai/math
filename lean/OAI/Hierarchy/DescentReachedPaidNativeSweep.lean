import OAI.Hierarchy.DescentReachedPaidRaster
import OAI.Hierarchy.DescentPaidSweepRun

namespace OAI
/-! # Both actual old-rack outputs of the native paid and actor sweeps -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSixParty.StarKeys
open DescentColonies DescentGL DescentWalshTables DescentPacking
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentSortedHaloRaster DescentHaloWalkRAM DescentSIMDLookup
open DescentScalarVenueMask DescentHostDirectory.SiteDecode DescentOrdinaryLocalBirth DescentSharedCableNames DescentPackedActorMask
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentScalarBookReshape
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
local notation "r" => BitDescription.scannedRows he T
local notation "capV" => Fin (S.groupCount i)×cap.V
local notation "sw" => branchWidth G (fun _ : (r).pairs=>T.z) ((r).profile c)
local notation "stepGraph" => rawGraph he T c
local notation "sel" => scanWorld he T c
local notation "next" => (ticket.advance arch).bit
local notation "units" => fun _ : (r).pairs=>T.z
local notation "stageLimit" => fun _ : (r).pairs=>le_refl T.z
local notation "layout" => bestLayout sw
local notation "group" => GadgetNetwork.newSite W.graph (r).pick layout (r).pack

local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c
local notation "addr" => MarkedWorld.address sel key (bookChart).hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel key (bookChart).hub T.k (gainExponent 20 T.Δ))
local notation "venue" => addr ∘ group
local notation "stageBits" => physicalBits G W.toWorld (r).pick units stageLimit ((r).profile c) arch.bit.recipe

local notation "A" => cap.placement
local notation "deg" => (A).degree
local notation "near" => groupedNear (A).near
local notation "bound" => (deg+1)^4*2^k
local notation "sites" => (A).site cap.vertex cap.valid.coordinates

local notation "roster" => hostRotor cap.vertex (hostRoster A (cap.vertex.trans Fin.valEmbedding))
local notation "reach" => Gather.reaching roster
local notation "halo" => reachedHalo ticket
local notation "name" => rackName (cap:=cap)

local notation "shelf"=>2^(packExponent 20 deg)+2
local notation "pitch"=>(2^(k+1)-1)*shelf
local notation "raw"=>2^(k+1)*shelf
local notation "used"=>fun p:(r).pairs=>(r).picked (p,0)
local notation "oldID"=>cap.order.trans Fin.valEmbedding
local notation "origin"=>outgoingSlot A oldID S cap.valid (r).pick used
local notation "breadth"=>DescentHaloWalkRAM.breadth deg
local notation "K"=>1+(A).cap*6
local notation "moves"=>rotor A (groupRank Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding))

open DescentPaidResidentCount
variable {mb : ℕ}
variable (tokens : Block k→Fin (1+cap.placement.cap*6)→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→
  Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
local notation "physical" => DescentScalarVenueMask.fields reach tokens (flags (cap:=cap)) k (gainExponent 20 deg) shelf pitch
local notation "stock" => Descriptors shelf k (A).pos (A).block (ticketParent (he:=he) (T:=T)) (ticketSlot (c:=c) ticket)
  (key∘group) cap.vertex (Function.Embedding.refl _) moves tokens
local notation "oldCensus" => fun x h g=>Census.count A (Equiv.refl _) cap.vertex mb h g x
local notation "counts" => DescentOrdinaryAtomFieldRAM.RoleCounts.priorValue reach oldCensus
local notation "cost" => fun u : W.graph.Site=>((A).records u).length
local notation "dest" => n.destination∘rawInput he T c ((r).state c)

local notation "OH" => Fintype.card cap.V
local notation "OG" => S.groupCount i

open DescentPackedZip ThreeFlat.RAM
variable (oldH grain floor w : ℕ) (ids charged : Expr)
local notation "labels" => fun l : Fin pitch=>Packed.token (some l)
local notation "tagBits" => Packed.bits pitch
local notation "rowN" => Sweep.rowCount oldH OG grain
local notation "paid₀" => Sweep.paidBank floor pitch bound (A).cap mb tagBits oldH OG grain
local notation "seen₀" => Sweep.aliveBank floor pitch bound (A).cap mb tagBits oldH OG grain
local notation "roof₀" => Sweep.roof floor pitch bound (A).cap mb tagBits oldH OG grain
local notation "code₀" => Sweep.program floor bound (A).cap mb oldH OG grain labels ids charged w
local notation "cost₀" => Sweep.ticks floor bound (A).cap mb oldH OG grain labels ids charged
local notation "done" => @Sweep.image pitch tagBits w floor bound (A).cap mb oldH OG grain labels ids charged
local notation "fields₀" => fun (h : Fin oldH) (g : Fin OG) j=>
  if inside:h.val<OH then physical ⟨h.val,inside⟩ g j else 0
local notation "charge₀" => fun (h : Fin oldH) (g : Fin OG) j=>
  if inside:h.val<OH then counts ⟨h.val,inside⟩ g j else 0

/-- Word reads include all padded hosts, every old group and every native local digit. -/
theorem paid_shelves_issued (m : Memory w) (early₁ : ids.Fits w floor) (early₂ : charged.Fits w floor)
    (allLabels : Source ids (fun h g=>encode tagBits _ (fields₀ h g)) grain m)
    (allCounts : Source charged (fun h g=>encode mb bound (charge₀ h g)) grain m)
    (space : roof₀<2^w) :
    (code₀).Exec m (done m) cost₀ ∧
    (∀(l : Fin pitch) (s : Row oldH OG grain),done m ((paid₀).base+l.val*rowN+(row oldH OG grain s).val)=
      ((data (fun (h : Fin oldH) g=>if inside:h.val<OH then
        paidRaster (mb:=mb) ticket tokens l ⟨h.val,inside⟩ g else 0) s).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    (∀(l : Fin pitch) (s : Row oldH OG grain),done m ((seen₀).base+l.val*rowN+(row oldH OG grain s).val)=
      ((data (fun (h : Fin oldH) g=>if inside:h.val<OH then
        actorRaster ticket tokens l ⟨h.val,inside⟩ g else 0) s).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    (∀a,a<floor ∨ roof₀≤a→ done m a=m a) ∧ CheapCode code₀ :=by
  have live (l : Fin pitch) : Packed.token (some l)≠0:=by
    intro h;have bad:=congrArg (Packed.readToken pitch) h
    rw [Packed.token_back] at bad
    change some l=none at bad
    cases bad
  have actual:=Sweep.any floor bound (A).cap mb oldH OG grain labels ids charged m early₁ early₂ space
  have read:=Sweep.issued floor bound (A).cap mb oldH OG grain labels ids charged m early₁ early₂
    fields₀ charge₀ allLabels allCounts live space
  have blank (u v : ℕ) : encode u v (fun _=>0)=0 :=by
    apply Fin.ext
    change (finFunctionFinEquiv (fun _ : Fin v=>(0:Cell u))).val=0
    simp
  refine ⟨actual.1,?_,?_,actual.2⟩
  · intro l s
    apply (read.1 l s).trans
    apply congrArg (fun f : Fin oldH→Fin OG→ Cell mb=>((data f s).val:Computability.VPVNP.BurstRAM.Word w))
    funext h g
    by_cases good : h.val<OH
    · simp only [good,dite_true,paidRaster]
    · have noMask:=Sweep.select_empty (DescentPackedActorMask.actors bound (A).cap) (Packed.token (some l))
      simp only [good,dite_false,blank,show DescentPackedActorMask.target tagBits _
        (Packed.token (some l)) 0=0 from noMask,DescentPaidResidentCount.empty]
  · intro l s
    apply (read.2 l s).trans
    apply congrArg (fun f : Fin oldH→Fin OG→ Cell 1=>((data f s).val:Computability.VPVNP.BurstRAM.Word w))
    funext h g
    by_cases good : h.val<OH
    · by_cases hit : ∃j,physical ⟨h.val,good⟩ g j=Packed.token (some l)
      · simp [good,actorRaster,hit]
        exact hit
      · simp [good,actorRaster,hit]
        exact fun j eq => hit ⟨j,eq⟩
    · simp [good,Ne.symm (live l)]

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
