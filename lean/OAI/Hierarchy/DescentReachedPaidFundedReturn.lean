import OAI.Hierarchy.DescentReachedPaidNativeSweep
import OAI.Hierarchy.DescentPaidSweepHeldRepacked
import OAI.Hierarchy.DescentPaidSweepRetainedField
import OAI.Hierarchy.DescentReachedCountRepacked

namespace OAI
/-! # Original reached-venue counts and held actor targets fund both ordinary output banks -/
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
local notation "paths₀"=>DescentHaloWalkRAM.breadth deg
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

open DescentPackedZip ThreeFlat.RAM PhysicalProcedure
open DescentOrdinaryAtomFieldRAM DescentOrdinaryRasterReturn DescentHaloWalkRAM
variable (oldH oldGrain grain start w venueFloor ingressRoof : ℕ) (wide : Fintype.card cap.V≤oldH) (op : Dated.Operands)
    (port : DescentPackedColony.Ports (DescentHaloWalkRAM.breadth cap.placement.degree)) (field : Bank)
    (full : Block k→Fin (1+cap.placement.cap*6)→Fin oldH→Fin (S.groupCount i)→
      Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
    (active : Fin oldH→Fin (S.groupCount i)→ Cell 1)
local notation "lifted" => cap.vertex.trans (Fin.castLEEmb wide)
local notation "padded" => Gather.reaching (hostRotor lifted (hostRoster A (cap.vertex.trans Fin.valEmbedding)))
local notation "labels" => fun l : Fin pitch=>Packed.token (some l)
local notation "tagBits" => Packed.bits pitch
local notation "rows" => oldH*chunks OG grain
local notation "L" => RoleCounts.Repitch.count oldH OG oldGrain grain k paths₀ mb start
local notation "C₀" => (L).roof
local notation "roof₀" => Sweep.HeldRepacked.roof start oldH OG oldGrain grain k paths₀ (A).cap mb tagBits pitch
local notation "pb" => Sweep.paidBank C₀ pitch bound (A).cap mb tagBits oldH OG grain
local notation "ab" => Sweep.aliveBank C₀ pitch bound (A).cap mb tagBits oldH OG grain
local notation "code" => Sweep.HeldRepacked.program start oldH OG oldGrain grain k paths₀ (A).cap mb tagBits pitch field port op.atoms labels w
local notation "time₀" => Sweep.HeldRepacked.ticks start oldH OG oldGrain grain k paths₀ (A).cap mb tagBits pitch field port op.atoms labels w
local notation "out" => Sweep.HeldRepacked.image start oldH OG oldGrain grain k paths₀ (A).cap mb tagBits pitch field port op.atoms labels

theorem census_hub_flags (h : Fin OH) (g : Fin OG) :
    Census.hub A cap.vertex h=flags (cap:=cap) h g :=by
  unfold Census.hub flags
  split
  · rename_i occupied
    cases q : (A).hub occupied.choose <;> simp
  · rfl

/-- The earlier ordinary actor ingress has executed in its original geometry.  The retained
    bank lies below the new date floor. The new run reads the old census and emits the
    original paid and alive rasters for every receiver including every padded host. -/
theorem paid_return_from_venue (old ingress now : Memory w) (rs : Fin oldH→Fin D→Option (Fin oldH))
    (stage : stageVenue cap wide op oldGrain mb venueFloor rs old)
    (rawRows : DescentPackedColony.Reads field (fun h g=>encode tagBits (actors bound (A).cap)
      (DescentScalarVenueMask.fields padded full active k (gainExponent 20 deg) shelf pitch h g)) grain ingress)
    (visible : DescentPackedColony.Accessible port field oldH OG grain w ingressRoof)
    (ready : DescentPackedColony.Mounted port (DescentSortedRoster.indexed padded) ingress OG grain)
    (real : ∀x j h g,full x j (Fin.castLEEmb wide h) g=tokens x j h g)
    (blank : ∀x j (h:Fin oldH) g,OH≤h.val→full x j h g=none)
    (flagsAgree : ∀h g,active (Fin.castLEEmb wide h) g=flags (cap:=cap) h g)
    (positive : 0<oldGrain) (earlier : venueFloor≤ start) (oldWords : ∀a<venueFloor,now a=old a)
    (protected_ : ingressRoof≤ start) (saved : ∀q< ingressRoof,now q=ingress q) (bounds : roof₀<2^w) :
    (code).Exec now (out now) time₀ ∧ CheapCode code ∧
    (∀a,a< start ∨ roof₀≤a→ out now a=now a) ∧
    (∀(l : Fin pitch) (s : Row oldH OG grain),out now ((pb).base+l.val*rows+(row oldH OG grain s).val)=
      ((data (fun h g=>extend (paidRaster (mb:=mb) ticket tokens l) h g) s).val:Computability.VPVNP.BurstRAM.Word w)) ∧
    ∀(l : Fin pitch) (s : Row oldH OG grain),out now ((ab).base+l.val*rows+(row oldH OG grain s).val)=
      ((data (fun h g=>extend (actorRaster ticket tokens l) h g) s).val:Computability.VPVNP.BurstRAM.Word w) :=by
  let countsLayout:=L
  let front:=RoleCounts.Repitch.phase oldH OG oldGrain grain k paths₀ mb start w port op.atoms
  let gathered:=front.image now
  have geo:=Sweep.geometry C₀ pitch bound (A).cap mb tagBits oldH OG grain
  have intervals:=RoleCounts.Repitch.intervals oldH OG oldGrain grain k paths₀ mb start
  have lo : start≤C₀ := intervals.1.trans intervals.2
  have hi : C₀≤roof₀ := geo.1.trans (geo.2.1.trans
    ((Nat.le_add_right ..).trans (geo.2.2.1.trans (geo.2.2.2.1.trans (Nat.le_add_right ..)))))
  have avail:=RoleControl.Layout.accessible_after visible protected_
  have fence:=avail.source
  have currentPorts:=RoleControl.Layout.previous_mounted visible _ saved ready
  have funded:=RoleCounts.run_original_on_ports cap wide op start venueFloor port field old now rs stage
    positive earlier oldWords avail currentPorts (hi.trans_lt bounds)
  have source:=Raster.held_field_reads wide cap.vertex (hostRoster A (cap.vertex.trans Fin.valEmbedding))
    k (gainExponent 20 deg) shelf pitch tokens full (flags (cap:=cap)) active
    field ingress now rawRows real blank flagsAgree fence.2.1 visible.srcRoom
    (fun a h=>saved a (h.trans_le ((Nat.add_le_add_left visible.srcRoom _).trans visible.source.2.2)))
  let expr:=Expr.lookup field .row
  have ef : expr.Fits w start:=⟨fence,trivial⟩
  have targetRead : Source expr (fun (h : Fin oldH) g=>encode tagBits _ (fun j=>extend
      (fun v u=>physical v u j) h g)) grain gathered:=fun s =>
    (eval_below expr _ now gathered ef (fun a ha=>funded.2.2 a (.inl ha))).trans (source s)
  have load : countsLayout.expr.Fits w C₀:=⟨countsLayout.result_fits (hi.trans_lt bounds) le_rfl,trivial⟩
  have printed:=paid_shelves_issued (mb:=mb) ticket tokens oldH grain C₀ w expr countsLayout.expr gathered
    (ProtocolRAMGeneratedWrite.fits_mono _ lo ef) load targetRead funded.2.1 bounds
  refine ⟨?_,?_,?_,printed.2.1,printed.2.2.1⟩
  · exact @Procedure.Exec.then w front.program
      (Sweep.program C₀ bound (A).cap mb oldH OG grain labels expr countsLayout.expr w)
      now gathered (out now) front.ticks (Sweep.ticks C₀ bound (A).cap mb oldH OG grain labels expr countsLayout.expr)
      funded.1 printed.1
  · intro pc reg pub exit a b e j
    exact @ProtocolRAM.cheap_seq w _ _ (@front.cheap) (@printed.2.2.2.2) pc reg pub exit a b e j
  · intro a h
    exact (printed.2.2.2.1 a (h.imp_left (fun t=>t.trans_le lo))).trans
      (funded.2.2 a (h.imp_right (fun t=>hi.trans t)))

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
