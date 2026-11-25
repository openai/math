import OAI.Hierarchy.DescentDatedReachedOriginSocket
import OAI.Hierarchy.DescentDatedSortedPathPadding

namespace OAI
/-! # Registered newborn stamp and genuine path at the upper operand receiver -/
namespace Hierarchy.DescentLocalArchiveOrder.PaddedOrigin
open DescentNetworkPartition Computability.BorderVNP.Crossing
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSixParty.StarKeys
open DescentColonies DescentGL DescentWalshTables DescentPacking
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentSortedHaloRaster DescentHaloWalkRAM DescentSIMDLookup
open DescentScalarVenueMask DescentHostDirectory.SiteDecode DescentOrdinaryLocalBirth DescentSharedCableNames DescentPackedActorMask
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentScalarBookReshape
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option maxRecDepth 4096
noncomputable section
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
local notation "M" => ticket.issued.common_chart he T c ((r).state c)

local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c
local notation "addr" => MarkedWorld.address sel key (bookChart).hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel key (bookChart).hub T.k (gainExponent 20 T.Δ))
local notation "venue" => addr ∘ group
local notation "base" => physicalBits G W.toWorld (r).pick units stageLimit ((r).profile c) arch.bit.recipe

local notation "A" => cap.placement
local notation "deg" => (A).degree
local notation "near" => groupedNear (A).near
local notation "bound" => DescentHaloWalkRAM.breadth deg*2^k
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
local notation "ticketSlots"=>1+(A).cap*6
local notation "moves"=>rotor A (groupRank Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding))

open DescentPaidResidentCount
variable {mb : ℕ}
variable (tokens : Block k→Fin (1+cap.placement.cap*6)→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→
  Ticket (DescentHaloWalkRAM.breadth cap.placement.degree) (2^(k+1)*(2^(packExponent 20 cap.placement.degree)+2)))
local notation "physical" => DescentScalarVenueMask.fields reach tokens (flags (cap:=cap)) k (gainExponent 20 deg) shelf pitch
local notation "stock" => Descriptors shelf k (A).pos (A).block (ticketParent (he:=he) (T:=T)) (ticketSlot (c:=c) ticket)
  (key∘group) cap.vertex (Function.Embedding.refl _) moves tokens
local notation "oldCensus" => fun x h g=>Census.count A (Equiv.refl _) cap.vertex mb h g x
local notation "bookCounts" => DescentOrdinaryAtomFieldRAM.RoleCounts.priorValue reach oldCensus
local notation "cost" => fun u : W.graph.Site=>((A).records u).length
local notation "dest" => n.destination∘rawInput he T c ((r).state c)

local notation "OH" => Fintype.card cap.V
local notation "OG" => S.groupCount i
local notation "NH" => Fintype.card target.V
local notation "NG" => S.groupCount (i+1)
variable (age : i<S.length) (radix : S.radix=2^k)
local notation "digits" => S.groupDigits age radix
local notation "coord" => DescentPaidResidentCount.occupies target.placement (Equiv.refl _) target.vertex


local notation "xn" => fun _ : (sel).graph.Site=>(0 : EuclideanSpace ℝ (Fin d))
local notation "yc" => fun _ : C=>(0 : EuclideanSpace ℝ (Fin d))
local notation "xnOk" => fun v : (sel).graph.Site=>(by simp : ‖xn v‖≤1)
local notation "ycOk" => fun v : C=>(by simp : ‖yc v‖≤1)
local notation "first" => quotientBits stepGraph group xn xnOk base
local notation "second" => quotientBits (quotient stepGraph group xn xnOk) addr yc ycOk first
local notation "dest_" => n.destination∘rawInput he T c ((r).state c)
variable {K₀ : ℕ} (fits₀ : maxNodes arch.bit≤K₀)
local notation "oldN" => K₀
local notation "N₀" => DescentPackedActorMask.nodes bound oldN (A).cap
variable (prior : Local arch.bit)
local notation "ord₀" => fun u => ((bounded arch.bit prior u).trans (Fin.castLEEmb fits₀))
variable (priorCount : Block k → Fin (Fintype.card cap.V) → Fin (S.groupCount i) → Cell mb)
variable (old_live : ∀u,(priorCount (cap.placement.block u) (cap.vertex (cap.placement.pos u).2) (cap.placement.pos u).1).val=
    Fintype.card (arch.bit.recipe u).Node)
variable (old_empty : ∀b h g,(¬∃u,cap.placement.block u=b ∧ cap.vertex (cap.placement.pos u).2=h ∧ (cap.placement.pos u).1=g)→priorCount b h g=0)
local notation "priorData" => DescentOrdinaryAtomFieldRAM.RoleCounts.priorValue reach priorCount

open DescentOrdinaryAtomFieldRAM DescentRetainedRangeDigits DescentOrdinaryAtomFieldRAM.ScalarOperand DescentHaloWalkRAM
variable {fieldBits : ℕ}
variable (previous : Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell (fieldBits*K₀))
    (born : Block k→Fin cap.placement.cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell fieldBits)

open DescentOrdinaryOriginMask DescentOrdinaryOriginPorts DescentOrdinaryAtomFieldRAM

local notation "chart" n:arg b:arg => originStampChart (cap:=cap) (K₀:=K₀) n b
local notation "register" n:arg b:arg v:arg => DescentScalarBookReshape.book
  (fun l h g=>selection N₀ n b (marked (rangeValues ticket arch tokens age radix priorCount previous born l) h g))
  (target.placement.block v) (hostIndex ticket (target.vertex (target.placement.pos v).2)) (target.placement.pos v).1

include fits₀ old_live old_empty in
/-- Transport the *same* chosen W stamp and its first-source group across the
old-host padding, retaining the unique raw receiver-to-donor path. -/
theorem padded_birth_socket_coordinates (auth:stock) (v:n.result.graph.Site) (node:((next).recipe v).Node)
    (pair:(r).pairs) (party:Fin 6) (fresh:roots ticket arch ⟨v,node⟩=.inr (pair,party))
    {b K' H:ℕ} (room:N₀<2^b) (fits:(advance ticket arch prior v node).val<K') (wide:OH≤H) :
    let u:=W.graph.src ((r).pick (pair,0))
    let host:=cap.vertex.trans (Fin.castLEEmb wide)
    let paddedReach:=Gather.reaching (hostRotor host (hostRoster A (cap.vertex.trans Fin.valEmbedding)))
    let at_:=currentLabel ticket arch v node
    ∃walk p:Fin breadth,
      DescentSortedRoster.indexed paddedReach (host at_.val.1.2) walk=some (host ((A).pos u).2) ∧
      Gather.select paddedReach (host at_.val.1.2) p=some (host ((A).pos u).2) ∧
      DescentDatedSourcePathDirectory.Sorted.rawAtOrdinal paddedReach (host at_.val.1.2) walk=p.val ∧
      ((A).pos u).1=at_.val.1.1 ∧
      ((encode b K').symm (register K' b v) ⟨(advance ticket arch prior v node).val,fits⟩).val=
        (candidate (chart K' b) walk ((A).block u) (.inr (origin pair,party))).val+1 :=by
  intro u host paddedReach at_
  obtain ⟨walk,stored,sourceGroup,stamp⟩:=birth_registered_stamp ticket arch tokens age radix fits₀ prior priorCount
    old_live old_empty previous born auth v node pair party fresh room fits
  obtain ⟨p,⟨found,_⟩,_⟩:=DescentDatedSourcePathDirectory.Sorted.raw_at reach (cap.vertex at_.val.1.2)
    (cap.vertex ((A).pos u).2) walk stored
  obtain ⟨ix,selection,rawPath⟩:=DescentDatedSourcePathDirectory.Sorted.host_coordinates wide cap.vertex
    (hostRoster A (cap.vertex.trans Fin.valEmbedding)) (cap.vertex at_.val.1.2) (cap.vertex ((A).pos u).2)
    walk p stored found
  exact ⟨walk,p,ix,selection,rawPath,sourceGroup,stamp⟩

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
