import OAI.Hierarchy.DescentScalarOwnerEvidence
import OAI.Hierarchy.DescentReachedScalarVenue

namespace OAI
/-! # Original owner-register tickets for the reached ordinary archive -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentStageEdgeReceipt
open DescentCableDonorNames DescentOrdinaryLocalBirth DescentHostDegree DescentHostDirectory DescentOrdinaryDonorHalo
open DescentNetworkPartition Computability.BorderVNP.Crossing DescentSharedCableNames DescentSixParty.StarKeys
open DescentColonies DescentGL DescentWalshTables DescentPacking
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentSortedHaloRaster DescentHaloWalkRAM DescentSIMDLookup
open DescentScalarVenueMask DescentHostDirectory.SiteDecode DescentOrdinaryLocalBirth DescentSharedCableNames DescentPackedActorMask
open scoped Classical
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
local notation "M" => ticket.issued.measured_chart he T c ((r).state c)

local notation "bookChart" => activeChart ticket
local notation "key" => (bookChart).key he T c
local notation "addr" => MarkedWorld.address sel key (bookChart).hub T.k (gainExponent 20 T.Δ)
local notation "C" => ↥(MarkedWorld.reclaimed sel key (bookChart).hub T.k (gainExponent 20 T.Δ))
local notation "venue" => addr ∘ group
local notation "base" => physicalBits G W.toWorld (r).pick units stageLimit ((r).profile c) arch.bit.recipe

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
local notation "P"=>DescentHaloWalkRAM.breadth deg
local notation "K"=>1+(A).cap*6
local notation "moves"=>rotor A (groupRank Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding))

local notation "col"=>nativeAddress he (A).stage
local notation "home"=>scanHomeAt he (A).stage
local notation "color"=>scanColorAt he (A).stage
local notation "rank"=>groupRank Fin.valEmbedding (cap.vertex.trans Fin.valEmbedding)

/-- The scalar archive and the ordinary matching program use the same old
owner register and the same native donor key, prior to hub merging. -/
theorem original_routes {short a : ℕ} (win : capV→Block k→Cell a) (profile : ℕ)
    (named : (A).SiteNamed rank) (edgeOrder : ∀e f,oldID e<oldID f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (fit : ∀u,(win ((A).pos u) ((A).block u)).val<2^short)
    (winner : ∀u,(win ((A).pos u) ((A).block u)).val=1+2*DescentPacking.PackedMatch.Local.heap (col (home u)).2+(color u).toNat)
    (df : (A).degree<2^short) :
    let tokens:=DescentScalarVenueMask.Stage.tokens (short:=short) A oldID S cap.valid rank win profile layout (Function.Embedding.refl _) cap.vertex shelf
    Descriptors shelf k (A).pos (A).block (ticketParent (he:=he) (T:=T)) (ticketSlot (c:=c) ticket) (key∘group) cap.vertex (Function.Embedding.refl _) moves tokens :=by
  intro tokens
  obtain rfl:=ticket.sourceRate;obtain rfl:=eq_of_heq ticket.placement
  let chart := activeChart ticket
  let rows := BitDescription.scannedRows he cap.placement.stage
  let lay := bestLayout (branchWidth G (fun _ : rows.pairs => cap.placement.stage.z) (rows.profile c))
  have eqn : (activeChart ticket).col=nativeAddress he cap.placement.stage := eq_of_heq (activeChart ticket).native
  have actual:=DescentScalarVenueMask.Stage.original_descriptors (short:=short) A oldID S cap.valid rank win he cap.valid.coordinates named fit winner df edgeOrder profile chart.same lay (Function.Embedding.refl _) cap.vertex shelf
  have parents : ticketParent (he:=he) (T:=cap.placement.stage) = DescentScalarVenueMask.Stage.parent A he := by
    funext x
    rcases x with u | ⟨p,j⟩ <;> rfl
  have slots : ticketSlot (c:=c) ticket = DescentScalarVenueMask.Stage.localSlot A oldID S cap.valid he := by
    funext x
    rcases x with u | ⟨p,j⟩ <;> rfl
  simp only [parents,slots,IssuedDonorChart.key,eqn]
  exact actual

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
