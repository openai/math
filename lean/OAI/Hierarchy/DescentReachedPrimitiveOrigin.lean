import OAI.Hierarchy.DescentReachedPaddedOrigin
import OAI.Hierarchy.DescentOrdinaryPalettePosted

namespace OAI
/-! The actual node-origin stamp decomposes into its old rack, block and node or first-grain birth. -/
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
local instance : Fintype (DescentSixParty.Merged W.graph (r).pick layout (r).pack) := (sel).graph.finiteSite
local notation "first" => quotientBits stepGraph group xn xnOk base
local notation "second" => quotientBits (quotient stepGraph group xn xnOk) addr yc ycOk first
local notation "dest_" => n.destination∘rawInput he T c ((r).state c)
variable {K₀ : ℕ} (fits₀ : maxNodes arch.bit≤K₀)
local notation "oldN" => K₀
local notation "N₀" => DescentPackedActorMask.nodes bound oldN (A).cap
variable (prior : Local arch.bit)
local notation "ord₀" => fun u => ((bounded arch.bit prior u).trans (Fin.castLEEmb fits₀))
open DescentOrdinaryAtomFieldRAM

def OriginFields (label : C) (saved : NodeOrder.All arch.bit ⊕ (r).pairs×Fin 6) (j : Fin N₀) : Prop :=
  match saved with
  | .inl u=>∃p:u.1∈(halo).member label,j=finProdFinEquiv ((halo).slot label ⟨u.1,p⟩,finSumFinEquiv (.inl (ord₀ u.1 u.2)))
  | .inr (p,who)=>∃at_:W.graph.src ((r).pick (p,0))∈(halo).member label,
      j=finProdFinEquiv ((halo).slot label ⟨_,at_⟩,finSumFinEquiv (.inr (finProdFinEquiv (origin p,who))))

private theorem fields_of_row (c₀ : C)
    (entry : Σt : {t : (stepGraph).Site // venue t=c₀},(base t.val).Node) :
    OriginFields ticket arch fits₀ prior c₀
      (DescentOrdinaryLocalBirth.origin arch.bit (r).pick units stageLimit ((r).profile c) group addr c₀ entry)
      (DescentOrdinaryLocalBirth.book A oldID S cap.valid arch.bit (r).pick units stageLimit ((r).profile c) used group addr
        halo (reachedHalo_members ticket).1 (reachedHalo_members ticket).2 ord₀ c₀ entry) := by
  rcases entry with ⟨⟨rawSite, hv⟩, t⟩
  cases rawSite with
  | inl u =>
    have h : u ∈ (halo).member c₀ := hv ▸ (reachedHalo_members ticket).1 u
    exact ⟨h,rfl⟩
  | inr fresh =>
    obtain ⟨p,j⟩:=fresh
    have h : W.graph.src ((r).pick (p,0)) ∈ (halo).member c₀ := hv ▸ (reachedHalo_members ticket).2 p j
    exact ⟨h,rfl⟩

theorem origin_fields (v : n.result.graph.Site) (node : ((next).recipe v).Node) :
    OriginFields ticket arch fits₀ prior (currentLabel ticket arch v node) (roots ticket arch ⟨v,node⟩)
      (originCandidate ticket arch fits₀ prior v node):=by
  let c₀:=currentLabel ticket arch v node
  let actual:=printed ticket arch v node node
  let rows:=DescentOrdinaryLocalBirth.roster arch.bit (r).pick units stageLimit ((r).profile c) group addr xn yc xnOk ycOk c₀
  have result:=fields_of_row ticket arch fits₀ prior c₀ (rows actual)
  have src:=(coefficientFiber_read arch.bit (r).pick units stageLimit ((r).profile c) group addr xn yc xnOk ycOk c₀ actual).symm.trans
    (printed_origin ticket arch v node node)
  exact src ▸ result

/-- In the issued physical rank, lookup at the signed four-hop endpoint lands on the authentic old site. -/
def OriginOperands (label : C) (saved : NodeOrder.All arch.bit ⊕ (r).pairs×Fin 6) (j : Fin N₀) : Prop :=
  let root:=bookRoot deg k oldN (A).cap j
  let block:=bookBlock deg k oldN (A).cap j
  let id : Fin oldN ⊕ Fin ((A).cap*6) :=finSumFinEquiv.symm (bookItem deg k oldN (A).cap j)
  let located (u:W.graph.Site):=DescentSortedRoster.indexed reach (cap.vertex label.val.1.2) root=some (cap.vertex ((A).pos u).2) ∧
    block=(A).block u ∧ ((A).pos u).1=label.val.1.1
  match saved with
  | .inl u=>located u.1 ∧ id=Sum.inl (ord₀ u.1 u.2)
  | .inr (p,who)=>located (W.graph.src ((r).pick (p,0))) ∧ id=Sum.inr (finProdFinEquiv (origin p,who))

theorem origin_operands (v : n.result.graph.Site) (node : ((next).recipe v).Node) :
    OriginOperands ticket arch fits₀ prior (currentLabel ticket arch v node) (roots ticket arch ⟨v,node⟩)
      (originCandidate ticket arch fits₀ prior v node):=by
  let label:=currentLabel ticket arch v node
  let idx:=originCandidate ticket arch fits₀ prior v node
  have auth:=origin_fields ticket arch fits₀ prior v node
  generalize chosen : (roots ticket arch ⟨v,node⟩)=known at auth ⊢
  cases known with
  | inl o =>
    obtain ⟨belongs,slot⟩:=auth
    have loc:=actual_donor ticket label o.1 belongs
    rw [slot]
    let donor : Fin bound := (halo).slot label ⟨o.fst,belongs⟩
    let kind : Fin oldN ⊕ Fin ((A).cap*6) := Sum.inl (ord₀ o.1 o.2)
    have outer := (finProdFinEquiv (m:=bound) (n:=oldN+(A).cap*6)).symm_apply_apply (donor,finSumFinEquiv kind)
    dsimp only [OriginOperands,bookRoot,bookBlock,bookItem]
    erw [outer]
    exact ⟨loc,finSumFinEquiv.symm_apply_apply kind⟩
  | inr who =>
    obtain ⟨p,party⟩:=who
    obtain ⟨belongs,slot⟩:=auth
    have loc:=actual_donor ticket label (W.graph.src ((r).pick (p,0))) belongs
    rw [slot]
    let donor : Fin bound := (halo).slot label ⟨W.graph.src ((r).pick (p,0)),belongs⟩
    let kind : Fin oldN ⊕ Fin ((A).cap*6) := Sum.inr (finProdFinEquiv (origin p,party))
    have outer := (finProdFinEquiv (m:=bound) (n:=oldN+(A).cap*6)).symm_apply_apply (donor,finSumFinEquiv kind)
    dsimp only [OriginOperands,bookRoot,bookBlock,bookItem]
    erw [outer]
    exact ⟨loc,finSumFinEquiv.symm_apply_apply kind⟩

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
