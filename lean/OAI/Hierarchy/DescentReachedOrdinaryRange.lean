import OAI.Hierarchy.DescentReachedPrimitiveOrigin
import OAI.Hierarchy.DescentOrdinaryRetainedRangeRead

namespace OAI
/-! # Reached ordinary range copies selected by the authentic old halo and node rank -/
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

def rangeInput (h : Fin OH) (g : Fin OG) : Cell (fieldBits*N₀) :=
  let candidates:=fun t : Fin N₀ => (DescentSortedRoster.indexed reach h (bookRoot deg k oldN (A).cap t)).elim 0
    (fun source=>item previous born (bookBlock deg k oldN (A).cap t) (bookItem deg k oldN (A).cap t) source g)
  encode fieldBits N₀ candidates

def rangeRaster (K' : ℕ) (l : Fin pitch) (h : Fin OH) (g : Fin OG) : Cell (fieldBits*K') :=
  let bits_:=originBits (K₀:=K₀) ticket arch tokens priorCount l h g
  DescentPackedLocalAtoms.pack fieldBits N₀ K' bits_ (rangeInput (cap:=cap) previous born h g)

/-- Actual outgoing range values, before the physical split of the old group into
the new group and block. All three native range columns use this same mask and walk. -/
def rangeValues (l : Fin pitch) :
    Values deg k K₀ (A).cap OH (NG*2^k) fieldBits (Packed.bits pitch) mb :=
  let _ := ticket
  let _ := arch
  { walks := reach
    old := fun b h g => previous b h ((digits).symm (finProdFinEquiv.symm g))
    born := fun b s j h g => born b s j h ((digits).symm (finProdFinEquiv.symm g))
    wanted := fun _ _ => Packed.token (some l)
    venues := fun h g => physical h ((digits).symm (finProdFinEquiv.symm g))
    counts := fun h g => priorData h ((digits).symm (finProdFinEquiv.symm g)) }

theorem range_values_book (K' : ℕ) (l : Fin pitch) (h : Fin OH) (g : Fin (NG*2^k)) :
    (rangeValues ticket arch tokens age radix priorCount previous born l).book K' h g =
      oldInput age radix (rangeRaster ticket arch tokens priorCount previous born K') l h g := by
  rfl

theorem range_values_returned (K' : ℕ) (b : Block k) :
    DescentScalarBookReshape.book
      (fun l h g => (rangeValues ticket arch tokens age radix priorCount previous born l).book K' h g) b =
    DescentScalarBookReshape.book (oldInput age radix (rangeRaster ticket arch tokens priorCount previous born K')) b := by
  rfl

include old_live old_empty in
/-- The original ticket's copy/ordinary-birth split, genuine stable selected stamp and
registered physical rank determine the archived source without any assumed origin table. -/
theorem range_at_old_node (auth : stock) (v : n.result.graph.Site) (node : ((next).recipe v).Node)
    (saved : NodeOrder.All arch.bit) (carried : roots ticket arch ⟨v,node⟩=Sum.inl saved)
    {b K' : ℕ} (wide : N₀<2^b) (fits : (advance ticket arch prior v node).val<K') :
    let column:=DescentScalarBookReshape.book (oldInput age radix (rangeRaster ticket arch tokens priorCount previous born K'))
      (target.placement.block v) (hostIndex ticket (target.vertex (target.placement.pos v).2)) (target.placement.pos v).1
    take ⟨(advance ticket arch prior v node).val,fits⟩ column =
      take (ord₀ saved.1 saved.2) (previous ((A).block saved.1) (cap.vertex ((A).pos saved.1).2) ((A).pos saved.1).1) := by
  have stamp:=origin_at_node ticket arch tokens age radix fits₀ prior priorCount old_live old_empty auth v node wide fits
  have donor:=origin_operands ticket arch fits₀ prior v node
  rw [carried] at donor
  obtain ⟨⟨loc,block,groupEq⟩,oldNode⟩:=donor
  dsimp only at stamp ⊢
  rw [selected_book ticket arch age radix v node] at stamp ⊢
  dsimp only [rangeRaster,rangeInput]
  erw [packed_at_stamp (a:=fieldBits) _ _ _ wide stamp]
  have rack : (splitKey (currentLabel ticket arch v node).val).2.1=(currentLabel ticket arch v node).val.1.2 := rfl
  have previousGroup : (splitKey (currentLabel ticket arch v node).val).1=(currentLabel ticket arch v node).val.1.1 := rfl
  rw [rack,previousGroup,loc]
  simp only [Option.elim_some,block,←groupEq,item,oldNode,Sum.elim_inl]

include fits₀ old_live old_empty in
/-- A new party reads the same packed origin candidate at its genuine anchor's outgoing
slot, original host, block and group. This also applies to each prior pointer header column. -/
theorem range_at_born_node (auth : stock) (v : n.result.graph.Site) (node : ((next).recipe v).Node)
    (p : (r).pairs) (party : Fin 6) (fresh : roots ticket arch ⟨v,node⟩=Sum.inr (p,party))
    {b K' : ℕ} (wide : N₀<2^b) (fits : (advance ticket arch prior v node).val<K') :
    let u:=W.graph.src ((r).pick (p,0))
    let column:=DescentScalarBookReshape.book (oldInput age radix (rangeRaster ticket arch tokens priorCount previous born K'))
      (target.placement.block v) (hostIndex ticket (target.vertex (target.placement.pos v).2)) (target.placement.pos v).1
    take ⟨(advance ticket arch prior v node).val,fits⟩ column =
      born ((A).block u) (origin p) party (cap.vertex ((A).pos u).2) ((A).pos u).1 := by
  have stamp:=origin_at_node ticket arch tokens age radix fits₀ prior priorCount old_live old_empty auth v node wide fits
  have donor:=origin_operands ticket arch fits₀ prior v node
  rw [fresh] at donor
  obtain ⟨⟨loc,block,groupEq⟩,source⟩:=donor
  dsimp only at stamp ⊢
  rw [selected_book ticket arch age radix v node] at stamp ⊢
  dsimp only [rangeRaster,rangeInput]
  erw [packed_at_stamp (a:=fieldBits) _ _ _ wide stamp]
  have rack : (splitKey (currentLabel ticket arch v node).val).2.1=(currentLabel ticket arch v node).val.1.2 := rfl
  have previousGroup : (splitKey (currentLabel ticket arch v node).val).1=(currentLabel ticket arch v node).val.1.1 := rfl
  rw [rack,previousGroup,loc]
  simp only [Option.elim_some,block,←groupEq,item,source,Sum.elim_inr,Equiv.symm_apply_apply]

include old_live old_empty in
/-- All primitive source columns use the same actual predecessor or original party anchor. -/
theorem original_field_at_node (auth : stock) (v : n.result.graph.Site) (node : ((next).recipe v).Node)
    {b K' : ℕ} (wide : N₀<2^b) (fits : (advance ticket arch prior v node).val<K') :
    let column:=DescentScalarBookReshape.book (oldInput age radix (rangeRaster ticket arch tokens priorCount previous born K'))
      (target.placement.block v) (hostIndex ticket (target.vertex (target.placement.pos v).2)) (target.placement.pos v).1
    take ⟨(advance ticket arch prior v node).val,fits⟩ column =
      Sum.elim (fun a : NodeOrder.All arch.bit=>
        take (ord₀ a.1 a.2) (previous ((A).block a.1) (cap.vertex ((A).pos a.1).2) ((A).pos a.1).1))
        (fun a : (r).pairs×Fin 6=>let u:=W.graph.src ((r).pick (a.1,0))
          born ((A).block u) (origin a.1) a.2 (cap.vertex ((A).pos u).2) ((A).pos u).1)
        (roots ticket arch ⟨v,node⟩) := by
  cases src : roots ticket arch ⟨v,node⟩ with
  | inl a=>
    exact range_at_old_node ticket arch tokens age radix fits₀ prior priorCount old_live old_empty
      previous born auth v node a src wide fits
  | inr a=>
    exact range_at_born_node ticket arch tokens age radix fits₀ prior priorCount old_live old_empty
      previous born auth v node a.1 a.2 src wide fits

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
