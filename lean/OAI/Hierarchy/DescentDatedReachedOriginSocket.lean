import OAI.Hierarchy.DescentReachedOrdinaryRange
import OAI.Hierarchy.DescentDatedOriginalStampPage
import OAI.Hierarchy.DescentDatedSortedPathSocket

namespace OAI
/-! # The actual selected stamp, its path, block, seat and party on the original W row -/
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

def originStampChart (K' b : ℕ) : Return :=
  ⟨deg,k,K₀,(A).cap,K',b,OH,pitch,NG,2^k,0⟩

local notation "chart" n:arg b:arg => originStampChart (cap:=cap) (K₀:=K₀) n b
local notation "register" n:arg b:arg v:arg => DescentScalarBookReshape.book
  (fun l h g=>selection N₀ n b (marked (rangeValues ticket arch tokens age radix priorCount previous born l) h g))
  (target.placement.block v) (hostIndex ticket (target.vertex (target.placement.pos v).2)) (target.placement.pos v).1

private theorem slot_parts (R : Return) (j : Fin (extent R)) :
    finProdFinEquiv (finProdFinEquiv (bookRoot R.degree R.depth R.oldNodes R.capacity j,
      bookBlock R.degree R.depth R.oldNodes R.capacity j),bookItem R.degree R.depth R.oldNodes R.capacity j)=j :=by
  obtain ⟨⟨pb,item⟩,rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨root,block⟩,rfl⟩ := finProdFinEquiv.surjective pb
  simp only [bookRoot,bookBlock,bookItem,Equiv.symm_apply_apply]

include fits₀ old_live old_empty in
/-- The truthful old leaf identifies its actual donor via the sorted predecessor roster,
the old node and block, and the one-based stamp read back on its original W register. -/
theorem old_registered_stamp (auth : stock) (v : n.result.graph.Site) (node : ((next).recipe v).Node)
    (saved : NodeOrder.All arch.bit) (carried : roots ticket arch ⟨v,node⟩=.inl saved)
    {b K' : ℕ} (wide : N₀<2^b) (fits : (advance ticket arch prior v node).val<K') :
    ∃walk : Fin breadth,
      DescentSortedRoster.indexed reach (cap.vertex (currentLabel ticket arch v node).val.1.2) walk=
        some (cap.vertex ((A).pos saved.1).2) ∧
      ((A).pos saved.1).1=(currentLabel ticket arch v node).val.1.1 ∧
      ((encode b K').symm (register K' b v) ⟨(advance ticket arch prior v node).val,fits⟩).val=
        (candidate (chart K' b) walk ((A).block saved.1) (.inl (ord₀ saved.1 saved.2))).val+1 :=by
  let R:=chart K' b
  let j:=originCandidate ticket arch fits₀ prior v node
  have data_:=origin_operands ticket arch fits₀ prior v node
  rw [carried] at data_
  obtain ⟨⟨path,block,grp⟩,head⟩:=data_
  let p:=bookRoot deg k oldN (A).cap j
  refine ⟨p,path,grp,?_⟩
  have item_:=congrArg (fun a : Fin oldN ⊕ Fin ((A).cap*6)=>finSumFinEquiv a) head
  simp only [Equiv.apply_symm_apply] at item_
  have name_ : j=candidate R p ((A).block saved.1) (.inl (ord₀ saved.1 saved.2)) :=by
    calc j = finProdFinEquiv (finProdFinEquiv (p,bookBlock deg k oldN (A).cap j),bookItem deg k oldN (A).cap j) :=(slot_parts R j).symm
         _ = _ := by rw [block,item_];rfl
  exact (origin_at_node ticket arch tokens age radix fits₀ prior priorCount old_live old_empty auth v node wide fits).trans
    (congrArg (fun z : Fin N₀=>z.val+1) name_)

include fits₀ old_live old_empty in
/-- On a genuinely new leaf, the very same origin stamp is the first outgoing
seat of the matched pair and its actual party, at the old host found by W. -/
theorem birth_registered_stamp (auth : stock) (v : n.result.graph.Site) (node : ((next).recipe v).Node)
    (pair : (r).pairs) (party : Fin 6) (fresh : roots ticket arch ⟨v,node⟩=.inr (pair,party))
    {b K' : ℕ} (wide : N₀<2^b) (fits : (advance ticket arch prior v node).val<K') :
    let u:=W.graph.src ((r).pick (pair,0))
    ∃walk : Fin breadth,
      DescentSortedRoster.indexed reach (cap.vertex (currentLabel ticket arch v node).val.1.2) walk=
        some (cap.vertex ((A).pos u).2) ∧ ((A).pos u).1=(currentLabel ticket arch v node).val.1.1 ∧
      ((encode b K').symm (register K' b v) ⟨(advance ticket arch prior v node).val,fits⟩).val=
        (candidate (chart K' b) walk ((A).block u) (.inr (origin pair,party))).val+1 :=by
  intro u
  let R:=chart K' b
  let j:=originCandidate ticket arch fits₀ prior v node
  have data_:=origin_operands ticket arch fits₀ prior v node
  rw [fresh] at data_
  obtain ⟨⟨path,block,grp⟩,head⟩:=data_
  let p:=bookRoot deg k oldN (A).cap j
  refine ⟨p,path,grp,?_⟩
  have item_:=congrArg (fun a : Fin oldN ⊕ Fin ((A).cap*6)=>finSumFinEquiv a) head
  simp only [Equiv.apply_symm_apply] at item_
  have name_ : j=candidate R p ((A).block u) (.inr (origin pair,party)) :=by
    calc j = finProdFinEquiv (finProdFinEquiv (p,bookBlock deg k oldN (A).cap j),bookItem deg k oldN (A).cap j) :=(slot_parts R j).symm
         _ = _ := by rw [block,item_];rfl
  exact (origin_at_node ticket arch tokens age radix fits₀ prior priorCount old_live old_empty auth v node wide fits).trans
    (congrArg (fun z : Fin N₀=>z.val+1) name_)

include fits₀ old_live old_empty in
/-- Decode the retained source both in the dense W slot convention and in
the raw path convention used on the measured operand bank. -/
theorem old_occurrence_coordinates (auth : stock) (v : n.result.graph.Site) (node : ((next).recipe v).Node)
    (saved : NodeOrder.All arch.bit) (carried : roots ticket arch ⟨v,node⟩=.inl saved)
    {b K' : ℕ} (wide : N₀<2^b) (fits : (advance ticket arch prior v node).val<K') :
    let label:=currentLabel ticket arch v node
    let receiver:=cap.vertex label.val.1.2
    ∃(inside : saved.1∈(halo).member label) (walk rawPath : Fin breadth),
      ((halo).slot label ⟨saved.1,inside⟩).val=walk.val*2^k+((A).block saved.1).val ∧
      DescentSortedRoster.indexed reach receiver walk=some (cap.vertex ((A).pos saved.1).2) ∧
      DescentDatedSourcePathDirectory.Sorted.rawAtOrdinal reach receiver walk=(rawPath).val ∧
      Gather.select reach receiver rawPath=some (cap.vertex ((A).pos saved.1).2) ∧
      ((encode b K').symm (register K' b v) ⟨(advance ticket arch prior v node).val,fits⟩).val=
        (candidate (chart K' b) walk ((A).block saved.1) (.inl (ord₀ saved.1 saved.2))).val+1 :=by
  intro label receiver
  obtain ⟨walk,lands,_,stamp⟩:=old_registered_stamp ticket arch tokens age radix fits₀ prior priorCount old_live old_empty
    previous born auth v node saved carried wide fits
  obtain ⟨rawPath,⟨found,read⟩,_⟩:=DescentDatedSourcePathDirectory.Sorted.raw_at reach receiver _ walk lands
  have name_:=origin_at_node ticket arch tokens age radix fits₀ prior priorCount old_live old_empty auth v node wide fits
  have equal : originCandidate ticket arch fits₀ prior v node=candidate (chart K' b) walk ((A).block saved.1) (.inl (ord₀ saved.1 saved.2)) :=
    Fin.ext (Nat.add_right_cancel (name_.symm.trans stamp))
  have trueSlot:=origin_fields ticket arch fits₀ prior v node
  rw [carried] at trueSlot
  obtain ⟨inside,issued⟩:=trueSlot
  rw [issued] at equal
  have ids := congrArg (fun q : Fin bound × Fin (K₀+(A).cap*6) => q.1)
    (finProdFinEquiv.injective equal)
  have slotValue (x : Fin breadth) (y : Fin (2^k)) :
      (finProdFinEquiv (x,y)).val = x.val*2^k+y.val := by
    rw [finProdFinEquiv_apply_val]
    ac_rfl
  exact ⟨inside,walk,rawPath,(congrArg Fin.val ids).trans (slotValue walk _),lands,read,found,stamp⟩

include fits₀ old_live old_empty in
/-- The true W birth's dense and rawPath path coordinates read the same first
outgoing source; the one-based raw socket subsequently uses that path. -/
theorem birth_occurrence_coordinates (auth : stock) (v : n.result.graph.Site) (node : ((next).recipe v).Node)
    (pair : (r).pairs) (party : Fin 6) (fresh : roots ticket arch ⟨v,node⟩=.inr (pair,party))
    {b K' : ℕ} (wide : N₀<2^b) (fits : (advance ticket arch prior v node).val<K') :
    let u:=W.graph.src ((r).pick (pair,0))
    let receiver:=cap.vertex (currentLabel ticket arch v node).val.1.2
    ∃walk rawPath : Fin breadth,
      DescentSortedRoster.indexed reach receiver walk=some (cap.vertex ((A).pos u).2) ∧
      DescentDatedSourcePathDirectory.Sorted.rawAtOrdinal reach receiver walk=(rawPath).val ∧
      Gather.select reach receiver rawPath=some (cap.vertex ((A).pos u).2) ∧
      ((encode b K').symm (register K' b v) ⟨(advance ticket arch prior v node).val,fits⟩).val=
        (candidate (chart K' b) walk ((A).block u) (.inr (origin pair,party))).val+1 :=by
  intro u receiver
  obtain ⟨walk,lands,_,stamp⟩:=birth_registered_stamp ticket arch tokens age radix fits₀ prior priorCount old_live old_empty
    previous born auth v node pair party fresh wide fits
  obtain ⟨rawPath,⟨found,read⟩,_⟩:=DescentDatedSourcePathDirectory.Sorted.raw_at reach receiver _ walk lands
  exact ⟨walk,rawPath,lands,read,found,stamp⟩

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
