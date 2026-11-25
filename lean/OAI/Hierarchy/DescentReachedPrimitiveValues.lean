import OAI.Hierarchy.DescentReachedPrimitiveOrigin
import OAI.Hierarchy.DescentOrdinaryPrimitiveWords
import OAI.Hierarchy.DescentPrimitivePaletteToken
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
local notation "first" => quotientBits stepGraph group xn xnOk base
local notation "second" => quotientBits (quotient stepGraph group xn xnOk) addr yc ycOk first
local notation "dest_" => n.destination∘rawInput he T c ((r).state c)
variable {K₀ : ℕ} (fits₀ : maxNodes arch.bit≤K₀)
local notation "oldN" => K₀
local notation "N₀" => DescentPackedActorMask.nodes bound oldN (A).cap
variable (prior : Local arch.bit)
local notation "ord₀" => fun u => ((bounded arch.bit prior u).trans (Fin.castLEEmb fits₀))
open DescentOrdinaryAtomFieldRAM

open DescentPrimitivePalette DescentOrdinaryAtomFieldRAM.ScalarOperand DescentPackedZip
variable {s Z p₀ : ℕ} (op : RotorSpec) (menu : Runnable F op)
variable (old : Encoding (Label G s Z op) (dictionary G op menu p₀) arch.bit) (limit : T.z≤Z)
local notation "post" => (Encoding.scanned G op menu old T he c limit).follow n
local notation "width" => printedBits G s Z op
local notation "tok" => token G s Z op

/-- Read-only projection of the same old signed halo and absolute local ordinal used by the native pool. -/
def candidateWord
    (previous : Block k→Fin OH→Fin OG→Cell (width*oldN))
    (born : Block k→Fin (A).cap→Fin 6→Fin OH→Fin OG→Cell width)
    (label : C) (j : Fin N₀) : Cell width :=
  (DescentSortedRoster.indexed reach (cap.vertex label.val.1.2) (bookRoot deg k oldN (A).cap j)).elim 0
    (fun h=>item previous born (bookBlock deg k oldN (A).cap j) (bookItem deg k oldN (A).cap j) h label.val.1.1)

variable (previous : Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell (printedBits G s Z op*K₀))
    (born : Block k→Fin cap.placement.cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell (printedBits G s Z op))
    (held : ∀u t,(encode (printedBits G s Z op) K₀).symm (previous (cap.placement.block u) (cap.vertex (cap.placement.pos u).2)
      (cap.placement.pos u).1) (((bounded arch.bit prior u).trans (Fin.castLEEmb fits₀)) t)=
      token G s Z op (old.atNode ⟨u,t⟩))
    (formed : ∀j who,let ar:=BitDescription.scannedRows he T;let u:=W.graph.src (ar.pick (j,0));
      born (cap.placement.block u) (outgoingSlot cap.placement (cap.order.trans Fin.valEmbedding) S cap.valid ar.pick (fun p : ar.pairs=>ar.picked (p,0)) j) who
        (cap.vertex (cap.placement.pos u).2) (cap.placement.pos u).1 = token G s Z op (bornLabel (s:=s) op (c:=c) limit j who))

include held formed in
theorem reached_ordinary_book_token (v : n.result.graph.Site) (node : ((next).recipe v).Node) :
    candidateWord (s:=s) (Z:=Z) (K₀:=K₀) ticket op previous born (currentLabel ticket arch v node)
      (originCandidate ticket arch fits₀ prior v node)=tok ((post).atNode ⟨v,node⟩):=by
  erw [ordinary_at op menu ticket arch old limit ⟨v,node⟩]
  have get:=origin_operands ticket arch fits₀ prior v node
  cases eqn : roots ticket arch ⟨v,node⟩ with
  | inl o =>
    rw [eqn] at get
    obtain ⟨⟨loc,block,groupEq⟩,tag⟩:=get
    simp only [candidateWord,loc,Option.elim_some,block,←groupEq,item,tag,Sum.elim_inl,take]
    exact held o.1 o.2
  | inr q =>
    obtain ⟨j,who⟩:=q
    rw [eqn] at get
    obtain ⟨⟨loc,block,groupEq⟩,tag⟩:=get
    simp only [candidateWord,loc,Option.elim_some,block,←groupEq,item,tag,Sum.elim_inr,Equiv.symm_apply_apply]
    exact formed j who

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
