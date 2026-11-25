import OAI.Hierarchy.DescentReachedPaddedOrigin

namespace OAI
/-! Vacant returned node slots clear every page of the ordinary W gather. -/
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

include prior fits₀ old_live old_empty in
/-- Every payload computed by this W mask is zero outside the original full node
placement. This includes a vacant receiver and a padded node of an occupied receiver. -/
theorem field_at_missing (auth : stock) {K' b a : ℕ} (wide : N₀<2^b)
    (values : Fin pitch→Fin OH→Fin OG→Cell (a*N₀))
    (h : Fin NH) (g : Fin NG) (x : Block k) (j : Fin K')
    (vacant : ¬∃v,coord h g x v ∧ j.val<Fintype.card ((next).recipe v).Node) :
    (encode a K').symm (DescentScalarBookReshape.book (oldInput age radix (fun l v c₀=>
      DescentPackedLocalAtoms.pack a N₀ K' (originBits (K₀:=K₀) ticket arch tokens priorCount l v c₀)
        (values l v c₀))) x (hostIndex ticket h) g) j=0:=by
  let pair:=finProdFinEquiv.symm (hostIndex ticket h)
  let grp:=(digits).symm (finProdFinEquiv.symm (finProdFinEquiv (g,x)))
  let bits₀:=originBits (K₀:=K₀) ticket arch tokens priorCount pair.2 pair.1 grp
  have empty_:=not_ne_iff.mp (mt (origin_book_iff ticket arch tokens age radix fits₀ prior priorCount old_live old_empty
    auth wide h g x j).mp vacant)
  change ((encode b K').symm (DescentOrdinaryOriginMask.selection N₀ K' b bits₀)) j=0 at empty_
  change ((encode a K').symm (DescentPackedLocalAtoms.pack a N₀ K' bits₀ (values pair.2 pair.1 grp))) j=0
  rw [DescentPackedLocalAtoms.pack,Equiv.symm_apply_apply,DescentPackedLocalAtoms.field]
  split
  · rename_i claimed
    obtain ⟨z₀,taken,rank⟩:=claimed
    have stamped:=DescentOrdinaryOriginMask.stamp_at N₀ K' b bits₀ j z₀ taken rank wide
    rw [empty_] at stamped
    change 0=z₀.val+1 at stamped
    omega
  · rfl

/-- Normalize the `origin` field of the registered physical stock. The selected
ordinal is computed from the mounted W rows and is zero at padded receiver hosts. -/
theorem registered_stamp_book {H field K' b : ℕ}
    (priorRows : (l : Fin pitch)→DescentOrdinaryAtomFieldRAM.ScalarOperand.Values deg k K₀ (A).cap H
      (NG*2^k) field (Packed.bits pitch) mb) (x : Block k) (h : Fin (H*pitch)) (g : Fin NG) :
    DescentScalarBookReshape.book (fun l i j=>DescentOrdinaryOriginMask.selection N₀ K' b
      (DescentOrdinaryOriginMask.marked (wideValues tokens age radix priorCount l (priorRows l)) i j)) x h g=
    DescentScalarBookReshape.book (fun l=>DescentOrdinaryRasterReturn.extend (H:=H)
      (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b) l)) x h g:=by
  exact selection_extends ticket arch tokens age radix priorCount _ _ _ _

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
