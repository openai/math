import OAI.Hierarchy.DescentReachedPrimitiveArchive
import OAI.Hierarchy.DescentPaddedNodeCells

namespace OAI
/-! Complete immutable ordinary role pages, including zero at vacant nodes and racks. -/
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

open DescentPrimitivePalette DescentOrdinaryAtomFieldRAM.ScalarOperand DescentPackedZip DescentOrdinaryPrimitiveCheckpoint DescentOrdinaryRasterReturn
variable {s Z p₀ : ℕ} (op : RotorSpec) (menu : Runnable F op)
variable (old : Encoding (Label G s Z op) (dictionary G op menu p₀) arch.bit) (limit : T.z≤Z)
local notation "post" => (Encoding.scanned G op menu old T he c limit).follow n
local notation "width" => printedBits G s Z op
local notation "tok" => token G s Z op

variable (previous : Block k→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell (printedBits G s Z op*K₀))
    (born : Block k→Fin cap.placement.cap→Fin 6→Fin (Fintype.card cap.V)→Fin (S.groupCount i)→Cell (printedBits G s Z op))
    (held : ∀u t,(encode (printedBits G s Z op) K₀).symm (previous (cap.placement.block u) (cap.vertex (cap.placement.pos u).2)
      (cap.placement.pos u).1) (((bounded arch.bit prior u).trans (Fin.castLEEmb fits₀)) t)=
      token G s Z op (old.atNode ⟨u,t⟩))
    (formed : ∀j who,let ar:=BitDescription.scannedRows he T;let u:=W.graph.src (ar.pick (j,0));
      born (cap.placement.block u) (outgoingSlot cap.placement (cap.order.trans Fin.valEmbedding) S cap.valid ar.pick (fun p : ar.pairs=>ar.picked (p,0)) j) who
        (cap.vertex (cap.placement.pos u).2) (cap.placement.pos u).1 = token G s Z op (bornLabel (s:=s) op (c:=c) limit j who))

variable (priorCount : Block k → Fin (Fintype.card cap.V) → Fin (S.groupCount i) → Cell mb)
variable (old_live : ∀u,(priorCount (cap.placement.block u) (cap.vertex (cap.placement.pos u).2) (cap.placement.pos u).1).val=
    Fintype.card (arch.bit.recipe u).Node)
variable (old_empty : ∀b h g,(¬∃u,cap.placement.block u=b ∧ cap.vertex (cap.placement.pos u).2=h ∧ (cap.placement.pos u).1=g)→priorCount b h g=0)
variable {H K' b : ℕ} (enough : Fintype.card cap.V≤H)
local notation "seats" => DescentScalarBookReshape.book (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b))
local notation "payloads" => DescentScalarBookReshape.book (oldInput age radix (fun _:Fin pitch=>originalPool (s:=s) (Z:=Z) (K₀:=K₀) (cap:=cap) op previous born))

variable {preM newM idM working saved : ℕ}
local notation "C₁" => primitiveLayout (K₀:=K₀) (s:=s) (Z:=Z) (cap:=cap) op H b K' preM newM idM working saved
local notation "remix" => (fun a : Fin (NG*2^k)=>(digits).symm (finProdFinEquiv.symm a))
local notation "near₁" => DescentSortedRoster.indexed reach

include old_live old_empty held formed in
theorem full_primitive_cells (stock₁ : (C₁).Stock)
    (past : ∀x h j,stock₁.previous x (h.castLE enough) j=previous x h (remix j))
    (birth : ∀x t a h j,stock₁.newborn ((C₁).bornIndex x t a) (h.castLE enough) j=born x t a h (remix j))
    (neighbors : ∀h p,stock₁.next (h.castLE enough) p=(near₁ h p).map (Fin.castLE enough))
    (stamps : ∀x h g,stock₁.origin x h g=DescentScalarBookReshape.book (fun l=>DescentOrdinaryRasterReturn.extend (H:=H)
      (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b) l)) x h g)
    (auth : stock) (wide : N₀<2^b) (x : Block k) (h : Fin (H*pitch)) (g : Fin NG) :
    stock₁.output x h g=encode width K' (fun j=>(Reached.NodeCells.atPhysical target next
      (advance ticket arch prior) x j h g).elim 0 (fun p=>tok ((post).atNode p))):=by
  apply (encode width K').symm.injective
  rw [Equiv.symm_apply_apply]
  funext j
  let names:=target.vertex.trans ((hostIndex ticket).toEmbedding.trans (Fin.castLEEmb (Nat.mul_le_mul_right pitch enough)))
  let cell:=Reached.NodeCells.atPhysical target next (advance ticket arch prior) x j h g
  have faith (u : target.V) : (names u).val=(target.vertex u).val:=rfl
  have covered:=wide_book_iff ticket arch tokens age radix fits₀ prior priorCount old_live old_empty auth wide enough h g x j
  have occurs:=Reached.NodeCells.atPhysical_live target next (advance ticket arch prior) x j h g names faith
  cases atCell:cell with
  | none=>
    have absent : ¬∃v,DescentPaidResidentCount.occupies target.placement (Equiv.refl _) names h g x v ∧
        j.val<Fintype.card ((next).recipe v).Node:=by
      rintro found
      obtain ⟨p,ok⟩:=occurs.mpr found
      exact Option.some_ne_none _ (ok.symm.trans atCell)
    have zero : ((encode b K').symm (stock₁.origin x h g) j).val=0:=by
      erw [stamps x h g]
      exact congrArg Fin.val (not_ne_iff.mp (fun live=>absent (covered.mp live)))
    change _=cell.elim 0 _
    rw [atCell]
    exact stock₁.hole x h g j zero
  | some a=>
    rcases a with ⟨v,node⟩
    obtain ⟨hr,hg,hx,hj⟩:=(Reached.NodeCells.atPhysical_some target next (advance ticket arch prior) x j h g v node).mp atCell
    have hh : widen enough (hostIndex ticket (target.vertex (target.placement.pos v).2))=h:=Fin.ext hr
    have indexFits : (advance ticket arch prior v node).val<K':=hj ▸ j.isLt
    have jEq : j=⟨(advance ticket arch prior v node).val,indexFits⟩:=Fin.ext hj
    have native:=reached_primitive_token ticket arch tokens age radix fits₀ prior op menu old limit previous born held formed
      priorCount old_live old_empty auth wide v node indexFits
    change _=cell.elim 0 _
    rw [atCell]
    change (encode width K').symm (select (stock₁.origin x h g) (stock₁.onBlock x h g)) j=_
    rw [←hh,←hg,←hx]
    erw [stamps,DescentOrdinaryRasterReturn.padded_book,Layout.book_on (C₁) stock₁ enough remix previous born near₁ past birth neighbors,jEq]
    exact native

include old_live old_empty held formed in
theorem full_primitive_bank {w : ℕ} (bank : Block k→ProtocolRAM.Bank) (m : Computability.VPVNP.BurstRAM.Memory w)
    (stock₁ : (C₁).Stock)
    (past : ∀x h j,stock₁.previous x (h.castLE enough) j=previous x h (remix j))
    (birth : ∀x t a h j,stock₁.newborn ((C₁).bornIndex x t a) (h.castLE enough) j=born x t a h (remix j))
    (neighbors : ∀h p,stock₁.next (h.castLE enough) p=(near₁ h p).map (Fin.castLE enough))
    (stamps : ∀x h g,stock₁.origin x h g=DescentScalarBookReshape.book (fun l=>DescentOrdinaryRasterReturn.extend (H:=H)
      (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b) l)) x h g)
    (auth : stock) (wide : N₀<2^b)
    (emitted : ∀x,DescentPackedColony.Reads (bank x) (stock₁.output x) saved m) (x : Block k) :
    DescentPackedColony.Reads (bank x) (fun (h : Fin (H*pitch)) (g : Fin NG)=>encode width K' (fun j=>
      (Reached.NodeCells.atPhysical target next (advance ticket arch prior) x j h g).elim 0
        (fun p=>tok ((post).atNode p)))) saved m:=by
  have values : stock₁.output x=fun h g=>encode width K' (fun j=>
      (Reached.NodeCells.atPhysical target next (advance ticket arch prior) x j h g).elim 0
        (fun p=>tok ((post).atNode p))) :=by
    funext h g
    exact full_primitive_cells (ticket:=ticket) (arch:=arch) (age:=age) (radix:=radix) (tokens:=tokens)
      (fits₀:=fits₀) (prior:=prior) (op:=op) (menu:=menu) (old:=old) (limit:=limit) (previous:=previous)
      (born:=born) (held:=held) (formed:=formed) (priorCount:=priorCount) (old_live:=old_live)
      (old_empty:=old_empty) (enough:=enough) stock₁ past birth neighbors stamps auth wide x h g
  exact values ▸ emitted x

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
