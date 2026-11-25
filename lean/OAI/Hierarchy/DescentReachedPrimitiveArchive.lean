import OAI.Hierarchy.DescentOrdinaryPaletteOriginalPool
import OAI.Hierarchy.DescentPrimitiveBankDigits
import OAI.Hierarchy.DescentReachedPrimitiveValues
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

def originalPool (h : Fin OH) (g : Fin OG) : Cell (width*N₀) :=
  encode width N₀ (fun t=>(DescentSortedRoster.indexed reach h (bookRoot deg k oldN (A).cap t)).elim 0
    (fun prev=>item previous born (bookBlock deg k oldN (A).cap t) (bookItem deg k oldN (A).cap t) prev g))

variable (priorCount : Block k → Fin (Fintype.card cap.V) → Fin (S.groupCount i) → Cell mb)
variable (old_live : ∀u,(priorCount (cap.placement.block u) (cap.vertex (cap.placement.pos u).2) (cap.placement.pos u).1).val=
    Fintype.card (arch.bit.recipe u).Node)
variable (old_empty : ∀b h g,(¬∃u,cap.placement.block u=b ∧ cap.vertex (cap.placement.pos u).2=h ∧ (cap.placement.pos u).1=g)→priorCount b h g=0)
variable {H K' b : ℕ} (enough : Fintype.card cap.V≤H)
local notation "seats" => DescentScalarBookReshape.book (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b))
local notation "payloads" => DescentScalarBookReshape.book (oldInput age radix (fun _:Fin pitch=>originalPool (s:=s) (Z:=Z) (K₀:=K₀) (cap:=cap) op previous born))

include old_live old_empty held formed in
theorem reached_primitive_token (auth : stock) (wide : N₀<2^b)
    (v : n.result.graph.Site) (node : ((next).recipe v).Node) (fits : (advance ticket arch prior v node).val<K') :
    let x:=target.placement.block v
    let h:=hostIndex ticket (target.vertex (target.placement.pos v).2)
    let g:=(target.placement.pos v).1
    (encode width K').symm (select ((seats) x h g) ((payloads) x h g)) ⟨(advance ticket arch prior v node).val,fits⟩=
      tok ((post).atNode ⟨v,node⟩):=by
  intro x h g
  have rank:=origin_at_node ticket arch tokens age radix fits₀ prior priorCount old_live old_empty auth v node wide fits
  rw [selected _ _ _ _ rank]
  have value:=reached_ordinary_book_token ticket arch fits₀ prior op menu old limit previous born held formed v node
  dsimp only [x,h,g]
  rw [selected_book ticket arch age radix v node]
  simp only [originalPool,Equiv.symm_apply_apply]
  exact value

include old_live old_empty held formed in
/-- The same code on a rectangular host roster, evaluated at the actual new actor's dense index. -/
theorem padded_primitive_token (auth : stock) (wide : N₀<2^b)
    (v : n.result.graph.Site) (node : ((next).recipe v).Node) (fits : (advance ticket arch prior v node).val<K') :
    let x:=target.placement.block v
    let h:=hostIndex ticket (target.vertex (target.placement.pos v).2)
    let g:=(target.placement.pos v).1
    let ids:=fun l=>extend (H:=H) (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b) l)
    let labels:=fun l=>extend (H:=H) (oldInput age radix (fun _:Fin pitch=>originalPool (s:=s) (Z:=Z) (K₀:=K₀) (cap:=cap) op previous born) l)
    (encode width K').symm (select (book ids x (widen enough h) g) (book labels x (widen enough h) g)) ⟨(advance ticket arch prior v node).val,fits⟩=
      tok ((post).atNode ⟨v,node⟩):=by
  intro x h g ids labels
  simpa only [ids,labels,padded_book] using reached_primitive_token ticket arch tokens age radix fits₀ prior op menu old limit
    previous born held formed priorCount old_live old_empty auth wide v node fits


/-- The concrete late primitive layout at this reached ordinary geometry. The four earlier bank pitches may vary independently. -/
def primitiveLayout (H d K' pre fresh ids work saved : ℕ) : DescentOrdinaryPrimitiveCheckpoint.Layout :=
  ⟨H,deg,k,(A).cap,pitch,NG,oldN,K',width,d,pre,fresh,ids,work,saved⟩

variable {preM newM idM working saved : ℕ}
local notation "C₁" => primitiveLayout (K₀:=K₀) (s:=s) (Z:=Z) (cap:=cap) op H b K' preM newM idM working saved
local notation "remix" => (fun a : Fin (NG*2^k)=>(digits).symm (finProdFinEquiv.symm a))
local notation "near₁" => DescentSortedRoster.indexed reach

include old_live old_empty held formed in
/-- Read the natural token of the actual archived node at its physical word address. This only requires
the genuine old, six-party and origin banks on the original live rectangle. -/
theorem native_primitive_token {w : ℕ} (bank : Fin (2^k)→ProtocolRAM.Bank)
    (m : Computability.VPVNP.BurstRAM.Memory w) (stock₁ : (C₁).Stock)
    (past : ∀x h j,stock₁.previous x (h.castLE enough) j=previous x h (remix j))
    (birth : ∀x t a h j,stock₁.newborn ((C₁).bornIndex x t a) (h.castLE enough) j=born x t a h (remix j))
    (neighbors : ∀h p,stock₁.next (h.castLE enough) p=(near₁ h p).map (Fin.castLE enough))
    (origins : ∀x h g,stock₁.origin x (widen enough h) g=(seats) x h g)
    (available : ∀x,DescentPackedColony.Reads (bank x) (stock₁.output x) saved m)
    (nonempty : 0<saved) (bitsFit : (width*K')*saved≤w) (auth : stock) (wide : N₀<2^b)
    (v : n.result.graph.Site) (node : ((next).recipe v).Node) (fits : (advance ticket arch prior v node).val<K') :
    let x:=target.placement.block v
    let h:=hostIndex ticket (target.vertex (target.placement.pos v).2)
    let g:=(target.placement.pos v).1
    (C₁).digitAt (bank x) m nonempty (widen enough h) g ⟨(advance ticket arch prior v node).val,fits⟩=
      (tok ((post).atNode ⟨v,node⟩)).val:=by
  intro x h g
  refine (Layout.read_digit (C₁) stock₁ x (bank x) m nonempty bitsFit (available x) (widen enough h) g ⟨_,fits⟩).trans ?_
  unfold Layout.Stock.output
  erw [origins x h g,Layout.book_on (C₁) stock₁ enough remix previous born near₁ past birth neighbors x h g]
  exact congrArg Fin.val (reached_primitive_token ticket arch tokens age radix fits₀ prior op menu old limit
    previous born held formed priorCount old_live old_empty auth wide v node fits)


end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

namespace Hierarchy.DescentOrdinaryPrimitiveCheckpoint
open DescentSIMDLookup
variable {N K b d : ℕ}
/-- The original reached mask orders precisely the same donor digits as the old/born book. -/
theorem from_stamp (f : Cell (1*N)) (pool : Fin N→Cell b) (n : Fin K) (j : Fin N)
    (active : (encode 1 N).symm f j≠0)
    (place : DescentPackedLocalAtoms.earlier ((encode 1 N).symm f) j=n.val) (room : N<2^d) :
    (encode b K).symm (select (DescentOrdinaryOriginMask.selection N K d f) (encode b N pool)) n=pool j:=by
  simpa only [Equiv.symm_apply_apply] using selected _ (encode b N pool) n j
    (DescentOrdinaryOriginMask.stamp_at N K d f n j active place room)

end Hierarchy.DescentOrdinaryPrimitiveCheckpoint

end OAI
