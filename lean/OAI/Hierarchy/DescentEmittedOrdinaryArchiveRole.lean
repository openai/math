import OAI.Hierarchy.DescentRegisteredRoleStock
import OAI.Hierarchy.DescentOrdinaryFullRoleCells
import OAI.Hierarchy.DescentRegisteredNodeChart

namespace OAI
/-! The complete ordinary primitive field in ArchiveRead, on the registered
bank and its actual physical lane layout. -/
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

open DescentSixParty.Chronology.DatePorts

variable (ports_ : DatePorts) (room_ : RangeRoom ports_ target (ticket.advance arch).bit)
    (L : DescentOrdinaryPrimitiveCheckpoint.Layout) (cool : L.Stock) (chart : L=primitiveLayout (K₀:=K₀) (s:=s) (Z:=Z) (cap:=cap) op H b K' preM newM idM working saved)
local notation "frozen" => (chart ▸ cool : (C₁).Stock)

include old_live old_empty held formed in
theorem emitted_primitive_archive {w : ℕ} (m : Computability.VPVNP.BurstRAM.Memory w)
    (published : L.Published cool ports_.archive.roles.bank m)
    (hosts_ : H*pitch=ports_.operandHosts) (nodes_ : K'=ports_.nodes) (pitch_ : saved=ports_.roleLanes)
    (past : ∀x h j,(frozen).previous x (h.castLE enough) j=previous x h (remix j))
    (birth : ∀x t a h j,(frozen).newborn ((C₁).bornIndex x t a) (h.castLE enough) j=born x t a h (remix j))
    (neighbors : ∀h p,(frozen).next (h.castLE enough) p=(near₁ h p).map (Fin.castLE enough))
    (stamps : ∀x h g,(frozen).origin x h g=DescentScalarBookReshape.book (fun l=>DescentOrdinaryRasterReturn.extend (H:=H)
      (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b) l)) x h g)
    (auth : stock) (wide : N₀<2^b)
    : ∀x : Fin (2^ports_.venue.k),DescentPackedColony.Reads (ports_.archive.roles.bank x.val)
        (fun h g=>encode width ports_.nodes (fun j=>(slotAt ports_ target next (advance ticket arch prior) room_ x j h g).elim 0
          (fun p=>tok ((post).atNode p)))) ports_.roleLanes m:=by
  have emitted : (C₁).Published frozen ports_.archive.roles.bank m:=Layout.Published.chart chart cool published
  apply primitive_of_cells ports_ target next (advance ticket arch prior) room_ op (post).atNode m hosts_ nodes_ pitch_
  intro x
  exact full_primitive_bank (ticket:=ticket) (arch:=arch) (age:=age) (radix:=radix) (tokens:=tokens)
    (fits₀:=fits₀) (prior:=prior) (op:=op) (menu:=menu) (old:=old) (limit:=limit) (previous:=previous) (born:=born)
    (held:=held) (formed:=formed) (priorCount:=priorCount) (old_live:=old_live) (old_empty:=old_empty)
    (enough:=enough) (fun q=>ports_.archive.roles.bank q.val) m frozen past birth neighbors stamps auth wide emitted x

include old_live old_empty in
theorem captured_primitive_archive {w : ℕ} (m : Computability.VPVNP.BurstRAM.Memory w)
    (published : L.Published cool ports_.archive.roles.bank m)
    (hosts_ : H*pitch=ports_.operandHosts) (nodes_ : K'=ports_.nodes) (pitch_ : saved=ports_.roleLanes)
    (previousNode : ∀u t,(encode width oldN).symm
      ((frozen).previous ((A).block u) ((cap.vertex ((A).pos u).2).castLE enough) (finProdFinEquiv (digits ((A).pos u).1)))
      (ord₀ u t)=tok (old.atNode ⟨u,t⟩))
    (bornParty : ∀j who,let u:=W.graph.src ((r).pick (j,0));
      (frozen).newborn ((C₁).bornIndex ((A).block u) (origin j) who) ((cap.vertex ((A).pos u).2).castLE enough)
        (finProdFinEquiv (digits ((A).pos u).1))=tok (bornLabel (s:=s) op (c:=c) limit j who))
    (neighbors : ∀h p,(frozen).next (h.castLE enough) p=(near₁ h p).map (Fin.castLE enough))
    (stamps : ∀x h g,(frozen).origin x h g=DescentScalarBookReshape.book (fun l=>DescentOrdinaryRasterReturn.extend (H:=H)
      (oldInput age radix (originRaster (K₀:=K₀) ticket arch tokens priorCount K' b) l)) x h g)
    (auth : stock) (wide : N₀<2^b)
    : ∀x : Fin (2^ports_.venue.k),DescentPackedColony.Reads (ports_.archive.roles.bank x.val)
        (fun h g=>encode width ports_.nodes (fun j=>(slotAt ports_ target next (advance ticket arch prior) room_ x j h g).elim 0
          (fun p=>tok ((post).atNode p)))) ports_.roleLanes m:=by
  let past:=fun (x : Block k) (h : Fin OH) (g : Fin OG)=>
    (frozen).previous x (h.castLE enough) (finProdFinEquiv (digits g))
  let fresh:=fun (x : Block k) (t : Fin (A).cap) (a : Fin 6) (h : Fin OH) (g : Fin OG)=>
    (frozen).newborn ((C₁).bornIndex x t a) (h.castLE enough) (finProdFinEquiv (digits g))
  exact emitted_primitive_archive (ticket:=ticket) (arch:=arch) (tokens:=tokens) (age:=age) (radix:=radix)
    (fits₀:=fits₀) (prior:=prior) (op:=op) (menu:=menu) (old:=old) (limit:=limit) (previous:=past)
    (born:=fresh) (held:=previousNode) (formed:=bornParty) (priorCount:=priorCount)
    (old_live:=old_live) (old_empty:=old_empty) (enough:=enough) (ports_:=ports_) (room_:=room_)
    (L:=L) (cool:=cool) (chart:=chart) m published hosts_ nodes_ pitch_
    (fun x h j => by
      simp [past]
      exact congrArg ((frozen).previous x (h.castLE enough)) (finProdFinEquiv.apply_symm_apply j).symm)
    (fun x t a h j => by
      simp [fresh]
      exact congrArg ((frozen).newborn ((C₁).bornIndex x t a) (h.castLE enough))
        (finProdFinEquiv.apply_symm_apply j).symm) neighbors stamps auth wide

end
end Hierarchy.DescentLocalArchiveOrder.PaddedOrigin

end OAI
