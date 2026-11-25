import OAI.Hierarchy.DescentNamedCutPrimitivePublished
import OAI.Hierarchy.DescentNamedCutNewbornToken
import OAI.Hierarchy.DescentEmittedOrdinaryArchiveRole
import OAI.Hierarchy.DescentCutStoredRole
import OAI.Hierarchy.DescentCutAcquiredOrigin
import OAI.Hierarchy.DescentPrimitiveStockChart
import OAI.Hierarchy.DescentRegisteredRoleHalo

namespace OAI
/-! The entire returned ordinary role register at a chosen physical cut. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentDatedAddressBook DescentCompiler.TerminalScale DescentCompiler Chronology DescentPacking.PackedMatch.Local.Stage.Dated
open DescentPacking.PackedMatch.Local.Stage
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 3500
set_option maxHeartbeats 650000

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "price" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "fee" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => price*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
variable {he : 0 ≤ fee} {hu : 0 ≤ u} {radix : S.radix=2^k}
variable {run : Epochs G hu he (h:=h) (C:=C) («Ht»:=Ht) (t:=S.rounds) S.height
      (initial X S.copies s (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S radix R run c)
local notation "P" => (Σ _ : Fin S.copies,Fin (Fintype.card (Port pins X.width)))
local notation "bits" => (fun _ : P=>s*1)
variable {W : MarkedWorld F 0 P bits} {i z D z' D' : ℕ} {rate : ℝ}
    {prior : Reached W G price fee S k i z D wire s} {T : StageInput W G rate fee}
    {nonneg : 0 ≤ fee} {choice : (T.result nonneg).Choice} {norm : Normalize ((T.result nonneg).state choice)}
    {next : Reached norm.result G price fee S k (i+1) z' D' wire s}
    (ticket : OrdinaryLink prior nonneg T choice norm next)
    (before : Path br.origin.source prior) (tail : Path next br.target)
    (cut : (Path.ordinary before ticket).append tail=br.path)
local notation "A" => prior.placement
local notation "calendar" => capCalendar G.b S.rounds g S.height


set_option quotPrecheck false
variable (ports : DatePorts) (op : RotorSpec) (tailBits drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "books₀" => OrdinaryBooks.atDate G S op g k i p tailBits drift degree payload seats ports
local notation "base₀" => (books₀).onTicket ticket g tailBits p f payload seats ports.venue.lanes ports.io.roster ordinary
local notation "floor₀" => (base₀).stageStart root
local notation "v₀" => DatePorts.ordinaryModel ports ticket op g tailBits p f drift degree payload seats root ordinary
local notation "entry₀" => (base₀).registeredEntry ports floor₀
local notation "mat₀" => (base₀).registered_match ports floor₀ (Nat.le_max_left ports.argumentsPerNode (S.retainedArgumentsAt G drift))

open DescentDatedPriorOperand DescentOperandStateBanks DescentHaloWalkRAM DescentSharedCableNames
open PhysicalOrdinary.ArgumentEntry
open DescentDatedOperandReadPipeline DescentSIMDLookup DescentPackedZip DescentPackedColony
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOperandVectorArena DescentOrdinaryOriginMask
open DescentRawCablePanel ProtocolRAM
open scoped Classical Fin.CommRing
local notation "sh₀" => (base₀).registered_geometry ports floor₀
local notation "rc₀" => (v₀).resolver
local notation "vx₀" => (v₀).vector
local notation "bn₀" => (v₀).bornBook
local notation "g₀" => (v₀).ticketReadGeometry
local notation "M₀" => (rc₀).lanes
local notation "W₀" => (vx₀).lanes*(vx₀).radix
local notation "vecAt" => (v₀).vectorStart floor₀
local notation "mouthEnd₀" => (v₀).originMouthEnd floor₀
local notation "headerEnd" => (v₀).operandHeaderEnd floor₀
local notation "e₀" => (v₀).material
local notation "fmt₀" => (v₀).ticket.depotShape (v₀).short
local notation "ps₀" => (v₀).operandPathStart floor₀
local notation "refs₀" => ((entry₀).directory (v₀) floor₀ (mat₀)).refs
local notation "Val₀" => References.Rows (v₀).vector (v₀).reference.degree (v₀).reference.k (v₀).reference.oldNodes
  (v₀).reference.capacity ((rc₀).size+2)
local notation "dims₀" => DatePorts.ordinary_header_dimensions ports ticket op g tailBits p f drift degree payload seats root ordinary
local notation "H₀" => (entry₀).clip.venue.hosts
local notation "G₀" => (entry₀).clip.venue.groups
local notation "pop₀" => (entry₀).population (v₀) floor₀
local notation "Active" => Fin H₀→Fin G₀→Cell (1*(entry₀).clip.venue.socket.blocks)
local notation "RealPeers" => Fin H₀→Fin (entry₀).clip.venue.socket.degree→Option (Fin H₀)

variable (w shelfHeader headerBase : ℕ) (pos : 0<k)
    (code : DatePorts.OrdinaryCodeRoom ports ticket op g tailBits p f drift degree payload seats root ordinary w)
    (exec : DatePorts.OrdinaryExecutionRoom ports ticket op g tailBits p f drift degree payload seats root ordinary
      w shelfHeader headerBase code)
local notation "wired" m:arg => DatePorts.ordinarySignedMemory ports ticket op g tailBits p f drift degree
  payload seats root ordinary w shelfHeader headerBase pos code exec m


local notation "steps₀" => (v₀).issuedSteps root ports (entry₀) code.signed w (mat₀) (sh₀) code.blocks code.paths
  code.slots code.chip code.endFit code.packed code.radix code.funded
local notation "donors" m:arg => DatePorts.ordinaryDonorMemory ports ticket op g tailBits p f drift degree
  payload seats root ordinary w shelfHeader headerBase pos code exec m
local notation "phys₀" => (v₀).withIssuedSigned
local notation "room₀" => (v₀).signedReturn floor₀ ports.io ports.archive.count (steps₀).parts (steps₀).adjacency w
local notation "page₀" => (⟨0,Nat.mul_pos (by decide : 0<7) code.slots⟩:Fin (7*(vx₀).operands))
open DescentGroupPeerOrder DescentStageEdgeReceipt DescentPacking.PackedMatch.Local

open DescentLocalArchiveOrder.PaddedOrigin DescentScalarVenueMask DescentPacking.PackedMatch.Local.Stage
open DescentGroupPeerOrder DescentOrdinaryAtomFieldRAM
local notation "deg₀" => prior.placement.degree
local notation "shelf" => DescentOrdinaryVenueReturn.shapeSlots deg₀
local notation "pitch₀" => (2^(k+1)-1)*shelf
local notation "trueCap" => prior.placement.cap
local notation "GS" => S.groupCount (i+1)*2^k
local notation "OG" => S.groupCount i
local notation "roleWidth" => (pop₀).roleBits
local notation "nb" => (v₀).reference.nameBits
local notation "mb" => (v₀).reference.countBits


variable {original:Memory w} (stores:CutStores X G S (radix:=radix) (f:=f) (g:=g) (p:=p) ticket ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec original)
local notation "peer_" => hostRotor (prior.vertex.trans (Fin.castLEEmb stores.oldFit))
  (hostRoster prior.placement (prior.vertex.trans Fin.valEmbedding))

open DescentLocalArchiveOrder DescentOrdinaryOriginMask DescentOrdinaryRasterReturn DescentPaidResidentCount
local notation "Hreal" => Fintype.card prior.V
local notation "actualRows" => (entry₀).clip.core.values stores.parts stores.active
local notation "realTokens" => fun x j (v:Fin Hreal) groupIndex=>actualRows x j (v.castLE stores.oldFit) groupIndex
local notation "countSource" => (entry₀).roleValues (v₀) stores.roles
local notation "realCounts" => fun x (v:Fin Hreal) groupIndex=>
  DescentOrdinaryAtomFieldRAM.RoleCounts.count (K:=ports.nodes) mb (countSource x (v.castLE stores.oldFit) groupIndex)
local notation "oldHosts" => prior.vertex.trans (Fin.castLEEmb stores.oldFit)
local notation "rrows" => DescentKernelHistory.BitDescription.scannedRows nonneg T
local notation "newSite" => GadgetNetwork.newSite _ (rrows).pick
  (bestLayout (branchWidth G (fun _:(rrows).pairs=>T.z) ((rrows).profile choice))) (rrows).pack
local notation "origMoves" => rotor A (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding))

open DescentLocalArchiveOrder.PaddedOrigin DescentOrdinaryPrimitiveCheckpoint DescentPrimitivePalette
open DescentKernelHistory DescentGL DescentSharedCableNames DescentRetainedRangeDigits DescentBundleHistory
local notation "Z₀" => S.grainAt G.b p 0
local notation "width_" => printedBits G s Z₀ op
local notation "L_" => (v₀).paletteShape
local notation "stock_" => cut_primitive_stock stores
local notation "chart_" => registered_node_chart X G S br ticket before tail cut op tailBits drift degree payload seats
    ports.venue.lanes ports ports.io.roster ordinary floor₀
local notation "tmp_" => (chart_ ▸ stock_)
local notation "out_" => DatePorts.ordinary (v₀) floor₀
local notation "limit_" => cut_palette_limit X G S br ticket before tail cut
local notation "saxis" => registered_role_axes X G S br ticket before tail cut op tailBits drift degree payload seats
    ports.venue.lanes ports ports.io.roster ordinary floor₀
variable (age:i<S.length) (arch:Archive W) (numbering:Local arch.bit)
  (places:DatePorts.RangeRoom ports prior arch.bit)
  {p₁:ℕ} (menu:Runnable F op)
  (labels:Encoding (Label G s Z₀ op) (dictionary G op menu p₁) arch.bit)
  (resident:∀x hostIndex groupIndex,(stores.roles x hostIndex groupIndex).val=(encode width_ ports.nodes (fun j=>
    (DatePorts.slotAt ports prior arch.bit numbering places (x.cast (congrArg (2^·) places.radix)) j hostIndex (groupIndex.cast places.groups)).elim 0
      (fun y=>token G s Z₀ op (labels.atNode y)))).val)
local notation "updated_" => (Encoding.scanned G op menu labels T nonneg choice limit_).follow norm
local notation "arch_" => (ticket.advance arch).bit
local notation "num_" => advance ticket arch numbering

set_option maxHeartbeats 1100000
set_option cleanup.letToHave false

include before tail cut in
private theorem cut_origin_after_chart (canonical:stores.Canonical)
    (x:Block k) (host:Fin (H₀*pitch₀)) (j:Fin (S.groupCount (i+1))) :
    (chart_ ▸ stock_).origin x host j = DescentScalarBookReshape.book
      (fun l=>DescentOrdinaryRasterReturn.extend (H:=H₀) (oldInput age radix
        (originRaster (K₀:=ports.nodes) ticket arch realTokens realCounts S.retainedNodes (L_).originBits) l)) x host j := by
  apply Fin.ext
  refine (Layout.chart_origin chart_ stock_ x host j).trans ?_
  exact congrArg Fin.val (cut_origin_bank (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket) (before:=before) (tail:=tail) (cut:=cut) (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (w:=w) (shelfHeader:=shelfHeader) (headerBase:=headerBase) (pos:=pos) (code:=code) (exec:=exec) (stores:=stores) age arch canonical page₀ x host j)

include before tail cut in
private theorem cut_neighbors_after_chart (canonical:stores.Canonical)
    (host:Fin Hreal) (socket:Fin (DescentHaloWalkRAM.breadth prior.placement.degree)) :
    (chart_ ▸ stock_).next (host.castLE stores.oldFit) socket =
    ((DescentSortedRoster.indexed (Gather.reaching (hostRotor prior.vertex (hostRoster A (prior.vertex.trans Fin.valEmbedding))))) host socket).map (Fin.castLE stores.oldFit) := by
  apply Layout.option_fin_eq
  refine (Layout.chart_peer chart_ stock_ (host.castLE stores.oldFit) socket).trans ?_
  change ((PhysicalOrdinary.primitiveRoster _ _ (DescentSortedRoster.indexed (Gather.reaching stores.rotor)) _ _).map Fin.val)=_
  rw [canonical.1]
  exact congrArg (Option.map Fin.val) (PhysicalOrdinary.registered_role_rotor stores.oldFit prior.vertex
    (hostRoster A (prior.vertex.trans Fin.valEmbedding)) host socket)

open DescentOrdinaryBorn DescentOrdinaryPaletteBirth
local notation "oldSite" j:arg => W.graph.src ((rrows).pick (j,0))
local notation "oldSlot" j:arg => DescentSharedCableNames.Stage.outgoing A (prior.order.trans Fin.valEmbedding) S prior.valid
  ⟨(rrows).pick (j,0),(A).quantum_positive _ ((rrows).picked (j,0))⟩
local notation "castLayout" => DescentLocalArchiveOrder.PaddedOrigin.primitiveLayout (K₀:=ports.nodes) («s»:=s) («Z»:=Z₀) (cap:=prior) op (v₀).vector.hosts (v₀).paletteShape.originBits S.retainedNodes (v₀).rasterLanes (v₀).bornBook.lanes (v₀).vector.lanes (v₀).palette.workLanes (v₀).palette.nextLanes
include before tail cut in
private theorem cut_birth_after_chart (j : (rrows).pairs) (party : Fin 6) :
    (chart_ ▸ stock_).newborn ((castLayout).bornIndex ((A).block (oldSite j)) (oldSlot j) party)
      ((prior.vertex ((A).pos (oldSite j)).2).castLE stores.oldFit)
      (finProdFinEquiv (S.groupDigits age radix ((A).pos (oldSite j)).1)) =
      token G s Z₀ op (bornLabel («s»:=s) op (c:=choice) limit_ j party) := by
  apply Fin.ext
  refine (Layout.chart_newborn chart_ stock_ ((A).block (oldSite j)) (oldSlot j) party
    ((prior.vertex ((A).pos (oldSite j)).2).castLE stores.oldFit) (finProdFinEquiv (S.groupDigits age radix ((A).pos (oldSite j)).1))).trans ?_
  exact congrArg Fin.val (cut_newborn_token X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec age stores
    (stock_).previous (stock_).origin (stock_).next j party)

local notation "rankOr" site:arg => (bounded arch.bit numbering site).trans (Fin.castLEEmb (maxNodes_le arch.bit places.capacity))
private def roleAtSelectedSource : Prop := ∀ (site : W.graph.Site) (node:(arch.bit.recipe site).Node) (j:Fin ports.nodes),
    j.val=(numbering site node).val →
    let yz:=finProdFinEquiv ((S.groupDigits age radix) ((A).pos site).1)
    let source:=(entry₀).roleValues (v₀) stores.roles
    (encode width_ ports.nodes).symm
      (source ((A).block site) ((prior.vertex ((A).pos site).2).castLE stores.oldFit) (yz.cast stores.groups.symm)) j=
      token G s Z₀ op (labels.atNode ⟨site,node⟩)
include before tail cut in
private theorem cut_previous_after_chart
    (held : roleAtSelectedSource (radix:=radix) (X:=X) (G:=G) (S:=S) (ticket:=ticket) (ports:=ports) (op:=op)
      (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary)
      (w:=w) (shelfHeader:=shelfHeader) (headerBase:=headerBase) (pos:=pos) (code:=code) (exec:=exec) (stores:=stores)
      (age:=age) (arch:=arch) (numbering:=numbering) (labels:=labels))
    (site : W.graph.Site) (node:(arch.bit.recipe site).Node) :
    (encode width_ ports.nodes).symm ((chart_ ▸ stock_).previous ((A).block site)
      ((prior.vertex ((A).pos site).2).castLE stores.oldFit) (finProdFinEquiv (S.groupDigits age radix ((A).pos site).1)))
      ((rankOr site) node) = token G s Z₀ op (labels.atNode ⟨site,node⟩) := by
  apply Fin.ext
  refine (Layout.chart_previous chart_ stock_ ((A).block site) ((prior.vertex ((A).pos site).2).castLE stores.oldFit)
    (finProdFinEquiv (S.groupDigits age radix ((A).pos site).1)) ((rankOr site) node)).trans ?_
  exact congrArg Fin.val (held site node ((rankOr site) node) rfl)

include before tail cut resident age in
theorem cut_primitive_archive (canonical:stores.Canonical)
    (nextRoom:DatePorts.RangeRoom out_ next arch_)
    (post:Memory w) (published:(L_).Published stock_ (out_).archive.roles.bank post):
    ∀x:Fin (2^(out_).venue.k),Reads ((out_).archive.roles.bank x.val)
      (fun hostIndex groupIndex=>encode width_ (out_).nodes (fun j=>(DatePorts.slotAt out_ next arch_ num_ nextRoom x j hostIndex groupIndex).elim 0
        (fun y=>token G s Z₀ op ((updated_).atNode y)))) (out_).roleLanes post:=by
  let chart:=chart_
  let st:=stock_
  have descriptors:=cut_stored_routes (X:=X) (G:=G) (S:=S) (ticket:=ticket) (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (w:=w) (shelfHeader:=shelfHeader) (headerBase:=headerBase) (pos:=pos) (code:=code) (exec:=exec) (stores:=stores) canonical
  have countWide:ports.nodes<2^mb:=(Nat.lt_succ_self _).trans_le (Nat.le_pow_clog (by decide) _)
  have counts:=cut_stored_counts (X:=X) (G:=G) (S:=S) (ticket:=ticket) (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (w:=w) (shelfHeader:=shelfHeader) (headerBase:=headerBase) (pos:=pos) (code:=code) (exec:=exec) (stores:=stores) (B:=arch.bit) (numbering:=numbering) (places:=places)
    (labels:=labels.atNode) (issued:=resident) countWide
  have axes:=saxis
  have room_ : DescentPackedActorMask.nodes ((prior.placement.degree+1)^4*2^k) ports.nodes trueCap<2^(L_).originBits:=by
    have sz:=congrArg DescentOrdinaryPrimitiveCheckpoint.Layout.candidates chart
    calc
      _ = (L_).candidates := sz.symm
      _ < 2^(L_).originBits := (v₀).originBits_fit
  refine captured_primitive_archive (ticket:=ticket) (arch:=arch) (tokens:=realTokens) (age:=age) (radix:=radix)
    (fits₀:=maxNodes_le arch.bit places.capacity) (prior:=numbering) (op:=op) (menu:=menu) (old:=labels)
    (limit:=limit_) (priorCount:=realCounts) (old_live:=counts.1) (old_empty:=counts.2) (enough:=stores.oldFit)
    (ports_:=out_) (room_:=nextRoom) (L:=L_) (cool:=st) (chart:=chart)
    post published axes.1 axes.2.1 axes.2.2 ?_ ?_ ?_ ?_ descriptors.1 room_
  · apply cut_previous_after_chart (radix:=radix) (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket) (before:=before) (tail:=tail) (cut:=cut) (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (w:=w) (shelfHeader:=shelfHeader) (headerBase:=headerBase) (pos:=pos) (code:=code) (exec:=exec) (stores:=stores) (age:=age) (arch:=arch) (numbering:=numbering) (places:=places) (labels:=labels)
    exact fun site node j rankEq=> cut_stored_role X G S ticket ports op tailBits drift degree payload seats root ordinary w shelfHeader headerBase pos code exec stores arch.bit numbering places labels.atNode resident age site node j rankEq
  · exact cut_birth_after_chart (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket) (before:=before) (tail:=tail) (cut:=cut) (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (w:=w) (shelfHeader:=shelfHeader) (headerBase:=headerBase) (pos:=pos) (code:=code) (exec:=exec) (stores:=stores) (age:=age)
  · exact cut_neighbors_after_chart (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket) (before:=before) (tail:=tail) (cut:=cut) (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (w:=w) (shelfHeader:=shelfHeader) (headerBase:=headerBase) (pos:=pos) (code:=code) (exec:=exec) (stores:=stores) canonical
  · exact cut_origin_after_chart (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket) (before:=before) (tail:=tail) (cut:=cut) (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (w:=w) (shelfHeader:=shelfHeader) (headerBase:=headerBase) (pos:=pos) (code:=code) (exec:=exec) (stores:=stores) (age:=age) (arch:=arch) canonical
end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
