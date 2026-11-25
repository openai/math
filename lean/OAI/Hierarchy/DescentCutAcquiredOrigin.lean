import OAI.Hierarchy.DescentCutAcquiredNumerals
import OAI.Hierarchy.DescentAcquiredOriginSelection
import OAI.Hierarchy.DescentCutAcquiredSources

namespace OAI
/-! Readback of the physically recorded old/new ordinal from the chosen cut. -/
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

/-- The concrete selected ticket source, clipped to its original hosts, is the actual
pre-normalization route for every old and newborn actor. -/
theorem cut_stored_routes (canonical:stores.Canonical):
    Descriptors shelf k (A).pos (A).block (ticketParent (he:=nonneg) (T:=T)) (ticketSlot (c:=choice) ticket)
      ((activeChart ticket).key nonneg T choice ∘ newSite) prior.vertex (Function.Embedding.refl _) origMoves realTokens ∧
    (∀x j (h:Fin H₀) groupIndex,Hreal≤h.val→actualRows x j h groupIndex=none) ∧
    ∀h groupIndex,stores.hubs (h.castLE stores.oldFit)=flags (cap:=prior) h groupIndex:=by
  exact cut_authentic_material (stores:=stores) canonical

include before tail cut in
theorem cut_origin_stamp (age:i<S.length) (arch:Archive _) (canonical:stores.Canonical)
    (pg:Fin (vx₀).pageCount) (l:Fin (vx₀).lows) (h:Fin (vx₀).hosts) (y:Fin GS):
    let axes:=selected_w_axes X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
    selection _ (rc₀).nodes (v₀).originBits (marked (stores.books pg l) h y)=
      DescentOrdinaryRasterReturn.extend (H:=H₀) (oldInput age radix
        (originRaster (K₀:=ports.nodes) ticket arch realTokens realCounts (rc₀).nodes (v₀).originBits) (l.cast axes.2.1)) h y:=by
  intro axes
  have truth:=cut_stored_routes (X:=X) (G:=G) (S:=S) (ticket:=ticket) (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (w:=w) (shelfHeader:=shelfHeader) (headerBase:=headerBase) (pos:=pos) (code:=code) (exec:=exec) (stores:=stores) canonical
  apply (cut_stamp_row (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket) (before:=before) (tail:=tail) (cut:=cut) (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (w:=w) (shelfHeader:=shelfHeader) (headerBase:=headerBase) (pos:=pos) (code:=code) (exec:=exec) (stores:=stores) age canonical pg l h y).trans
  exact acquired_stamp (fieldBits:=(v₀).reference.bits) (K₀:=ports.nodes) ticket arch realTokens age radix realCounts stores.oldFit
    actualRows (fun h _=>stores.hubs h) countSource (l.cast axes.2.1) h y
    (fun _ _ _ _=>rfl) truth.2.1 truth.2.2 (fun _ _ _=>rfl)

/-- Crossing the compact low pitch changes only the proof of the finite host address. -/
theorem cut_book_cast {H Q Q' J r a:ℕ} (eq:Q=Q')
    (left:Fin Q→Fin H→Fin (J*r)→Cell a) (right:Fin Q'→Fin H→Fin (J*r)→Cell a)
    (rows:∀l h y,left l h y=right (l.cast eq) h y)
    (x:Fin r) (h:Fin (H*Q')) (g:Fin J):
    DescentScalarBookReshape.book left x (h.cast (congrArg (H*·) eq.symm)) g=
      DescentScalarBookReshape.book right x h g:=by
  subst Q'
  exact rows _ _ _

include before tail cut in
theorem cut_origin_bank (age:i<S.length) (arch:Archive _) (canonical:stores.Canonical)
    (pg:Fin (vx₀).pageCount) (x:Block k) (h:Fin (H₀*pitch₀)) (selectedGroup:Fin (S.groupCount (i+1))):
    let axes:=selected_w_axes X G S br ticket before tail cut ports op tailBits drift degree payload seats root ordinary
    DescentScalarBookReshape.book (fun l h groupIndex=>selection _ (rc₀).nodes (v₀).originBits (marked (stores.books pg l) h groupIndex))
       x (h.cast (congrArg (H₀*·) axes.2.1.symm)) selectedGroup=
      DescentScalarBookReshape.book (fun l=>DescentOrdinaryRasterReturn.extend (H:=H₀)
        (oldInput age radix (originRaster (K₀:=ports.nodes) ticket arch realTokens realCounts (rc₀).nodes (v₀).originBits) l)) x h selectedGroup:=by
  intro axes
  apply cut_book_cast (H:=H₀) (J:=S.groupCount (i+1)) (r:=2^k) axes.2.1
  exact (cut_origin_stamp (X:=X) (G:=G) (S:=S) (br:=br) (ticket:=ticket) (before:=before) (tail:=tail) (cut:=cut) (ports:=ports) (op:=op) (tailBits:=tailBits) (drift:=drift) (degree:=degree) (payload:=payload) (seats:=seats) (root:=root) (ordinary:=ordinary) (w:=w) (shelfHeader:=shelfHeader) (headerBase:=headerBase) (pos:=pos) (code:=code) (exec:=exec) (stores:=stores) age arch canonical pg)

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
