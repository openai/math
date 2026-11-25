import OAI.Hierarchy.DescentCalendarOriginalPeers
import OAI.Hierarchy.DescentNamedOriginalDonors
import OAI.Hierarchy.DescentOriginalDonorActorWords
import OAI.Hierarchy.DescentOriginalDonorWordWidths
import OAI.Hierarchy.DescentCalendarOriginalContact

namespace OAI
/-! # Original donor words reached from the selected root packet and previous actor flags -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentGL DescentDenseHostOrder
open DescentResetPeerUnionRAM DescentPackedColony DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentPaidResidentCount.Reset DescentSIMDLookup DescentPackedZip DescentContactDonorFront
open DescentGroupPeerOrder DescentResetLocalRoster DescentResetStemKey DescentStageEdgeReceipt
open DescentPacking.PackedMatch.Local.Stage DescentSharedCableNames.Stage DescentIssuedFallbackPanel
open DescentSixParty.Chronology DescentPackedWalsh DescentResetGates DescentResetHostSize
open DescentPackedZip DescentFallbackPeriod.Projected.Receiver DescentPlainTerminal.Suffix
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) (M nextM : ℕ) (calendar : List ℕ)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "cc" => (T).commonDepth
local notation "H" => S.hostSize i
local notation "pad" => input.valid.host
local notation "idt" => input.vertex.trans (Fin.castLEEmb pad)
local notation "tall" => B.frame.host.symm.toEmbedding.trans idt
local notation "named" => (Z).rawHostRank T tall
local notation "J" => 2^cc
local notation "cap" => (A).cap
local notation "deg" => (A).degree
local notation "Ht" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-cc
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "pitch" => H*shelf
local notation "span_" => H*chunks J M
local notation "full" => (A).wire*((A).z*G.b)*cap
variable (paid : cap=(calendar.take i).prod*256)
local notation "boundCap" => (calendar.take i).prod*256
local notation "field" => ResetMiddle.fieldWidth D boundCap n k Ht
local notation "sheets" => CandidateSheets.fromBoard S ctl.board k tail i D f g boundCap nextM
local notation "metaBits" => (sheets).metaBits
local notation "phys" => setupFront S ctl.board k tail i D f g M nextM field metaBits C ctl.bitsR calendar
local notation "bits" => (phys).peer.bits
variable {bw N K R hm l tiny t bit : ℕ}
  (rc : Receiver deg cap N (Z).n r cc H (S.groupCount i) K R M hm l tiny field Ht bw)
  (E : EstimatorArena) (stencil : StencilBook) (source : StencilBook.Sources)
  (base split hubWidth : ℕ) (ports : Ports deg) (oldId oldHub : Bank)
  (fee total portPitch groupDigits batches factor : ℕ)
  (primitive : CanonicalTag (2^(Z).n)→Cell bit) (page : RootPage r (2^(Z).n))
local notation "layer" => DescentRecordedRotorLayers.width f cap
local notation "book" => rc.issuedBook E stencil source base split hubWidth ports oldId (.lit cap)
  f fee full total portPitch (Z).graph (Z).width C groupDigits batches layer factor primitive page
local notation "src" => rc.atlasSources E stencil source base split hubWidth ports oldId (.lit cap)
  f fee full total portPitch (Z).graph (Z).width C groupDigits batches layer factor primitive page
variable (space : rc.PreparedFits book) (mem : Memory bw)
  (directory : ℕ) (actorBank : Bank) (before : Memory bw)
local notation "dir" => (⟨directory,H,shelf,chunks J M⟩ : DescentResetNewActorDirectory.Layout)
local notation "floor" => (dir).endAddress
local notation "originBanks" => EarlierBanks.fromRoot rc book src oldId oldHub dir actorBank
local notation "old" => EarlierBanks.castTo input.branch (calendar_residual B) paid B.dimension originBanks
local notation "original" => calendarOriginals S ctl.board k tail i D f g M nextM field metaBits C ctl.bitsR calendar floor old
local notation "scene" => (phys).fromOriginals floor original (dir).flags (dir).count (dir).inverse
local notation "initial" => (dir).result actorBank before
local notation "next" => (phys).oldKeys floor
local notation "geom" => peerLayout B next H M (phys).privateBits ((phys).stemField+2) bits
local notation "origin" => (geom).endAddress
local notation "donor" => peerDonorShape B H M field (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3))
local notation "start" => (donor).endAddress origin
local notation "CA" => contactLayout B start H M field bits
local notation "sensors" => Shape.move (canonical_donor B M nextM field metaBits calendar paid) (old).donor
variable (safe : (phys).SceneRoom floor scene bw) (x : OriginalArrays B pad field)
  (levels : Fin H→ℕ) (unit : 0 < (Z).unit)
local notation "vals" => calendarRootWord (t:=t) B x M nextM metaBits calendar paid rc book space mem levels
local notation "job" => (donor).sender origin
local notation "ceiling" => rc.headerEnd book
local notation "middle" => rc.preparedMid book space mem
local notation "finalRoots" => rc.preparedImage book space mem
local notation "axis" => congrArg (fun u=>2^(u-cc)) B.keyWidth
local notation "cat_" => RootTemplates.arena ceiling H J M r (Z).n deg
local notation "head_" => stencil.header base
local notation "num" => Fintype.card input.V
local notation "marks" => originalCable B x


variable {date : PhysicalReset} {startDate : ℕ} (I : date.DateInputs startDate bw)
local notation "V₀" => date.successor
local notation "area₀" => date.rebased startDate
local notation "H₁" => (V₀).sheets.hosts
local notation "start₀" => (V₀).actorEnd area₀
local notation "dir₀" => (V₀).actor.directory ((V₀).middle.stop area₀)
local notation "original₀" => calendarOriginals S ctl.board k tail i D f g M nextM field metaBits C ctl.bitsR calendar start₀ old
local notation "good" => contactOutputs B H M field (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3))
    (S.groupCount (i+1)) (2^k) nextM (phys).contact.outputBits metaBits
local notation "raw" => calendar_sender_raw B field (fun lo j v b=>DescentResetOppositePayload.widened
    deg cap field (originalCable B x v b lo j))
local notation "L" => 2^(S.groupWidth k tail i+k-cc)
local notation "signedSlots" => L*(2*cap)

include safe unit

noncomputable def original_packet_donors {nbits p : ℕ} (recorded : B.Recorded p)
    (hdr : OriginalHeader B pad rc book mem)
    (μ : DescentGL.Layout (Z).k) (won : HEq μ B.frame.basis)
    (packet : RootPacket B rc book space mem hdr src x nbits t)
    (level : r < 2^nbits) (one : 1 < 2^nbits) (mass : 2^r*full < 2^nbits)
    (codes : 2*DescentFallbackShapeTable.rows r (2^(Z).n) ≤ 2^t)
    (active : 0 < full) (quotaPos : 0 < quota S.rounds) (degreePos : 0 < 32*Nat.clog 2 (2*deg))
    (depths : ∀v,levels (idt v)=(Z).placement.b (B.frame.host v))
    (precision : t ≤ field) (depthFit : r+1 < 2^field) (capFit : cap < 2^field)
    (elapsed : 0 < i) (sorted : SourceSorted W input.order)
    (baseRoom : max (max r (2^(Z).n)) (2^r) < 2^field) (dimension : (Z).n < field)
    (socketRoom : rootSlots r (2^(Z).n)*(2^(Z).n+2^Ht) < 2^field)
    (heightRoom : Ht < 2^field) (portRoom : deg ≤ 2^field)
    (lanes : 0 < M) (physicalHosts : stencil.hosts=H) (extent : H < 2^bw)
    (counted : ∀q : Row H J M,source.count.eval middle ((row H J M q).val:Word bw)=(num:Word bw))
    (owner : ∀q : Row H J M,(Expr.lookup oldId .row).eval middle ((row H J M q).val:Word bw)=(q.1.val:Word bw))
    (chart : (head_).chart.Resident middle) (addresses : (head_).depth.Fits bw ceiling)
    (priorDepths : source.levels.Fits bw ceiling)
    (range : ∀v : Fin H,v.val < num → v.val*(stencil.m+1) < source.levels.size)
    (observedDepth : ∀v : Fin H,v.val < num → middle (source.levels.base+v.val*(stencil.m+1))=(levels v:Word bw))
    (common : ∀v : Fin H,v.val < num → cc ≤ levels v ∧ levels v < 2^bw)
    (shortDepth : ∀v : Fin H,v.val < num → levels v-cc+1 < 2^field)
    (low : Ht+2 < bw) (rankRoom : Ht+2 ≤ field)
    (area : (src).OperandRoom H J M bw ceiling)
    (rootsFit : ∀s root j,let pg:=privatePage («r»:=r) (n:=(Z).n) s root
      ;(((book).table pg).2.reads j).Fits bw ((cat_).middle (rootIndex r (2^(Z).n) pg).val))
    (rootsPacked : ∀s root,let pg:=privatePage («r»:=r) (n:=(Z).n) s root
      ;M*max (((book).table pg).2.field*((book).table pg).1) ((book).table pg).2.outputBits ≤ bw/2)
    (rootEnd : rc.preparedEnd book ≤ directory)
    (kept : ∀a,a < rc.preparedEnd book → before a=finalRoots a)
    (actorFit : actorBank.Fits bw directory) (actorSpan : pitch*chunks J M ≤ actorBank.size)
    (occupied : ∀l (p : Row H J M),before (actorBank.base+l.val*span_+(row H J M p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B pad) l) p).val:Word bw))
    (chunkRoom : chunks J M ≤ 2^bw) (keyRoom : next < 2^bw)
    (idFit : oldId.Fits bw rc.origin) (idRoom : span_ ≤ oldId.size)
    (hostWords : ∀q : Row H J M,mem (oldId.base+(row H J M q).val)=(q.1.val:Word bw))
    (donorRoom : (donor).Space origin sensors bw) (romRoom : origin < 2^bw)
    (endRoom : (CA).endAddress < 2^bw) (packedMarker : M*max (field*8) bits ≤ bw/2)
    (wordPositive : 0 < field) (packedDonor : (job).Packed bw)
    (boardWidth : M*max (field*(CA).oldFields) (CA).viewBits ≤ bw/2)
    (shapeWidth : shelf ≤ 2^field) (markerWidth : (deg+1)*shelf < 2^bits)
    (room : Program.endAddress (CA).endAddress H shelf deg (peerEvidenceRows B) bits M < 2^bw)
    (maxHost : h≤2^k) (cal : MixedGeometry B M nextM calendar V₀ area₀)
    (registered : NumberGeometry B I) (goodWire : I.DonorWiring) (ok : I.Ready)
    (grid : dir₀=dir) (front : (V₀).front=phys) (back : HEq I.earlier original₀)
    (ss : (V₀).sheets=sheets) (bound : Fintype.card B.next.V≤H₁)
    (newHosts : H₁≤2^bw) (dirRoom : (dir).endAddress<2^bw)
    (right : (CA).endAddress≤(phys).trunkEnd floor)
    (remote : (good).marker ((phys).trunkEnd floor)+H*chunks J M<2^bw)
    (items : M*max (field*(signedSlots+1)) field≤bw/2) :
    WordDonors B M nextM calendar I cal pad bound registered initial:=by
  have checked:=calendar_original_probe
    (B := B) (M := M) (nextM := nextM) («field» := field)
    («metaBits» := metaBits) (calendar := calendar) (paid := paid) (rc := rc)
    (E := E) (stencil := stencil) (source := source) (base := base)
    (split := split) (hubWidth := hubWidth) (ports := ports) (oldId := oldId)
    (oldHub := oldHub) (fee := fee) (total := total) (portPitch := portPitch)
    (groupDigits := groupDigits) (batches := batches) (factor := factor) (primitive := primitive)
    (page := page) (space := space) (mem := mem) (directory := directory)
    (actorBank := actorBank) (before := before) (safe := safe) (x := x)
    (levels := levels) (unit := unit) (recorded := recorded) (hdr := hdr)
    (μ := μ) (won := won) (packet := packet) (level := level)
    (one := one) (mass := mass) (codes := codes) (active := active)
    (quotaPos := quotaPos) (degreePos := degreePos) (depths := depths) (precision := precision)
    (depthFit := depthFit) (capFit := capFit) (elapsed := elapsed) (sorted := sorted)
    (baseRoom := baseRoom) (dimension := dimension) (socketRoom := socketRoom) (heightRoom := heightRoom)
    (portRoom := portRoom) (lanes := lanes) (physicalHosts := physicalHosts) (extent := extent)
    (counted := counted) (owner := owner) (chart := chart) (addresses := addresses)
    (priorDepths := priorDepths) (range := range) (observedDepth := observedDepth) (common := common)
    (shortDepth := shortDepth) (low := low) (rankRoom := rankRoom) (area := area)
    (rootsFit := rootsFit) (rootsPacked := rootsPacked) (rootEnd := rootEnd) (kept := kept)
    (actorFit := actorFit) (actorSpan := actorSpan) (occupied := occupied) (chunkRoom := chunkRoom)
    (keyRoom := keyRoom) (idFit := idFit) (idRoom := idRoom) (hostWords := hostWords)
    (donorRoom := donorRoom) (romRoom := romRoom) (endRoom := endRoom) (packedMarker := packedMarker)
    (wordPositive := wordPositive) (packedDonor := packedDonor) (boardWidth := boardWidth) (shapeWidth := shapeWidth)
    (markerWidth := markerWidth) (room := room)
  have since : start₀=floor:=congrArg DescentResetNewActorDirectory.Layout.endAddress grid
  have wide : M≤bw:=(Nat.le_mul_of_pos_right M ((by omega : 0<field*8).trans_le (Nat.le_max_left ..))).trans
    (packedMarker.trans (Nat.div_le_self ..))
  obtain ⟨readCount,readInv,smallCount,invRoom⟩:=
    actual_donor_directory B pad directory actorBank before lanes wide occupied actorFit actorSpan chunkRoom dirRoom
  have limits:=numbered_widths B boundCap nextM
  have stock:=contact_field_room B M nextM calendar paid maxHost
  have originalCells:=measured_sender_from_calendar (B:=B) (M:=M) (calendar:=calendar) (rc:=rc) («book»:=book)
    (space:=space) (mem:=mem) (hdr:=hdr) (x:=x) elapsed sorted
  have groupLaw:J=S.groupCount (i+1)*(2^k):= by
    exact group_size B
  apply named_original_donors (B:=B) (oldBatch:=M) (batch:=nextM) (calendar:=calendar) (paid:=paid)
    (I:=I) (cal:=cal) («pad»:=pad) (xs:=calendar_sender_values B M field rc book space mem (calendar_sender_matrix B M field rc book space mem hdr x)) («raw»:=raw) («old»:=old) (frontEq:=front) (oldEq:=back)
    ok initial goodWire registered bound
  · rw [since]
    exact donorRoom
  · rw [since]
    exact endRoom
  · exact packedMarker
  · rw [since,grid]
    exact checked.1
  · rw [since]
    exact right
  · rw [since]
    exact packedDonor
  · rw [since]
    exact boardWidth
  · rw [since]
    exact remote
  · exact stock
  · exact items
  · exact groupLaw
  · exact originalCells
  · simpa only [ss] using limits.1
  · simpa only [ss] using limits.2.1
  · exact limits.2.2
  · simpa only [grid] using readCount
  · simpa only [grid] using readInv
  · exact smallCount
  · exact newHosts
  · simpa only [grid] using invRoom

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
