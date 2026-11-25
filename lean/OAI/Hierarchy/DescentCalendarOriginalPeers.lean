import OAI.Hierarchy.DescentCalendarSenderRoster
import OAI.Hierarchy.DescentCalendarWindowOrigins
import OAI.Hierarchy.DescentCalendarIssuedRootPages
import OAI.Hierarchy.DescentPreparedSenderRoom

namespace OAI
/-! # The dated reset peer directory and private pages from the one original root packet -/
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
set_option hygiene false
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) (M nextM field metaBits : ℕ) (calendar : List ℕ)
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

include safe unit

/-- Read the actual signed, tagged, matrix, rank and private-root columns. All
four families of original peers use the actor directory produced after these
columns and the same chronological memory at the start of the peer program. -/
theorem calendar_original_probe {nbits p : ℕ} (recorded : B.Recorded p)
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
    (room : Program.endAddress (CA).endAddress H shelf deg (peerEvidenceRows B) bits M < 2^bw) :
    (job).Before sensors
      (calendar_sender_values B M field rc book space mem
        (calendar_sender_matrix B M field rc book space mem hdr x))
      (hostRotor idt (hostRoster (A) ((idt).trans Fin.valEmbedding)))
      (calendar_sender_raw B field (fun lo j v b=>DescentResetOppositePayload.widened deg cap field (originalCable B x v b lo j)))
      (RawTables.image (Z).graph r Ht geom (peerTemplate B) ((phys).probeStart floor scene initial)) ∧
    ((∃found : Fin pitch→Fin 3→Option (Fin pitch),
      (∀v j,(phys).preScalar floor scene safe initial ((phys).peer.rawPeers ((phys).peers floor)+j.val*pitch+v.val)=
        (target (found v j):Word bw)) ∧
      (∀v : B.next.V,DescentSortedRoster.present (selfPeers found) (named v)=(insert v ((Z).emittedNear T v)).map named) ∧
      ∀v : B.next.V,(∀j,found (named v) j≠some (named v)) ↔ v∉(Z).emittedNear T v) ∧
    ∀s root,Reads (rc.privatePageBank book s root) (vals s root) M ((phys).preScalar floor scene safe initial)) ∧
    ∃keys : Fin (stemsCount B)→Fin H→Block cc→Cell (field+2),
      PeerOrigins B pad (⟨keys,(Z).sparseActor T tall,vals⟩ : PriorPeerWords B H (phys).privateBits (field+2))
        unit (privatePanelAt B (private_count_eq B)) := by
  have short:=packet.short
  have sites:=packet.sites
  have tags:=packet.tagged
  have wires:=packet.signed
  have physicalRoster:=packet.mounted
  have edge : floor ≤ next:=by
    rw [calendar_peer_stop B M nextM field metaBits ctl.bitsR calendar paid floor]
    unfold Columns.stop Columns.start
    omega
  have cuts : directory ≤ floor:=Nat.le_add_right ..
  have head : ceiling ≤ rc.preparedEnd book:=Nat.le_add_right ..
  have grow := head.trans rootEnd
  have lane (j : Block r) : span_ ≤ ((src).here j).size:=Nat.le_pow_clog (by decide) _
  have signedSize (a : Block r) (j : Fin (2*cap)) : span_ ≤ ((src).signed a j).size:=Nat.le_pow_clog (by decide) _
  have sourceBudget:=(rc.sender_prior_fits book (EarlierBanks.rankTicket r (Z).n) src oldId area signedSize idFit
    ((rootEnd.trans (cuts.trans edge)).trans_lt keyRoom))
  have val (v hi j) : (originalColumn (t:=t) B x v hi j).val=x.stencil v hi (j.cast axis) :=
    Fin.val_cast_of_lt (short v hi _)
  have siteRead (a : Block r) : Reads ((src).here a)
      (fun v hi => ((originalColumn (t:=t) B x v hi a).val : Cell field)) M middle := by
    have row : (fun v hi => ((originalColumn (t:=t) B x v hi a).val : Cell field)) =
        (fun v hi => (x.stencil v hi (a.cast axis) : Cell field)) := by
      funext v hi
      rw [val]
    rw [row]
    exact sites a
  have tagRead (a : Block r) : Reads ((src).tagged a)
      (fun v hi => (((originalColumn (t:=t) B x v hi a).val + 1 : ℕ) : Cell field)) M middle := by
    have row : (fun v hi => (((originalColumn (t:=t) B x v hi a).val + 1 : ℕ) : Cell field)) =
        (fun v hi => ((x.stencil v hi (a.cast axis) + 1 : ℕ) : Cell field)) := by
      funext v hi
      rw [val]
    rw [row]
    exact tags a
  have privateRows:=calendar_issued_root_pages (t:=t) B M nextM field metaBits calendar paid rc E stencil source base split
    hubWidth ports oldId fee full total portPitch groupDigits batches factor primitive page space mem before x levels
    lanes physicalHosts extent counted owner chart addresses priorDepths range observedDepth common shortDepth capFit
    low rankRoom area.remoteShape physicalRoster (fun j=>⟨area.localShape j,lane j⟩)
    (fun a j=>⟨area.ports a j,signedSize a j⟩) siteRead tagRead
    (fun a j=>wires j a) rootsFit rootsPacked ((rootEnd.trans (cuts.trans edge)).trans_lt keyRoom) kept
  obtain ⟨keyFits,keySpan,access,loaded,own,tagged,signs⟩:=calendar_window_receipt B calendar paid rc book
    space mem src oldId oldHub directory actorBank before x rootEnd kept actorFit chunkRoom (edge.trans_lt keyRoom)
    area.remoteShape physicalRoster sites tags wires
  have preserved:=rc.before_header book space mem
  have portFit:=area.remoteShape 0
  have stayed (a : ℕ) (h : a < ceiling) : before a=middle a:=(kept a (h.trans_le head)).trans (preserved a h)
  have routes:=Chooser.mounted_before ports ((src).tagged 0) x.peers middle finalRoots physicalRoster preserved portFit
  have beforeRoutes:=Chooser.mounted_before ports ((src).tagged 0) x.peers middle before physicalRoster stayed portFit
  have afterWire (a : Block r) (j : Fin (2*cap)) := Chooser.reads_before ((src).signed a j) _
    middle finalRoots (wires j a) preserved (area.ports a j) (signedSize a j)
  obtain ⟨⟨setup,measured⟩,signed,sender⟩:=calendar_sender_probes B M nextM field metaBits calendar paid rc book
    space mem src oldId oldHub directory actorBank before hdr x safe elapsed sorted baseRoom dimension socketRoom
    heightRoom portRoom actorFit chunkRoom keyRoom romRoom rootEnd kept low rankRoom sourceBudget
    (Chooser.accessible_before _ _ portFit head) packet.matrix afterWire routes idFit idRoom hostWords
  refine ⟨?_,?_⟩
  · have rosterEq : x.peers = hostRotor idt (hostRoster (A) ((idt).trans Fin.valEmbedding)) :=
      packet.routes.trans (sender_roster input)
    exact (congrArg (fun peers => (job).Before sensors
      (calendar_sender_values B M field rc book space mem
        (calendar_sender_matrix B M field rc book space mem hdr x)) peers
      (calendar_sender_raw B field (fun lo j v b => DescentResetOppositePayload.widened deg cap field (originalCable B x v b lo j)))
      (RawTables.image (Z).graph r Ht geom (peerTemplate B) ((phys).probeStart floor scene initial))) rosterEq).mp sender
  exact calendar_peer_registers B M nextM field metaBits calendar paid rc book space mem src oldId oldHub
    directory actorBank before safe x levels unit recorded hdr μ won packet.word short level one mass codes active quotaPos
    degreePos depths precision depthFit capFit keyFits keySpan access loaded own tagged signs rootEnd privateRows
    actorFit actorSpan occupied chunkRoom keyRoom (Chooser.bank_before portFit.roster grow) portFit.rosterRoom
    beforeRoutes.roster donorRoom endRoom packedMarker _ _ setup measured signed wordPositive packedDonor sender
    boardWidth shapeWidth markerWidth room

/-- The chronological sparse peers and all retained original root rows. -/
theorem calendar_original_peers {nbits p : ℕ} (recorded : B.Recorded p)
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
    (room : Program.endAddress (CA).endAddress H shelf deg (peerEvidenceRows B) bits M < 2^bw) :
    (∃found : Fin pitch→Fin 3→Option (Fin pitch),
      (∀v j,(phys).preScalar floor scene safe initial ((phys).peer.rawPeers ((phys).peers floor)+j.val*pitch+v.val)=
        (target (found v j):Word bw)) ∧
      (∀v : B.next.V,DescentSortedRoster.present (selfPeers found) (named v)=(insert v ((Z).emittedNear T v)).map named) ∧
      ∀v : B.next.V,(∀j,found (named v) j≠some (named v)) ↔ v∉(Z).emittedNear T v) ∧
    ∀s root,Reads (rc.privatePageBank book s root) (vals s root) M ((phys).preScalar floor scene safe initial) := by
  exact (calendar_original_probe
    (B := B) (M := M) (nextM := nextM) (field := field)
    (metaBits := metaBits) (calendar := calendar) (paid := paid) (rc := rc)
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
    (markerWidth := markerWidth) (room := room)).2.1

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
