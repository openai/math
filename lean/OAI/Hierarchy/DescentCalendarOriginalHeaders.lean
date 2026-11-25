import OAI.Hierarchy.DescentCalendarOriginalStems
import OAI.Hierarchy.DescentReachedCalendarTrunk

namespace OAI
/-! # Original signed-stem and trunk headers on the same attained calendar memory -/
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

open DescentResetFieldAssembler
local notation "newH" => S.hostSize (i+1)
local notation "groups" => S.groupCount (i+1)
local notation "oldLows" => 2^(S.groupWidth k tail i+k-cc)
local notation "sourceSlot" => Fin oldLows × Fin (2*cap)
local notation "ordinal" => DescentResetStemPackedIssue.ordinal oldLows cap
local notation "stemValues" => fun h hi j=>(x.stencil h hi j:Cell t)

variable {nbits p : ℕ} (recorded : B.Recorded p)
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
    (rootsFit : ∀s root j,let pg:=privatePage («r» :=r) (n:=(Z).n) s root
      ;(((book).table pg).2.reads j).Fits bw ((cat_).middle (rootIndex r (2^(Z).n) pg).val))
    (rootsPacked : ∀s root,let pg:=privatePage («r» :=r) (n:=(Z).n) s root
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
    (hubFit : oldHub.Fits bw directory) (hubSpan : H ≤ oldHub.size)
    (hubRead : ∀v : input.V,before (oldHub.base+(input.vertex v).val)=((input.placement.hub v).toNat : Word bw))
    (width : (metaBits*7)*nextM ≤ bw) (trunkRoom : (phys).trunkEnd floor < 2^bw)
    (degreeWord : B.next.placement.degree+1<2^metaBits) (capWord : B.next.placement.cap<2^metaBits)
    (alphabet : 5≤2^metaBits) (wordAlphabet : 5≤2^bw)
include unit recorded hdr μ won packet level one mass codes active quotaPos degreePos depths precision depthFit capFit
  elapsed sorted baseRoom dimension socketRoom heightRoom portRoom lanes physicalHosts extent counted owner
  chart addresses priorDepths range observedDepth common shortDepth low rankRoom area rootsFit rootsPacked
  rootEnd kept actorFit actorSpan occupied chunkRoom keyRoom idFit idRoom hostWords donorRoom romRoom endRoom
  packedMarker wordPositive packedDonor boardWidth shapeWidth markerWidth room hubFit hubSpan hubRead width
  trunkRoom degreeWord capWord alphabet wordAlphabet

private theorem calendar_headers_and_registers :
    ((∀(x₀ : Fin (2^k)) (j : Fin (stemsCount B)),
      ((phys).stemOperand floor x₀.val j.val).Fits bw ((phys).trunkEnd floor) ∧
      DescentPackedZip.Source ((phys).stemOperand floor x₀.val j.val)
        (fun (h₀ : Fin newH) g₀=>DescentResetFieldAssembler.raw metaBits (actualMeta B (originalTrunkRack B) x₀ (stemShelf B j) h₀ g₀))
        nextM (((phys).trunkScene floor scene safe).image initial)) ∧
    ∀x₀ : Fin (2^k),((phys).trunkOperand floor x₀.val).Fits bw ((phys).trunkEnd floor) ∧
      DescentPackedZip.Source ((phys).trunkOperand floor x₀.val)
        (fun (h₀ : Fin newH) g₀=>DescentResetFieldAssembler.raw metaBits (actualMeta B (originalTrunkRack B) x₀ (trunkCandidate B) h₀ g₀))
        nextM (((phys).trunkScene floor scene safe).image initial)) ∧ ActorTrunkReads B input.valid.host phys floor scene safe initial:=by
  have stems:=calendar_original_stems
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
    (markerWidth := markerWidth) (room := room)
    (hubFit:=hubFit) (hubSpan:=hubSpan) (hubRead:=hubRead) (width:=width) (trunkRoom:=trunkRoom)
  have drawn:=(calendar_original_peers
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
    (markerWidth := markerWidth) (room := room)).1
  have early : floor < 2^bw := ((phys).floor_before floor scene safe).trans_lt
    (((phys).front_order floor).1.trans_lt (((phys).front_order floor).2.1.trans_lt safe.stems.final))
  have positive : 0 < max (field*8) bits := (by omega : 0 < field*8).trans_le (Nat.le_max_left ..)
  have machine : M ≤ bw := (Nat.le_mul_of_pos_right M positive).trans (packedMarker.trans (Nat.div_le_self ..))
  have actor := calendar_stem_actor_registers B M directory actorBank oldHub before lanes machine occupied
    actorFit actorSpan chunkRoom early hubFit hubSpan hubRead
  obtain ⟨_,_,_,prefixRead,_,_⟩:=paid_actor_result B input.valid.host directory actorBank before
    lanes machine occupied actorFit actorSpan chunkRoom early
  have pitchEq : (phys).peer.hosts=pitch:=congrArg (H*·) (calendar_palette B)
  have atRanks : ((phys).trunkBanks floor scene).number.base=(dir).ranks.base:=
    (phys).trunk_prefix_base floor scene (dir).ranks.base (by
      change (dir).ranks.base+pitch=(dir).ranks.base+(phys).peer.hosts
      rw [pitchEq])
  have rankEnd : ((phys).trunkBanks floor scene).number.base+pitch≤floor:=by
    rw [atRanks]
    exact Nat.le_of_lt actor.lowCount
  have invEnd:=(dir).ordered.2.2.2.2.2.2.2
  have actual := reached_trunk_with_registers B M nextM field metaBits calendar paid floor old (dir).flags (dir).count
    (dir).inverse safe initial recorded actor.inverseSize actor.lowCount invEnd rankEnd actor.counted
    actor.inverseRead (by simpa only [atRanks] using prefixRead) drawn stems.2.1
    degreeWord capWord alphabet wordAlphabet (by simpa only [Nat.mul_comm 7 metaBits] using width) trunkRoom
  exact ⟨⟨stems.2.2.2,actual.1.2⟩,actual.2⟩


/-- The same original receipt supplies every stem and the trunk on every compact candidate block. -/
theorem calendar_original_headers :
    (∀(x₀ : Fin (2^k)) (j : Fin (stemsCount B)),
      ((phys).stemOperand floor x₀.val j.val).Fits bw ((phys).trunkEnd floor) ∧
      DescentPackedZip.Source ((phys).stemOperand floor x₀.val j.val)
        (fun (h₀ : Fin newH) g₀=>DescentResetFieldAssembler.raw metaBits (actualMeta B (originalTrunkRack B) x₀ (stemShelf B j) h₀ g₀))
        nextM (((phys).trunkScene floor scene safe).image initial)) ∧
    ∀x₀ : Fin (2^k),((phys).trunkOperand floor x₀.val).Fits bw ((phys).trunkEnd floor) ∧
      DescentPackedZip.Source ((phys).trunkOperand floor x₀.val)
        (fun (h₀ : Fin newH) g₀=>DescentResetFieldAssembler.raw metaBits (actualMeta B (originalTrunkRack B) x₀ (trunkCandidate B) h₀ g₀))
        nextM (((phys).trunkScene floor scene safe).image initial) := by
  exact (calendar_headers_and_registers
    (B:=B) (M:=M) (nextM:=nextM) (field:=field) (metaBits:=metaBits) (calendar:=calendar) (paid:=paid)
    (rc:=rc) (E:=E) (stencil:=stencil) (source:=source) (base:=base) (split:=split) (hubWidth:=hubWidth)
    (ports:=ports) (oldId:=oldId) (oldHub:=oldHub) (fee:=fee) (total:=total) (portPitch:=portPitch)
    (groupDigits:=groupDigits) (batches:=batches) (factor:=factor) (primitive:=primitive) (page:=page)
    (space:=space) (mem:=mem) (directory:=directory) (actorBank:=actorBank) (before:=before) (safe:=safe)
    (x:=x) (levels:=levels) (unit:=unit) (recorded:=recorded) (hdr:=hdr) (μ:=μ) (won:=won) (packet:=packet)
    (level:=level) (one:=one) (mass:=mass) (codes:=codes) (active:=active) (quotaPos:=quotaPos)
    (degreePos:=degreePos) (depths:=depths) (precision:=precision) (depthFit:=depthFit) (capFit:=capFit)
    (elapsed:=elapsed) (sorted:=sorted) (baseRoom:=baseRoom) (dimension:=dimension) (socketRoom:=socketRoom)
    (heightRoom:=heightRoom) (portRoom:=portRoom) (lanes:=lanes) (physicalHosts:=physicalHosts)
    (extent:=extent) (counted:=counted) (owner:=owner) (chart:=chart) (addresses:=addresses)
    (priorDepths:=priorDepths) (range:=range) (observedDepth:=observedDepth) (common:=common)
    (shortDepth:=shortDepth) (low:=low) (rankRoom:=rankRoom) (area:=area) (rootsFit:=rootsFit)
    (rootsPacked:=rootsPacked) (rootEnd:=rootEnd) (kept:=kept) (actorFit:=actorFit) (actorSpan:=actorSpan)
    (occupied:=occupied) (chunkRoom:=chunkRoom) (keyRoom:=keyRoom) (idFit:=idFit) (idRoom:=idRoom)
    (hostWords:=hostWords) (donorRoom:=donorRoom) (romRoom:=romRoom) (endRoom:=endRoom)
    (packedMarker:=packedMarker) (wordPositive:=wordPositive) (packedDonor:=packedDonor)
    (boardWidth:=boardWidth) (shapeWidth:=shapeWidth) (markerWidth:=markerWidth) (room:=room) (hubFit:=hubFit)
    (hubSpan:=hubSpan) (hubRead:=hubRead) (width:=width) (trunkRoom:=trunkRoom) (degreeWord:=degreeWord)
    (capWord:=capWord) (alphabet:=alphabet) (wordAlphabet:=wordAlphabet)).1

/-- Original calendar prefix reads at the same actor entry used by the priced trunk. -/
theorem calendar_trunk_prepared :
    ActorTrunkReads B input.valid.host phys floor scene safe initial := by
  exact (calendar_headers_and_registers
    (B:=B) (M:=M) (nextM:=nextM) (field:=field) (metaBits:=metaBits) (calendar:=calendar) (paid:=paid)
    (rc:=rc) (E:=E) (stencil:=stencil) (source:=source) (base:=base) (split:=split) (hubWidth:=hubWidth)
    (ports:=ports) (oldId:=oldId) (oldHub:=oldHub) (fee:=fee) (total:=total) (portPitch:=portPitch)
    (groupDigits:=groupDigits) (batches:=batches) (factor:=factor) (primitive:=primitive) (page:=page)
    (space:=space) (mem:=mem) (directory:=directory) (actorBank:=actorBank) (before:=before) (safe:=safe)
    (x:=x) (levels:=levels) (unit:=unit) (recorded:=recorded) (hdr:=hdr) (μ:=μ) (won:=won) (packet:=packet)
    (level:=level) (one:=one) (mass:=mass) (codes:=codes) (active:=active) (quotaPos:=quotaPos)
    (degreePos:=degreePos) (depths:=depths) (precision:=precision) (depthFit:=depthFit) (capFit:=capFit)
    (elapsed:=elapsed) (sorted:=sorted) (baseRoom:=baseRoom) (dimension:=dimension) (socketRoom:=socketRoom)
    (heightRoom:=heightRoom) (portRoom:=portRoom) (lanes:=lanes) (physicalHosts:=physicalHosts)
    (extent:=extent) (counted:=counted) (owner:=owner) (chart:=chart) (addresses:=addresses)
    (priorDepths:=priorDepths) (range:=range) (observedDepth:=observedDepth) (common:=common)
    (shortDepth:=shortDepth) (low:=low) (rankRoom:=rankRoom) (area:=area) (rootsFit:=rootsFit)
    (rootsPacked:=rootsPacked) (rootEnd:=rootEnd) (kept:=kept) (actorFit:=actorFit) (actorSpan:=actorSpan)
    (occupied:=occupied) (chunkRoom:=chunkRoom) (keyRoom:=keyRoom) (idFit:=idFit) (idRoom:=idRoom)
    (hostWords:=hostWords) (donorRoom:=donorRoom) (romRoom:=romRoom) (endRoom:=endRoom)
    (packedMarker:=packedMarker) (wordPositive:=wordPositive) (packedDonor:=packedDonor)
    (boardWidth:=boardWidth) (shapeWidth:=shapeWidth) (markerWidth:=markerWidth) (room:=room) (hubFit:=hubFit)
    (hubSpan:=hubSpan) (hubRead:=hubRead) (width:=width) (trunkRoom:=trunkRoom) (degreeWord:=degreeWord)
    (capWord:=capWord) (alphabet:=alphabet) (wordAlphabet:=wordAlphabet)).2

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
