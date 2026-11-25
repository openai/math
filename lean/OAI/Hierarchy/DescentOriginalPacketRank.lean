import OAI.Hierarchy.DescentOriginalPacketTrunk
import OAI.Hierarchy.DescentOriginalPacketMeta
import OAI.Hierarchy.DescentOriginalCapturedRanks
import OAI.Hierarchy.DescentOriginalStemFields
import OAI.Hierarchy.DescentOriginalStemPostedRun
import OAI.Hierarchy.DescentStemPublishedCoordinates

namespace OAI
/-! # Native rank and signed-window inputs obtained from one selected root packet -/
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
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wireBound hist : ℕ}
    {input : Reached W G q ε S k i z D wireBound hist} {ctl : ResetRates G S k D n h C f g cut tail}
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

open DescentResetCandidatePair DescentSortedRoster
local notation "observations" hdr:arg => calendar_sender_values B M field rc book space mem
  (calendar_sender_matrix B M field rc book space mem hdr x)
local notation "sectors" => DescentResetFieldAssembler.CandidateSheet.index (stemsCount B) (contactCount B) (privateCount B)
local notation "directoryRaster" => (Z).rawHostRank T tall
local notation "oldChart" key:arg => (⟨key,(Z).sparseActor T tall,vals⟩ :
  PriorPeerWords B H (phys).privateBits (field+2))
local notation "captureChart" cal:arg hdr:arg key:arg near:arg => measured_menu B M nextM calendar I cal pad
  (priorAtWidth B (calendar_private_width B M nextM field metaBits calendar paid) (oldChart key))
  (observations hdr) raw near
local notation "compactRaster" bound:arg => rackOf B (((Z).denseHostRank T tall).trans (Fin.castLEEmb bound))
open DescentResetNewActorDirectory DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentResetRankedWindows DescentResetCandidatePair DescentPackedZip DescentResetFieldAssembler
open DescentResetOriginalSlots
open DescentResetPublicParentWord
open DescentContactDonorSelection DescentParallelBase
section OriginalReceipt
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
    (ok : I.Ready)
    (grid : dir₀=dir) (front : (V₀).front=phys) (back : HEq I.earlier original₀)
    (ss : (V₀).sheets=sheets) (bound : Fintype.card B.next.V≤H₁)
    (newHosts : H₁≤2^bw) (dirRoom : (dir).endAddress<2^bw)
    (right : (CA).endAddress≤(phys).trunkEnd floor)
    (remote : (good).marker ((phys).trunkEnd floor)+H*chunks J M<2^bw)
    (items : M*max (field*(signedSlots+1)) field≤bw/2)
    (hubFit : oldHub.Fits bw directory) (hubSpan : H ≤ oldHub.size)
    (hubRead : ∀v : input.V,before (oldHub.base+(input.vertex v).val)=((input.placement.hub v).toNat : Word bw))
    (width : (metaBits*7)*nextM ≤ bw) (trunkRoom : (phys).trunkEnd floor < 2^bw)
    (degreeWord : B.next.placement.degree+1<2^metaBits) (capWord : B.next.placement.cap<2^metaBits)
    (alphabet : 5≤2^metaBits) (wordAlphabet : 5≤2^bw)
    (geo : PhysicalReset.DateInputs.SheetGeometry I)
    (hx : (V₀).receiver.blocks=2^k) (hs : I.sectors.stems=stemsCount B)
    (hc : I.sectors.contacts=contactCount B) (hp : I.sectors.privates=privateCount B)
    (oldFits : I.earlier.oldRoster.Fits bw directory) (oldSize : H*deg≤I.earlier.oldRoster.size)
    (oldRead : ∀a j,before (I.earlier.oldRoster.base+(a.val*deg+j.val))=
      (target (hostRotor idt (hostRoster (A) ((idt).trans Fin.valEmbedding)) a j):Word bw))
    (pageAddr : ∀s root,I.earlier.pages s root=rc.privatePageBank book s (chartTicket B M nextM calendar cal root))
    (dateEnd : (good).endAddress ((phys).trunkEnd floor)<2^bw)
    (joints : shelf*2^Nat.clog 2 (deg+2)≤2^metaBits)
    (lanePositive : 0<I.masked.lanes)
    (rankFit : I.masked.lanes*max (I.masked.field*5) I.masked.field≤bw/2)
    (maskFit : I.masked.lanes*max (I.masked.field*9) (I.masked.field*7)≤bw/2)
    (shape : NumberGeometry B I) (scalar : I.OriginalScalarLayout) (wire : I.DonorWiring)
    (stem : PostedStemGeometry B date) (basis : PostedStemBasis B I initial)
    (hosts : (V₀).receiver.hosts=H₁) (groups : (V₀).receiver.groups=S.groupCount (i+1))
    (sameGroups : (V₀).sheets.groups=S.groupCount (i+1))
    (sameLanes : (V₀).receiver.lanes=(V₀).sheets.lanes)
include B M nextM calendar paid rc E stencil source base split hubWidth ports oldId oldHub fee total portPitch
  groupDigits batches factor primitive page space mem directory actorBank before safe x levels unit I
  recorded hdr μ won packet level one mass codes active quotaPos degreePos depths precision depthFit capFit
  elapsed sorted baseRoom dimension socketRoom heightRoom portRoom lanes physicalHosts extent counted owner
  chart addresses priorDepths range observedDepth common shortDepth low rankRoom area rootsFit rootsPacked
  rootEnd kept actorFit actorSpan occupied chunkRoom keyRoom idFit idRoom hostWords donorRoom romRoom endRoom
  packedMarker wordPositive packedDonor boardWidth shapeWidth markerWidth room maxHost cal ok grid front back ss
  bound newHosts dirRoom right remote items hubFit hubSpan hubRead width trunkRoom degreeWord capWord alphabet
  wordAlphabet geo hx hs hc hp oldFits oldSize oldRead pageAddr dateEnd joints lanePositive rankFit maskFit
  shape scalar wire stem basis hosts groups sameGroups sameLanes

theorem original_packet_rank_controls_aux :
    ActorTrunkReads B input.valid.host (V₀).front start₀ ((V₀).issuedScene area₀ I.earlier) I.sceneFits initial ∧
    ∃ R : I.MeasuredChannels (Fintype.card B.next.V),PhysicalReset.DateInputs.CaptureRoom R initial ∧ CapturedSelf B I R ∧
      (∀v,present (selfPeers (renumberPeer cal.peerSlots R.near)) (directoryRaster v)=
        (insert v ((Z).emittedNear T v)).map directoryRaster) ∧
      (∀v,present (renumberPeer cal.peerSlots R.near) (directoryRaster v)=((Z).emittedNear T v).map directoryRaster) ∧
      Nonempty (RankSources B (b:=(V₀).sheets.metaBits) (t:=originalBits D k n Ht cap (programCount ctl.board Ht) g)
        (M:=(V₀).sheets.lanes) (compactRaster bound) ((V₀).rankPorts area₀)
        (sheetHeader B ((V₀).sheetsStart area₀) I.sectors.pageBits)
        (sheetOriginal B ((V₀).sheetsStart area₀) I.sectors.pageBits)
        (((V₀).rankPortPhase area₀ bw).image (I.before_ports ok initial))):=by
  constructor
  · exact original_packet_trunk
      (B:=B) (M:=M) (nextM:=nextM) (calendar:=calendar) (paid:=paid) (rc:=rc) (E:=E) (stencil:=stencil)
      (source:=source) (base:=base) (split:=split) (hubWidth:=hubWidth) (ports:=ports) (oldId:=oldId)
      (oldHub:=oldHub) (fee:=fee) (total:=total) (portPitch:=portPitch) (groupDigits:=groupDigits)
      (batches:=batches) (factor:=factor) (primitive:=primitive) (page:=page) (space:=space) (mem:=mem)
      (directory:=directory) (actorBank:=actorBank) (before:=before) (safe:=safe) (x:=x) (levels:=levels)
      (unit:=unit) (recorded:=recorded) (hdr:=hdr) (μ:=μ) (won:=won) (packet:=packet) (level:=level) (one:=one)
      (mass:=mass) (codes:=codes) (active:=active) (quotaPos:=quotaPos) (degreePos:=degreePos) (depths:=depths)
      (precision:=precision) (depthFit:=depthFit) (capFit:=capFit) (elapsed:=elapsed) (sorted:=sorted)
      (baseRoom:=baseRoom) (dimension:=dimension) (socketRoom:=socketRoom) (heightRoom:=heightRoom)
      (portRoom:=portRoom) (lanes:=lanes) (physicalHosts:=physicalHosts) (extent:=extent) (counted:=counted)
      (owner:=owner) (chart:=chart) (addresses:=addresses) (priorDepths:=priorDepths) (range:=range)
      (observedDepth:=observedDepth) (common:=common) (shortDepth:=shortDepth) (low:=low) (rankRoom:=rankRoom)
      (area:=area) (rootsFit:=rootsFit) (rootsPacked:=rootsPacked) (rootEnd:=rootEnd) (kept:=kept)
      (actorFit:=actorFit) (actorSpan:=actorSpan) (occupied:=occupied) (chunkRoom:=chunkRoom) (keyRoom:=keyRoom)
      (idFit:=idFit) (idRoom:=idRoom) (hostWords:=hostWords) (donorRoom:=donorRoom) (romRoom:=romRoom)
      (endRoom:=endRoom) (packedMarker:=packedMarker) (wordPositive:=wordPositive) (packedDonor:=packedDonor)
      (boardWidth:=boardWidth) (shapeWidth:=shapeWidth) (markerWidth:=markerWidth) (room:=room) (hubFit:=hubFit)
      (hubSpan:=hubSpan) (hubRead:=hubRead) (width:=width) (trunkRoom:=trunkRoom) (degreeWord:=degreeWord)
      (capWord:=capWord) (alphabet:=alphabet) (wordAlphabet:=wordAlphabet) (I:=I) (grid:=grid) (front:=front)
      (back:=back)
  ·
    have «meta»:=original_packet_meta
      (B:=B) (M:=M) (nextM:=nextM) (calendar:=calendar) (paid:=paid)
      (rc:=rc) (E:=E) (stencil:=stencil) (source:=source) (base:=base)
      (split:=split) (hubWidth:=hubWidth) (ports:=ports) (oldId:=oldId) (oldHub:=oldHub)
      (fee:=fee) (total:=total) (portPitch:=portPitch) (groupDigits:=groupDigits) (batches:=batches)
      (factor:=factor) (primitive:=primitive) (page:=page) (space:=space) (mem:=mem)
      (directory:=directory) (actorBank:=actorBank) (before:=before) (safe:=safe) (x:=x)
      (levels:=levels) (unit:=unit) (recorded:=recorded) (hdr:=hdr) (μ:=μ)
      (won:=won) (packet:=packet) (level:=level) (one:=one) (mass:=mass)
      (codes:=codes) (active:=active) (quotaPos:=quotaPos) (degreePos:=degreePos) (depths:=depths)
      (precision:=precision) (depthFit:=depthFit) (capFit:=capFit) (elapsed:=elapsed) (sorted:=sorted)
      (baseRoom:=baseRoom) (dimension:=dimension) (socketRoom:=socketRoom) (heightRoom:=heightRoom) (portRoom:=portRoom)
      (lanes:=lanes) (physicalHosts:=physicalHosts) (extent:=extent) (counted:=counted) (owner:=owner)
      (chart:=chart) (addresses:=addresses) (priorDepths:=priorDepths) (range:=range) (observedDepth:=observedDepth)
      (common:=common) (shortDepth:=shortDepth) (low:=low) (rankRoom:=rankRoom) (area:=area)
      (rootsFit:=rootsFit) (rootsPacked:=rootsPacked) (rootEnd:=rootEnd) (kept:=kept) (actorFit:=actorFit)
      (actorSpan:=actorSpan) (occupied:=occupied) (chunkRoom:=chunkRoom) (keyRoom:=keyRoom) (idFit:=idFit)
      (idRoom:=idRoom) (hostWords:=hostWords) (donorRoom:=donorRoom) (romRoom:=romRoom) (endRoom:=endRoom)
      (packedMarker:=packedMarker) (wordPositive:=wordPositive) (packedDonor:=packedDonor) (boardWidth:=boardWidth) (shapeWidth:=shapeWidth)
      (markerWidth:=markerWidth) (room:=room) (maxHost:=maxHost) (cal:=cal) (ok:=ok)
      (grid:=grid) (front:=front) (back:=back) (ss:=ss) (bound:=bound)
      (_newHosts:=newHosts) (dirRoom:=dirRoom) (right:=right) (remote:=remote) (items:=items)
      (hubFit:=hubFit) (hubSpan:=hubSpan) (hubRead:=hubRead) (width:=width) (trunkRoom:=trunkRoom)
      (degreeWord:=degreeWord) (capWord:=capWord) (alphabet:=alphabet) (wordAlphabet:=wordAlphabet) (geo:=geo)
      (hx:=hx) (hs:=hs) (hc:=hc) (hp:=hp) (oldFits:=oldFits)
      (oldSize:=oldSize) (oldRead:=oldRead) (pageAddr:=pageAddr) (dateEnd:=dateEnd) (joints:=joints)
      (lanePositive:=lanePositive) (rankFit:=rankFit) (maskFit:=maskFit)
    have donors:=original_packet_donors
      (B:=B) (M:=M) (nextM:=nextM) (calendar:=calendar) (paid:=paid)
      (rc:=rc) (E:=E) (stencil:=stencil) (source:=source) (base:=base)
      (split:=split) (hubWidth:=hubWidth) (ports:=ports) (oldId:=oldId) (oldHub:=oldHub)
      (fee:=fee) (total:=total) (portPitch:=portPitch) (groupDigits:=groupDigits) (batches:=batches)
      (factor:=factor) (primitive:=primitive) (page:=page) (space:=space) (mem:=mem)
      (directory:=directory) (actorBank:=actorBank) (before:=before) (safe:=safe) (x:=x)
      (levels:=levels) (unit:=unit) (recorded:=recorded) (hdr:=hdr) (μ:=μ)
      (won:=won) (packet:=packet) (level:=level) (one:=one) (mass:=mass)
      (codes:=codes) (active:=active) (quotaPos:=quotaPos) (degreePos:=degreePos) (depths:=depths)
      (precision:=precision) (depthFit:=depthFit) (capFit:=capFit) (elapsed:=elapsed) (sorted:=sorted)
      (baseRoom:=baseRoom) (dimension:=dimension) (socketRoom:=socketRoom) (heightRoom:=heightRoom) (portRoom:=portRoom)
      (lanes:=lanes) (physicalHosts:=physicalHosts) (extent:=extent) (counted:=counted) (owner:=owner)
      (chart:=chart) (addresses:=addresses) (priorDepths:=priorDepths) (range:=range) (observedDepth:=observedDepth)
      (common:=common) (shortDepth:=shortDepth) (low:=low) (rankRoom:=rankRoom) (area:=area)
      (rootsFit:=rootsFit) (rootsPacked:=rootsPacked) (rootEnd:=rootEnd) (kept:=kept) (actorFit:=actorFit)
      (actorSpan:=actorSpan) (occupied:=occupied) (chunkRoom:=chunkRoom) (keyRoom:=keyRoom) (idFit:=idFit)
      (idRoom:=idRoom) (hostWords:=hostWords) (donorRoom:=donorRoom) (romRoom:=romRoom) (endRoom:=endRoom)
      (packedMarker:=packedMarker) (wordPositive:=wordPositive) (packedDonor:=packedDonor) (boardWidth:=boardWidth) (shapeWidth:=shapeWidth)
      (markerWidth:=markerWidth) (room:=room) (maxHost:=maxHost) (cal:=cal) (ok:=ok)
      (grid:=grid) (front:=front) (back:=back) (ss:=ss) (bound:=bound)
      (newHosts:=newHosts) (dirRoom:=dirRoom) (right:=right) (remote:=remote) (items:=items)
      (registered:=shape) (goodWire:=wire)
    have signed:=calendar_original_stem_published
      (B:=B) (M:=M) (nextM:=nextM) («field»:=field) («metaBits»:=metaBits)
      (calendar:=calendar) (paid:=paid) (rc:=rc) (E:=E) (stencil:=stencil)
      (source:=source) (base:=base) (split:=split) (hubWidth:=hubWidth) (ports:=ports)
      (oldId:=oldId) (oldHub:=oldHub) (fee:=fee) (total:=total) (portPitch:=portPitch)
      (groupDigits:=groupDigits) (batches:=batches) (factor:=factor) (primitive:=primitive) (page:=page)
      (space:=space) (mem:=mem) (directory:=directory) (actorBank:=actorBank) (before:=before)
      (safe:=safe) (x:=x) (levels:=levels) (unit:=unit) (recorded:=recorded)
      (hdr:=hdr) (μ:=μ) (won:=won) (packet:=packet) (level:=level)
      (one:=one) (mass:=mass) (codes:=codes) (active:=active) (quotaPos:=quotaPos)
      (degreePos:=degreePos) (depths:=depths) (precision:=precision) (depthFit:=depthFit) (capFit:=capFit)
      (elapsed:=elapsed) (sorted:=sorted) (baseRoom:=baseRoom) (dimension:=dimension) (socketRoom:=socketRoom)
      (heightRoom:=heightRoom) (portRoom:=portRoom) (lanes:=lanes) (physicalHosts:=physicalHosts) (extent:=extent)
      (counted:=counted) (owner:=owner) (chart:=chart) (addresses:=addresses) (priorDepths:=priorDepths)
      (range:=range) (observedDepth:=observedDepth) (common:=common) (shortDepth:=shortDepth) (low:=low)
      (rankRoom:=rankRoom) (area:=area) (rootsFit:=rootsFit) (rootsPacked:=rootsPacked) (rootEnd:=rootEnd)
      (kept:=kept) (actorFit:=actorFit) (actorSpan:=actorSpan) (occupied:=occupied) (chunkRoom:=chunkRoom)
      (keyRoom:=keyRoom) (idFit:=idFit) (idRoom:=idRoom) (hostWords:=hostWords) (donorRoom:=donorRoom)
      (romRoom:=romRoom) (endRoom:=endRoom) (packedMarker:=packedMarker) (wordPositive:=wordPositive) (packedDonor:=packedDonor)
      (boardWidth:=boardWidth) (shapeWidth:=shapeWidth) (markerWidth:=markerWidth) (room:=room) (hubFit:=hubFit)
      (hubSpan:=hubSpan) (hubRead:=hubRead) (width:=width) (trunkRoom:=trunkRoom)
    have since : start₀=floor:=congrArg DescentResetNewActorDirectory.Layout.endAddress grid
    have earlier : HEq I.earlier original:=back.trans (by rw [since])
    obtain ⟨hostEq,laneEq,signedEq,digitEq⟩:=named_stem_dimensions (ctl:=ctl) (date:=date) nextM boundCap ss
    have published:=named_stem_at_directory B I dir grid front original earlier safe hostEq laneEq signedEq digitEq initial signed
    have wide : M≤bw:=(Nat.le_mul_of_pos_right M ((by omega : 0<field*8).trans_le (Nat.le_max_left ..))).trans
      (packedMarker.trans (Nat.div_le_self ..))
    obtain ⟨⟨keys,near,held,four,three⟩,words⟩:=«meta»
    let prior:=priorAtWidth B (calendar_private_width B M nextM field metaBits calendar paid) (oldChart keys)
    have clipped : Fintype.card B.next.V≤I.masked.hosts:=held.used
    have fieldReads:=original_stem_fields B M nextM calendar I cal pad prior (observations hdr) raw near
      initial held ok clipped stem basis published
    exact original_captured_ranks_aux (B:=B) (oldBatch:=M) (batch:=nextM) (calendar:=calendar)
      (paid:=paid) (I:=I) (cal:=cal) («pad»:=pad) (prior:=prior) (xs:=observations hdr) («raw»:=raw)
      (floor₀:=directory) («src»:=actorBank) (before:=before) (bound:=bound) (hx:=hx) (hs:=hs) (hc:=hc) (hp:=hp)
      ok sorted elapsed recorded hosts groups sameGroups sameLanes grid lanes wide occupied actorFit actorSpan
      chunkRoom dirRoom ⟨⟨near,held,four,three⟩,words⟩ shape scalar fieldReads donors

theorem original_packet_rank_and_trunk :
    ActorTrunkReads B input.valid.host (V₀).front start₀ ((V₀).issuedScene area₀ I.earlier) I.sceneFits initial ∧
    ∃ R : I.MeasuredChannels (Fintype.card B.next.V),PhysicalReset.DateInputs.CaptureRoom R initial ∧
      (∀v,present (selfPeers (renumberPeer cal.peerSlots R.near)) (directoryRaster v)=
        (insert v ((Z).emittedNear T v)).map directoryRaster) ∧
      (∀v,present (renumberPeer cal.peerSlots R.near) (directoryRaster v)=((Z).emittedNear T v).map directoryRaster) ∧
      Nonempty (RankSources B (b:=(V₀).sheets.metaBits) (t:=originalBits D k n Ht cap (programCount ctl.board Ht) g)
        (M:=(V₀).sheets.lanes) (compactRaster bound) ((V₀).rankPorts area₀)
        (sheetHeader B ((V₀).sheetsStart area₀) I.sectors.pageBits)
        (sheetOriginal B ((V₀).sheetsStart area₀) I.sectors.pageBits)
        (((V₀).rankPortPhase area₀ bw).image (I.before_ports ok initial))):=by
  obtain ⟨trunk,R,seen,_,four,three,ranks⟩:=original_packet_rank_controls_aux
    (B:=B) (M:=M) (nextM:=nextM) (calendar:=calendar) (paid:=paid) (rc:=rc) (E:=E) (stencil:=stencil)
    (source:=source) (base:=base) (split:=split) (hubWidth:=hubWidth) (ports:=ports) (oldId:=oldId)
    (oldHub:=oldHub) (fee:=fee) (total:=total) (portPitch:=portPitch) (groupDigits:=groupDigits)
    (batches:=batches) (factor:=factor) (primitive:=primitive) (page:=page) (space:=space) (mem:=mem)
    (directory:=directory) (actorBank:=actorBank) (before:=before) (safe:=safe) (x:=x) (levels:=levels)
    (unit:=unit) (I:=I) (recorded:=recorded) (hdr:=hdr) (μ:=μ) (won:=won) (packet:=packet) (level:=level)
    (one:=one) (mass:=mass) (codes:=codes) (active:=active) (quotaPos:=quotaPos) (degreePos:=degreePos)
    (depths:=depths) (precision:=precision) (depthFit:=depthFit) (capFit:=capFit) (elapsed:=elapsed)
    (sorted:=sorted) (baseRoom:=baseRoom) (dimension:=dimension) (socketRoom:=socketRoom)
    (heightRoom:=heightRoom) (portRoom:=portRoom) (lanes:=lanes) (physicalHosts:=physicalHosts) (extent:=extent)
    (counted:=counted) (owner:=owner) (chart:=chart) (addresses:=addresses) (priorDepths:=priorDepths)
    (range:=range) (observedDepth:=observedDepth) (common:=common) (shortDepth:=shortDepth) (low:=low)
    (rankRoom:=rankRoom) (area:=area) (rootsFit:=rootsFit) (rootsPacked:=rootsPacked) (rootEnd:=rootEnd)
    (kept:=kept) (actorFit:=actorFit) (actorSpan:=actorSpan) (occupied:=occupied) (chunkRoom:=chunkRoom)
    (keyRoom:=keyRoom) (idFit:=idFit) (idRoom:=idRoom) (hostWords:=hostWords) (donorRoom:=donorRoom)
    (romRoom:=romRoom) (endRoom:=endRoom) (packedMarker:=packedMarker) (wordPositive:=wordPositive)
    (packedDonor:=packedDonor) (boardWidth:=boardWidth) (shapeWidth:=shapeWidth) (markerWidth:=markerWidth)
    (room:=room) (maxHost:=maxHost) (cal:=cal) (ok:=ok) (grid:=grid) (front:=front) (back:=back) (ss:=ss)
    (bound:=bound) (newHosts:=newHosts) (dirRoom:=dirRoom) (right:=right) (remote:=remote) (items:=items)
    (hubFit:=hubFit) (hubSpan:=hubSpan) (hubRead:=hubRead) (width:=width) (trunkRoom:=trunkRoom)
    (degreeWord:=degreeWord) (capWord:=capWord) (alphabet:=alphabet) (wordAlphabet:=wordAlphabet) (geo:=geo)
    (hx:=hx) (hs:=hs) (hc:=hc) (hp:=hp) (oldFits:=oldFits) (oldSize:=oldSize) (oldRead:=oldRead)
    (pageAddr:=pageAddr) (dateEnd:=dateEnd) (joints:=joints) (lanePositive:=lanePositive) (rankFit:=rankFit)
    (maskFit:=maskFit) (shape:=shape) (scalar:=scalar) (wire:=wire) (stem:=stem) (basis:=basis) (hosts:=hosts)
    (groups:=groups) (sameGroups:=sameGroups) (sameLanes:=sameLanes)
  exact ⟨trunk,R,seen,four,three,ranks⟩

theorem original_packet_rank :
    ∃ R : I.MeasuredChannels (Fintype.card B.next.V),PhysicalReset.DateInputs.CaptureRoom R initial ∧
      (∀v,present (selfPeers (renumberPeer cal.peerSlots R.near)) (directoryRaster v)=
        (insert v ((Z).emittedNear T v)).map directoryRaster) ∧
      (∀v,present (renumberPeer cal.peerSlots R.near) (directoryRaster v)=((Z).emittedNear T v).map directoryRaster) ∧
      Nonempty (RankSources B (b:=(V₀).sheets.metaBits) (t:=originalBits D k n Ht cap (programCount ctl.board Ht) g)
        (M:=(V₀).sheets.lanes) (compactRaster bound) ((V₀).rankPorts area₀)
        (sheetHeader B ((V₀).sheetsStart area₀) I.sectors.pageBits)
        (sheetOriginal B ((V₀).sheetsStart area₀) I.sectors.pageBits)
        (((V₀).rankPortPhase area₀ bw).image (I.before_ports ok initial))):=by
  exact (original_packet_rank_and_trunk
    (B:=B) (M:=M) (nextM:=nextM) (calendar:=calendar) (paid:=paid) (rc:=rc) (E:=E) (stencil:=stencil)
    (source:=source) (base:=base) (split:=split) (hubWidth:=hubWidth) (ports:=ports) (oldId:=oldId)
    (oldHub:=oldHub) (fee:=fee) (total:=total) (portPitch:=portPitch) (groupDigits:=groupDigits)
    (batches:=batches) (factor:=factor) (primitive:=primitive) (page:=page) (space:=space) (mem:=mem)
    (directory:=directory) (actorBank:=actorBank) (before:=before) (safe:=safe) (x:=x) (levels:=levels)
    (unit:=unit) (I:=I) (recorded:=recorded) (hdr:=hdr) (μ:=μ) (won:=won) (packet:=packet) (level:=level)
    (one:=one) (mass:=mass) (codes:=codes) (active:=active) (quotaPos:=quotaPos) (degreePos:=degreePos)
    (depths:=depths) (precision:=precision) (depthFit:=depthFit) (capFit:=capFit) (elapsed:=elapsed)
    (sorted:=sorted) (baseRoom:=baseRoom) (dimension:=dimension) (socketRoom:=socketRoom)
    (heightRoom:=heightRoom) (portRoom:=portRoom) (lanes:=lanes) (physicalHosts:=physicalHosts) (extent:=extent)
    (counted:=counted) (owner:=owner) (chart:=chart) (addresses:=addresses) (priorDepths:=priorDepths)
    (range:=range) (observedDepth:=observedDepth) (common:=common) (shortDepth:=shortDepth) (low:=low)
    (rankRoom:=rankRoom) (area:=area) (rootsFit:=rootsFit) (rootsPacked:=rootsPacked) (rootEnd:=rootEnd)
    (kept:=kept) (actorFit:=actorFit) (actorSpan:=actorSpan) (occupied:=occupied) (chunkRoom:=chunkRoom)
    (keyRoom:=keyRoom) (idFit:=idFit) (idRoom:=idRoom) (hostWords:=hostWords) (donorRoom:=donorRoom)
    (romRoom:=romRoom) (endRoom:=endRoom) (packedMarker:=packedMarker) (wordPositive:=wordPositive)
    (packedDonor:=packedDonor) (boardWidth:=boardWidth) (shapeWidth:=shapeWidth) (markerWidth:=markerWidth)
    (room:=room) (maxHost:=maxHost) (cal:=cal) (ok:=ok) (grid:=grid) (front:=front) (back:=back) (ss:=ss)
    (bound:=bound) (newHosts:=newHosts) (dirRoom:=dirRoom) (right:=right) (remote:=remote) (items:=items)
    (hubFit:=hubFit) (hubSpan:=hubSpan) (hubRead:=hubRead) (width:=width) (trunkRoom:=trunkRoom)
    (degreeWord:=degreeWord) (capWord:=capWord) (alphabet:=alphabet) (wordAlphabet:=wordAlphabet) (geo:=geo)
    (hx:=hx) (hs:=hs) (hc:=hc) (hp:=hp) (oldFits:=oldFits) (oldSize:=oldSize) (oldRead:=oldRead)
    (pageAddr:=pageAddr) (dateEnd:=dateEnd) (joints:=joints) (lanePositive:=lanePositive) (rankFit:=rankFit)
    (maskFit:=maskFit) (shape:=shape) (scalar:=scalar) (wire:=wire) (stem:=stem) (basis:=basis) (hosts:=hosts)
    (groups:=groups) (sameGroups:=sameGroups) (sameLanes:=sameLanes)).2
end OriginalReceipt

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
