import OAI.Hierarchy.DescentStemCalendarRegister
import OAI.Hierarchy.DescentCalendarOriginalPeers
import OAI.Hierarchy.DescentPhysicalCalendarStem
import OAI.Hierarchy.DescentCalendarStemActorRegisters

namespace OAI
/-! # The seven stem fields read at the original chronological reset date -/
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

include unit

/-- Both observations use the same earlier actor directory, bitmap, signed
stencil rows and mounted peer before the trunk scan. -/
theorem calendar_original_stem_sources {nbits p : ℕ} (recorded : B.Recorded p)
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
    (hubFit : oldHub.Fits bw directory) (hubSpan : H ≤ oldHub.size)
    (hubRead : ∀v : input.V,before (oldHub.base+(input.vertex v).val)=((input.placement.hub v).toNat : Word bw))
    (width : (metaBits*7)*nextM ≤ bw) (trunkRoom : (phys).trunkEnd floor < 2^bw) :
    (((phys).received floor scene safe).Runs initial ∧
    (∀(x₀ : Fin (2^k)) side (slot : sourceSlot) (p : Row newH groups nextM),
      ((phys).received floor scene safe).image initial ((phys).stemOutput floor+
        (finProdFinEquiv (x₀,ordinal (side,slot))).val*(newH*chunks groups nextM)+(row newH groups nextM p).val)=
      ((data (fun r₀ g₀=>(originalTrunkRack B r₀).elim 0 (fun v=>DescentResetFieldAssembler.raw metaBits («meta» B ((g₀,v),x₀)
        (localOrigin B ((g₀,v),x₀) (stemIndex B side slot))))) p).val:Word bw)) ∧
    ((phys).trunkScene floor scene safe).Runs initial ∧
      ∀(x₀ : Fin (2^k)) (j : Fin (stemsCount B)),
        ((phys).stemOperand floor x₀.val j.val).Fits bw ((phys).trunkEnd floor) ∧
        DescentPackedZip.Source ((phys).stemOperand floor x₀.val j.val)
          (fun (h₀ : Fin newH) g₀=>DescentResetFieldAssembler.raw metaBits (actualMeta B (originalTrunkRack B) x₀ (stemShelf B j) h₀ g₀))
          nextM (((phys).trunkScene floor scene safe).image initial)) ∧
    ∃val : Fin (2^k)→Fin (stemsCount B)→Fin newH→Fin groups→Cell field,
      (∀x j,let term:=((phys).job (scene).stems).signedTerm ((phys).parentEnd floor) ((phys).parent floor).base x.val j.val
        term.Fits bw ((phys).mixed floor) ∧ Source term (val x j) nextM (((phys).trunkScene floor scene safe).image initial)) ∧
      ∀x j h₀ g₀ v,(originalTrunkRack B h₀)=some v→val x j h₀ g₀=(stemObservedChip B (originalTrunkRack B) x j h₀ g₀:Cell field) := by
  obtain ⟨⟨network,emitted,four,absence⟩,_⟩ := calendar_original_peers
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
  have early : floor < 2^bw := ((phys).floor_before floor scene safe).trans_lt
    (((phys).front_order floor).1.trans_lt (((phys).front_order floor).2.1.trans_lt safe.stems.final))
  obtain ⟨keyFits,keySpan,access,mounted,locals,tags,signed⟩ :=
    calendar_window_receipt B calendar paid rc book space mem src oldId oldHub directory actorBank before x
      rootEnd kept actorFit chunkRoom early area.remoteShape packet.mounted packet.sites packet.tagged packet.signed
  have positive : 0 < max (field*8) bits := (by omega : 0 < field*8).trans_le (Nat.le_max_left ..)
  have machine : M ≤ bw := (Nat.le_mul_of_pos_right M positive).trans (packedMarker.trans (Nat.div_le_self ..))
  have actor := calendar_stem_actor_registers B M directory actorBank oldHub before lanes machine occupied
    actorFit actorSpan chunkRoom early hubFit hubSpan hubRead
  have hubEq : (old).oldHub=oldHub := EarlierBanks.cast_hub input.branch (calendar_residual B) paid B.dimension originBanks
  have extent_eq : (phys).peer.hosts=pitch := congrArg (H*·) (calendar_palette B)
  have neighbor (j : Fin 3) (v : Fin pitch) :
      let p₀:=(phys).peer
      let pt:=(phys).peers floor
      Program.output pt H p₀.shapes D p₀.bits p₀.evidenceLanes p₀.evidenceGroups (scene).peers.old
        (scene).peers.test (scene).peers.src ((phys).prePeers floor scene safe initial)
        (p₀.rawPeers pt+j.val*p₀.hosts+v.val)=(target (network v j):Word bw) := by
    have h:=((phys).peer.three_word (scene).peers ((phys).peers floor)
      ((phys).prePeers floor scene safe initial) safe.peers j (v.cast extent_eq.symm)).symm
    refine h.trans ?_
    change (phys).preScalar floor scene safe initial
      ((phys).peer.rawPeers ((phys).peers floor) + j.val * (phys).peer.hosts + v.val) = _
    rw [extent_eq]
    exact emitted v j
  have words (v hi lo) : (stemValues v hi lo).val=x.stencil v hi lo := Fin.val_cast_of_lt (packet.short v hi lo)
  have hosts : (idt).trans Fin.valEmbedding = input.vertex.trans Fin.valEmbedding := by
    ext v
    rfl
  have complete:=calendar_stem B M nextM field metaBits ctl.bitsR calendar paid floor old
    (dir).flags (dir).count (dir).inverse safe initial x.word x.fits hdr.signedBits x.onWire
    stemValues x.peers x.marks (fun v hi lo=>by simpa only [words] using x.localRead v hi lo)
    x.peerRead (by intro v hi lo j; have mark := x.markRead v hi lo j; rw [B.order_eq, hosts] at mark; exact mark) keyFits keySpan access mounted
    (by simpa only [words] using locals) (by simpa only [words, Nat.cast_add, Nat.cast_one] using tags) signed network
    actor.counted actor.inverseRead actor.bitmap (by simpa only [hubEq] using actor.hubRead)
    actor.lowCount actor.lowInv actor.lowMask (by simpa only [hubEq] using actor.lowHub) neighbor
    actor.inverseSize (by simpa only [hubEq] using actor.hubSize) lanes width trunkRoom recorded four absence
  have signedWords:=calendar_signed B M nextM field metaBits ctl.bitsR calendar paid floor old
    (dir).flags (dir).count (dir).inverse safe initial x.word x.fits hdr.signedBits x.onWire
    stemValues x.peers x.marks (fun v hi lo=>by simpa only [words] using x.localRead v hi lo)
    x.peerRead (by intro v hi lo j; have mark := x.markRead v hi lo j; rw [B.order_eq, hosts] at mark; exact mark) keyFits keySpan access mounted
    (by simpa only [words] using locals) (by simpa only [words, Nat.cast_add, Nat.cast_one] using tags) signed network
    actor.counted actor.inverseRead actor.bitmap (by simpa only [hubEq] using actor.hubRead)
    actor.lowCount actor.lowInv actor.lowMask (by simpa only [hubEq] using actor.lowHub) neighbor
    actor.inverseSize (by simpa only [hubEq] using actor.hubSize) lanes width trunkRoom recorded four absence
  exact ⟨complete,signedWords⟩

/-- Evaluate the compact stem row on the actor directory produced from the incoming venue.
The raw neighbor ordinals and the signed donor keys use the same private root packet. -/
theorem calendar_original_stems {nbits p : ℕ} (recorded : B.Recorded p)
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
    (hubFit : oldHub.Fits bw directory) (hubSpan : H ≤ oldHub.size)
    (hubRead : ∀v : input.V,before (oldHub.base+(input.vertex v).val)=((input.placement.hub v).toNat : Word bw))
    (width : (metaBits*7)*nextM ≤ bw) (trunkRoom : (phys).trunkEnd floor < 2^bw) :
    ((phys).received floor scene safe).Runs initial ∧
    (∀(x₀ : Fin (2^k)) side (slot : sourceSlot) (p : Row newH groups nextM),
      ((phys).received floor scene safe).image initial ((phys).stemOutput floor+
        (finProdFinEquiv (x₀,ordinal (side,slot))).val*(newH*chunks groups nextM)+(row newH groups nextM p).val)=
      ((data (fun r₀ g₀=>(originalTrunkRack B r₀).elim 0 (fun v=>DescentResetFieldAssembler.raw metaBits («meta» B ((g₀,v),x₀)
        (localOrigin B ((g₀,v),x₀) (stemIndex B side slot))))) p).val:Word bw)) ∧
    ((phys).trunkScene floor scene safe).Runs initial ∧
      ∀(x₀ : Fin (2^k)) (j : Fin (stemsCount B)),
        ((phys).stemOperand floor x₀.val j.val).Fits bw ((phys).trunkEnd floor) ∧
        DescentPackedZip.Source ((phys).stemOperand floor x₀.val j.val)
          (fun (h₀ : Fin newH) g₀=>DescentResetFieldAssembler.raw metaBits (actualMeta B (originalTrunkRack B) x₀ (stemShelf B j) h₀ g₀))
          nextM (((phys).trunkScene floor scene safe).image initial) :=by
  have both:=calendar_original_stem_sources
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
  exact both.1

/-- The unmasked former signed chip on its original compressed actor and low coordinates. -/
theorem calendar_original_signed {nbits p : ℕ} (recorded : B.Recorded p)
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
    (hubFit : oldHub.Fits bw directory) (hubSpan : H ≤ oldHub.size)
    (hubRead : ∀v : input.V,before (oldHub.base+(input.vertex v).val)=((input.placement.hub v).toNat : Word bw))
    (width : (metaBits*7)*nextM ≤ bw) (trunkRoom : (phys).trunkEnd floor < 2^bw) :
    ∃val : Fin (2^k)→Fin (stemsCount B)→Fin newH→Fin groups→Cell field,
      (∀x j,let term:=((phys).job (scene).stems).signedTerm ((phys).parentEnd floor) ((phys).parent floor).base x.val j.val
        term.Fits bw ((phys).mixed floor) ∧ Source term (val x j) nextM (((phys).trunkScene floor scene safe).image initial)) ∧
      ∀x j h₀ g₀ v,(originalTrunkRack B h₀)=some v→val x j h₀ g₀=(stemObservedChip B (originalTrunkRack B) x j h₀ g₀:Cell field) :=by
  have both:=calendar_original_stem_sources
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
  exact both.2

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
