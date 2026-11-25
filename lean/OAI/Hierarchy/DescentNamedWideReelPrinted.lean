import OAI.Hierarchy.DescentTerminalRectangularAliases
import OAI.Hierarchy.DescentTerminalBoundaryPointer
import OAI.Hierarchy.DescentTerminalSocketOccupation
import OAI.Hierarchy.DescentNamedCableFields
import OAI.Hierarchy.DescentTerminalExteriorHeaderBudget
import OAI.Hierarchy.DescentTerminalAcquiredPorts
import OAI.Hierarchy.DescentTerminalPreflightReelFrame
import OAI.Hierarchy.DescentNamedWidePaidPrinted
import OAI.Hierarchy.DescentNamedWidePaidSource

namespace OAI
/-! # The paid terminal leaf on the actual native validation-finished reel image -/
namespace Hierarchy.DescentSixParty.SeedNamed
open CorrectionFrame
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphPositions DescentTerminalGraphVolume DescentTerminalCableOrder DescentKernelHistory
open DescentBundleHistory DescentPrimitivePalette DescentRotor DescentResetGates CorrectionBatch
open DescentTerminalBinReaddress DescentTerminalPorts Computability.BorderVNP.Crossing
open DescentTerminalEmitter DescentTerminalEmitter.Branch DescentTerminalChipRuntime
open DescentTerminalVertexFields DescentTerminalHeaderScatter DescentTerminalSiteShelves
open DescentTerminalScalarTransposes DescentTerminalDenseWindow DescentTerminalRecipeRows
open DescentTerminalScalarPadded DescentTerminalCompiledPrefix DescentEpochTagKeys
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 12288
set_option maxHeartbeats 1400000
set_option Elab.async false
set_option cleanup.letToHave false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin Branch.archive Branch.bundleShape

open Lean Elab Term in
local elab "observedApply% " fn:term:arg "[" args:term,* "]" : term => do
  let e ← elabTerm fn none
  return mkAppN e (← args.getElems.mapM fun arg => elabTerm arg none)

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W q piece : ℕ}
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0<(W*piece)) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
variable (c : ((Epochs.finish G _ _ ((normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten)).choose)).Choice)
local notation "b" => issued X G S ordinary reset branch positive room shorten c
local notation "world" => (last).state c
local notation "net" => (world).graph
local notation "s" => S.firstWidth G.b p
local notation "Z" => S.grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "U" => Label G s Z rot
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "nodeCap" => S.epochPower^S.localTokenExponent
local notation "venues" => S.groupCount S.length*2^k
local notation "palette" => Palette.relabel X G S ordinary reset branch positive room shorten c
local notation "sh" => Palette.leafShape X G S ordinary reset branch positive room shorten c
local notation "archive" => Branch.archive X G S b positive

variable {j rest : ℕ} (base : S.baseGroups=2^tail) (width : S.groupWidth k tail 0+k=j+(j+rest))
variable (age : 0<S.height) (wFit : NativeBranch.binLimit (k:=k) S ≤ W)
  (qFit : NativeBranch.localLimit G S ≤ q) (qh : 0<q)
local notation "ord" => Branch.leafOrder X G S b positive base width
local notation "seedOne" => (Nat.le_max_left 1 (max reset.bitsR (C*reset.bitsR)))

open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalExteriorPackets DescentTerminalPublicIdentity
open DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall DescentPackedProfileTape
open DescentSeedRoot DescentExteriorShelf DescentTerminalPrimitiveArena
local notation "E₀" => Fintype.card (Port P X.width)
local notation "H₀" => S.hostSize S.length
local notation "count₀" => E₀*2^(j+rest)
variable (template:DescentTerminalCompiledPrefix.Shape) (sitesPositive:0<(S.hostSize S.length)) (rawWords headerRows paidRows:ℕ)
local notation "cfg" => Branch.exteriorShape template E₀ j rest s rawWords headerRows H₀ sitesPositive
variable (pool : terminalPool X G S (W*piece) q W n h C f g ≤ ((Branch.exteriorShape template (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b (W*piece)) rawWords headerRows (S.hostSize S.length) sitesPositive)).terminal.pool)
    (raw : terminalRawRows X G S (W*piece) q n h C f g ≤ ((Branch.exteriorShape template (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b (W*piece)) rawWords headerRows (S.hostSize S.length) sitesPositive)).terminal.plane.rawRows)
local notation "leaf" => normalizedLeaf X G S ordinary reset branch positive room shorten c
  base width age wFit qFit qh cfg pool raw
local notation "groupsAt" => S.groupCount S.length
local notation "hostGraph" => (world).graph
local notation "sites" => (ord).site
local notation "arityCap" => Branch.leaf_arity X G S b positive base width qFit
local notation "box" => Branch.leaf_local_room X G S b positive base width
local notation "rowNames" => Branch.leaf_name X G S b positive base width
local notation "argNames" => Branch.leaf_arg X G S b positive base width
open DescentTerminalCompiledPrefix.AddressPlan DescentTerminalEmitter.Compact
open DescentTerminalLocalPortBook DescentTerminalSpanBook DescentTerminalBinPack
open DescentTerminalPreflightSpace ThreeFlat.RAM PhysicalProcedure

open DescentPackedEpochFold DescentExteriorMatrixUpdate DescentPackedSeed DescentSeedRoot
open ThreeFlat Routing Diagonal
variable {w K:ℕ} (payloadBits:ℕ) (fit:(S.firstWidth G.b (W*piece))<2^w)
local notation "chart" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
local notation "fmt" => Branch.geometryFormat G S k g p tail q R rot headerRows paidRows
local notation "pre" => Branch.preflightSpec X G S k g p tail ({fmt with binSize:=W}:Branch.PreflightFormat)
variable (begin_ rom : ℕ) (peer:Bank) (old:Fin ((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).scalar.blocks→Fin (2*((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).cap)→Bank)
    (org:ℕ) (homes:Bank) (other:AddressPlan.Input)
variable {arity groups stride oldTags:ℕ} (codec:DescentEpochTagKeys.Codec (Label G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) oldTags)
local notation "tagCount" => DescentBundleTagKeys.capacity oldTags arity groups p stride
local notation "V" => (⟨q,tagCount,cap,nodeCap,cap,p,groupsAt⟩:Home.Format)
local notation "pages₀" => (pre).scanPages org q
local notation "total" => (pages₀).total
local notation "modulo" => (pages₀).modulo
local notation "boundary" => (pages₀).boundaries
local notation "T" => (RouteSources.Tables.mk 4 venues (venues*NativeBranch.localLimit G S)
  (NativeBranch.localLimit G S) (Book.tokenBits (venues*NativeBranch.localLimit G S)) W q K)
local notation "B" => (pre).pageBits
local notation "grain" => p
local notation "codes" => DescentTerminalScalarHeader.range q tagCount cap nodeCap cap p venues
variable (lo packWidth : ℕ)
local notation "rawSize" => s
local notation "seed" => (chart).seed
local notation "clockCap" => G.C
local notation "steps" => (chart).layout
local notation "front" => end_ (lo+extent packWidth steps) clockCap packWidth+17*DescentExteriorShelf.span j rest s E₀
local notation "extra" => DescentTerminalPublicIdentity.total K W q piece codes rawWords count₀
local notation "publicBase" => front+DescentTerminalPaidBoot.total K W q piece codes rawWords
local notation "Full" => DescentTerminalFullPins.Candidate ((chart).Pin⊕Hidden E₀ j rest s) K W q piece rawWords
variable (all : (DescentTerminalFullPins.Candidate (((normalizedPackedChart X G S ordinary reset branch positive room shorten w fit)).Pin⊕Hidden (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b (W*piece))) K W q piece rawWords)→Bool)
local notation "paint" => all ∘ DescentTerminalFullPins.chip
local notation "past_" => all ∘ DescentTerminalFullPins.history ∘ Sum.inr
local notation "originalMatrix" => Branch.publicLayout X G S b positive base width
local notation "oldHost" => Branch.publicHost X G S b positive base width
local notation "power" => NativeBranch.copy_power S (radix:=ordinary.radix) base width
local notation "I_" => (pre).reachedInput begin_ rom q piece W K codes front peer old total modulo homes
                          boundary cfg V other T (pre).vertices B
local notation "R_" => (pre).channels begin_
local notation "start" => (pre).maskBase begin_
local notation "C_" => meter V R_ start
local notation "base_" => afterMeter V cfg R_ start
local notation "A_" => rowArena cfg I_ base_
local notation "X_" => (pre).controls begin_
local notation "J_" => (pre).chipInput begin_ rom q grain peer old total modulo homes boundary cfg other
local notation "portTokenBits" => Book.tokenBits (venues*NativeBranch.localLimit G S)
local notation "M" => venues*NativeBranch.localLimit G S

variable (head : ℕ) (short : ((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).vertices*DescentTerminalVertexFields.span (((⟨q,(DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).publicArity (((⟨q,(DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).roles (((⟨q,(DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).privateWords (((⟨q,(DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).nodes (((⟨q,(DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).addresses (((⟨q,(DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).piece≤(((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).pageBits))
local notation "literal" => ScalarLiterals.data q (V).roles (V).privateWords (V).nodes (V).addresses grain (pre).vertices W B
  (cfg).terminal.pool qh ((T).columns A_ (J_).sources) ((T).value (fun _ _=>0))
local notation "O_" => registers V cfg R_ start head
local notation "plan_" => AddressPlan.layout cfg I_ base_ O_
local notation "loaded" => input V cfg I_ R_ start head short literal
local notation "values" => portTable (G:=4) («V»:=(pre).vertices) («M»:=M) (A:=(pre).arguments) (a:=portTokenBits) q
local notation "expr" => Book.expression ((pre).parts begin_)
local notation "out_" => (pre).afterSiteControls begin_ q grain peer old total modulo homes boundary
local notation "afterCode" => (pre).afterSiteProgram begin_ q grain peer old total modulo homes boundary
local notation "afterTime" => (pre).afterSiteTime begin_ q grain peer old total modulo homes boundary



local notation "routerMem" => fun post:Memory w=>Suffix.events cfg plan_ (C_).layout ((A_).mount (loaded post))

local notation "rsite" => fun v => (((leaf).shape v).recipe positive).restricted
local notation "bookCode" => DescentBundleTagKeys.codec codec arity groups p stride
local notation "recipes" => DescentTerminalBundleRows.recipes ord rsite positive (leaf).birth (bookCode).store
local notation "ranks" => DescentTerminalChronologicalChip.charts (arity:=arity) (groups:=groups) (stride:=stride)
  hostGraph (leaf).home (leaf).native (leaf).external (leaf).nodes (leaf).ops
  (leaf).bit (leaf).shape positive (leaf).birth (leaf).hidden codec
local notation "hH" => fun i v => (DescentTerminalRestrictedRows.hidden_bound (leaf).bit (leaf).shape
  positive ((ord).node i v)).trans ((leaf).countsFit ((ord).node i v))
local notation "hN" => fun i v => (leaf).atoms ((ord).node i v)
local notation "hA" => fun i v u => (((leaf).shape ((ord).node i v)).recipe_refs positive u).symm ▸
  (leaf).refs ((ord).node i v) u

local notation "onBoard" mu:arg => Suffix.sockets cfg plan_ ((A_).mount (loaded mu))
local notation "nativeCandidate" mu => ((A_).mount (loaded mu))
local notation "memAt" mu:arg => DescentTerminalEmitter.issued (cfg).terminal (plan_).emit (plan_).directory
  (maskedMem (C_).layout (plan_).directory (S.hostSize S.length) (onBoard mu))

local notation "bookSeed" => (pre).reachedRoutes begin_ rom q piece W K codes front peer old total modulo homes boundary (cfg) V other T
local notation "emptyCode" => (DescentTerminalChronologicalBooks.empty q tagCount cap nodeCap cap p venues p).val
local notation "bankSet" => DescentTerminalChipBootWords.chipBanks (K:=K) (W:=W) (q:=q)
  («p»:=piece) codes (plan_).emit front emptyCode
local notation "meterAt" mu:arg => (A_).mount (loaded mu)
local notation "payloadOut" input:arg => packagePins X S.copies s (Branch.copyInput X s (power).symm input)

local notation "history_" => all ∘ DescentTerminalFullPins.history ∘ Sum.inl
local notation "accepted" => ∃c,(chart).read history_=some c
local notation "wall" => AddressPlan.takeOff (cfg) I_ base_
local notation "compact" => end_ (lo+extent packWidth steps) G.C packWidth
local notation "firstFree" => front+extra
local notation "dst" => finalAt firstFree lo packWidth steps
local notation "seedBase" => DescentWideSeedFlags.endInput X S.copies s payloadBits
local notation "seedRows" => DescentPackedSeed.rows X S.copies s payloadBits
local notation "B₀" => S.groupWidth k tail 0+k
variable (fence:ℕ) (count:ℕ→ℕ) (plan:Reel)
variable (primitive m:Memory w)
local notation "preflight" => out_ ((X_).after values expr m)
local notation "copied" => relocated j rest s E₀ compact wall preflight
local notation "kept" => plan.result j rest s E₀ B₀ S.length wall copied
local notation "post" => oldStateAt firstFree lo G.C packWidth (seedBase+seedRows) steps count history_ kept
variable (original:Port ((2^(j+(j+rest))*(S.firstWidth G.b (W*piece)))*P) (copiesWidth (2^(j+(j+rest))*(S.firstWidth G.b (W*piece))) X.width)→Bool)
local notation "tape" => Root.widePackedImage X S.copies s payloadBits w seed lo G.C packWidth steps compact
  (DescentExterior.publicRows X original) (Sum.elim history_ past_)
local notation "backing" => DescentTerminalPublicIdentity.back paint w codes count₀
local notation "originalTape" => Root.appended front extra tape backing
local notation "checked" => DescentWideSeedFlags.countedAt X S.copies s payloadBits seed history_ originalTape

section FixedHeaders
open DescentTerminalGrainProfiles DescentTerminalDenseHeaderBoot DescentSortedRoster
open DescentTerminalLocalPortBook.Rasters DescentPackedColony
local notation "format_" => ({fmt with binSize:=W}:Branch.PreflightFormat)
local notation "eqs_" => Branch.preflight_caps (tail:=tail) X G S b format_
local notation "host_" => (b).target.vertex.trans (Fin.castLEEmb (b).target.valid.host)
local notation "rasters_" => Branch.presented (eqs_).1 (eqs_).2.1 ((pre).rasters begin_ peer old)
local notation "decode_" => Branch.decodeBook S G base ordinary.radix p q (pre).degree (pre).cap
  (pre).printBits (by change 3+1≤4; decide)
local notation "privateTape_" => DescentTerminalHeaderGroups.stream («p»:=p) hostGraph (leaf).home
  (leaf).native (leaf).external (leaf).nodes (leaf).ops q positive (H₀*H₀)
local notation "publicTape_" => DescentTerminalExteriorHeaders.stream (q:=q) («p»:=p) hostGraph
  (leaf).home (leaf).native (leaf).external (leaf).nodes (leaf).ops H₀
local notation "cohorts_" => Computability.BorderVNP.FragmentBucket.count (Branch.cohortHome X G S b positive base)

open private Hierarchy.DescentTerminalPreflightSpace.Spec.maskStartRoom from OAI.Hierarchy.DescentTerminalAcquiredPorts

private theorem roomParts {x y W w sockets hosts : ℕ} (row : x = y) (word : x+W < 2^w)
    (three : hosts*3 < 2^w) (inh : 0 < hosts) (bounded : sockets < 2^w) :
    y+W < 2^w ∧ 2 < 2^w ∧ hosts < 2^w ∧ sockets < 2^w := by omega

include ordinary reset branch positive room shorten c base width age wFit qFit qh pool raw in
/-- The measured machine bounds all numerical header fields, including the last
allocator carry and the absent-neighbor sentinel on the three-socket roster. -/
theorem Branch.fixed_header_room (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (peerRows:H₀*(pre).degree≤peer.size) (space:AddressPlan.last V cfg I_ R_ start<2^w)
    (rowCount:(cfg).terminal.rows=paidRows) (size:(cfg).terminal.pool=K*W)
    (allRows:(cfg).terminal.rows=K*W) :
    paidRows+W<2^w ∧ 2<2^w ∧ H₀<2^w ∧ H₀*(pre).degree<2^w := by
  obtain ⟨ab,bc,cd,de,ef⟩:=AddressPlan.stages cfg I_ base_
  have arena:(A_).finish<2^w:=ab.trans_lt (bc.trans_lt (cd.trans_lt (de.trans_lt (ef.trans_lt space))))
  have fit := Hierarchy.DescentTerminalPreflightSpace.Spec.maskStartRoom V cfg I_ R_ start space
  have original:=(pre).all_lower begin_ fit
  have slots : H₀*(pre).degree<2^w:=peerRows.trans_lt
    ((Nat.le_add_left peer.size peer.base).trans_lt (boot.roster.trans_lt original.1))
  have three : H₀*3<2^w:=slots
  have cells:=issued_purchase X G S ordinary reset branch positive room shorten c q W qh (leaf).wp ord rfl
  have bought:=((cells.trans pool).trans_eq size).trans_eq allRows.symm
  have word:=site_cursor_word_room cfg I_ base_ arena sites (leaf).wp bought
  exact roomParts rowCount word three sitesPositive slots

/-- The same public row cap covers both independent scans, including empty groups. -/
theorem Branch.fixed_header_lengths (headerRoom:(cfg).terminal.pool≤headerRows) :
    (privateTape_).length≤headerRows ∧ (publicTape_).length≤headerRows := by
  have paid:=issued_purchase X G S ordinary reset branch positive room shorten c q W qh (leaf).wp ord rfl
  have rows:=paid.trans (pool.trans headerRoom)
  constructor
  · exact (DescentTerminalHeaderGroups.paid_length hostGraph (leaf).home (leaf).native (leaf).external
      (leaf).nodes (leaf).ops (leaf).wp positive (H₀*H₀)).trans rows
  · exact (DescentTerminalExteriorHeaders.paid_length hostGraph (leaf).home (leaf).native (leaf).external
      (leaf).nodes (leaf).ops (leaf).wp).trans rows

private theorem reelPeerCover {h d d' : ℕ} (dims : d = d')
    (rawPeers : Fin h → Fin d → Option (Fin h)) (fromHost toHost : Fin h)
    (fromSet : present (DescentSortedRoster.indexed rawPeers) fromHost = present rawPeers fromHost)
    (toSet : present (DescentSortedRoster.indexed rawPeers) toHost = present rawPeers toHost)
    (adjacent : toHost ∈ present rawPeers fromHost ∧ fromHost ∈ present rawPeers toHost) :
    toHost ∈ present (Branch.fixedRoster dims rawPeers) fromHost ∧
    fromHost ∈ present (Branch.fixedRoster dims rawPeers) toHost := by
  rw [Branch.fixedRoster_present, Branch.fixedRoster_present, fromSet, toSet]
  exact adjacent

private theorem reelLayerDates (x : Spec) (beginAt : ℕ) :
    x.cohortEnd beginAt ≤ x.literalBase beginAt ∧ x.cohortEnd beginAt ≤ x.bookEnd beginAt := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩ := x.layers beginAt
  exact ⟨h0.trans (h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))),
    h0.trans (h1.trans (h2.trans h3))⟩

private theorem reelBins {depthN siteN grainN rowQ binW lim : ℕ} {portsN tagT : Type}
    [Fintype portsN] {portBits : portsN → ℕ} {reelGraph : Network depthN portsN portBits}
    (o : Order reelGraph siteN grainN) (r : ∀ v, Recipe tagT (DescentTerminalBundleRows.SiteRef («p» := grainN) reelGraph v))
    (hp : 0 < grainN) (born : ∀ v, (r v).Node ↪ ℕ) (bounded : Bins (W := binW) (q := rowQ) o.site ≤ lim) :
    Bins (W := binW) (q := rowQ) (DescentTerminalBundleRows.site o r hp born) ≤ lim :=
  bounded

local notation "headerOrder" => DescentTerminalCableOrder.order hostGraph (leaf).home (leaf).native p (leaf).external (leaf).nodes (leaf).ops
local notation "headerBins" n:arg => reelBins (binW:=W) (rowQ:=q) (lim:=K) headerOrder rsite positive (leaf).birth ((leaf).binsFit (cfg) n)

/-- Both header incidences at the validated reel image, from the measured signed wings,
cohort census, six issued books and original shared lookup tables. -/
def Branch.fixed_reel_header_records (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (oldPeers:Fin H₀→Fin (b).target.placement.degree→Option (Fin H₀))
    (raster:DescentTerminalLocalPortBook.Rasters.Inputs («p»:=p) (bw:=(pre).printBits) (argc:=Nat.clog 2 (q+1))
      (b).target.placement host_ S (b).target.valid (b).target.order oldPeers rasters_ primitive)
    (bookAt:m=(pre).bookAtPrimitive begin_ peer old decode_ primitive)
    (book:Book.Issued ((pre).parts begin_) (fun i:Fin H₀=>issue (sites i) (box i) (rowNames i) (argNames i)) m)
    (pageReads:(pages₀).Reads m)
    (peerRows:H₀*(pre).degree≤peer.size)
    (peerData:∀(i:Fin H₀)(l:Fin (pre).degree),primitive (peer.base+(i.val*(pre).degree+l.val))=
      (target (Branch.fixedRoster (eqs_).1 oldPeers i l):Computability.VPVNP.BurstRAM.Word w))
    (census:∀i:Fin H₀,primitive (((pre).census begin_).base+i.val)=(cohorts_ i:Computability.VPVNP.BurstRAM.Word w))
    (early:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).cohortEnd begin_)
    (tables:∀j<DescentTerminalDenseHeaderBoot.extent q p,primitive (rom+j)=DescentTerminalDenseHeaderBoot.back w q p j)
    (livePrivate:(privateTape_).length≤headerRows) (livePublic:(publicTape_).length≤headerRows)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w)
    (rowCount:(cfg).terminal.rows=paidRows) (allRows:(cfg).terminal.rows=K*W) (size:(cfg).terminal.pool=K*W)
    (counter:paidRows+W<2^w) (high:2<2^w) (hosts:H₀<2^w) (sockets:H₀*(pre).degree<2^w)
    (late:dst<(pre).cohortEnd begin_) (ceiling:start≤fence)
    (romSide:rom+DescentTerminalDenseHeaderBoot.extent q p≤firstFree ∨ dst<rom)
    (selected:c=(normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow history_)
    (wideSeed:2*digitsNeeded s≤payloadBits) (positiveWord:0<w) (fitsSeed:seedBase+(seedRows+1)<2^w)
    (topSeed:seedBase+(seedRows+1)≤lo) (positiveGrain:0<packWidth)
    (below:firstFree≤fence) (before:dst<wall)
    (lower:∀a∈shelves packWidth lo 0 steps,count a.ordinal<lo)
    (words:∀a∈steps,DescentPackedProfileTape.slots a.seats packWidth*packWidth<2^w)
    (fits:dst+1<2^w) (geometry:plan.Room w B₀ S.length fence wall)
    (top:wall+DescentExteriorShelf.span j rest s E₀+E₀<2^w)
    (apart:compact+32*DescentExteriorShelf.span j rest s E₀≤wall)
    (copyRoom:wall+17*DescentExteriorShelf.span j rest s E₀<2^w)
    (historyWords:∀a,lo≤a→a<compact→preflight a=checked a)
    (exterior:∀(col:Fin 17) (u:ℕ),u<DescentExteriorShelf.span j rest s E₀→
      preflight ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u)=
        checked ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u))
    (history:(b).path.savedRotations plan fence tail preflight)
    (window:∀u<extra,preflight (front+u)=checked (front+u)) :
    { _cols : ControlColumns (K:=K) (W:=W) (q:=q) (piece:=piece) (w:=w) (cfg).terminal (plan_).emit (memAt post) hostGraph (leaf).home (leaf).native
      (leaf).external (leaf).nodes (leaf).ops rsite positive (leaf).birth (leaf).wp qh
      (headerBins size) bankSet // DescentTerminalDenseHeaderRAM.Reads (plan_).emit.plane.header
      (DescentTerminalHeaderGroups.padded (n:=headerRows) privateTape_) post } := by
  have folded:=wide_paid_post_reel (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset)
    (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten)
    (w:=w) (payloadBits:=payloadBits) (fit:=fit) («V»:=V) («U»:=(cfg)) (I:=I_) («R»:=R_)
    (begin_:=start) (pub:=count₀) («codes»:=codes) (all:=all) (width:=width) (outer:=original)
    lo packWidth fence count plan preflight wideSeed positiveWord fitsSeed topSeed positiveGrain below
    before lower words fits geometry top apart copyRoom historyWords exterior (fun _ => (congrArg (fun choice => (SeedNamed.issued X G S ordinary reset branch positive room shorten choice).path.savedRotations plan fence tail preflight) selected).mp history) window
  have roomDates := reelLayerDates (pre) begin_
  have romTop := early.trans roomDates.1
  have saved:=(pre).reel_ports begin_ rom q piece W K codes front peer old total modulo homes boundary (cfg) V other T (pre).vertices B
    preflight post fence firstFree dst folded.2.2 late ceiling romTop romSide
  have staticSpace := Hierarchy.DescentTerminalPreflightSpace.Spec.maskStartRoom V cfg I_ R_ start space
  have active : 0 < (pre).strips := by change 0 < 3 + _; exact Nat.add_pos_left (by decide) _
  have prior (addr:ℕ) (lo:addr<(pre).weights begin_) : m addr=primitive addr := by
    rw [bookAt]
    exact (pre).book_at_primitive_low begin_ peer old decode_ primitive staticSpace active
      boot.roster boot.oldCables addr lo
  let hdr:=(bodyPlane (cfg) I_ base_).header
  let out:Fin 4→Bank:=![hdr.rem,hdr.whole,hdr.index,hdr.control]
  have cableFields:=Branch.fixed_cable_fields_width X G S b positive base width q R rot headerRows paidRows W
    begin_ peer old primitive values oldPeers raster paid actors total modulo homes boundary boot staticSpace
    qh peerRows peerData livePrivate rom out early tables
  have current:(pre).cableInput begin_ peer old decode_ values primitive=(X_).after values expr m := by
    simp only [bookAt,Spec.cableInput]
  let cableClaim (before : Memory w) : Prop :=
    let chain := (pre).cables begin_ peer old
    let final := chain.final q p before
    DescentTerminalDenseHeaderRAM.Reads
      (DescentTerminalDenseHeaderBoot.layout q p rom chain.printer.output (out 0) (out 1) (out 2) (out 3))
      (DescentTerminalHeaderGroups.padded (n:=headerRows) privateTape_) final ∧
      ∀ j : Fin (H₀*(pre).degree), chain.printer.prefix.read final (j.val : Computability.VPVNP.BurstRAM.Word w) =
        ((DescentTerminalWidthRowsRAM.passed q p (DescentTerminalGrainProfiles.slotCount («p»:=p)
          (Branch.fixedRoster (eqs_).1 oldPeers) hostGraph (leaf).home) (j.val+1)).length : Computability.VPVNP.BurstRAM.Word w)
  have moved : cableClaim ((X_).after values expr m) := (congrArg cableClaim current).mp cableFields
  let roster:=Branch.fixedRoster (eqs_).1 oldPeers
  have cover (e:(hostGraph).Edge) (_:0<(hostGraph).width e) :
      (leaf).home ((hostGraph).dst e)∈present roster ((leaf).home ((hostGraph).src e)) ∧
      (leaf).home ((hostGraph).src e)∈present roster ((leaf).home ((hostGraph).dst e)) := by
    have atSrc:=Counter.mounted_present (b).target.placement host_ oldPeers raster.near
      ((b).target.placement.pos ((hostGraph).src e)).2
    have atDst:=Counter.mounted_present (b).target.placement host_ oldPeers raster.near
      ((b).target.placement.pos ((hostGraph).dst e)).2
    exact reelPeerCover (eqs_).1 oldPeers _ _ atSrc atDst
      (Counter.all_adjacent (b).target.placement host_ oldPeers raster.near e)
  have edge (e:(hostGraph).Edge) : p∣(hostGraph).width e := by
    have d:=(b).target.valid.divides e
    rw [(b).target.grain] at d
    exact (dvd_mul_right p G.b).trans d
  have pin (z:Σ _:Fin S.copies,Fin E₀) : p∣s*1 := by
    rw [Nat.mul_one]
    unfold AtomSchedule.firstWidth AtomSchedule.grainAt
    exact ⟨G.b^(S.rounds*S.height-S.ordinaryDone 0)*G.b,by ac_rfl⟩
  have cells:=issued_purchase X G S ordinary reset branch positive room shorten _ q W qh (leaf).wp ord rfl
  have purchased_:purchased W (fun i=>(sites i).rows q)≤paidRows :=
    ((cells.trans pool).trans_eq size).trans_eq (allRows.symm.trans rowCount)
  have rows:paidRows=K*W:=rowCount.symm.trans allRows
  have censusEnd:=(pre).census_end begin_
  have limit:H₀≤((pre).census begin_).size:=Nat.le_pow_clog (by decide) _
  have beforeWeights : (pre).cohortEnd begin_ ≤ (pre).weights begin_ :=
    ((pre).layers begin_).1.trans ((pre).layers begin_).2.1
  have bookRom (j:ℕ) (hj:j<DescentTerminalDenseHeaderBoot.extent q p) :
      m (rom+j)=DescentTerminalDenseHeaderBoot.back w q p j :=
    (prior _ ((Nat.add_lt_add_left hj rom).trans_le (early.trans beforeWeights))).trans (tables j hj)
  have bookPeer (i:Fin H₀) (l:Fin (pre).degree) : m (peer.base+(i.val*(pre).degree+l.val))=
      (target (roster i l):Computability.VPVNP.BurstRAM.Word w) := by
    have inRow : i.val*(pre).degree+l.val < H₀*(pre).degree := by
      calc
        _ < i.val*(pre).degree+(pre).degree := Nat.add_lt_add_left l.isLt _
        _ = (i.val+1)*(pre).degree := (Nat.succ_mul ..).symm
        _ ≤ _ := Nat.mul_le_mul_right _ i.isLt
    exact (prior _ ((Nat.add_lt_add_left (inRow.trans_le peerRows) peer.base).trans_le (boot.roster.trans beforeWeights))).trans (peerData i l)
  have bookCensus (i:Fin H₀) : m (((pre).census begin_).base+i.val)=(cohorts_ i:Computability.VPVNP.BurstRAM.Word w) :=
    (prior _ ((Nat.add_lt_add_left (i.isLt.trans_le limit) _).trans_le (censusEnd.trans beforeWeights))).trans (census i)
  have heightRows:(pre).paidRows=K*W:=rows
  exact (pre).acquired_ports_width_after begin_ rom q piece W K codes front peer old total modulo homes boundary
    (cfg) V other T (pre).vertices B roster hostGraph (leaf).home (leaf).native (leaf).external
    (leaf).nodes (leaf).ops positive qh (leaf).wp rsite (leaf).birth box (fun i n => rowNames i n) argNames
    (headerBins size) head emptyCode m values short paid actors boot
    (early.trans roomDates.2) full space allRows rows edge pin
    (Branch.fixedRoster_sorted (eqs_).1 oldPeers) cover (leaf).fit purchased_ counter high hosts sockets
    book pageReads.counts pageReads.nextRow bookRom active rfl peerRows bookPeer cohorts_
    (Branch.cohort_cap X G S b positive base) bookCensus
    (fun i=>(Branch.site_public_grains X G S b positive base i).symm)
    livePrivate livePublic moved.1 moved.2 post
    (by simpa only [Spec.afterSiteControls,heightRows] using saved.1)
    (by simpa only [Spec.afterSiteControls,heightRows] using saved.2.1)
    (by simpa only [Spec.afterSiteControls,heightRows] using saved.2.2)

def Branch.fixed_reel_headers (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (oldPeers:Fin H₀→Fin (b).target.placement.degree→Option (Fin H₀))
    (raster:DescentTerminalLocalPortBook.Rasters.Inputs («p»:=p) (bw:=(pre).printBits) (argc:=Nat.clog 2 (q+1))
      (b).target.placement host_ S (b).target.valid (b).target.order oldPeers rasters_ primitive)
    (bookAt:m=(pre).bookAtPrimitive begin_ peer old decode_ primitive)
    (book:Book.Issued ((pre).parts begin_) (fun i:Fin H₀=>issue (sites i) (box i) (rowNames i) (argNames i)) m)
    (pageReads:(pages₀).Reads m)
    (peerRows:H₀*(pre).degree≤peer.size)
    (peerData:∀(i:Fin H₀)(l:Fin (pre).degree),primitive (peer.base+(i.val*(pre).degree+l.val))=
      (target (Branch.fixedRoster (eqs_).1 oldPeers i l):Computability.VPVNP.BurstRAM.Word w))
    (census:∀i:Fin H₀,primitive (((pre).census begin_).base+i.val)=(cohorts_ i:Computability.VPVNP.BurstRAM.Word w))
    (early:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).cohortEnd begin_)
    (tables:∀j<DescentTerminalDenseHeaderBoot.extent q p,primitive (rom+j)=DescentTerminalDenseHeaderBoot.back w q p j)
    (livePrivate:(privateTape_).length≤headerRows) (livePublic:(publicTape_).length≤headerRows)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w)
    (rowCount:(cfg).terminal.rows=paidRows) (allRows:(cfg).terminal.rows=K*W) (size:(cfg).terminal.pool=K*W)
    (counter:paidRows+W<2^w) (high:2<2^w) (hosts:H₀<2^w) (sockets:H₀*(pre).degree<2^w)
    (late:dst<(pre).cohortEnd begin_) (ceiling:start≤fence)
    (romSide:rom+DescentTerminalDenseHeaderBoot.extent q p≤firstFree ∨ dst<rom)
    (selected:c=(normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow history_)
    (wideSeed:2*digitsNeeded s≤payloadBits) (positiveWord:0<w) (fitsSeed:seedBase+(seedRows+1)<2^w)
    (topSeed:seedBase+(seedRows+1)≤lo) (positiveGrain:0<packWidth)
    (below:firstFree≤fence) (before:dst<wall)
    (lower:∀a∈shelves packWidth lo 0 steps,count a.ordinal<lo)
    (words:∀a∈steps,DescentPackedProfileTape.slots a.seats packWidth*packWidth<2^w)
    (fits:dst+1<2^w) (geometry:plan.Room w B₀ S.length fence wall)
    (top:wall+DescentExteriorShelf.span j rest s E₀+E₀<2^w)
    (apart:compact+32*DescentExteriorShelf.span j rest s E₀≤wall)
    (copyRoom:wall+17*DescentExteriorShelf.span j rest s E₀<2^w)
    (historyWords:∀a,lo≤a→a<compact→preflight a=checked a)
    (exterior:∀(col:Fin 17) (u:ℕ),u<DescentExteriorShelf.span j rest s E₀→
      preflight ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u)=
        checked ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u))
    (history:(b).path.savedRotations plan fence tail preflight)
    (window:∀u<extra,preflight (front+u)=checked (front+u)) :
    ControlColumns (K:=K) (W:=W) (q:=q) (piece:=piece) (w:=w) (cfg).terminal (plan_).emit (memAt post) hostGraph (leaf).home (leaf).native
      (leaf).external (leaf).nodes (leaf).ops rsite positive (leaf).birth (leaf).wp qh
      (headerBins size) bankSet := by
  exact (Branch.fixed_reel_header_records (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch)
    (positive:=positive) (room:=room) (shorten:=shorten) (c:=c) (base:=base) (width:=width) (age:=age)
    (wFit:=wFit) (qFit:=qFit) (qh:=qh) (template:=template) (sitesPositive:=sitesPositive)
    (rawWords:=rawWords) (headerRows:=headerRows) (paidRows:=paidRows) (pool:=pool) (raw:=raw)
    (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom) (peer:=peer) (old:=old) (org:=org)
    (homes:=homes) (other:=other) (lo:=lo) (packWidth:=packWidth) (all:=all)
    (head:=head) (short:=short) (fence:=fence) (count:=count) (plan:=plan) (primitive:=primitive)
    (m:=m) (original:=original)
    paid actors boot oldPeers raster bookAt book pageReads peerRows peerData census early tables livePrivate livePublic
    full space rowCount allRows size counter high hosts sockets late ceiling romSide selected wideSeed positiveWord
    fitsSeed topSeed positiveGrain below before lower words fits geometry top apart copyRoom historyWords exterior
    history window).1

include short in
/-- The five original private profile banks at the dated post-reel snapshot. -/
theorem Branch.fixed_reel_widths (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (oldPeers:Fin H₀→Fin (b).target.placement.degree→Option (Fin H₀))
    (raster:DescentTerminalLocalPortBook.Rasters.Inputs («p»:=p) (bw:=(pre).printBits) (argc:=Nat.clog 2 (q+1))
      (b).target.placement host_ S (b).target.valid (b).target.order oldPeers rasters_ primitive)
    (bookAt:m=(pre).bookAtPrimitive begin_ peer old decode_ primitive)
    (book:Book.Issued ((pre).parts begin_) (fun i:Fin H₀=>issue (sites i) (box i) (rowNames i) (argNames i)) m)
    (pageReads:(pages₀).Reads m)
    (peerRows:H₀*(pre).degree≤peer.size)
    (peerData:∀(i:Fin H₀)(l:Fin (pre).degree),primitive (peer.base+(i.val*(pre).degree+l.val))=
      (target (Branch.fixedRoster (eqs_).1 oldPeers i l):Computability.VPVNP.BurstRAM.Word w))
    (census:∀i:Fin H₀,primitive (((pre).census begin_).base+i.val)=(cohorts_ i:Computability.VPVNP.BurstRAM.Word w))
    (early:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).cohortEnd begin_)
    (tables:∀j<DescentTerminalDenseHeaderBoot.extent q p,primitive (rom+j)=DescentTerminalDenseHeaderBoot.back w q p j)
    (livePrivate:(privateTape_).length≤headerRows) (livePublic:(publicTape_).length≤headerRows)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w)
    (rowCount:(cfg).terminal.rows=paidRows) (allRows:(cfg).terminal.rows=K*W) (size:(cfg).terminal.pool=K*W)
    (counter:paidRows+W<2^w) (high:2<2^w) (hosts:H₀<2^w) (sockets:H₀*(pre).degree<2^w)
    (late:dst<(pre).cohortEnd begin_) (ceiling:start≤fence)
    (romSide:rom+DescentTerminalDenseHeaderBoot.extent q p≤firstFree ∨ dst<rom)
    (selected:c=(normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow history_)
    (wideSeed:2*digitsNeeded s≤payloadBits) (positiveWord:0<w) (fitsSeed:seedBase+(seedRows+1)<2^w)
    (topSeed:seedBase+(seedRows+1)≤lo) (positiveGrain:0<packWidth)
    (below:firstFree≤fence) (before:dst<wall)
    (lower:∀a∈shelves packWidth lo 0 steps,count a.ordinal<lo)
    (words:∀a∈steps,DescentPackedProfileTape.slots a.seats packWidth*packWidth<2^w)
    (fits:dst+1<2^w) (geometry:plan.Room w B₀ S.length fence wall)
    (top:wall+DescentExteriorShelf.span j rest s E₀+E₀<2^w)
    (apart:compact+32*DescentExteriorShelf.span j rest s E₀≤wall)
    (copyRoom:wall+17*DescentExteriorShelf.span j rest s E₀<2^w)
    (historyWords:∀a,lo≤a→a<compact→preflight a=checked a)
    (exterior:∀(col:Fin 17) (u:ℕ),u<DescentExteriorShelf.span j rest s E₀→
      preflight ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u)=
        checked ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u))
    (history:(b).path.savedRotations plan fence tail preflight)
    (window:∀u<extra,preflight (front+u)=checked (front+u)) :
    DescentTerminalDenseHeaderRAM.Reads (plan_).emit.plane.header
      (DescentTerminalHeaderGroups.padded (n:=headerRows) privateTape_) post := by
  have made_ := observedApply% (@Branch.fixed_reel_header_records) [F, (inferInstance : Field F), cp, P, X, G, S, k, cut, tail, n, h, C, f, g, W, q, piece, ordinary,
    reset, branch, positive, room, shorten, c, j, rest, base, width, age, wFit, qFit, qh, template,
    sitesPositive, rawWords, headerRows, paidRows, pool, raw, w, K, payloadBits, fit, begin_, rom, peer,
    old, org, homes, other, arity, groups, stride, oldTags, lo, packWidth, all, head, short, fence,
    count, plan, primitive, m, original, paid, actors, boot, oldPeers, raster, bookAt, book, pageReads,
    peerRows, peerData, census, early, tables, livePrivate, livePublic, full, space, rowCount, allRows,
    size, counter, high, hosts, sockets, late, ceiling, romSide, selected, wideSeed, positiveWord,
    fitsSeed, topSeed, positiveGrain, below, before, lower, words, fits, geometry, top, apart, copyRoom,
    historyWords, exterior, history, window]
  exact made_.2

/-- Every occupied cable has a pair number in the selected rectangular header. -/
theorem Branch.fixed_pair_bound (e:(hostGraph).Edge) :
    DescentTerminalCableOrder.pairIndex hostGraph (leaf).home e<H₀*H₀ := by
  exact DescentTerminalHeaderDraft.pair_bound ((leaf).home ((hostGraph).src e)) ((leaf).home ((hostGraph).dst e))

end FixedHeaders

set_option maxHeartbeats 2400000 in
def wide_reel_printed (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w) (rowCount:(cfg).terminal.rows=paidRows)
    (allRows:(cfg).terminal.rows=K*W) (size:(cfg).terminal.pool=K*W)
    (retained : j≤S.groupWidth k tail S.length+k) (headerLow:head<start)
    (prior:∀u<(pre).weights begin_,out_ ((X_).after values expr m) u=primitive u)
    (late:dst<(pre).cohortEnd begin_) (ceiling:start≤fence) (tableSide:dst<org)
    (book:Book.Issued ((pre).parts begin_) (fun i:Fin H₀=>issue (sites i) (box i) (rowNames i) (argNames i)) m)
    (pageReads:(pages₀).Reads m)
    (occ : ∀ (i : Fin (S.hostSize S.length)) (c' : Fin (groupsAt*2^k)),blankAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (measured (C_).layout (onBoard primitive) (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap)
      (A:=cap) (w:=p) (groups:=groupsAt) i) c' ≠ 0 ↔ ∃u,(b).target.chart ord rfl i u=c')
    (oldCells : ∀i u,PrimitiveReceipts (q:=q) (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i)
      u (venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
        (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
          (measured (C_).layout (onBoard primitive) (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) i)
        ((b).target.rawResident ord rfl i u))))
    (selected:c=(normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow history_)
    (admitted:accepted) (wideSeed:2*digitsNeeded s≤payloadBits) (fitsSeed:seedBase+(seedRows+1)<2^w)
    (topSeed:seedBase+(seedRows+1)≤lo) (positiveGrain:0<packWidth)
    (below:firstFree≤fence) (before:dst<wall)
    (lower:∀a∈shelves packWidth lo 0 steps,count a.ordinal<lo)
    (words:∀a∈steps,DescentPackedProfileTape.slots a.seats packWidth*packWidth<2^w)
    (fits:dst+1<2^w) (geometry:plan.Room w B₀ S.length fence wall)
    (top:wall+DescentExteriorShelf.span j rest s E₀+E₀<2^w)
    (apart:compact+32*DescentExteriorShelf.span j rest s E₀≤wall)
    (copyRoom:wall+17*DescentExteriorShelf.span j rest s E₀<2^w)
    (historyWords:∀a,lo≤a→a<compact→preflight a=checked a)
    (exterior:∀(col:Fin 17) (u:ℕ),u<DescentExteriorShelf.span j rest s E₀→
      preflight ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u)=
        checked ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u))
    (history:(b).path.savedRotations plan fence tail preflight)
    (window:∀u<extra,preflight (front+u)=checked (front+u))
    (valid:∀a,stagesOK (originalMatrix a) (publicRows X original a) (projected past_ false a) (projected past_ true a))
    (homeSide:dst<homes.base)
    (homeRead:∀i:Fin count₀,homes.read preflight (i.val:Computability.VPVNP.BurstRAM.Word w)=((oldHost i).val:Computability.VPVNP.BurstRAM.Word w))
    (rect:q*p=2^j*s) (positiveWord:0<w) (pack:2^j*s≤w)
    (leaves:(cfg).terminal.leaves=(cfg).terminal.pool)
    (budgetHeight:ℕ) (roleCount:0<tagCount) (spare:0<B) (smallPage:32*B≤budgetHeight)
    (smallRows:32*W≤budgetHeight) (smallCircuit:16*(q*p)≤budgetHeight)
    (large:10≤budgetHeight) (addressBits:budgetHeight/2≤w)
    (headers:ControlColumns (cfg).terminal (plan_).emit (memAt post) hostGraph (leaf).home (leaf).native
      (leaf).external (leaf).nodes (leaf).ops rsite positive (leaf).birth (leaf).wp qh
      ((leaf).binsFit (cfg) size) bankSet) :
    (leaf).Printed (cfg) (arity:=arity) (groups:=groups) (stride:=stride) codec plan_ (C_).layout
      (meterAt post) bankSet (AddressPlan.chip (cfg) I_ base_) (paint ∘ Sum.inr) (payloadOut original)
      (paint ∘ Sum.inl) B := by
  subst c
  have real := wide_paid_post_reel (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset)
    (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten)
    (w:=w) (payloadBits:=payloadBits) (fit:=fit) («V»:=V) («U»:=(cfg)) (I:=I_) («R»:=R_)
    (begin_:=start) (pub:=count₀) («codes»:=codes) (all:=all) (width:=width) (outer:=original)
    lo packWidth fence count plan preflight wideSeed positiveWord fitsSeed topSeed positiveGrain below before
    lower words fits geometry top apart copyRoom historyWords exterior (fun _=>history) window
  have homeKept (i:Fin count₀) : (I_).homes.read post (i.val:Computability.VPVNP.BurstRAM.Word w) =
      homes.read preflight (i.val:Computability.VPVNP.BurstRAM.Word w) := by
    change homes.read post (i.val:Computability.VPVNP.BurstRAM.Word w)=_
    let u:=homes.base+(i.val:Computability.VPVNP.BurstRAM.Word w).val%homes.size
    have high : u<homes.base+homes.size := Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _
    have homeTop:=(boot.homes)
    obtain ⟨s₀,s₁,s₂,s₃,s₄,s₅,s₆,s₇,s₈⟩:=(pre).layers begin_
    exact real.2.2 u (by omega) (.inr (homeSide.trans_le (Nat.le_add_right ..)))
  apply wide_paid_printed (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset)
    (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (c:=_)
    (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
    (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
    (paidRows:=paidRows) (pool:=pool) (raw:=raw) (begin_:=begin_) (rom:=rom)
    (peer:=peer) (old:=old) (org:=org) (homes:=homes) (other:=other) (codec:=codec)
    («rawSize»:=s) («seed»:=seed) (lo:=lo) («clockCap»:=G.C) (packWidth:=packWidth) («steps»:=steps)
    (all:=all) (head:=head) (short:=short) primitive m post paid actors boot romTop full space rowCount
    allRows size retained headerLow fence firstFree dst prior real.2.2 late ceiling tableSide book pageReads
    occ oldCells original valid (real.1 admitted) (fun i => (homeKept i).trans (homeRead i)) payloadBits real.2.1 rect positiveWord pack
    leaves budgetHeight roleCount spare smallPage smallRows smallCircuit large addressBits headers

section FixedHeaders
open DescentTerminalGrainProfiles DescentTerminalDenseHeaderBoot DescentSortedRoster
open DescentTerminalLocalPortBook.Rasters DescentPackedColony
local notation "format_" => ({fmt with binSize:=W}:Branch.PreflightFormat)
local notation "eqs_" => Branch.preflight_caps (tail:=tail) X G S b format_
local notation "host_" => (b).target.vertex.trans (Fin.castLEEmb (b).target.valid.host)
local notation "rasters_" => Branch.presented (eqs_).1 (eqs_).2.1 ((pre).rasters begin_ peer old)
local notation "decode_" => Branch.decodeBook S G base ordinary.radix p q (pre).degree (pre).cap
  (pre).printBits (by change 3+1≤4; decide)
local notation "privateTape_" => DescentTerminalHeaderGroups.stream («p»:=p) hostGraph (leaf).home
  (leaf).native (leaf).external (leaf).nodes (leaf).ops q positive (H₀*H₀)
local notation "publicTape_" => DescentTerminalExteriorHeaders.stream (q:=q) («p»:=p) hostGraph
  (leaf).home (leaf).native (leaf).external (leaf).nodes (leaf).ops H₀
local notation "cohorts_" => Computability.BorderVNP.FragmentBucket.count (Branch.cohortHome X G S b positive base)


open private Hierarchy.DescentTerminalPreflightSpace.Spec.maskStartRoom from OAI.Hierarchy.DescentTerminalAcquiredPorts

include age in
/-- The observed signed rasters generate all six Book columns at the reached date. -/
theorem Branch.observed_reel_book
    (paid actors:Fin (pre).scalar.blocks→Bank) (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (oldPeers:Fin H₀→Fin (b).target.placement.degree→Option (Fin H₀))
    (raster:DescentTerminalLocalPortBook.Rasters.Inputs («p»:=p) (bw:=(pre).printBits) (argc:=Nat.clog 2 (q+1))
      (b).target.placement host_ S (b).target.valid (b).target.order oldPeers rasters_ primitive)
    (bookAt:m=(pre).bookAtPrimitive begin_ peer old decode_ primitive)
    (retained:j≤S.groupWidth k tail S.length+k)
    (token:2^(pre).printBits<2^w) (space:AddressPlan.last V cfg I_ R_ start<2^w) :
    Book.Issued ((pre).parts begin_) (fun i:Fin H₀=>issue (sites i) (box i) (rowNames i) (argNames i)) m := by
  have elapsed : 0<S.length := by unfold AtomSchedule.length;positivity
  have whole : p∣s := by
    unfold AtomSchedule.firstWidth AtomSchedule.grainAt
    exact ⟨G.b^(S.rounds*S.height-S.ordinaryDone 0)*G.b,by ac_rfl⟩
  have startRoom := Hierarchy.DescentTerminalPreflightSpace.Spec.maskStartRoom V cfg I_ R_ start space
  have codeRoom : ((pre).issuedBook begin_ peer old).stop < 2^w := by
    rw [(pre).print_stop begin_ peer old]
    exact ((pre).all_lower begin_ startRoom).2.2.2.2.1
  rw [bookAt]
  exact (Branch.bookOnDimensions X G S b positive base width (eqs_).1 (eqs_).2.1 (by change 3+1≤4; decide)
    ((pre).rasters begin_ peer old) q (pre).printBits ((pre).bookBegin begin_) ((pre).weights begin_)
    primitive elapsed retained whole oldPeers raster
    ((pre).source_before_weights begin_ peer old startRoom boot.roster boot.oldCables) le_rfl token codeRoom).2.2.1

/-- Terminal printing from the actual signed roster, cohort census and two header passes. -/
private theorem presented_geometry {du du' nb ca ca' : ℕ} (hd:du=du') (hc:ca=ca')
    (r:DescentTerminalLocalPortBook.Rasters du' nb ca') :
    (Branch.presented hd hc r).geometry=r.geometry := by
  cases hd
  cases hc
  rfl

/-- Each marked site's existing scalar receipt reads the original public arity bank. -/
theorem Branch.reel_occupation_from_words (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w)
    (hostRoom:H₀≤2^w) (groupRoom:groupsAt≤w)
    (words:∀(i:Fin H₀)(x:DescentColonies.Block k),primitive (((R_).occupied x).base+i.val)=
      ((DescentSIMDLookup.encode 1 groupsAt (fun g=>if ∃v:(hostGraph).Site,
        (b).target.home v=i ∧ ((b).target.placement.pos v).1=g ∧ (b).target.placement.block v=x
        then 1 else 0 : Fin groupsAt→DescentSIMDLookup.Cell 1)).val:Computability.VPVNP.BurstRAM.Word w)) (i:Fin H₀) (key:Fin (groupsAt*2^k)) :
    blankAt (measured (C_).layout (onBoard primitive) (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap)
      (A:=cap) (w:=p) (groups:=groupsAt) i) key≠0 ↔ ∃u,(b).target.chart ord rfl i u=key := by
  have early := (pre).earlier begin_ rom q piece W K codes front peer old total modulo homes boundary
    cfg V other T (pre).vertices B paid actors boot romTop full space
  have bounds (x:DescentColonies.Block k) : ((R_).occupied x).base+((R_).occupied x).size≤ start := by
    exact (congrArg (fun a : Bank => a.base+a.size) (MaskAllocation.Channels.occupied_at R_ x).symm).trans_le
      ((pre).channels_before begin_ (finProdFinEquiv (x,(0:Fin 9))))
  exact (b).target.sockets_occupation ord rfl cfg I_ R_ start head short literal primitive primitive
    early space hostRoom groupRoom ((pre).prior begin_).actorSize (fun x h=>words h x)
    start le_rfl bounds (fun _ _=>rfl) i key

private theorem reel_presence_one {indicator : Fin 2} (on_ : indicator ≠ 0) : indicator.val = 1 := by
  have below := indicator.isLt
  have nonzero : indicator.val ≠ 0 := fun eqn => on_ (Fin.ext eqn)
  omega

/-- The measured live flag uses the same bank as the registered occupancy bit. -/
theorem Branch.reel_live_from_occupation
    (occupied:∀ i c',blankAt (measured (C_).layout (onBoard primitive) (q:=q) (t:=tagCount)
      (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) i) c' ≠ 0 ↔
      ∃u,(b).target.chart ord rfl i u=c') :
    ∀i u,venueField (cellAt (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap)
      (A:=cap) (w:=p) (groups:=groupsAt) (C_).layout (onBoard primitive) i)
      ((b).target.rawResident ord rfl i u)) (.inr (.inl ()))=1 := by
  intro i u
  let venue := (ord).node i u
  let coordinate := (b).target.rawResident ord rfl i u
  have marked := (occupied i coordinate).2 ⟨((ord).nodes i).symm u, rfl⟩
  have read := DescentTerminalPrimitiveFrames.live_at (q:=q) (t:=tagCount) (H:=cap)
    (N:=nodeCap) (A:=cap) («p»:=p) (groups:=groupsAt) (R_) start (onBoard primitive)
    ((b).target.placement.block venue) i ((b).target.placement.pos venue).1 rfl
  exact read.trans (reel_presence_one marked)

set_option maxHeartbeats 3200000
set_option cleanup.letToHave false
/-- The original extent remains visible at the attained primitive socket of every named site. -/
theorem Branch.reel_population_from_words (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w)
    (hostRoom:H₀≤2^w)
    (words:∀v:(hostGraph).Site,DescentSIMDLookup.digit (Nat.clog 2 (nodeCap+1)) (((b).target.placement).pos v).1.val
      (primitive ((((pre).channels begin_).primitive (((b).target.placement).block v) 3).base+((b).target.home v).val)).val=
      Fintype.card ((Branch.archive X G S b positive).bit.recipe v).Node) :
    ∀ i (u : Fin (Fintype.card ((ord).Nodes i))),
      venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap)
      (w:=p) (groups:=groupsAt) (C_).layout (onBoard primitive) i) ((b).target.rawResident ord rfl i u))
      nodeCount=Fintype.card ((recipes i u).Node) := by
  intro i u
  let v:(hostGraph).Site:=(ord).node i u
  have here:(b).target.home v=i:=(((ord).nodes i).symm u).property
  have early := (pre).earlier begin_ rom q piece W K codes front peer old total modulo homes boundary
    cfg V other T (pre).vertices B paid actors boot romTop full space
  have atSockets := AddressPlan.sockets_measured V cfg I_ R_ start head short literal primitive early space
    ((pre).channels_before begin_) i
  let readAt := fun data : BlockFields q tagCount cap nodeCap cap p groupsAt (2^k) =>
    venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) data
      (finProdFinEquiv (((b).target.placement.pos v).1,(b).target.placement.block v))) nodeCount
  refine (congrArg readAt atSockets).trans ?_
  apply DescentTerminalRolePrefix.population (q:=q) (t:=tagCount) (hid:=cap)
    (N:=nodeCap) (slots:=cap) («p»:=p) (groups:=groupsAt) (R_) start primitive
    (((b).target.placement).block v) i (((b).target.placement).pos v).1 hostRoom
  · change H₀≤2^(Nat.clog 2 H₀)
    exact Nat.le_pow_clog (by decide) _
  · have paid := words v
    rw [here] at paid
    refine paid.trans (Fintype.card_congr ?_)
    exact Equiv.refl _

theorem Branch.reel_public_arity (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w)
    (oldCells : ∀ (i : Fin (S.hostSize S.length)) (u : Fin (Fintype.card ((ord).Nodes i))),PrimitiveReceipts (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i)
      u (venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)  (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (C_).layout (onBoard primitive) i)
        ((b).target.rawResident ord rfl i u))))
    (v:(hostGraph).Site) :
    let A := (b).target.placement
    let h := host_ (A.pos v).2
    let rack := rasters_
    let shelf := MaskAllocation.shelf (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap)
      («p»:=p) (groups:=groupsAt) rack.geometry 0
    venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)  (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap)
      (w:=p) (groups:=groupsAt) shelf primitive h) (finProdFinEquiv ((A.pos v).1,A.block v))) publicArity=
      DescentTerminalGraphRows.arity hostGraph p v := by
  let i := (ord).home v
  let u := (ord).nodes i ⟨v,rfl⟩
  have vertex : (ord).node i u=v :=
    congrArg Subtype.val (((ord).nodes i).symm_apply_apply ⟨v,rfl⟩)
  let readAt (table : BlockFields q tagCount cap nodeCap cap p groupsAt (2^k)) (z : (hostGraph).Site) :=
    venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
      (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
        (groups:=groupsAt) (blocks:=2^k) table
        (finProdFinEquiv (((b).target.placement.pos z).1,(b).target.placement.block z))) publicArity
  let exactAt (z : (hostGraph).Site) := readAt
    (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
      (groups:=groupsAt) (blocks:=2^k) (C_).layout (onBoard primitive) i) z =
    DescentTerminalGraphRows.arity hostGraph p z
  have atVertex : exactAt ((ord).node i u) := (oldCells i u).ports
  have atV : exactAt v := (congrArg exactAt vertex).mp atVertex
  have early := (pre).earlier begin_ rom q piece W K codes front peer old total modulo homes boundary
    cfg V other T (pre).vertices B paid actors boot romTop full space
  have sockets := AddressPlan.sockets_measured V cfg I_ R_ start head short literal primitive early space
    ((pre).channels_before begin_) i
  have atSocket := congrArg (fun table => readAt table v) sockets
  let inspect (ch : MaskAllocation.Channels (2^k)) := readAt
    (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
      (groups:=groupsAt) (blocks:=2^k)
      (MaskAllocation.shelf (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) («p»:=p)
        (groups:=groupsAt) ch 0) primitive i) v
  have atRack := congrArg inspect
    (presented_geometry (eqs_).1 (eqs_).2.1 ((pre).rasters begin_ peer old))
  exact atRack.trans (atSocket.symm.trans atV)

/-- Transport the entire scalar field record from the attained primitive shelf to the
socket memory used by the terminal emitter at the same physical group and block. -/
theorem Branch.reel_receipts_from_shelf (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w) (test:Prop→Prop)
    (receipts:∀ (i : Fin (S.hostSize S.length)) (u : Fin (Fintype.card ((ord).Nodes i))),PrimitiveReceipts (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i)
      u (venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)  (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap)
        (w:=p) (groups:=groupsAt) (C_).layout primitive i)
        (finProdFinEquiv ((((b).target.placement).pos ((ord).node i u)).1,((b).target.placement).block ((ord).node i u))))) test) :
    ∀ (i : Fin (S.hostSize S.length)) (u : Fin (Fintype.card ((ord).Nodes i))),PrimitiveReceipts (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i)
      u (venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)  (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap)
        (w:=p) (groups:=groupsAt) (C_).layout (onBoard primitive) i)
        ((b).target.rawResident ord rfl i u))) test:=by
  intro i u
  have early:=(pre).earlier begin_ rom q piece W K codes front peer old total modulo homes boundary
    cfg V other T (pre).vertices B paid actors boot romTop full space
  have atSockets := AddressPlan.sockets_measured V cfg I_ R_ start head short literal primitive early space
    ((pre).channels_before begin_) i
  let venue := (ord).node i u
  let readAt := fun data : BlockFields q tagCount cap nodeCap cap p groupsAt (2^k) =>
    venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) data
      (finProdFinEquiv (((b).target.placement.pos venue).1,(b).target.placement.block venue)))
  have observed := congrArg readAt atSockets
  exact (congrArg (fun table =>
    PrimitiveReceipts (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap)
      (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i) u table test) observed).mpr (receipts i u)




theorem Branch.reel_ports_from_shelf (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w)
    (atSites : ∀v:(hostGraph).Site,
      venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap)
        (w:=p) (groups:=groupsAt) (blocks:=2^k) (MaskAllocation.shelf (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) («p»:=p) (groups:=groupsAt) (rasters_).geometry 0) primitive (host_ (((b).target.placement).pos v).2))
        (finProdFinEquiv ((((b).target.placement).pos v).1,((b).target.placement).block v))) publicArity=
          DescentTerminalGraphRows.arity hostGraph p v) :
    ∀ (i : Fin (S.hostSize S.length)) (u : Fin (Fintype.card ((ord).Nodes i))),venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap)
      (w:=p) (groups:=groupsAt) (blocks:=2^k) (C_).layout (onBoard primitive) i) ((b).target.rawResident ord rfl i u))
        publicArity=(sites i).arity u := by
  intro i u
  let v : (hostGraph).Site := (ord).node i u
  have here : host_ (((b).target.placement).pos v).2 = i := (((ord).nodes i).symm u).property
  let readAt (table : BlockFields q tagCount cap nodeCap cap p groupsAt (2^k)) :=
    venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
      (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
        (groups:=groupsAt) (blocks:=2^k) table
        (finProdFinEquiv (((b).target.placement.pos v).1,(b).target.placement.block v))) publicArity
  let inspect (ch : MaskAllocation.Channels (2^k)) (idx : Fin (S.hostSize S.length)) := readAt
    (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
      (groups:=groupsAt) (blocks:=2^k)
      (MaskAllocation.shelf (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) («p»:=p)
        (groups:=groupsAt) ch 0) primitive idx)
  have atSite : inspect (rasters_).geometry (host_ (((b).target.placement).pos v).2) =
      DescentTerminalGraphRows.arity hostGraph p v := atSites v
  have atRow := (congrArg (inspect (rasters_).geometry) here).symm.trans atSite
  have atRack := congrArg (fun ch => inspect ch i)
    (presented_geometry (eqs_).1 (eqs_).2.1 ((pre).rasters begin_ peer old))
  have early := (pre).earlier begin_ rom q piece W K codes front peer old total modulo homes boundary
    cfg V other T (pre).vertices B paid actors boot romTop full space
  have sockets := AddressPlan.sockets_measured V cfg I_ R_ start head short literal primitive early space
    ((pre).channels_before begin_) i
  exact (congrArg readAt sockets).trans (atRack.symm.trans atRow)

private abbrev reelOperandNumber {tt ar : ℕ} (q₀ : ℕ) (r₀ : Recipe (Fin tt) (Fin ar))
    (hidden : r₀.Hidden ↪ ℕ) (u : r₀.Node) (j : Fin (r₀.arity u)) : ℕ :=
  (r₀.operand u j).elim (fun port => port.val+1) (fun name => q₀+(DescentTerminalChronologicalBooks.ordinal hidden name).val+1)

private theorem reelOperandNumber_congr {tt ar : ℕ} (q₀ : ℕ) (r₀ : Recipe (Fin tt) (Fin ar))
    (earlierNames laterNames : r₀.Hidden ↪ ℕ) (same : ∀ a, DescentTerminalChronologicalBooks.ordinal earlierNames a = DescentTerminalChronologicalBooks.ordinal laterNames a)
    (u : r₀.Node) (j : Fin (r₀.arity u)) :
    reelOperandNumber q₀ r₀ earlierNames u j = reelOperandNumber q₀ r₀ laterNames u j := by
  exact congrArg (fun h => (r₀.operand u j).elim (fun a => a.val+1) h)
    (funext fun a => congrArg (fun slot : Fin (Fintype.card r₀.Hidden) => q₀+slot.val+1) (same a))

open DescentLocalPrivateNames in
/-- Reindex a physical reference word from the executed pointer lookup into the same
site's masked operand slot, including the private first-use numbering. -/
theorem Branch.reel_operands_from_shelf (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w)
    {oldNodes oldArgs:ℕ}
    (physicalNodes:∀v:(net).Site,Fintype.card (((leaf).shape v).recipe positive).Node≤oldNodes)
    (physicalArgs:∀v:(net).Site,∀u,(((leaf).shape v).recipe positive).arity u≤oldArgs)
    (atSites:∀(v:(net).Site) (u:(((leaf).shape v).recipe positive).Node)
      (j:Fin ((((leaf).shape v).recipe positive).arity u)),
      venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap)
        (w:=p) (groups:=groupsAt) (blocks:=2^k) (MaskAllocation.shelf (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) («p»:=p) (groups:=groupsAt) (rasters_).geometry 0) primitive (host_ (((b).target.placement).pos v).2))
        (finProdFinEquiv ((((b).target.placement).pos v).1,((b).target.placement).block v)))
        (nodeArg ((DescentTerminalChronologicalBooks.ordinal ((leaf).birth v) u).castLE ((leaf).atoms v))
          (j.castLE ((((leaf).shape v).recipe_refs positive u).symm ▸ (leaf).refs v u)))=
      DescentTerminalBoundaryPointer.num (q:=q) net positive v ((ord).operandRank v)
        (((leaf).shape v).recipe positive) (bookCode).store
        ((firstAlias _ (DescentTerminalPointerIssue.slot _ ((leaf).birth v) (physicalNodes v) (physicalArgs v))).trans
          Fin.valEmbedding) u j) :
    ∀ (i : Fin (S.hostSize S.length)) (z : Fin (Fintype.card ((ord).Nodes i))) (u:((recipes i) z).Node) (j:Fin (((recipes i) z).arity u)),
      venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
        (groups:=groupsAt) (blocks:=2^k) (C_).layout (onBoard primitive) i) ((b).target.rawResident ord rfl i z))
        (nodeArg ((DescentTerminalChronologicalBooks.ordinal ((ranks i).atom z) u).castLE ((leaf).atoms ((ord).node i z))) (j.castLE (((((leaf).shape ((ord).node i z)).recipe_refs positive u).symm ▸ (leaf).refs ((ord).node i z) u) : ((recipes i) z).arity u ≤ cap)))=
      reelOperandNumber q ((recipes i) z) ((ranks i).hidden z) u j := by
  intro i z u j
  let v : (net).Site := (ord).node i z
  have here : host_ (((b).target.placement).pos v).2=i := (((ord).nodes i).symm z).property
  let readAt (table : BlockFields q tagCount cap nodeCap cap p groupsAt (2^k)) :=
    venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
      (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
        (groups:=groupsAt) (blocks:=2^k) table
        (finProdFinEquiv (((b).target.placement.pos v).1,(b).target.placement.block v)))
      (nodeArg ((DescentTerminalChronologicalBooks.ordinal ((ranks i).atom z) u).castLE ((leaf).atoms ((ord).node i z))) (j.castLE (((((leaf).shape ((ord).node i z)).recipe_refs positive u).symm ▸ (leaf).refs ((ord).node i z) u) : ((recipes i) z).arity u ≤ cap)))
  let inspect (ch : MaskAllocation.Channels (2^k)) (idx : Fin (S.hostSize S.length)) := readAt
    (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
      (groups:=groupsAt) (blocks:=2^k)
      (MaskAllocation.shelf (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap)
        («p»:=p) (groups:=groupsAt) ch 0) primitive idx)
  let rect : (((leaf).shape v).recipe positive).UsedWord ↪ ℕ := (firstAlias (((leaf).shape v).recipe positive) (DescentTerminalPointerIssue.slot (((leaf).shape v).recipe positive) ((leaf).birth v)
    (physicalNodes v) (physicalArgs v))).trans Fin.valEmbedding
  have atSite : inspect (rasters_).geometry (host_ (((b).target.placement).pos v).2) =
      DescentTerminalBoundaryPointer.num (q:=q) net positive v ((ord).operandRank v)
        (((leaf).shape v).recipe positive) (bookCode).store rect u j := atSites v u j
  have atRow := (congrArg (inspect (rasters_).geometry) here).symm.trans atSite
  have atRack := congrArg (fun ch => inspect ch i)
    (presented_geometry (eqs_).1 (eqs_).2.1 ((pre).rasters begin_ peer old))
  have early := (pre).earlier begin_ rom q piece W K codes front peer old total modulo homes boundary
    cfg V other T (pre).vertices B paid actors boot romTop full space
  have sockets := AddressPlan.sockets_measured V cfg I_ R_ start head short literal primitive early space
    ((pre).channels_before begin_) i
  have transported := (congrArg readAt sockets).trans (atRack.symm.trans atRow)
  have aliases (a : ((recipes i) z).Hidden) :
      DescentTerminalChronologicalBooks.ordinal rect a = DescentTerminalChronologicalBooks.ordinal ((ranks i).hidden z) a :=
    rectangle_packed_ordinal _ ((leaf).birth v) (physicalNodes v) (physicalArgs v)
      (Branch.private_card_fit X G S b positive seedOne age branch v) a
  apply transported.trans
  exact reelOperandNumber_congr q ((recipes i) z) rect ((ranks i).hidden z) aliases u j

private theorem observed_reel_facts (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (space:AddressPlan.last V cfg I_ R_ start<2^w) (rowCount:(cfg).terminal.rows=paidRows)
    (allRows:(cfg).terminal.rows=K*W) (size:(cfg).terminal.pool=K*W)
    (retained : j≤S.groupWidth k tail S.length+k) (bookWidth:2^(pre).printBits<2^w)
    (oldPeers:Fin H₀→Fin (b).target.placement.degree→Option (Fin H₀))
    (raster:DescentTerminalLocalPortBook.Rasters.Inputs («p»:=p) (bw:=(pre).printBits) (argc:=Nat.clog 2 (q+1))
      (b).target.placement host_ S (b).target.valid (b).target.order oldPeers rasters_ primitive)
    (bookAt:m=(pre).bookAtPrimitive begin_ peer old decode_ primitive)
    (peerRows:H₀*(pre).degree≤peer.size) (headerRoom:(cfg).terminal.pool≤headerRows) :
    (paidRows+W<2^w ∧ 2<2^w ∧ H₀<2^w ∧ H₀*(pre).degree<2^w) ∧
    ((privateTape_).length≤headerRows ∧ (publicTape_).length≤headerRows) ∧
    Book.Issued ((pre).parts begin_) (fun i:Fin H₀=>issue (sites i) (box i) (rowNames i) (argNames i)) m := by
  have limits := observedApply% (@Branch.fixed_header_room) [F, (inferInstance : Field F), cp, P, X, G, S, k, cut, tail, n, h, C, f, g, W, q, piece,
    ordinary, reset, branch, positive, room, shorten, c, j, rest, base, width, age,
    wFit, qFit, qh, template, sitesPositive, rawWords, headerRows, paidRows, pool, raw, w, K, fit,
    begin_, rom, peer, old, org, homes, other, arity, groups, stride, oldTags, lo, packWidth,
    paid, actors, boot, peerRows, space, rowCount, size, allRows]
  have headerLengths := observedApply% (@Branch.fixed_header_lengths) [F, (inferInstance : Field F), cp, P, X, G, S, k, cut, tail, n, h, C, f, g, W, q, piece,
    ordinary, reset, branch, positive, room, shorten, c, j, rest, base, width, age,
    wFit, qFit, qh, template, sitesPositive, rawWords, headerRows, pool, raw, headerRoom]
  have book := observedApply% (@Branch.observed_reel_book) [F, (inferInstance : Field F), cp, P, X, G, S, k, cut, tail, n, h, C, f, g, W, q, piece,
    ordinary, reset, branch, positive, room, shorten, c, j, rest, base, width, age,
    template, sitesPositive, rawWords, headerRows, paidRows, w, K, fit, begin_, rom, peer, old,
    org, homes, other, arity, groups, stride, oldTags, lo, packWidth, primitive, m,
    paid, actors, boot, oldPeers, raster, bookAt, retained, bookWidth, space]
  have counter := limits.1
  have high := limits.2.1
  have hosts := limits.2.2.1
  have sockets := limits.2.2.2
  have livePrivate := headerLengths.1
  have livePublic := headerLengths.2
  exact ⟨⟨counter,high,hosts,sockets⟩, ⟨livePrivate,livePublic⟩, book⟩

def wide_observed_printed (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w) (rowCount:(cfg).terminal.rows=paidRows)
    (allRows:(cfg).terminal.rows=K*W) (size:(cfg).terminal.pool=K*W)
    (retained : j≤S.groupWidth k tail S.length+k) (headerLow:head<start)
    (prior:∀u<(pre).weights begin_,out_ ((X_).after values expr m) u=primitive u)
    (late:dst<(pre).cohortEnd begin_) (ceiling:start≤fence) (tableSide:dst<org)
    (bookWidth:2^(pre).printBits<2^w)
    (pageReads:(pages₀).Reads m)
    (occ : ∀ (i : Fin (S.hostSize S.length)) (c' : Fin (groupsAt*2^k)),blankAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (measured (C_).layout (onBoard primitive) (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap)
      (A:=cap) (w:=p) (groups:=groupsAt) i) c' ≠ 0 ↔ ∃u,(b).target.chart ord rfl i u=c')
    (oldCells : ∀i u,PrimitiveReceipts (q:=q) (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i)
      u (venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
        (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
          (measured (C_).layout (onBoard primitive) (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) i)
        ((b).target.rawResident ord rfl i u))))
    (selected:c=(normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow history_)
    (admitted:accepted) (wideSeed:2*digitsNeeded s≤payloadBits) (fitsSeed:seedBase+(seedRows+1)<2^w)
    (topSeed:seedBase+(seedRows+1)≤lo) (positiveGrain:0<packWidth)
    (below:firstFree≤fence) (before:dst<wall)
    (lower:∀a∈shelves packWidth lo 0 steps,count a.ordinal<lo)
    (words:∀a∈steps,DescentPackedProfileTape.slots a.seats packWidth*packWidth<2^w)
    (fits:dst+1<2^w) (geometry:plan.Room w B₀ S.length fence wall)
    (top:wall+DescentExteriorShelf.span j rest s E₀+E₀<2^w)
    (apart:compact+32*DescentExteriorShelf.span j rest s E₀≤wall)
    (copyRoom:wall+17*DescentExteriorShelf.span j rest s E₀<2^w)
    (historyWords:∀a,lo≤a→a<compact→preflight a=checked a)
    (exterior:∀(col:Fin 17) (u:ℕ),u<DescentExteriorShelf.span j rest s E₀→
      preflight ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u)=
        checked ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u))
    (history:(b).path.savedRotations plan fence tail preflight)
    (window:∀u<extra,preflight (front+u)=checked (front+u))
    (valid:∀a,stagesOK (originalMatrix a) (publicRows X original a) (projected past_ false a) (projected past_ true a))
    (homeSide:dst<homes.base)
    (homeRead:∀i:Fin count₀,homes.read preflight (i.val:Computability.VPVNP.BurstRAM.Word w)=((oldHost i).val:Computability.VPVNP.BurstRAM.Word w))
    (rect:q*p=2^j*s) (positiveWord:0<w) (pack:2^j*s≤w)
    (leaves:(cfg).terminal.leaves=(cfg).terminal.pool)
    (budgetHeight:ℕ) (roleCount:0<tagCount) (spare:0<B) (smallPage:32*B≤budgetHeight)
    (smallRows:32*W≤budgetHeight) (smallCircuit:16*(q*p)≤budgetHeight)
    (large:10≤budgetHeight) (addressBits:budgetHeight/2≤w)
    (oldPeers:Fin H₀→Fin (b).target.placement.degree→Option (Fin H₀))
    (raster:DescentTerminalLocalPortBook.Rasters.Inputs («p»:=p) (bw:=(pre).printBits) (argc:=Nat.clog 2 (q+1))
      (b).target.placement host_ S (b).target.valid (b).target.order oldPeers rasters_ primitive)
    (bookAt:m=(pre).bookAtPrimitive begin_ peer old decode_ primitive)
    (peerRows:H₀*(pre).degree≤peer.size)
    (peerData:∀(i:Fin H₀)(l:Fin (pre).degree),primitive (peer.base+(i.val*(pre).degree+l.val))=
      (target (Branch.fixedRoster (eqs_).1 oldPeers i l):Computability.VPVNP.BurstRAM.Word w))
    (census:∀i:Fin H₀,primitive (((pre).census begin_).base+i.val)=(cohorts_ i:Computability.VPVNP.BurstRAM.Word w))
    (early:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).cohortEnd begin_)
    (tables:∀j<DescentTerminalDenseHeaderBoot.extent q p,primitive (rom+j)=DescentTerminalDenseHeaderBoot.back w q p j)
    (headerRoom:(cfg).terminal.pool≤headerRows)
    (romSide:rom+DescentTerminalDenseHeaderBoot.extent q p≤firstFree ∨ dst<rom)
    :
    (leaf).Printed (cfg) (arity:=arity) (groups:=groups) (stride:=stride) codec plan_ (C_).layout
      (meterAt post) bankSet (AddressPlan.chip (cfg) I_ base_) (paint ∘ Sum.inr) (payloadOut original)
      (paint ∘ Sum.inl) B := by
  have observedFacts := observedApply% (@observed_reel_facts) [F, (inferInstance : Field F), cp, P, X, G, S, k, cut, tail, n, h, C, f, g, W, q, piece, ordinary, reset,
    branch, positive, room, shorten, c, j, rest, base, width, age, wFit, qFit, qh, template, sitesPositive,
    rawWords, headerRows, paidRows, pool, raw, w, K, fit, begin_, rom, peer, old, org, homes, other, arity,
    groups, stride, oldTags, lo, packWidth, primitive, m, paid, actors, boot, space, rowCount, allRows, size,
    retained, bookWidth, oldPeers, raster, bookAt, peerRows, headerRoom]
  have counter := observedFacts.1.1
  have high := observedFacts.1.2.1
  have hosts := observedFacts.1.2.2.1
  have sockets := observedFacts.1.2.2.2
  have livePrivate := observedFacts.2.1.1
  have livePublic := observedFacts.2.1.2
  have book := observedFacts.2.2
  have columns := observedApply% (@Branch.fixed_reel_headers) [F, (inferInstance : Field F), cp, P, X, G, S, k, cut, tail, n, h, C, f, g, W, q, piece, ordinary, reset,
    branch, positive, room, shorten, c, j, rest, base, width, age, wFit, qFit, qh, template, sitesPositive,
    rawWords, headerRows, paidRows, pool, raw, w, K, payloadBits, fit, begin_, rom, peer, old, org, homes,
    other, arity, groups, stride, oldTags, lo, packWidth, all, head, short, fence, count, plan, primitive, m,
    original, paid, actors, boot, oldPeers, raster, bookAt, book, pageReads, peerRows, peerData, census,
    early, tables, livePrivate, livePublic, full, space, rowCount, allRows, size, counter, high, hosts,
    sockets, late, ceiling, romSide, selected, wideSeed, positiveWord, fitsSeed, topSeed, positiveGrain,
    below, before, lower, words, fits, geometry, top, apart, copyRoom, historyWords, exterior, history,
    window]
  exact observedApply% (@wide_reel_printed) [F, (inferInstance : Field F), cp, P, X, G, S, k, cut, tail, n, h, C, f, g, W, q, piece, ordinary, reset,
    branch, positive, room, shorten, c, j, rest, base, width, age, wFit, qFit, qh, template, sitesPositive,
    rawWords, headerRows, paidRows, pool, raw, w, K, payloadBits, fit, begin_, rom, peer, old, org, homes,
    other, arity, groups, stride, oldTags, codec, lo, packWidth, all, head, short, fence, count, plan,
    primitive, m, original, paid, actors, boot, romTop, full, space, rowCount, allRows, size, retained,
    headerLow, prior, late, ceiling, tableSide, book, pageReads, occ, oldCells, selected, admitted, wideSeed,
    fitsSeed, topSeed, positiveGrain, below, before, lower, words, fits, geometry, top, apart, copyRoom,
    historyWords, exterior, history, window, valid, homeSide, homeRead, rect, positiveWord, pack, leaves,
    budgetHeight, roleCount, spare, smallPage, smallRows, smallCircuit, large, addressBits, columns]

/-- The identical observed-history data also determine the complete private width scan. -/
theorem wide_observed_widths (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (_romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w) (rowCount:(cfg).terminal.rows=paidRows)
    (allRows:(cfg).terminal.rows=K*W) (size:(cfg).terminal.pool=K*W)
    (retained : j≤S.groupWidth k tail S.length+k) (_headerLow:head<start)
    (_prior:∀u<(pre).weights begin_,out_ ((X_).after values expr m) u=primitive u)
    (late:dst<(pre).cohortEnd begin_) (ceiling:start≤fence) (_tableSide:dst<org)
    (bookWidth:2^(pre).printBits<2^w)
    (pageReads:(pages₀).Reads m)
    (_occ : ∀ (i : Fin (S.hostSize S.length)) (c' : Fin (groupsAt*2^k)),blankAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (measured (C_).layout (onBoard primitive) (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap)
      (A:=cap) (w:=p) (groups:=groupsAt) i) c' ≠ 0 ↔ ∃u,(b).target.chart ord rfl i u=c')
    (_oldCells : ∀i u,PrimitiveReceipts (q:=q) (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i)
      u (venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
        (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
          (measured (C_).layout (onBoard primitive) (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) i)
        ((b).target.rawResident ord rfl i u))))
    (selected:c=(normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow history_)
    (_admitted:accepted) (wideSeed:2*digitsNeeded s≤payloadBits) (fitsSeed:seedBase+(seedRows+1)<2^w)
    (topSeed:seedBase+(seedRows+1)≤lo) (positiveGrain:0<packWidth)
    (below:firstFree≤fence) (before:dst<wall)
    (lower:∀a∈shelves packWidth lo 0 steps,count a.ordinal<lo)
    (words:∀a∈steps,DescentPackedProfileTape.slots a.seats packWidth*packWidth<2^w)
    (fits:dst+1<2^w) (geometry:plan.Room w B₀ S.length fence wall)
    (top:wall+DescentExteriorShelf.span j rest s E₀+E₀<2^w)
    (apart:compact+32*DescentExteriorShelf.span j rest s E₀≤wall)
    (copyRoom:wall+17*DescentExteriorShelf.span j rest s E₀<2^w)
    (historyWords:∀a,lo≤a→a<compact→preflight a=checked a)
    (exterior:∀(col:Fin 17) (u:ℕ),u<DescentExteriorShelf.span j rest s E₀→
      preflight ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u)=
        checked ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u))
    (history:(b).path.savedRotations plan fence tail preflight)
    (window:∀u<extra,preflight (front+u)=checked (front+u))
    (_valid:∀a,stagesOK (originalMatrix a) (publicRows X original a) (projected past_ false a) (projected past_ true a))
    (_homeSide:dst<homes.base)
    (_homeRead:∀i:Fin count₀,homes.read preflight (i.val:Computability.VPVNP.BurstRAM.Word w)=((oldHost i).val:Computability.VPVNP.BurstRAM.Word w))
    (_rect:q*p=2^j*s) (positiveWord:0<w) (_pack:2^j*s≤w)
    (_leaves:(cfg).terminal.leaves=(cfg).terminal.pool)
    (budgetHeight:ℕ) (_roleCount:0<tagCount) (_spare:0<B) (_smallPage:32*B≤budgetHeight)
    (_smallRows:32*W≤budgetHeight) (_smallCircuit:16*(q*p)≤budgetHeight)
    (_large:10≤budgetHeight) (_addressBits:budgetHeight/2≤w)
    (oldPeers:Fin H₀→Fin (b).target.placement.degree→Option (Fin H₀))
    (raster:DescentTerminalLocalPortBook.Rasters.Inputs («p»:=p) (bw:=(pre).printBits) (argc:=Nat.clog 2 (q+1))
      (b).target.placement host_ S (b).target.valid (b).target.order oldPeers rasters_ primitive)
    (bookAt:m=(pre).bookAtPrimitive begin_ peer old decode_ primitive)
    (peerRows:H₀*(pre).degree≤peer.size)
    (peerData:∀(i:Fin H₀)(l:Fin (pre).degree),primitive (peer.base+(i.val*(pre).degree+l.val))=
      (target (Branch.fixedRoster (eqs_).1 oldPeers i l):Computability.VPVNP.BurstRAM.Word w))
    (census:∀i:Fin H₀,primitive (((pre).census begin_).base+i.val)=(cohorts_ i:Computability.VPVNP.BurstRAM.Word w))
    (early:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).cohortEnd begin_)
    (tables:∀j<DescentTerminalDenseHeaderBoot.extent q p,primitive (rom+j)=DescentTerminalDenseHeaderBoot.back w q p j)
    (headerRoom:(cfg).terminal.pool≤headerRows)
    (romSide:rom+DescentTerminalDenseHeaderBoot.extent q p≤firstFree ∨ dst<rom)
    :
    DescentTerminalDenseHeaderRAM.Reads (plan_).emit.plane.header
      (DescentTerminalHeaderGroups.padded (n:=headerRows) privateTape_) post := by
  have observedFacts := observedApply% (@observed_reel_facts) [F, (inferInstance : Field F), cp, P, X, G, S, k, cut, tail, n, h, C, f, g, W, q, piece, ordinary, reset,
    branch, positive, room, shorten, c, j, rest, base, width, age, wFit, qFit, qh, template, sitesPositive,
    rawWords, headerRows, paidRows, pool, raw, w, K, fit, begin_, rom, peer, old, org, homes, other, arity,
    groups, stride, oldTags, lo, packWidth, primitive, m, paid, actors, boot, space, rowCount, allRows, size,
    retained, bookWidth, oldPeers, raster, bookAt, peerRows, headerRoom]
  have counter := observedFacts.1.1
  have high := observedFacts.1.2.1
  have hosts := observedFacts.1.2.2.1
  have sockets := observedFacts.1.2.2.2
  have livePrivate := observedFacts.2.1.1
  have livePublic := observedFacts.2.1.2
  have book := observedFacts.2.2
  have made_ := observedApply% (@Branch.fixed_reel_header_records) [F, (inferInstance : Field F), cp, P, X, G, S, k, cut, tail, n, h, C, f, g, W, q, piece, ordinary,
    reset, branch, positive, room, shorten, c, j, rest, base, width, age, wFit, qFit, qh, template,
    sitesPositive, rawWords, headerRows, paidRows, pool, raw, w, K, payloadBits, fit, begin_, rom, peer,
    old, org, homes, other, arity, groups, stride, oldTags, lo, packWidth, all, head, short, fence,
    count, plan, primitive, m, original, paid, actors, boot, oldPeers, raster, bookAt, book, pageReads,
    peerRows, peerData, census, early, tables, livePrivate, livePublic, full, space, rowCount, allRows,
    size, counter, high, hosts, sockets, late, ceiling, romSide, selected, wideSeed, positiveWord,
    fitsSeed, topSeed, positiveGrain, below, before, lower, words, fits, geometry, top, apart, copyRoom,
    historyWords, exterior, history, window]
  exact made_.2


end FixedHeaders

end
end Hierarchy.DescentSixParty.SeedNamed

-- The dependent signatures in this file are expensive to index for library suggestions.
-- Limit the exclusion to this export so importing modules retain their usual search settings.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun prior =>
    ["fixed_header_room", "fixed_header_lengths", "fixed_reel_widths",
     "fixed_pair_bound", "observed_reel_book", "reel_occupation_from_words",
     "reel_live_from_occupation", "reel_population_from_words", "reel_public_arity",
     "reel_receipts_from_shelf", "reel_ports_from_shelf", "reel_operands_from_shelf",
     "wide_observed_widths"] ++ prior

end OAI
