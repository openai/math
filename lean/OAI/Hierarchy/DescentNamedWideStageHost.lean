import OAI.Hierarchy.DescentNamedWideFlightSources
import OAI.Hierarchy.DescentNamedWideChoiceFactors
import OAI.Hierarchy.DescentNamedCopyPin
import OAI.Hierarchy.DescentCanonicalSeedHistory
import OAI.Hierarchy.DescentPhysicalStageHost

namespace OAI
/-! # Simultaneous physical host for the original normalized paid run -/
namespace Hierarchy.DescentSixParty.SeedNamed
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
open DescentTerminalHost DescentTerminalThreshold DescentTerminalLast DescentTerminalRAM
open DescentTerminalReadout DescentTerminalFixedISAHost CorrectionFrame DescentTerminalChipPins
open ThreeFlat Routing Diagonal TraceBanks
open Computability.VPVNP.RAMMemory TaggedShorterControlHistory Tagged Tagged.SortLift TaggedShorterHistoryOrder
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 32768
set_option maxHeartbeats 7000000
set_option cleanup.letToHave false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin Branch.archive Branch.bundleShape

attribute [local irreducible] DescentTerminalLast.program DescentTerminalLast.ticks
  DescentTerminalChipRuntime.program DescentTerminalChipRuntime.clocks
  complete ProtocolRAM.machine CheapISA.machine

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
local instance : Fintype (chart).Pin := (chart).finite
local notation "fmt" => Branch.geometryFormat G S k g p tail q R rot headerRows paidRows
local notation "pre" => Branch.preflightSpec X G S k g p tail ({fmt with binSize:=W}:Branch.PreflightFormat)
variable (begin_ rom : ℕ) (peer:Bank) (old:Fin ((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).scalar.blocks→Fin (2*((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).cap)→Bank)
    (org:ℕ) (homes:Bank) (other:AddressPlan.Input)
local notation "arity" => max 8 (2^S.capGain)
local notation "groups" => cap
local notation "stride" => R
local notation "oldTags" => DescentPrimitivePalette.colors G s Z rot
local notation "codec" => DescentPrimitivePalette.codec (G:=G) («s»:=s) («Z»:=Z) rot
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

variable (head : ℕ) (short : ((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).vertices*DescentTerminalVertexFields.span (((⟨q,(DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).publicArity (((⟨q,(DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).roles (((⟨q,(DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).privateWords (((⟨q,(DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).nodes (((⟨q,(DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).addresses (((⟨q,(DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(S.epochPower^S.localTokenExponent),(NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))),(W*piece),(S.groupCount S.length)⟩:Home.Format))).piece≤(((Branch.preflightSpec X G S k g (W*piece) tail ({(Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR))) (RotorSpec.ofRates reset) headerRows paidRows) with binSize:=W}:Branch.PreflightFormat))).pageBits))
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
local notation "ranks" => DescentTerminalChronologicalChip.charts («arity»:=arity) («groups»:=groups) («stride»:=stride)
  hostGraph (leaf).home (leaf).native (leaf).external (leaf).nodes (leaf).ops
  (leaf).bit (leaf).shape positive (leaf).birth (leaf).hidden codec
local notation "hH" => fun i v => (DescentTerminalRestrictedRows.hidden_bound (leaf).bit (leaf).shape
  positive ((ord).node i v)).trans ((leaf).countsFit ((ord).node i v))
local notation "hN" => fun i v => (leaf).atoms ((ord).node i v)
local notation "hA" => fun i v u => (((leaf).shape ((ord).node i v)).recipe_refs positive u).symm ▸
  (leaf).refs ((ord).node i v) u

local notation "onBoard" mu:arg => Suffix.sockets cfg plan_ ((A_).mount (loaded mu))
local notation "nativeCandidate" mu:arg => ((A_).mount (loaded mu))
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

variable (middle:Procedure w) (cost:ℕ)
local notation "initialFlag" => seedBase+seedRows
local notation "foldSites" => controlsAt firstFree lo G.C packWidth steps count (fun _=>initialFlag)
local notation "prefixCode" => DescentWideSeedFlags.check X S.copies s payloadBits w
local notation "paidCode" => (((((prefixCode).seq (middle.seq (relocate j rest s E₀ w compact wall))).seq
    (plan.program j rest s E₀ w B₀ S.length wall)).seq (fold w initialFlag dst foldSites)).seq
    (AddressPlan.clock V cfg I_ R_ start head short literal (bw:=w)))
local notation "paidTime" => ((4+(seedRows+1)*66+(cost+(4+18*(17*DescentExteriorShelf.span j rest s E₀))))+
    (10+((4+58*S.length)+(4+16*E₀))))+bill initialFlag dst foldSites+AddressPlan.time V cfg I_ R_ start head
local notation "pinMap" => DescentTerminalFullPins.widePins X S.copies s payloadBits w seed lo G.C packWidth steps count₀ codes
local notation "finalMem" => AddressPlan.output V cfg I_ R_ start head short literal post
local notation "flag" => flagAt (j:=j) (r:=rest) (t:=s) (e:=E₀) wall
local notation "charge" => fun v=> (normalizedLeaf X G S ordinary reset branch positive room shorten v
  base width age wFit qFit qh cfg pool raw).debt cfg
local notation "active" => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow history_
local notation "reachedBranch" => issued X G S ordinary reset branch positive room shorten active
local notation "rawTrace" => (reachedBranch).path.selections

local notation "extPins" => Port ((S.copies*s)*P) (copiesWidth (S.copies*s) X.width)
local notation "view" x₀:arg => Branch.copyInput X s power x₀
variable (primitiveBank booksBank:((Port ((S.copies*(S.firstWidth G.b (W*piece)))*P) (copiesWidth (S.copies*(S.firstWidth G.b (W*piece))) X.width))→Bool)→((DescentTerminalFullPins.Candidate (((normalizedPackedChart X G S ordinary reset branch positive room shorten w fit)).Pin⊕Hidden (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b (W*piece))) K W q piece rawWords)→Bool)→Memory w) (machine:sliceWidth W q piece≤w)
local notation "sourceAt" x₀:arg z₀:arg c₀:arg => WideObservedSources (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (pool:=pool) (raw:=raw) (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom)
      (peer:=peer) (old:=old) (org:=org) (homes:=homes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=fence) (count:=count) (plan:=plan) («codec»:=codec) (short:=short) (all:=z₀) (c:=c₀)
      (primitive:=(primitiveBank x₀ z₀)) (m:=(booksBank x₀ z₀)) (original:=view x₀)
local notation "nativeAt" x₀:arg z₀:arg => WideHeldFlightSources (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom)
      (peer:=peer) (old:=old) (org:=org) (homes:=homes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=fence) (count:=count) (plan:=plan) (all:=z₀) (m:=(booksBank x₀ z₀)) (original:=view x₀) (middle:=middle)
      (cost:=cost) («arity»:=arity) («groups»:=groups) («stride»:=stride) («oldTags»:=oldTags) (K:=K)
local notation "leafAt" u:arg => normalizedLeaf X G S ordinary reset branch positive room shorten u base width
  age wFit qFit qh cfg pool raw
local notation "bootFor" x₀:arg z₀:arg => Root.appended front extra
    (Root.widePackedImage X S.copies s payloadBits w seed lo G.C packWidth steps compact
      (DescentExterior.publicRows X (view x₀)) (Sum.elim (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inl)
      (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inr)))
    (DescentTerminalPublicIdentity.back (z₀ ∘ DescentTerminalFullPins.chip) w codes count₀)
local notation "postFor" x₀:arg z₀:arg => oldStateAt firstFree lo G.C packWidth initialFlag steps count
  (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inl)
  (plan.result j rest s E₀ B₀ S.length wall
    (relocated j rest s E₀ compact wall (out_ ((X_).after values expr (booksBank x₀ z₀)))))
local notation "finalFor" x₀:arg z₀:arg => AddressPlan.output V cfg I_ R_ start head short literal (postFor x₀ z₀)
local notation "cols" => AddressPlan.observationColumns V cfg I_ R_ start head dst

local notation "candidatePrior" => wideChoicePrior X G S ordinary reset branch positive room shorten w fit base width
local notation "seedNet" => wideChoiceCircuit (K:=K) (W:=W) (q:=q) (piece:=piece) X G S ordinary reset branch positive room shorten w fit (j:=j) (rest:=rest) cfg
local notation "tableValue" => DescentTerminalChronologicalBooks.menu (fun key args=>
  bundleScalar p (DescentPrimitivePalette.dictionary («s»:=s) («Z»:=Z) G rot reset.menu p)
    ((DescentBundleTagKeys.codec codec arity groups p stride).read key) args)
local notation "numBins" => DescentTerminalChronologicalBooks.Keys q tagCount cap nodeCap cap p venues p
local notation "numSlots" => (cfg).terminal.pool
local notation "cpu" => AddressPlan.chip cfg I_ base_
local notation "tapeDesc" => (cols).tape cpu (K*W)
local notation "widthWord" => q*p
local notation "initMap" => fun i=>(pinMap i).map (Sum.map (Branch.copyPin X s power) id) id

variable (counterBits lower upper:ℕ) (Cbank:DescentCensusRAM.Banks w (((Branch.exteriorShape template (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b (W*piece)) rawWords headerRows (S.hostSize S.length) sitesPositive)).terminal.pool) (DescentTerminalChronologicalBooks.Keys q (DescentBundleTagKeys.capacity (DescentPrimitivePalette.colors G (S.firstWidth G.b (W*piece)) (S.grainAt G.b (W*piece) 0) (RotorSpec.ofRates reset)) (max 8 (2^S.capGain)) ((NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))) (W*piece) ((max 1 (max reset.bitsR (C*reset.bitsR))))) (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (S.epochPower^S.localTokenExponent) (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (W*piece) (S.groupCount S.length*2^k) (W*piece)))
local notation "fed" => (paidCode).seq (DescentTerminalChipRuntime.program cpu bankSet w (K*W) numSlots)
local notation "whole" => complete tapeDesc Cbank (cut:=lower) (stop:=upper) (rows:=rawWords) (word:=widthWord) fed
local notation "pcs" => (whole).labels+3
local notation "regs" => (whole).registers+1
local notation "binsPaid" => Fintype.card Unit+numBins+1
local notation "obs" => rawWords+binsPaid
local notation "fuel" => paidTime+clocks (K*W) numSlots+ticks tapeDesc Cbank rawWords widthWord+3
local notation "runtime" => CheapISA.hostFuel fuel

include machine in
theorem wide_paid_stage_host
    (native:∀(x₀:extPins→Bool)(z₀:Full→Bool),nativeAt x₀ z₀)
    (measured:∀(x₀:extPins→Bool)(z₀:Full→Bool)(c₀:(last).Choice),
      candidatePrior x₀ (erased z₀)=some c₀→sourceAt x₀ z₀ c₀)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (headerRoom:(cfg).terminal.pool≤headerRows) (headersPositive:0<headerRows)
    (chipRoom:DescentTerminalChipRuntime.Room cpu bankSet w (K*W) numSlots) (dataRoom:q*p≤w)
    (word:Nat.log 2 (NativeBranch.privateMax G S p)+1≤w) (wordPositive:0<w)
    (ready:Ready tapeDesc Cbank lower upper rawWords widthWord)
    (hp:pcs≤2^(w+1)) (hr:regs≤2^(w+1)) (initialRoom:firstFree≤2^w)
    (ht:runtime+obs≤2^(CheapISA.width w+1)) (before:∀i,(cols).seed i<lower)
    (traceWord:depth widthWord≤w+1) (counters:counterBits≤w+1) (positiveCounter:0<counterBits)
    (seedFit:∀t,charge t<2^w)
    (countsFit:∀t,Fintype.card (DescentTerminalSeedFactors.Occurs (fun _:Unit=>charge t) (Fin numSlots))<2^counterBits)
    (budget rate:ℕ) (height:4≤budget) (widthRate:w≤rate*budget)
    (addr:(CheapISA.dataBase pcs regs+firstFree)+(runtime+obs)≤2^(3*budget))
    (Y:Approximation F cp (Tagged.pins budget budget))
    (M₀ J₀ price:ℕ)
    (bill_:(4*((seedNet).cells+(seedNet).internal)+9*(rawWords*widthWord)+binsPaid*counterBits+
      Fintype.card Full+Fintype.card extPins+
      (257*(1000*(2*(7*(rate+6))+2)*(2*4^7+1))+256*fixedISAPrice*(rate+6))*
        (pcs+regs+firstFree+fuel+obs+2^budget+1)*(budget+1))*2^J₀≤price*(S.copies*s)*(M₀+2^J₀*E₀)) :
    ∃calls:ℕ,∃H:Host F cp ((S.copies*s)*P) (Sockets (List.replicate calls (CollapseOracle.tagCall budget Y))),
      Agrees (independentCopies (S.copies*s) X) (tableApprox H.width (exactValue _ H)) ∧
      hostSize H*2^J₀≤price*(S.copies*s)*(M₀+2^J₀*E₀) := by
  have obsAt (x₀:extPins→Bool) := wide_observed_current
    (W:=W) (q:=q) (piece:=piece) (K:=K) (w:=w) («arity»:=arity) («groups»:=groups)
    («stride»:=stride) («oldTags»:=oldTags) (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset)
    (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) (base:=base) (width:=width)
    (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh) (template:=template) (sitesPositive:=sitesPositive)
    (rawWords:=rawWords) (headerRows:=headerRows) (paidRows:=paidRows) (pool:=pool) (raw:=raw)
    (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom) (peer:=peer) (old:=old)
    (org:=org) (homes:=homes) (other:=other) («codec»:=codec) (lo:=lo) (packWidth:=packWidth)
    (head:=head) (short:=short) (fence:=fence) (count:=count) (plan:=plan) (original:=view x₀)
    (middle:=middle) (cost:=cost) (primitiveBank:=primitiveBank x₀) (booksBank:=booksBank x₀)
    (machine:=machine) (native x₀) (measured x₀) romTop headerRoom headersPositive
  apply DescentTerminalFixedISAHost.physical_stage_host_dependent
    (F:=F) (I:=Unit) (A:=(chart).Pin ⊕ Hidden E₀ j rest s)
    («arity»:=cp) (pins:=P) («groups»:=S.groupCount 0) (radix:=k) («R»:=S.copies) («s»:=s)
    (Gheight:=S.height) (dateDepth:=h) (menu:=C)
    (depthBound:=GroupStage.depthBound (atRound S.rounds) n f g) (rounds:=S.rounds)
    (u:=(1 / ((s : ℝ) * (S.epochPower^S.priceExponent : ℝ))) * (S.epochPower^S.priceExponent : ℝ))
    (ε:=((S.initialSites*S.copies : ℕ) : ℝ) / S.epochPower)
    (K:=K) (Cap:=W) (q:=q) (piece:=piece) (w:=w) (S0:=firstFree)
    (rows:=rawWords) (slots:=numSlots) (bins:=numBins) (word:=widthWord)
    (W:=counterBits) (cut:=lower) (stop:=upper) (X:=X) (G:=G) (hu:=by positivity) (he:=by positivity) (epochPlan:=(cert).choose)
    (digits:=S.initialDigits ordinary.radix) (D:=cols) (P0:=cpu) (L0:=bankSet)
    (chipRoom:=chipRoom) (dataRoom:=dataRoom) (positive:=wordPositive) (C:=Cbank) (ready:=ready)
    (Q:=paidCode) (hp:=hp) (hr:=hr) (st:=(0:Computability.VPVNP.BurstRAM.Word w)) (initialRoom:=initialRoom) (time:=paidTime)
    (ht:=ht) (before:=before) (short:=traceWord) (width:=counters) (init:=initMap)
    (seedCircuit:=seedNet) (original:=fun _:Unit=>(2:F)) (table:=tableValue)
    budget rate height widthRate addr Y (fun x₀ z₀=>bootFor x₀ z₀) ?_
    (fun x₀ z₀=>finalFor x₀ z₀) (fun x₀=>(obsAt x₀).2.1) ((obsAt fun _=>false).2.2.1)
    (fun x₀ _=>candidatePrior x₀) (fun x₀ _=>wideChoice_single X G S ordinary reset branch positive room shorten w fit base width x₀)
    (fun x₀ c₀ pay=>(leafAt c₀).contents cfg (K₀:=K) pay (packagePins X S.copies s x₀))
    (fun c₀=>DescentTerminalCableOrder.edgeCode ((last).state c₀).graph (leafAt c₀).home (leafAt c₀).native)
    (fun c₀=>(leafAt c₀).volume) (Nat.mul_pos qh positive) positiveCounter (fun t (_:Unit)=>charge t)
    (fun x₀ c₀ pay=>(leafAt c₀).keys cfg («arity»:=arity) («groups»:=groups) («stride»:=stride) codec machine pay
      (packagePins X S.copies s x₀)) (fun c₀ _=>seedFit c₀) countsFit ?_ ?_ M₀ J₀ price bill_
  · intro x₀ z₀ i
    exact (Branch.copyPin_eval X s power x₀ z₀ (pinMap i)).trans ((obsAt x₀).1 z₀ i)
  · intro x₀
    let installedAt (y : extPins → Bool) : Prop :=
      Current cols cpu bankSet (fun (_ : RowBit rawWords (q*p) → Bool) => candidatePrior x₀)
        (fun u pay => (leafAt u).contents cfg (K₀:=K) pay (packagePins X S.copies s y))
        (fun u => ∑ e, ((last).state u).graph.width e) (fun u (_ : Unit) => charge u)
        (fun u pay => (leafAt u).keys cfg («arity»:=arity) («groups»:=groups) («stride»:=stride)
          codec machine pay (packagePins X S.copies s y)) (fun z₀ => finalFor x₀ z₀)
    exact Eq.mp (congrArg installedAt (Branch.copyInput_back X s power x₀)) (obsAt x₀).2.2.2
  · intro x₀ z₀ c₀ pay selected
    exact wideChoice_factors (K:=K) X G S ordinary reset branch positive room shorten w fit base width cfg
      age wFit qFit qh pool raw dataRoom machine word x₀ z₀ c₀ pay selected

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
