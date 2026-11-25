import OAI.Hierarchy.DescentTerminalPreflightPointerPages
import OAI.Hierarchy.DescentTerminalObservedRoster
import OAI.Hierarchy.DescentPublicEarlyReel
import OAI.Hierarchy.DescentEarnedScalarArguments
import OAI.Hierarchy.DescentNamedTerminalPointerPins
import OAI.Hierarchy.DescentNamedShelfWidths
import OAI.Hierarchy.DescentTerminalLateReelRoom
import OAI.Hierarchy.DescentTerminalPreflightEarlier
import OAI.Hierarchy.DescentWideSeedOriginalInvoice
import OAI.Hierarchy.DescentExteriorLateReel
import OAI.Hierarchy.DescentTerminalFundedReadback
import OAI.Hierarchy.DescentNamedSeedCounted
import OAI.Hierarchy.DescentNamedWideReelPrinted
import OAI.Hierarchy.DescentNamedWidePaidFlight
import OAI.Hierarchy.DescentTerminalPlacedFlight

namespace OAI
/-! # Original dated inputs for the accepted leaf and its cable histogram -/
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
set_option maxHeartbeats 1500000
set_option cleanup.letToHave false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin Branch.archive Branch.bundleShape

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

local notation "onBoard" mu => Suffix.sockets cfg plan_ ((A_).mount (loaded mu))
local notation "nativeCandidate" mu => ((A_).mount (loaded mu))
local notation "memAt" mu => DescentTerminalEmitter.issued (cfg).terminal (plan_).emit (plan_).directory
  (maskedMem (C_).layout (plan_).directory (S.hostSize S.length) (onBoard mu))

local notation "bookSeed" => (pre).reachedRoutes begin_ rom q piece W K codes front peer old total modulo homes boundary (cfg) V other T
local notation "emptyCode" => (DescentTerminalChronologicalBooks.empty q tagCount cap nodeCap cap p venues p).val
local notation "bankSet" => DescentTerminalChipBootWords.chipBanks (K:=K) (W:=W) (q:=q)
  («p»:=piece) codes (plan_).emit front emptyCode
local notation "meterAt" mu => (A_).mount (loaded mu)
local notation "payloadOut" input => packagePins X S.copies s (Branch.copyInput X s (power).symm input)

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



local notation "layoutAt" => (fun a=>(Branch.publicLayout X G S (issued X G S ordinary reset branch positive room shorten a) positive base width))
local notation "which" => proposed (chart).read layoutAt (publicRows X original) (all ∘ DescentTerminalFullPins.history)

local notation "coord_" => (
  payloadBits≤w ∧ q*p≤w ∧ 2*digitsNeeded s≤payloadBits ∧ 0<w ∧ seedBase+(seedRows+1)<2^w ∧
  seedBase+(seedRows+1)≤lo ∧ 0<packWidth ∧ firstFree≤fence ∧ dst<wall ∧
  (∀a∈shelves packWidth lo 0 steps,count a.ordinal<lo) ∧
  (∀v∈steps,DescentPackedProfileTape.slots v.seats packWidth*packWidth<2^w) ∧ dst+1<2^w ∧
  plan.Room w B₀ S.length fence wall ∧ wall+DescentExteriorShelf.span j rest s E₀+E₀<2^w ∧
  compact+32*DescentExteriorShelf.span j rest s E₀≤wall ∧ wall+17*DescentExteriorShelf.span j rest s E₀<2^w ∧
  2^j*s≤w ∧ (∀v∈steps,DescentTerminalEpochBits.width v.C*packWidth≤w) ∧
  (∀f,((R_).bank f).base+((R_).bank f).size≤ start) ∧ head<start ∧
  AddressPlan.Earlier cfg I_ base_ (C_).layout w ∧ AddressPlan.last V cfg I_ R_ start<2^w ∧ dst<start ∧
  (head<fence ∧ (head<firstFree ∨ dst<head)) ∧
  (∀f u,u<((R_).bank f).size→let addr:=((R_).bank f).base+u
    addr<fence ∧ (addr<firstFree ∨ dst<addr)))

/-- Static word and arena layout before and after the funded runtime. -/
def WideFlightCoordinates : Prop := coord_

/- Only earlier, physically measured word ranges and fixed sizes of the purchase are required.
The selected routed branch and both exterior rasters are recovered from the actual checked input. -/
local notation "rawRowsChecking" actorCheck:arg readCheck:arg nodeTest:arg conditions:arg => (  ∃paid:Fin (pre).scalar.blocks→Bank,
  ∃actors:Fin (pre).scalar.blocks→Bank,
  ∃budgetHeight:ℕ,
  ∃oldPeers:Fin H₀→Fin (b).target.placement.degree→Option (Fin H₀),
  ((pre).Before begin_ paid actors old peer total modulo homes boundary) ∧
  (rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_) ∧
  (front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start) ∧
  (readCheck (AddressPlan.last V cfg I_ R_ start<2^w)) ∧
  ((cfg).terminal.rows=paidRows) ∧
  ((cfg).terminal.rows=K*W) ∧
  ((cfg).terminal.pool=K*W) ∧
  (readCheck (j≤S.groupWidth k tail S.length+k)) ∧
  (readCheck (head<start)) ∧
  (∀u<(pre).weights begin_,out_ ((X_).after values expr m) u=primitive u) ∧
  (dst<(pre).cohortEnd begin_) ∧
  (start≤fence) ∧
  (dst<org) ∧
  (2^(pre).printBits<2^w) ∧
  ((pages₀).Reads m) ∧
  (actorCheck (∀ i c',blankAt (measured (C_).layout (onBoard primitive) (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap)
      (A:=cap) (w:=p) (groups:=groupsAt) i) c' ≠ 0 ↔ ∃u,(b).target.chart ord rfl i u=c')) ∧
  (∀ (i : Fin (S.hostSize S.length)) (u : Fin (Fintype.card ((ord).Nodes i))), PrimitiveReceipts (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i)
      u (venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (C_).layout (onBoard primitive) i)
        ((b).target.rawResident ord rfl i u))) nodeTest) ∧
  (readCheck (2*digitsNeeded s≤payloadBits)) ∧
  (readCheck (seedBase+(seedRows+1)<2^w)) ∧
  (readCheck (seedBase+(seedRows+1)≤lo)) ∧
  (readCheck (0<packWidth)) ∧
  (readCheck (firstFree≤fence)) ∧
  (readCheck (dst<wall)) ∧
  (readCheck (∀a∈shelves packWidth lo 0 steps,count a.ordinal<lo)) ∧
  (readCheck (∀a∈steps,DescentPackedProfileTape.slots a.seats packWidth*packWidth<2^w)) ∧
  (readCheck (dst+1<2^w)) ∧
  (readCheck (plan.Room w B₀ S.length fence wall)) ∧
  (readCheck (wall+DescentExteriorShelf.span j rest s E₀+E₀<2^w)) ∧
  (readCheck (compact+32*DescentExteriorShelf.span j rest s E₀≤wall)) ∧
  (readCheck (wall+17*DescentExteriorShelf.span j rest s E₀<2^w)) ∧
  (readCheck (∀a,lo≤a→a<compact→preflight a=checked a)) ∧
  (readCheck (∀(col:Fin 17) (u:ℕ),u<DescentExteriorShelf.span j rest s E₀→
      preflight ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u)=
        checked ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u))) ∧
  (readCheck ((b).path.savedRotations plan fence tail preflight)) ∧
  (readCheck (∀u<extra,preflight (front+u)=checked (front+u))) ∧
  (dst<homes.base) ∧
  (readCheck (∀i:Fin count₀,homes.read preflight (i.val:Computability.VPVNP.BurstRAM.Word w)=((oldHost i).val:Computability.VPVNP.BurstRAM.Word w))) ∧
  (q*p=2^j*s) ∧
  (readCheck (0<w)) ∧
  (readCheck (2^j*s≤w)) ∧
  ((cfg).terminal.leaves=(cfg).terminal.pool) ∧
  (0<tagCount) ∧
  (0<B) ∧
  (32*B≤budgetHeight) ∧
  (32*W≤budgetHeight) ∧
  (16*(q*p)≤budgetHeight) ∧
  (10≤budgetHeight) ∧
  (budgetHeight/2≤w) ∧
  (conditions oldPeers) ∧
  (m=(pre).bookAtPrimitive begin_ peer old decode_ primitive) ∧
  (H₀*(pre).degree≤peer.size) ∧
  (∀(i:Fin H₀)(l:Fin (pre).degree),primitive (peer.base+(i.val*(pre).degree+l.val))=
      (target (Branch.fixedRoster (eqs_).1 oldPeers i l):Computability.VPVNP.BurstRAM.Word w)) ∧
  (readCheck (∀i:Fin H₀,primitive (((pre).census begin_).base+i.val)=(cohorts_ i:Computability.VPVNP.BurstRAM.Word w))) ∧
  (rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).cohortEnd begin_) ∧
  (∀j<DescentTerminalDenseHeaderBoot.extent q p,primitive (rom+j)=DescentTerminalDenseHeaderBoot.back w q p j) ∧
  ((cfg).terminal.pool≤headerRows) ∧
  (rom+DescentTerminalDenseHeaderBoot.extent q p≤firstFree ∨ dst<rom))

/-- The same dated inputs with an independently supplied physical condition on the roster. -/
def WideObservedSourcesWith (conditions : (Fin H₀→Fin (b).target.placement.degree→Option (Fin H₀))→Prop) (maskTest : Prop→Prop := id) (reelTest : Prop→Prop := id) (nodeTest : Prop→Prop := id) :
    Prop := rawRowsChecking maskTest reelTest nodeTest conditions

local notation "rowsChecking" actorCheck:arg readCheck:arg nodeTest:arg conditions:arg =>
  WideObservedSourcesWith (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch)
    (positive:=positive) (room:=room) (shorten:=shorten) (base:=base) (width:=width) (age:=age)
    (wFit:=wFit) (qFit:=qFit) (qh:=qh) (template:=template) (sitesPositive:=sitesPositive)
    (rawWords:=rawWords) (headerRows:=headerRows) (paidRows:=paidRows) (pool:=pool) (raw:=raw)
    (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom) (peer:=peer) (old:=old)
    (org:=org) (homes:=homes) (other:=other) (codec:=codec) (lo:=lo) (packWidth:=packWidth) (all:=all)
    (head:=head) (short:=short) (fence:=fence) (count:=count) (plan:=plan) (primitive:=primitive)
    (m:=m) (original:=original) (c:=c) conditions actorCheck readCheck nodeTest
local notation "rowsTesting" actorCheck:arg readCheck:arg conditions:arg => rowsChecking actorCheck readCheck id conditions
local notation "rowsTestingActor" actorCheck:arg conditions:arg => rowsTesting actorCheck id conditions
local notation "sourceRowsFor" conditions:arg => rowsTestingActor id conditions
local notation "sourceRows" => sourceRowsFor (fun oldPeers=>DescentTerminalLocalPortBook.Rasters.Inputs («p»:=p) (bw:=(pre).printBits) (argc:=Nat.clog 2 (q+1))
      (b).target.placement host_ S (b).target.valid (b).target.order oldPeers rasters_ primitive)




/-- Assemble the named site pages from the single original checked execution, the
resident header and the public scalar invoice.  The private book header is issued on
the same raster as the primitive recorder. -/
theorem wide_earned_site_pages_of_layout (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start)
    (rowsEq:(cfg).terminal.rows=paidRows) (localRows:(cfg).terminal.rows=K*W) (roomPool:(cfg).terminal.pool=K*W)
    («copied»:∀u<(pre).weights begin_,out_ ((X_).after values expr m) u=primitive u)
    (roof:dst<(pre).cohortEnd begin_) (fenceRoom:start≤fence) (beforeLuts:dst<org)
    (lut:(pages₀).Reads m) (homeStart:dst<homes.base)
    (leafCount:(cfg).terminal.leaves=(cfg).terminal.pool)
    (scalar:EarnedScalarArguments j s p q W tagCount B (pre).printBits h w)
    (book:m=(pre).bookAtPrimitive begin_ peer old decode_ primitive)
    (seats:H₀*(pre).degree≤peer.size)
    (ports:∀(i:Fin H₀)(l:Fin (pre).degree),primitive (peer.base+(i.val*(pre).degree+l.val))=
      (target (Branch.fixedRoster (eqs_).1 ((b).target.terminalRoster (b).target.valid.host) i l):Computability.VPVNP.BurstRAM.Word w))
    (header:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).cohortEnd begin_)
    (dense:∀j<DescentTerminalDenseHeaderBoot.extent q p,primitive (rom+j)=DescentTerminalDenseHeaderBoot.back w q p j)
    (poolHeader:(cfg).terminal.pool≤headerRows) (under:rom+DescentTerminalDenseHeaderBoot.extent q p≤firstFree)
    (cells:∀ (i : Fin (S.hostSize S.length)) (u : Fin (Fintype.card ((ord).Nodes i))), PrimitiveReceipts (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i)
      u (venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (C_).layout (onBoard primitive) i)
        ((b).target.rawResident ord rfl i u))) (fun _ => True)) :
    rowsChecking (fun _:Prop=>True) (fun _:Prop=>True) (fun _:Prop=>True)
      (fun raw=>raw=(b).target.terminalRoster (b).target.valid.host):=by
  rcases scalar with ⟨packing,positiveTags,positivePage,pageRoom,binRoom,packedRoom,large,wordBits,printed⟩
  exact ⟨paid,actors,h,(b).target.terminalRoster (b).target.valid.host,
    boot, romTop, full, True.intro, rowsEq,
    localRows, roomPool, True.intro, True.intro, «copied»,
    roof, fenceRoom, beforeLuts, printed, lut,
    True.intro, cells, True.intro, True.intro, True.intro,
    True.intro, True.intro, True.intro, True.intro, True.intro,
    True.intro, True.intro, True.intro, True.intro, True.intro,
    True.intro, True.intro, True.intro, True.intro, homeStart,
    True.intro, packing, True.intro, True.intro, leafCount,
    positiveTags, positivePage, pageRoom, binRoom, packedRoom,
    large, wordBits, rfl, book, seats,
    ports, True.intro, header, dense, poolHeader,
    Or.inl under⟩


/-- Readbacks of the genuine packed branch in the memory used by the terminal. -/
def WideCapturedRows : Prop := DescentTerminalFundedReadback.Capture lo compact j rest s E₀ extra
  checked preflight ((b).path.savedRotations plan fence tail preflight) ∧ coord_

/-- Physical cohort counts and terminal packet destinations at one acquired branch. -/
def WideMeasuredPackets : Prop :=
  j≤S.groupWidth k tail S.length+k ∧
  (∀i:Fin count₀,homes.read preflight (i.val:Computability.VPVNP.BurstRAM.Word w)=((oldHost i).val:Computability.VPVNP.BurstRAM.Word w)) ∧
  (∀i:Fin H₀,primitive (((pre).census begin_).base+i.val)=(cohorts_ i:Computability.VPVNP.BurstRAM.Word w)) ∧
  ∀i:Fin H₀,(primitive (((pre).frozenRoster begin_).base+i.val)).val=Branch.frozenRosterCode X G S b positive base i

/-- Change the measured roster condition at the same booked memory and retain every
other dated read, frame, and width check. -/
theorem wide_source_rows_mono
    {before after_ : (Fin H₀→Fin (b).target.placement.degree→Option (Fin H₀))→Prop}
    (carry : ∀rs,before rs→after_ rs) (sourceData : sourceRowsFor before) : sourceRowsFor after_ := by
  obtain ⟨paid,actors,budgetHeight,oldPeers,boot,romTop,full,space,rowCount,allRows,size,retained,headerLow,prior,late,ceiling,tableSide,bookWidth,pageReads,occ,oldCells,wideSeed,fitsSeed,topSeed,positiveGrain,below,before,lower,words,fits,geometry,top,apart,copyRoom,historyWords,exterior,history,window,homeSide,homeRead,rect,positiveWord,pack,leaves,roleCount,spare,smallPage,smallRows,smallCircuit,large,addressBits,date,bookAt,peerRows,peerData,census,early,tables,headerRoom,romSide⟩:=sourceData
  exact ⟨paid,actors,budgetHeight,oldPeers,boot,romTop,full,space,rowCount,allRows,size,retained,headerLow,prior,late,ceiling,tableSide,bookWidth,pageReads,occ,oldCells,wideSeed,fitsSeed,topSeed,positiveGrain,below,before,lower,words,fits,geometry,top,apart,copyRoom,historyWords,exterior,history,window,homeSide,homeRead,rect,positiveWord,pack,leaves,roleCount,spare,smallPage,smallRows,smallCircuit,large,addressBits,carry oldPeers date,bookAt,peerRows,peerData,census,early,tables,headerRoom,romSide⟩

/-- Fill the four original dated observations directly from the physical execution
receipt. The other site inputs are kept at the same primitive and booked memories. -/
theorem wide_restore_capture {mask : Prop→Prop} {nodeTest : Prop→Prop}
    {cond : (Fin H₀→Fin (b).target.placement.degree→Option (Fin H₀))→Prop}
    (captured : DescentTerminalFundedReadback.Capture lo compact j rest s E₀ extra checked preflight
      ((b).path.savedRotations plan fence tail preflight) ∧ coord_)
    (measured : j≤S.groupWidth k tail S.length+k ∧
      (∀i:Fin count₀,homes.read preflight (i.val:Computability.VPVNP.BurstRAM.Word w)=((oldHost i).val:Computability.VPVNP.BurstRAM.Word w)) ∧
      ∀i:Fin H₀,primitive (((pre).census begin_).base+i.val)=(cohorts_ i:Computability.VPVNP.BurstRAM.Word w))
    (sources : rowsChecking mask (fun _:Prop=>True) nodeTest cond) : rowsChecking mask id nodeTest cond := by
  obtain ⟨data,_,_,wordSeed,posWord,seedWord,seedStart,grainPos,bookSide,winSide,indices,slotsFit,
    votedRoom,trackRoom,packRoom,rawSide,lastRoom,edgeBits,_,_,headStart,_,endWord,_,_,_⟩:=captured
  obtain ⟨paid,actors,budgetHeight,oldPeers,boot,romTop,full,space,rowCount,allRows,size,retained,headerLow,prior,late,ceiling,tableSide,bookWidth,pageReads,occ,oldCells,wideSeed,fitsSeed,topSeed,positiveGrain,below,before,lower,words,fits,geometry,top,apart,copyRoom,historyWords,exterior,history,window,homeSide,homeRead,rect,positiveWord,pack,leaves,roleCount,spare,smallPage,smallRows,smallCircuit,large,addressBits,date,bookAt,peerRows,peerData,census,early,tables,headerRoom,romSide⟩:=sources
  exact ⟨paid,actors,budgetHeight,oldPeers,boot,romTop,full,endWord,rowCount,allRows,size,measured.1,headStart,prior,late,ceiling,tableSide,bookWidth,pageReads,occ,oldCells,wordSeed,seedWord,seedStart,grainPos,bookSide,winSide,indices,slotsFit,votedRoom,trackRoom,packRoom,rawSide,lastRoom,data.original,data.columns,data.saved,data.appendix,homeSide,measured.2.1,rect,posWord,edgeBits,leaves,roleCount,spare,smallPage,smallRows,smallCircuit,large,addressBits,date,bookAt,peerRows,peerData,measured.2.2,early,tables,headerRoom,romSide⟩


/-- Supply every occupied-site test from the original packed actor word at this
same primitive snapshot. This also tests exterior sites and sites with no nodes. -/
theorem wide_restore_actor_rows {condition : (Fin H₀→Fin (b).target.placement.degree→Option (Fin H₀))→Prop}
    (actorsRead : 2^(pre).printBits<2^w → H₀≤2^w ∧ groupsAt≤w ∧
      ∀(h:Fin H₀)(x:DescentColonies.Block k),primitive (((R_).occupied x).base+h.val)=
        ((DescentSIMDLookup.encode 1 groupsAt (fun g=>if ∃v:(hostGraph).Site,
          (b).target.home v=h ∧ ((b).target.placement.pos v).1=g ∧ (b).target.placement.block v=x
          then 1 else 0 : Fin groupsAt→DescentSIMDLookup.Cell 1)).val:Computability.VPVNP.BurstRAM.Word w))
    (sourceData : rowsTestingActor (fun _:Prop=>True) condition) : sourceRowsFor condition := by
  obtain ⟨paid,actors,budgetHeight,oldPeers,boot,romTop,full,space,rowCount,allRows,size,retained,headerLow,prior,late,ceiling,tableSide,bookWidth,pageReads,occ,oldCells,remaining⟩:=sourceData
  obtain ⟨hostRoom,groupRoom,read⟩:=actorsRead bookWidth
  have occupation := Branch.reel_occupation_from_words
    («F»:=F) («cp»:=cp) («P»:=P) («X»:=X) («G»:=G) («S»:=S)
    («k»:=k) («cut»:=cut) («tail»:=tail) («n»:=n) («h»:=h) («C»:=C)
    («f»:=f) («g»:=g) («W»:=W) («q»:=q) («piece»:=piece) («ordinary»:=ordinary)
    («reset»:=reset) («branch»:=branch) («positive»:=positive) («room»:=room) («shorten»:=shorten) («c»:=c)
    («j»:=j) («rest»:=rest) («base»:=base) («width»:=width) («qh»:=qh) («template»:=template)
    («sitesPositive»:=sitesPositive) («rawWords»:=rawWords) («headerRows»:=headerRows) («paidRows»:=paidRows) («w»:=w) («K»:=K)
    («fit»:=fit) («begin_»:=begin_) («rom»:=rom) («peer»:=peer) («old»:=old) («org»:=org)
    («homes»:=homes) («other»:=other) («arity»:=arity) («groups»:=groups) («stride»:=stride) («oldTags»:=oldTags)
    («lo»:=lo) («packWidth»:=packWidth) («head»:=head) («short»:=short) («primitive»:=primitive)
    paid actors boot romTop full space hostRoom groupRoom read
  exact ⟨paid,actors,budgetHeight,oldPeers,boot,romTop,full,space,rowCount,allRows,size,retained,headerLow,prior,late,ceiling,tableSide,bookWidth,pageReads,occupation,oldCells,remaining⟩

/-- Recover the occupied mask and the named node extent from their two real native banks. -/
theorem wide_restore_native_counts {condition : (Fin H₀→Fin (b).target.placement.degree→Option (Fin H₀))→Prop}
    (actorsRead : 2^(pre).printBits<2^w → H₀≤2^w ∧ groupsAt≤w ∧
      ∀(h:Fin H₀)(x:DescentColonies.Block k),primitive (((R_).occupied x).base+h.val)=
        ((DescentSIMDLookup.encode 1 groupsAt (fun g=>if ∃v:(hostGraph).Site,
          (b).target.home v=h ∧ ((b).target.placement.pos v).1=g ∧ (b).target.placement.block v=x
          then 1 else 0 : Fin groupsAt→DescentSIMDLookup.Cell 1)).val:Computability.VPVNP.BurstRAM.Word w))
    (ports : 2^(pre).printBits<2^w → ∀v:(hostGraph).Site,
      venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k) (measured (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap)
        (w:=p) (groups:=groupsAt) (blocks:=2^k) (MaskAllocation.shelf (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) («p»:=p) (groups:=groupsAt) (rasters_).geometry 0) primitive (host_ (((b).target.placement).pos v).2))
        (finProdFinEquiv ((((b).target.placement).pos v).1,((b).target.placement).block v))) publicArity=
          DescentTerminalGraphRows.arity hostGraph p v)
    (population:∀v:(hostGraph).Site,DescentSIMDLookup.digit (Nat.clog 2 (nodeCap+1)) (((b).target.placement).pos v).1.val
      (primitive ((((pre).channels begin_).primitive (((b).target.placement).block v) 3).base+((b).target.home v).val)).val=
      Fintype.card ((Branch.archive X G S b positive).bit.recipe v).Node)
    (sourceData : rowsChecking (fun _:Prop=>True) id (fun _:Prop=>True) condition) : sourceRowsFor condition := by
  obtain ⟨paid,actors,budgetHeight,oldPeers,boot,romTop,full,space,rowCount,allRows,size,retained,headerLow,prior,late,ceiling,tableSide,bookWidth,pageReads,occ,oldCells,remaining⟩:=sourceData
  obtain ⟨hostRoom,groupRoom,read⟩:=actorsRead bookWidth
  have occupation := Branch.reel_occupation_from_words
    («F»:=F) («cp»:=cp) («P»:=P) («X»:=X) («G»:=G) («S»:=S)
    («k»:=k) («cut»:=cut) («tail»:=tail) («n»:=n) («h»:=h) («C»:=C)
    («f»:=f) («g»:=g) («W»:=W) («q»:=q) («piece»:=piece) («ordinary»:=ordinary)
    («reset»:=reset) («branch»:=branch) («positive»:=positive) («room»:=room) («shorten»:=shorten) («c»:=c)
    («j»:=j) («rest»:=rest) («base»:=base) («width»:=width) («qh»:=qh) («template»:=template)
    («sitesPositive»:=sitesPositive) («rawWords»:=rawWords) («headerRows»:=headerRows) («paidRows»:=paidRows) («w»:=w) («K»:=K)
    («fit»:=fit) («begin_»:=begin_) («rom»:=rom) («peer»:=peer) («old»:=old) («org»:=org)
    («homes»:=homes) («other»:=other) («arity»:=arity) («groups»:=groups) («stride»:=stride) («oldTags»:=oldTags)
    («lo»:=lo) («packWidth»:=packWidth) («head»:=head) («short»:=short) («primitive»:=primitive)
    paid actors boot romTop full space hostRoom groupRoom read
  have present := Branch.reel_live_from_occupation
    («F»:=F) («cp»:=cp) («P»:=P) («X»:=X) («G»:=G) («S»:=S)
    («k»:=k) («cut»:=cut) («tail»:=tail) («n»:=n) («h»:=h) («C»:=C)
    («f»:=f) («g»:=g) («W»:=W) («q»:=q) («piece»:=piece) («ordinary»:=ordinary)
    («reset»:=reset) («branch»:=branch) («positive»:=positive) («room»:=room) («shorten»:=shorten) («c»:=c)
    («j»:=j) («rest»:=rest) («base»:=base) («width»:=width) («qh»:=qh) («template»:=template)
    («sitesPositive»:=sitesPositive) («rawWords»:=rawWords) («headerRows»:=headerRows) («paidRows»:=paidRows) («w»:=w) («K»:=K)
    («fit»:=fit) («begin_»:=begin_) («rom»:=rom) («peer»:=peer) («old»:=old) («org»:=org)
    («homes»:=homes) («other»:=other) («arity»:=arity) («groups»:=groups) («stride»:=stride) («oldTags»:=oldTags)
    («lo»:=lo) («packWidth»:=packWidth) («head»:=head) («short»:=short) («primitive»:=primitive)
    occupation
  have counted := Branch.reel_population_from_words
    («F»:=F) («cp»:=cp) («P»:=P) («X»:=X) («G»:=G) («S»:=S)
    («k»:=k) («cut»:=cut) («tail»:=tail) («n»:=n) («h»:=h) («C»:=C)
    («f»:=f) («g»:=g) («W»:=W) («q»:=q) («piece»:=piece) («ordinary»:=ordinary)
    («reset»:=reset) («branch»:=branch) («positive»:=positive) («room»:=room) («shorten»:=shorten) («c»:=c)
    («j»:=j) («rest»:=rest) («base»:=base) («width»:=width) («age»:=age) («wFit»:=wFit)
    («qFit»:=qFit) («qh»:=qh) («template»:=template) («sitesPositive»:=sitesPositive) («rawWords»:=rawWords) («headerRows»:=headerRows)
    («paidRows»:=paidRows) («pool»:=pool) («raw»:=raw) («w»:=w) («K»:=K) («fit»:=fit)
    («begin_»:=begin_) («rom»:=rom) («peer»:=peer) («old»:=old) («org»:=org) («homes»:=homes)
    («other»:=other) («arity»:=arity) («groups»:=groups) («stride»:=stride) («oldTags»:=oldTags) («codec»:=codec)
    («lo»:=lo) («packWidth»:=packWidth) («head»:=head) («short»:=short) («primitive»:=primitive)
    paid actors boot romTop full space hostRoom population
  have public_ := Branch.reel_ports_from_shelf
    («F»:=F) («cp»:=cp) («P»:=P) («X»:=X) («G»:=G) («S»:=S)
    («k»:=k) («cut»:=cut) («tail»:=tail) («n»:=n) («h»:=h) («C»:=C)
    («f»:=f) («g»:=g) («W»:=W) («q»:=q) («piece»:=piece) («ordinary»:=ordinary)
    («reset»:=reset) («branch»:=branch) («positive»:=positive) («room»:=room) («shorten»:=shorten) («c»:=c)
    («j»:=j) («rest»:=rest) («base»:=base) («width»:=width) («qh»:=qh) («template»:=template)
    («sitesPositive»:=sitesPositive) («rawWords»:=rawWords) («headerRows»:=headerRows) («paidRows»:=paidRows) («w»:=w) («K»:=K)
    («fit»:=fit) («begin_»:=begin_) («rom»:=rom) («peer»:=peer) («old»:=old) («org»:=org)
    («homes»:=homes) («other»:=other) («arity»:=arity) («groups»:=groups) («stride»:=stride) («oldTags»:=oldTags)
    («lo»:=lo) («packWidth»:=packWidth) («head»:=head) («short»:=short) («primitive»:=primitive)
    paid actors boot romTop full space (ports bookWidth)
  exact ⟨paid,actors,budgetHeight,oldPeers,boot,romTop,full,space,rowCount,allRows,size,retained,headerLow,prior,late,ceiling,tableSide,bookWidth,pageReads,occupation,(fun i u=>PrimitiveReceipts.with_measured_counts (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i) u _ (oldCells i u) (public_ i u) (present i u) (counted i u)),remaining⟩






def WideObservedSources : Prop := sourceRows

theorem wide_observed_live (seen:which=some c) :
    sourceRows → Nonempty ((leaf).Printed (cfg) (arity:=arity) (groups:=groups) (stride:=stride) codec plan_ (C_).layout
      (meterAt post) bankSet (AddressPlan.chip (cfg) I_ base_) (paint ∘ Sum.inr) (payloadOut original)
      (paint ∘ Sum.inl) B) ∧ (DescentTerminalDenseHeaderRAM.Reads (plan_).emit.plane.header
      (DescentTerminalHeaderGroups.padded (n:=headerRows) privateTape_) post) := by
  intro input
  obtain ⟨paid,actors,budgetHeight,oldPeers,boot,romTop,full,space,rowCount,allRows,size,retained,headerLow,prior,late,ceiling,tableSide,bookWidth,pageReads,occ,oldCells,wideSeed,fitsSeed,topSeed,positiveGrain,below,before,lower,words,fits,geometry,top,apart,copyRoom,historyWords,exterior,history,window,homeSide,homeRead,rect,positiveWord,pack,leaves,roleCount,spare,smallPage,smallRows,smallCircuit,large,addressBits,raster,bookAt,peerRows,peerData,census,early,tables,headerRoom,romSide⟩:=input
  have ok:=(DescentExteriorShelf.proposed_eq ..).mp seen
  have dec:(chart).read history_=some c:=ok.1
  have installed:history_=(chart).store c:=((chart).read_iff _ _).mp dec
  have selected:c=(normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow history_:=
    ((congrArg (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow installed).trans ((normalizedRoute X G S ordinary reset branch positive room shorten w fit).stored c)).symm
  have admitted:accepted:=⟨c,dec⟩
  have valid:∀a,stagesOK (originalMatrix a) (publicRows X original a) (projected past_ false a) (projected past_ true a):=
    (canonical_iff ..).mpr ok.2
  constructor
  · exact ⟨wide_observed_printed (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch)
      (positive:=positive) (room:=room) (shorten:=shorten) (c:=c) (base:=base) (width:=width) (age:=age)
      (wFit:=wFit) (qFit:=qFit) (qh:=qh) (template:=template) (sitesPositive:=sitesPositive)
      (rawWords:=rawWords) (headerRows:=headerRows) (paidRows:=paidRows) (pool:=pool) (raw:=raw)
      (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom) (peer:=peer) (old:=old)
      (org:=org) (homes:=homes) (other:=other) (codec:=codec) (lo:=lo) (packWidth:=packWidth)
      (all:=all) (head:=head) (short:=short) (fence:=fence) (count:=count) (plan:=plan)
      (primitive:=primitive) (m:=m) (original:=original)
      paid actors boot romTop full space rowCount allRows size retained headerLow prior late ceiling tableSide
      bookWidth pageReads occ oldCells selected admitted wideSeed fitsSeed topSeed positiveGrain below before lower
      words fits geometry top apart copyRoom historyWords exterior history window valid homeSide homeRead rect
      positiveWord pack leaves budgetHeight roleCount spare smallPage smallRows smallCircuit large addressBits
      oldPeers raster bookAt peerRows peerData census early tables headerRoom romSide⟩
  · exact wide_observed_widths (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch)
      (positive:=positive) (room:=room) (shorten:=shorten) (c:=c) (base:=base) (width:=width) (age:=age)
      (wFit:=wFit) (qFit:=qFit) (qh:=qh) (template:=template) (sitesPositive:=sitesPositive)
      (rawWords:=rawWords) (headerRows:=headerRows) (paidRows:=paidRows) (pool:=pool) (raw:=raw)
      (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom) (peer:=peer) (old:=old)
      (org:=org) (homes:=homes) (other:=other) (codec:=codec) (lo:=lo) (packWidth:=packWidth)
      (all:=all) (head:=head) (short:=short) (fence:=fence) (count:=count) (plan:=plan)
      (primitive:=primitive) (m:=m) (original:=original)
      paid actors boot romTop full space rowCount allRows size retained headerLow prior late ceiling tableSide
      bookWidth pageReads occ oldCells selected admitted wideSeed fitsSeed topSeed positiveGrain below before lower
      words fits geometry top apart copyRoom historyWords exterior history window valid homeSide homeRead rect
      positiveWord pack leaves budgetHeight roleCount spare smallPage smallRows smallCircuit large addressBits
      oldPeers raster bookAt peerRows peerData census early tables headerRoom romSide

set_option maxHeartbeats 7000000 in
/-- At an admitted branch the actually measured private mask channels account for every
used word. The single carried register supplies the total declared private volume. -/
theorem wide_selected_seed (seen:which=some c) (input:sourceRows) (held:(b).path.Held head preflight) :
    AddressPlan.SeedCount V R_ start head (cfg).sites preflight ((leaf).debt cfg) := by
  have printed:=Classical.choice (wide_observed_live (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (pool:=pool) (raw:=raw) (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom)
      (peer:=peer) (old:=old) (org:=org) (homes:=homes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=fence) (count:=count) (plan:=plan) (codec:=codec) (short:=short) (all:=all) (c:=c)
      (primitive:=primitive) (m:=m) (original:=original) seen input).1
  obtain ⟨paid,actors,budgetHeight,oldPeers,boot,romTop,full,space,rowCount,allRows,size,retained,headerLow,prior,late,ceiling,tableSide,bookWidth,pageReads,occ,oldCells,wideSeed,fitsSeed,topSeed,positiveGrain,below,before,lower,words,fits,geometry,top,apart,copyRoom,historyWords,exterior,history,window,homeSide,homeRead,rect,positiveWord,pack,leaves,roleCount,spare,smallPage,smallRows,smallCircuit,large,addressBits,raster,bookAt,peerRows,peerData,census,early,tables,headerRoom,romSide⟩:=input
  have layoutEarlier := (pre).earlier begin_ rom q piece W K codes front peer old total modulo homes boundary
    cfg V other T (pre).vertices B paid actors boot romTop full space
  let chargeAt (i:Fin H₀):=measured (C_).layout preflight (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap)
    (A:=cap) (w:=p) (groups:=groupsAt) i
  have row (i:Fin H₀):chargeAt i=measured (C_).layout (onBoard primitive)
      (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) i :=
    (AddressPlan.sockets_measured V cfg I_ R_ start head short literal preflight layoutEarlier space
      ((pre).channels_before begin_) i).symm.trans
      ((pre).measured_after_preflight begin_ V cfg I_ head short literal primitive primitive preflight
        (fun _ _=>rfl) prior layoutEarlier space i)
  let localRow:=fun v=>((leaf).shape v).recipe positive
  have each (i:Fin H₀):privateHome (chargeAt i)=∑v,Fintype.card (recipes i v).UsedWord := by
    refine (congrArg (fun data : BlockFields q tagCount cap nodeCap cap p groupsAt (2^k) =>
      privateHome (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
        (groups:=groupsAt) (blocks:=2^k) data) (row i)).trans ?_
    apply (b).target.private_home_arguments ord rfl i _ (recipes i) (ranks i) (hH i) (hN i) (hA i)
      (fun _ _=>le_refl p) (printed.short i) (occ i)
    intro u
    apply ArgumentReads.of_allowed
    exact PrimitiveReceipts.read (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i)
      (fun _ _=>le_refl p) (printed.short i) u _ (oldCells i u)
  have privateCount:AddressPlan.usedWords V R_ start (cfg).sites preflight=
      DescentTerminalObservedExponent.liveCount positive ((last).state c).graph (leaf).bit (leaf).shape := calc
    _ = ∑i:Fin H₀,∑v,Fintype.card (recipes i v).UsedWord:=Finset.sum_congr rfl (fun i _=>each i)
    _ = _:=DescentTerminalBundleRows.private_rows_volume ((last).state c).graph ord positive localRow
      (leaf).birth (bookCode).store
  refine ⟨DescentTerminalObservedExponent.volume ((last).state c).graph (leaf).bit,?_,?_⟩
  · exact Branch.held_volume X G S b positive held
  · rw [privateCount]
    exact DescentTerminalObservedExponent.partition positive ((last).state c).graph (leaf).bit (leaf).shape


open DescentTerminalEpochDecoder
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

local notation "fundedFacts" measuredDebt => (
  payloadBits≤w ∧ q*p≤w ∧ 2*digitsNeeded s≤payloadBits ∧ 0<w ∧ seedBase+(seedRows+1)<2^w ∧
  seedBase+(seedRows+1)≤lo ∧ 0<packWidth ∧ firstFree≤fence ∧ dst<wall ∧
  (∀a∈shelves packWidth lo 0 steps,count a.ordinal<lo) ∧
  (∀v∈steps,DescentPackedProfileTape.slots v.seats packWidth*packWidth<2^w) ∧ dst+1<2^w ∧
  plan.Room w B₀ S.length fence wall ∧ wall+DescentExteriorShelf.span j rest s E₀+E₀<2^w ∧
  compact+32*DescentExteriorShelf.span j rest s E₀≤wall ∧ wall+17*DescentExteriorShelf.span j rest s E₀<2^w ∧
  middle.Exec checked preflight cost ∧ CheapCode middle ∧ preflight initialFlag=checked initialFlag ∧
  (∀a,lo≤a→a<compact→preflight a=checked a) ∧
  (∀(col:Fin 17)(u:ℕ),u<DescentExteriorShelf.span j rest s E₀→
    preflight ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u)=
      checked ((DescentExteriorShelf.bank j rest s E₀ compact col.val).base+u)) ∧
  (∀i,i<((chart).rows history_).length→∀v,(rawTrace)[i]?=some v→(preflight (count i)).val=selectionCount G v) ∧
  (accepted→(reachedBranch).path.savedRotations plan fence tail preflight) ∧
  2^j*s≤w ∧ (∀v∈steps,DescentTerminalEpochBits.width v.C*packWidth≤w) ∧
  (∀f,((R_).bank f).base+((R_).bank f).size≤ start) ∧ head<start ∧
  AddressPlan.Earlier cfg I_ base_ (C_).layout w ∧ AddressPlan.last V cfg I_ R_ start<2^w ∧ dst<start ∧
  measuredDebt ∧
  (head<fence ∧ (head<firstFree ∨ dst<head)) ∧
  (∀f u,u<((R_).bank f).size→let addr:=((R_).bank f).base+u
    addr<fence ∧ (addr<firstFree ∨ dst<addr)))

local notation "nativeFlow" => fundedFacts (∀v,proposed (chart).read layoutAt (publicRows X original) (Sum.elim history_ past_)=some v→
    AddressPlan.SeedCount V R_ start head (cfg).sites preflight (charge v))
local notation "carriedFlow" => fundedFacts (∀v,which=some v→(issued X G S ordinary reset branch positive room shorten v).path.Held head preflight)

def WideFlightSources : Prop := nativeFlow

def WideHeldFlightSources : Prop := carriedFlow

private theorem shelf_ordinal_lt {A : Type} (shelfWidth lo j : ℕ) (ss : List (DescentTerminalEpochChart.Source A))
    (a : DescentPackedEpochShelves.Shelf A) (mem : a∈shelves shelfWidth lo j ss) : a.ordinal<j+ss.length :=by
  induction ss generalizing lo j with
  | nil=>simp [shelves] at mem
  | cons item ss ih=>
    rcases List.mem_cons.mp mem with head|tail
    · subst a
      change j<j+(ss.length+1)
      omega
    · have q:=ih (lo+DescentPackedEpochShelves.space shelfWidth item) (j+1) tail
      simpa only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using q

private theorem flightAddressBounds {seedEnd packedBase packedEnd firstUnused voteAddress replayStart frameAddress maskAddress launchAddress tableSpan columns epochs wordBound : ℕ}
    (seedLo : seedEnd ≤ packedBase) (loPacked : packedBase ≤ packedEnd) (sourceSpace : packedEnd + 17*tableSpan ≤ firstUnused)
    (firstVote : firstUnused ≤ voteAddress) (voteEarly : voteAddress < replayStart) (earlyFrame : replayStart+17*tableSpan ≤ frameAddress)
    (frameStart : frameAddress ≤ maskAddress) (workGap : maskAddress+epochs+1 ≤ launchAddress) (room24 : launchAddress+24*tableSpan < wordBound)
    (extBound : columns ≤ tableSpan) :
    seedEnd < wordBound ∧ voteAddress < launchAddress ∧ voteAddress+1 < wordBound ∧ launchAddress < wordBound ∧
    launchAddress+tableSpan+columns < wordBound ∧ packedEnd+32*tableSpan ≤ launchAddress ∧ launchAddress+17*tableSpan < wordBound := by omega

private theorem flightPadRoom (lowAddress padA padB padC padD : ℕ) :
    lowAddress ≤ lowAddress + padA + padB + padC + padD := by omega

private theorem positiveFlightWidth {d bits word : ℕ} (hd : 0<d) (fits : 2*d≤bits)
    (arch : bits≤word) : 0<word := by omega

set_option maxHeartbeats 2500000 in
/-- The original packed seed, copied counts, and two traversals of the rotation
reel determine all word and address conditions of the terminal verifier. -/
theorem wide_flight_coordinates (earlyPlan : Reel) (earlyFence earlyRoof : ℕ)
    (paid oldActors : Fin (pre).scalar.blocks→Bank)
    (chosenPlan : plan=earlyPlan.late start) (chosenFence : fence=start)
    (chosenPack : packWidth=DescentPackedEpochShelves.grain (payloadBits/2) G.C)
    (shelfBase : lo=DescentWideSeedFlags.selectorBase X S.copies s payloadBits (steps).length)
    («copied» : ∀i,i<(steps).length→count i=seedBase+seedRows+1+i)
    (seedWord : 2*digitsNeeded s≤payloadBits) (epochWord : 2*unit G.C≤payloadBits/2)
    (architecture : payloadBits≤w) (chipWord : q*p≤w) (edgeWord : 2^j*s≤w)
    (seatsWord : S.batch+2*packWidth<2^w) (ageFits : S.length≤H₀)
    (earlierRoom : earlyPlan.Room w B₀ S.length earlyFence (DescentExteriorMatrixUpdate.Calendar.earlyAt S k tail earlyRoof))
    (reelAfter : dst<DescentExteriorMatrixUpdate.Calendar.earlyAt S k tail earlyRoof)
    (replayed : DescentExteriorMatrixUpdate.Calendar.earlyEnd S k tail earlyRoof j rest s E₀≤begin_)
    (headerBelow : head<begin_) (headerVote : head<firstFree ∨ dst<head)
    (dated : (pre).Before begin_ paid oldActors old peer total modulo homes boundary)
    (dictionary : rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (lastFit : AddressPlan.last V cfg I_ R_ start<2^w) : coord_ :=by
  let H:=DescentExteriorShelf.span j rest s E₀
  have firstToVote : firstFree≤dst:=Nat.le_add_right ..
  have source : lo≤compact:=by
    change lo≤lo+_+_+_
    simp only [Nat.add_assoc, Nat.le_add_right]
  have seedLow : seedBase+(seedRows+1)≤lo:=by
    rw [shelfBase]
    change seedBase+(seedRows+1)≤ seedBase+seedRows+1+_
    simpa only [Nat.add_assoc] using Nat.le_add_right (seedBase+seedRows+1) (steps).length
  have replayBound : DescentExteriorMatrixUpdate.Calendar.earlyAt S k tail earlyRoof +17*H≤begin_ :=
    (Nat.add_le_add_left (le_max_left ..) _).trans replayed
  have startLow : begin_≤ start:=by
    obtain ⟨layer1,layer2,layer3,layer4,layer5,layer6,layer7,layer8,layer9⟩ := (pre).layers begin_
    exact ((pre).cohort_le begin_).trans (layer1.trans (layer2.trans (layer3.trans (layer4.trans
      (layer5.trans (layer6.trans (layer7.trans (layer8.trans layer9))))))))
  have replayAt : DescentExteriorMatrixUpdate.Calendar.earlyAt S k tail earlyRoof≤begin_ :=
    (Nat.le_add_right _ _).trans replayBound
  have afterReel := replayAt.trans startLow
  have voteLow := reelAfter.trans_le afterReel
  have gap:=AddressPlan.late_gap V cfg I_ R_ start S.length ageFits
  have flight : wall+24*H≤DescentTerminalDataPlane.Arena.finish (cfg).terminal.plane wall:=by
    change wall+24*H≤wall+24*H+_+_+4*_+4*_
    exact flightPadRoom _ _ _ _ _
  obtain ⟨_,_,_,afterFlight,finish⟩:=AddressPlan.stages cfg I_ base_
  have room24 : wall+24*H<2^w:=(flight.trans (afterFlight.trans finish)).trans_lt lastFit
  have exterior : E₀≤H:=
    (Nat.le_mul_of_pos_right E₀ (Nat.two_pow_pos (j+rest))).trans
      (DescentExteriorShelf.row_room j rest s E₀)
  have shelvesBefore : compact+17*H≤firstFree:=Nat.le_add_right ..
  have widthPos : 0<digitsNeeded s:=Nat.zero_lt_succ _
  have lists:=normalized_shelf_widths X G S ordinary reset branch positive room shorten w fit
  have positivePack : 0<packWidth:=by
    rw [chosenPack]
    exact (DescentSIMDLookup.occupancy _ _ (Nat.zero_lt_succ _) epochWord).1
  have letters : DescentTerminalEpochBits.width G.C*packWidth≤w:=by
    have fits:=DescentSIMDLookup.lanes_fit (payloadBits/2) (unit G.C)
    rw [← Nat.mul_comm] at fits
    change (DescentTerminalEpochBits.width G.C+1)*DescentPackedEpochShelves.grain (payloadBits/2) G.C≤_ at fits
    rw [←chosenPack,Nat.add_mul,one_mul] at fits
    exact ((Nat.le_add_right _ _).trans fits).trans ((Nat.div_le_self ..).trans ((Nat.div_le_self ..).trans architecture))
  have lowCount : ∀a∈shelves packWidth lo 0 steps,count a.ordinal<lo:=by
    intro a member
    have idx : a.ordinal<(steps).length:=by simpa using shelf_ordinal_lt packWidth lo 0 steps a member
    rw [«copied» _ idx,shelfBase]
    change seedBase+seedRows+1+a.ordinal<seedBase+seedRows+1+(steps).length
    exact Nat.add_lt_add_left idx _
  have perShelf : ∀v∈steps,DescentPackedProfileTape.slots v.seats packWidth*packWidth<2^w:=by
    intro v member
    have n:=(lists v member).2
    have d:=Nat.div_mul_le_self v.seats packWidth
    change (v.seats/packWidth+2)*packWidth<_
    rw [Nat.add_mul]
    exact (Nat.add_le_add_right (d.trans n) _).trans_lt seatsWord
  have firstFit : firstFree≤ start:=firstToVote.trans voteLow.le
  have actualBefore:=(pre).earlier begin_ rom q piece W K codes front peer old total modulo homes boundary
    cfg V other T (pre).vertices B paid oldActors dated dictionary firstFit lastFit
  obtain ⟨seedFits,voteWall,voteFits,wallFits,columnsFit,twoReels,reelFits⟩ :=
    flightAddressBounds seedLow source shelvesBefore firstToVote reelAfter replayBound startLow gap room24 exterior
  have reelFitsAt : plan.Room w B₀ S.length fence wall := by
    rw [chosenPlan,chosenFence]
    exact AddressPlan.late_reel V cfg I_ R_ earlyPlan earlierRoom afterReel ageFits wallFits
  have fenceFits : firstFree≤fence := chosenFence.symm ▸ firstFit
  have headFits : head<fence := chosenFence.symm ▸ (headerBelow.trans_le startLow)
  refine ⟨architecture,chipWord,seedWord,positiveFlightWidth widthPos seedWord architecture,seedFits,
    seedLow,positivePack,fenceFits,voteWall,lowCount,perShelf,voteFits,reelFitsAt,columnsFit,twoReels,
    reelFits,edgeWord,?_,(pre).channels_before begin_,headerBelow.trans_le startLow,actualBefore,lastFit,
    voteLow,⟨headFits,headerVote⟩,?_⟩
  · intro v member
    rw [(lists v member).1]
    exact letters
  · intro f u uFit
    have high:=(pre).channels_before begin_ f
    have low:=((pre).cohort_le begin_).trans ((pre).channels_after_cohorts begin_ f)
    have belowStart := (Nat.add_lt_add_left uFit ((R_).bank f).base).trans_le high
    exact ⟨chosenFence.symm ▸ belowStart, Or.inr ((reelAfter.trans_le replayAt).trans_le (low.trans (Nat.le_add_right _ _)))⟩


/-- The dated readback has an identical source and destination memory, code, and cost
to the final verifier. The typed receipt can be obtained directly from
`Branch.original_funded_readback` and `Branch.funded_preflight_held`. -/
theorem wide_held_from_funded (geometry:coord_)
    (receipt:DescentTerminalFundedReadback.Receipt middle cost checked preflight initialFlag lo compact j rest s E₀ extra
      (fun out=>(∀i,i<((chart).rows history_).length→∀v,(rawTrace)[i]?=some v→
        (out (count i)).val=selectionCount G v) ∧
        (accepted→(reachedBranch).path.savedRotations plan fence tail out) ∧
        (∀v,which=some v→(issued X G S ordinary reset branch positive room shorten v).path.Held head out))) :
    carriedFlow := by
  obtain ⟨arch,pay,wseed,pos,seedFits,seedTop,grainPos,lowWork,flagLow,lowCount,slotsFit,flagFit,
    room_,top,apart,copy,edges,roles,channels,headLow,early_,last_,dstLow,headSide,channelSide⟩:=geometry
  exact ⟨arch,pay,wseed,pos,seedFits,seedTop,grainPos,lowWork,flagLow,lowCount,slotsFit,flagFit,
    room_,top,apart,copy,receipt.executed,receipt.cheap,receipt.seed,receipt.original,receipt.columns,
    receipt.observed.1,receipt.observed.2.1,edges,roles,channels,headLow,early_,last_,dstLow,
    receipt.observed.2.2,headSide,channelSide⟩

/-- Instantiation for the original count capture, whose i-th low address is capture+i.
The early matrix slot is lifted through the fixed later fence, and the attained branch
is identified from the actual coherent history pin stream. -/
theorem wide_held_from_original (geometry:coord_) (earlyReel:Reel) (capture originalFence:ℕ)
    (countSlot:∀i,count i=capture+i) (raiseFence:originalFence≤fence)
    (latePlan:plan=earlyReel.late fence) (matrixRoom:fence+S.length+1<2^w) {extraReads:Memory w→Prop}
    (funding:DescentTerminalFundedReadback.Receipt middle cost checked preflight initialFlag lo compact j rest s E₀ extra
      (fun out=>(∀i v,i<((chart).rows history_).length→(rawTrace)[i]?=some v→
        (out (capture+i)).val=selectionCount G v) ∧
        (accepted→(reachedBranch).path.savedRotations earlyReel originalFence tail out) ∧ extraReads out))
    (held:(∃v,which=some v)→(reachedBranch).path.Held head preflight) : carriedFlow := by
  apply wide_held_from_funded (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom)
      (peer:=peer) (old:=old) (org:=org) (homes:=homes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=fence) (count:=count) (plan:=plan) (all:=all) (m:=m) (original:=original) (middle:=middle)
      (cost:=cost) (arity:=arity) (groups:=groups) (stride:=stride) (oldTags:=oldTags) (K:=K) geometry
  apply funding.map
  rintro ⟨physical,issued_,_⟩
  refine ⟨fun i hi v hv=>?_,fun yes=>?_,?_⟩
  · rw [countSlot]
    exact physical i v hi hv
  · rw [latePlan]
    exact (reachedBranch).path.saved_late earlyReel originalFence (issued_ yes) raiseFence matrixRoom
  · intro v valid
    have dec:(chart).read history_=some v:=((DescentExteriorShelf.proposed_eq ..).mp valid).1
    have stored:history_=(chart).store v:=((chart).read_iff _ _).mp dec
    have selected : v=active := ((congrArg (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow stored).trans ((normalizedRoute X G S ordinary reset branch positive room shorten w fit).stored v)).symm
    exact (congrArg (fun choice => (issued X G S ordinary reset branch positive room shorten choice).path.Held head preflight) selected).mpr (held ⟨v,valid⟩)



/-- On an arbitrary input the partial physical debt read is required only on an admitted
selection. The same attained primitive operand rows supply its missing live volume. -/
theorem wide_flight_from_held (flow:carriedFlow)
    (incoming:∀v,which=some v→WideObservedSources (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (pool:=pool) (raw:=raw) (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom)
      (peer:=peer) (old:=old) (org:=org) (homes:=homes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=fence) (count:=count) (plan:=plan) (codec:=codec) (short:=short) (all:=all) (c:=v)
      (primitive:=primitive) (m:=m) (original:=original)) : nativeFlow := by
  obtain ⟨arch,payload,wseed,wordPos,fitsSeed,topSeed,grainPos,below,
    before,low,words,fits,geometry,top,apart,copyRoom,
    stage,cheap,measured,archivedWords,exterior,physical,issued_,bits,
    stored,channels,header_,early_,space,verdict,sticky,privateKept,
    channelKept⟩:=flow
  refine ⟨arch,payload,wseed,wordPos,fitsSeed,topSeed,grainPos,below,
    before,low,words,fits,geometry,top,apart,copyRoom,
    stage,cheap,measured,archivedWords,exterior,physical,issued_,bits,
    stored,channels,header_,early_,space,verdict,?_,privateKept,
    channelKept⟩
  intro v hit
  have oldBits:Sum.elim history_ past_=all ∘ DescentTerminalFullPins.history:=by funext i;cases i <;>rfl
  have yes:which=some v:=(congrArg (proposed (chart).read layoutAt (publicRows X original)) oldBits).symm.trans hit
  exact wide_selected_seed (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (pool:=pool) (raw:=raw) (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom)
      (peer:=peer) (old:=old) (org:=org) (homes:=homes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=fence) (count:=count) (plan:=plan) (codec:=codec) (short:=short) (all:=all) (c:=v)
      (primitive:=primitive) (m:=m) (original:=original) yes (incoming v yes) (sticky v yes)


set_option maxHeartbeats 3500000 in
/-- The prior read, initial and terminal addresses, clock and debt are fixed by the original
geometry on every Boolean assignment, including rejected candidates. -/
theorem wide_native_flight (flow:nativeFlow) :
    AddressPlan.Flight paidCode firstFree paidTime pinMap original all originalTape finalMem dst flag
      (O_).deadBits which charge := by
  obtain ⟨arch,payload,wseed,wordPos,fitsSeed,topSeed,grainPos,below,before,low,words,fits,
    geometry,top,apart,copyRoom,stage,cheap,measured,archivedWords,exterior,physical,issued_,bits,
    stored,channels,header_,early_,space,verdict,observed,privateKept,channelKept⟩:=flow
  have live:=wide_paid_history_flight (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset)
    (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten) («p»:=p) (w:=w) (payloadBits:=payloadBits)
    (fit:=fit) («V»:=V) («U»:=cfg) (I:=I_) («R»:=R_) (begin_:=start) (privateAt:=head) (short:=short)
    («literal»:=literal) (pub:=count₀) («codes»:=codes) (all:=all) (width:=width) (outer:=original)
    lo packWidth fence count plan middle preflight cost arch payload wseed wordPos fitsSeed topSeed grainPos
    below before low words fits geometry top apart copyRoom stage cheap measured archivedWords exterior physical issued_
    rfl bits stored channels header_ early_ space verdict charge observed privateKept channelKept
  have oldBits: Sum.elim history_ past_ = all ∘ DescentTerminalFullPins.history := by funext i;cases i <;>rfl
  have selected := congrArg (proposed (chart).read layoutAt (publicRows X original)) oldBits
  exact (congrArg (fun proposedWinner => AddressPlan.Flight paidCode firstFree paidTime pinMap original all originalTape
    finalMem dst flag (O_).deadBits proposedWinner charge) selected).mp live


theorem native_clock_geometry (flow:nativeFlow) :
    AddressPlan.Earlier cfg I_ base_ (C_).layout w ∧ AddressPlan.last V cfg I_ R_ start<2^w ∧ dst<start := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,old,space,verdict,_⟩:=flow
  exact ⟨old,space,verdict⟩


variable (primitiveBank booksBank:((DescentTerminalFullPins.Candidate (((normalizedPackedChart X G S ordinary reset branch positive room shorten w fit)).Pin⊕Hidden (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b (W*piece))) K W q piece rawWords)→Bool)→Memory w) (machine:sliceWidth W q piece≤w)
local notation "sourceAt" z₀:arg c₀:arg => WideObservedSources (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (pool:=pool) (raw:=raw) (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom)
      (peer:=peer) (old:=old) (org:=org) (homes:=homes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=fence) (count:=count) (plan:=plan) (codec:=codec) (short:=short) (all:=z₀) (c:=c₀)
      (primitive:=(primitiveBank z₀)) (m:=(booksBank z₀)) (original:=original)
local notation "nativeAt" z₀:arg => WideHeldFlightSources (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom)
      (peer:=peer) (old:=old) (org:=org) (homes:=homes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=fence) (count:=count) (plan:=plan) (all:=z₀) (m:=(booksBank z₀)) (original:=original) (middle:=middle)
      (cost:=cost) (arity:=arity) (groups:=groups) (stride:=stride) (oldTags:=oldTags) (K:=K)
local notation "leafAt" u:arg => normalizedLeaf X G S ordinary reset branch positive room shorten u base width
  age wFit qFit qh cfg pool raw
local notation "oldChoice" => (fun (_:RowBit rawWords (q*p)→Bool) tapeBits=>
  proposed (chart).read layoutAt (publicRows X original) tapeBits)
local notation "bootFor" z₀:arg => Root.appended front extra
    (Root.widePackedImage X S.copies s payloadBits w seed lo G.C packWidth steps compact
      (DescentExterior.publicRows X original) (Sum.elim (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inl)
      (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inr)))
    (DescentTerminalPublicIdentity.back (z₀ ∘ DescentTerminalFullPins.chip) w codes count₀)
local notation "postFor" z₀:arg => oldStateAt firstFree lo G.C packWidth initialFlag steps count
  (z₀ ∘ DescentTerminalFullPins.history ∘ Sum.inl)
  (plan.result j rest s E₀ B₀ S.length wall
    (relocated j rest s E₀ compact wall (out_ ((X_).after values expr (booksBank z₀)))))
local notation "finalFor" z₀:arg => AddressPlan.output V cfg I_ R_ start head short literal (postFor z₀)
local notation "dataAt" u:arg => fun pay=>(leafAt u).contents cfg (K₀:=K) pay (payloadOut original)
local notation "keyAt" u:arg => fun pay=>(leafAt u).keys cfg (arity:=arity) (groups:=groups)
    (stride:=stride) codec machine pay (payloadOut original)
local notation "cols" => AddressPlan.observationColumns V cfg I_ R_ start head dst

private theorem preflightLiteralBeforeMask (spec : DescentTerminalPreflightSpace.Spec) (baseAddress : ℕ) :
    spec.literalBase baseAddress ≤ spec.maskBase baseAddress := by
  rw [spec.draft_size baseAddress]
  exact Nat.le_add_right ..

set_option maxHeartbeats 6500000 in
/-- The execution, initial pin identities and all four low observations belong to the same
physical tape and paid procedure for every candidate. A rejected assignment only needs its
actual run. An admitted choice exposes its issued leaf and private cable header. -/
theorem wide_observed_current
    (native:∀z₀:Full→Bool,nativeAt z₀)
    (measured:∀(z₀:Full→Bool)(c₀:(last).Choice),
      oldChoice (poolBits z₀) (erased z₀)=some c₀→sourceAt z₀ c₀)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (headerRoom:(cfg).terminal.pool≤headerRows) (headersPositive:0<headerRows) :
    (∀(z₀:Full→Bool) i,Sum.elim (Sum.elim original z₀) id (pinMap i)=
      ThreeFlat.Diagonal.TraceWords.bits
        (ThreeFlat.Diagonal.TraceBanks.wide ((bootFor z₀) i.1.val)) i.2) ∧
    (∀z₀:Full→Bool,(paidCode).Exec (Computability.VPVNP.RAMMemory.initialMemory firstFree (bootFor z₀)) (finalFor z₀) paidTime) ∧
    CheapCode paidCode ∧ Current cols (AddressPlan.chip cfg I_ base_) bankSet oldChoice
      (fun u=>dataAt u) (fun u=>∑e,((last).state u).graph.width e) (fun u (_:Unit)=>charge u)
      (fun u=>keyAt u) (fun z₀=>finalFor z₀) := by
  have live (z₀:Full→Bool) (c₀:(last).Choice) (hit:oldChoice (poolBits z₀) (erased z₀)=some c₀) :=
    wide_observed_live (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (pool:=pool) (raw:=raw) (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom)
      (peer:=peer) (old:=old) (org:=org) (homes:=homes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=fence) (count:=count) (plan:=plan) (codec:=codec) (short:=short) (all:=z₀) (c:=c₀)
      (primitive:=(primitiveBank z₀)) (m:=(booksBank z₀)) (original:=original) hit (measured z₀ c₀ hit)
  have earned (z₀:Full→Bool) := wide_flight_from_held (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (pool:=pool) (raw:=raw) (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom)
      (peer:=peer) (old:=old) (org:=org) (homes:=homes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=fence) (count:=count) (plan:=plan) (all:=z₀) (m:=(booksBank z₀)) (original:=original) (middle:=middle)
      (cost:=cost) (arity:=arity) (groups:=groups) (stride:=stride) (oldTags:=oldTags) (K:=K) (short:=short) (codec:=codec) (primitive:=(primitiveBank z₀)) (native z₀) (measured z₀)
  have runs (z₀:Full→Bool) := wide_native_flight (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (pool:=pool) (raw:=raw) (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom)
      (peer:=peer) (old:=old) (org:=org) (homes:=homes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=fence) (count:=count) (plan:=plan) (all:=z₀) (m:=(booksBank z₀)) (original:=original) (middle:=middle)
      (cost:=cost) (arity:=arity) (groups:=groups) (stride:=stride) (oldTags:=oldTags) (K:=K) (short:=short) (earned z₀)
  let z₀ : Full→Bool:=fun _=>false
  have limits:=native_clock_geometry (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows)
      (paidRows:=paidRows) (pool:=pool) (raw:=raw) (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom)
      (peer:=peer) (old:=old) (org:=org) (homes:=homes) (other:=other) (lo:=lo) (packWidth:=packWidth) (head:=head)
      (fence:=fence) (count:=count) (plan:=plan) (all:=z₀) (m:=(booksBank z₀)) (original:=original) (middle:=middle)
      (cost:=cost) (arity:=arity) (groups:=groups) (stride:=stride) (oldTags:=oldTags) (K:=K) (earned z₀)
  have low:=(pre).ports_before begin_ rom q p peer old total modulo homes boundary cfg other romTop
  have literalToMask := preflightLiteralBeforeMask (pre) begin_
  apply AddressPlan.placed_flight (F:=F) («T»:=(last).Choice) (Tag:=U)
    (G:=G) (σ:=S) (k:=k) (K:=K) (W:=W) (q:=q) (piece:=piece) (bitsW:=w)
    (H:=cap) (nodesN:=nodeCap) (addrN:=cap) (verts:=venues) (initial:=oldTags)
    (arity:=arity) (groups:=groups) (stride:=stride)
    (reached:=fun u=>(issued X G S ordinary reset branch positive room shorten u).target)
    («V»:=V) («cfg»:=cfg) (I:=I_) («R»:=R_) («start»:=start) (header:=head)
    (seedAt:=dst) (short:=short) («literal»:=literal) («world»:=(last).state) («leaf»:=fun u=>leafAt u)
    (book:=codec) (machine:=machine) (outer:=payloadOut original) (before_:=fun z₀=>postFor z₀)
    (old:=oldChoice) («front»:=front) (empty:=emptyCode) (external:=original)
    (Q:=paidCode) (pins:=pinMap) (headerWords:=fun z₀=>bootFor z₀)
    limits.1 limits.2.1 limits.2.2 headersPositive (fun i=>(low.1 i).trans literalToMask) runs
    (fun _=>H₀*H₀)
  · intro c₀ e
    exact Branch.fixed_pair_bound (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows) (pool:=pool)
      (raw:=raw) (c:=c₀) e
  · intro c₀
    exact (Branch.fixed_header_lengths (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch) (positive:=positive) (room:=room)
      (shorten:=shorten) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (template:=template) (sitesPositive:=sitesPositive) (rawWords:=rawWords) (headerRows:=headerRows) (pool:=pool)
      (raw:=raw) (c:=c₀) headerRoom).1
  · exact fun z₀ c₀ hit=>(live z₀ c₀ hit).2
  · exact fun z₀ c₀ hit=>Classical.choice (live z₀ c₀ hit).1


end FixedHeaders
end
end Hierarchy.DescentSixParty.SeedNamed

-- These theorem signatures are expensive to index for library suggestions.
-- Limit the exclusion to this export so importing modules keep their usual search settings.
run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.modifyState env fun prior =>
    ["wide_earned_site_pages_of_layout", "wide_source_rows_mono", "wide_restore_capture",
     "wide_restore_actor_rows", "wide_restore_native_counts", "wide_observed_live",
     "wide_selected_seed", "wide_flight_coordinates", "wide_held_from_funded",
     "wide_held_from_original", "wide_flight_from_held", "wide_native_flight",
     "native_clock_geometry", "wide_observed_current"] ++ prior

end OAI
