import OAI.Hierarchy.DescentNamedWideFlightSources

namespace OAI
/-! Earned scalar invoices at a width independent of the static graph index. -/
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
local notation "s" => S.firstWidth G.b p
local notation "rot" => RotorSpec.ofRates reset
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "cap" => NativeBranch.privateSlotCapacity G S R
local notation "nodeCap" => S.epochPower^S.localTokenExponent
local notation "venues" => S.groupCount S.length*2^k
local notation "archive" => Branch.archive X G S b positive

variable {j rest : ℕ} (base : S.baseGroups=2^tail) (width : S.groupWidth k tail 0+k=j+(j+rest))
variable (age : 0<S.height) (wFit : NativeBranch.binLimit (k:=k) S ≤ W)
  (qFit : NativeBranch.localLimit G S ≤ q) (qh : 0<q)
local notation "ord" => Branch.leafOrder X G S b positive base width
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
local notation "seed" => (chart).seed
local notation "clockCap" => G.C
local notation "steps" => (chart).layout
local notation "front" => end_ (lo+extent packWidth steps) clockCap packWidth+17*DescentExteriorShelf.span j rest s E₀
local notation "extra" => DescentTerminalPublicIdentity.total K W q piece codes rawWords count₀
variable (all : (DescentTerminalFullPins.Candidate (((normalizedPackedChart X G S ordinary reset branch positive room shorten w fit)).Pin⊕Hidden (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b (W*piece))) K W q piece rawWords)→Bool)
local notation "paint" => all ∘ DescentTerminalFullPins.chip
local notation "past_" => all ∘ DescentTerminalFullPins.history ∘ Sum.inr
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
local notation "history_" => all ∘ DescentTerminalFullPins.history ∘ Sum.inl
local notation "wall" => AddressPlan.takeOff (cfg) I_ base_
local notation "compact" => end_ (lo+extent packWidth steps) G.C packWidth
local notation "firstFree" => front+extra
local notation "dst" => finalAt firstFree lo packWidth steps
variable (fence:ℕ) (count:ℕ→ℕ) (plan:Reel)
variable (primitive m:Memory w)
local notation "preflight" => out_ ((X_).after values expr m)
local notation "copied" => relocated j rest s E₀ compact wall preflight
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
local notation "decode_" => Branch.decodeBook S G base ordinary.radix p q (pre).degree (pre).cap
  (pre).printBits (by change 3+1≤4; decide)
local notation "rowsChecking" actorCheck:arg readCheck:arg nodeTest:arg conditions:arg =>
  WideObservedSourcesWith (X:=X) (G:=G) (S:=S) (ordinary:=ordinary) (reset:=reset) (branch:=branch)
    (positive:=positive) (room:=room) (shorten:=shorten) (base:=base) (width:=width) (age:=age)
    (wFit:=wFit) (qFit:=qFit) (qh:=qh) (template:=template) (sitesPositive:=sitesPositive)
    (rawWords:=rawWords) (headerRows:=headerRows) (paidRows:=paidRows) (pool:=pool) (raw:=raw)
    (payloadBits:=payloadBits) (fit:=fit) (begin_:=begin_) (rom:=rom) (peer:=peer) (old:=old)
    (org:=org) (homes:=homes) (other:=other) (codec:=codec) (lo:=lo) (packWidth:=packWidth) (all:=all)
    (head:=head) (short:=short) (fence:=fence) (count:=count) (plan:=plan) (primitive:=primitive)
    (m:=m) (original:=original) (c:=c) conditions actorCheck readCheck nodeTest
/-- Assemble the named site pages using the scalar invoice’s own declared height. -/
theorem wide_earned_site_pages_of_layout_at_height (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start)
    (rowsEq:(cfg).terminal.rows=paidRows) (localRows:(cfg).terminal.rows=K*W) (roomPool:(cfg).terminal.pool=K*W)
    («copied»:∀u<(pre).weights begin_,out_ ((X_).after values expr m) u=primitive u)
    (roof:dst<(pre).cohortEnd begin_) (fenceRoom:start≤fence) (beforeLuts:dst<org)
    (lut:(pages₀).Reads m) (homeStart:dst<homes.base)
    (leafCount:(cfg).terminal.leaves=(cfg).terminal.pool)
    {scalarHeight : ℕ} (scalar:EarnedScalarArguments j s p q W tagCount B (pre).printBits scalarHeight w)
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
  exact ⟨paid,actors,scalarHeight,(b).target.terminalRoster (b).target.valid.host,
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



end FixedHeaders
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
