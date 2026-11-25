import OAI.Hierarchy.DescentNamedReelEntering
import OAI.Hierarchy.DescentNamedWideSourceRows
import OAI.Hierarchy.DescentTerminalBranchPaidJoin

namespace OAI
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphPositions DescentTerminalGraphVolume DescentTerminalCableOrder DescentKernelHistory
open DescentBundleHistory DescentPrimitivePalette DescentRotor DescentResetGates CorrectionBatch
open DescentTerminalBinReaddress DescentTerminalPorts Computability.BorderVNP.Crossing
open DescentTerminalEmitter DescentTerminalEmitter.Branch DescentTerminalChipRuntime
open DescentTerminalVertexFields DescentTerminalHeaderScatter DescentTerminalSiteShelves
open DescentTerminalScalarTransposes DescentTerminalDenseWindow DescentTerminalRecipeRows
open DescentTerminalScalarPadded DescentTerminalCompiledPrefix DescentEpochTagKeys
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM CorrectionFrame
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1200000

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W q piece : ℕ}
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
attribute [local irreducible] Branch.archive Branch.bundleShape
variable (branch : G.b ≤ 2^S.capGain) (positive : 0<W*piece) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
variable (c : (Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice)
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
variable (template:DescentTerminalCompiledPrefix.Shape) (sitesPositive : 0 < S.hostSize S.length) (rawWords headerRows paidRows:ℕ)
local notation "cfg" => Branch.exteriorShape template E₀ j rest s rawWords headerRows H₀ sitesPositive
private abbrev paidGeometry := Branch.exteriorShape template E₀ j rest s rawWords headerRows H₀ sitesPositive
variable (pool : terminalPool X G S (W*piece) q W n h C f g ≤
      (paidGeometry (W := W) (piece := piece) X G S (j := j) (rest := rest) template sitesPositive rawWords headerRows).terminal.pool)
    (raw : terminalRawRows X G S (W*piece) q n h C f g ≤
      (paidGeometry (W := W) (piece := piece) X G S (j := j) (rest := rest) template sitesPositive rawWords headerRows).terminal.plane.rawRows)
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


variable {w K:ℕ}
local notation "fmt" => Branch.geometryFormat G S k g p tail q R rot headerRows paidRows
local notation "pre" => Branch.preflightSpec X G S k g p tail ({fmt with binSize:=W}:Branch.PreflightFormat)
variable (begin_ rom : ℕ) (peer:Bank) (old:Fin (2^k)→Fin (2*((capCalendar G.b S.rounds g S.height).prod*256))→Bank)
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
variable {α : Type} (rawSize : ℕ) (seed : Select X S.copies rawSize→α)
    (lo clockCap packWidth : ℕ) (steps : List (Source α))
local notation "front" => end_ (lo+extent packWidth steps) clockCap packWidth+17*DescentExteriorShelf.span j rest s E₀
local notation "extra" => DescentTerminalPublicIdentity.total K W q piece codes rawWords count₀
local notation "publicBase" => front+DescentTerminalPaidBoot.total K W q piece codes rawWords
local notation "Full" => DescentTerminalFullPins.Candidate (α⊕Hidden E₀ j rest s) K W q piece rawWords
variable (all : DescentTerminalFullPins.Candidate (α ⊕ Hidden (Fintype.card (Port P X.width)) j rest (S.firstWidth G.b (W*piece))) K W q piece rawWords → Bool)
local notation "paint" => all ∘ DescentTerminalFullPins.chip
local notation "past_" => all ∘ DescentTerminalFullPins.history ∘ Sum.inr
local notation "originalMatrix" => Branch.publicLayout (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) («p»:=p) («R»:=R) (radix:=ordinary.radix) (r:=(cert).choose) (c:=c) X G S b positive base width
local notation "oldHost" => Branch.publicHost (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) («p»:=p) («R»:=R) (radix:=ordinary.radix) (r:=(cert).choose) (c:=c) X G S b positive base width
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

variable (head : ℕ) (short : (S.groupCount S.length * 2^k) * DescentTerminalVertexFields.span q
    (DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride)
    (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C * reset.bitsR))))
    (S.epochPower^S.localTokenExponent)
    (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C * reset.bitsR)))) (W*piece) ≤
    max 1 ((S.groupCount S.length * 2^k) * actualSpan G S (RotorSpec.ofRates reset) q (W*piece)
      (max 1 (max reset.bitsR (C * reset.bitsR)))))
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
local notation "nativeCandidate" mu:arg => ((A_).mount (loaded mu))
local notation "memAt" mu:arg => DescentTerminalEmitter.issued (cfg).terminal (plan_).emit (plan_).directory
  (maskedMem (C_).layout (plan_).directory (S.hostSize S.length) (onBoard mu))

local notation "bookSeed" => (pre).reachedRoutes begin_ rom q piece W K codes front peer old total modulo homes boundary (cfg) V other T
local notation "emptyCode" => (DescentTerminalChronologicalBooks.empty q tagCount cap nodeCap cap p venues p).val
local notation "bankSet" => DescentTerminalChipBootWords.chipBanks (K:=K) (W:=W) (q:=q)
  («p»:=piece) codes (plan_).emit front emptyCode
local notation "meterAt" mu:arg => (A_).mount (loaded mu)
local notation "payloadOut" inputValue:arg => packagePins X S.copies s (Branch.copyInput X s (power).symm inputValue)

/- Construct an explicitly specialized application without re-inferring the dependent
binder domains at every argument. The kernel checks the resulting application. -/
open Lean Elab Term in
local elab "paidApply% " fn:term:arg "[" args:term,* "]" : term => do
  let fvar ← elabTerm fn none
  let xs ← args.getElems.mapM fun arg => elabTerm arg none
  return mkAppN fvar xs

/-- The original sixteen retained arrays provide the very same paid candidate to the
covered header, cable and chip workers and the printed normalized terminal leaf. -/
def wide_paid_printed (primitive m post:Memory w) (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes (cfg).terminal.plane.rawRows (cfg).packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w) (rowCount:(cfg).terminal.rows=paidRows)
    (allRows:(cfg).terminal.rows=K*W) (size:(cfg).terminal.pool=K*W)
    (retained : j≤S.groupWidth k tail S.length+k) (headerLow:head<start)
    (fence firstFree dst:ℕ)
    (prior:∀u<(pre).weights begin_,out_ ((X_).after values expr m) u=primitive u)
    (saved:∀u,u<fence→(u<firstFree ∨ dst<u)→post u=out_ ((X_).after values expr m) u)
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
    (original : Port ((2^(j+(j+rest))*s)*P) (copiesWidth (2^(j+(j+rest))*s) X.width)→Bool)
    (valid : ∀a,stagesOK (originalMatrix a) (publicRows X original a) (projected past_ false a) (projected past_ true a))
    (heap : Loaded (AddressPlan.takeOff (cfg) I_ base_) originalMatrix (publicRows X original) past_ post)
    (homeRead : ∀i:Fin count₀,homes.read post (i.val:Computability.VPVNP.BurstRAM.Word w)=((oldHost i).val:Computability.VPVNP.BurstRAM.Word w))
    (payloadBits : ℕ)
    (retainedBoot : ∀a<extra,post (front+a)=DescentTerminalFullPins.wideHeader X S.copies rawSize payloadBits w
      seed lo clockCap packWidth steps count₀ codes original all (front+a))
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
  have actualEarly:=(pre).earlier begin_ rom q piece W K codes front peer old total modulo homes boundary
    (cfg) V other T (pre).vertices B paid actors boot romTop full space
  have homeLow : (I_).homes.base+(I_).homes.size≤ start := by
    change homes.base+homes.size≤ start
    have h₁:=boot.homes
    obtain ⟨e₀,e₁,e₂,e₃,e₄,e₅,e₆,e₇,e₈⟩:=(pre).layers begin_
    exact h₁.trans (e₀.trans (e₁.trans (e₂.trans (e₃.trans (e₄.trans (e₅.trans (e₆.trans (e₇.trans e₈))))))))
  have sourceData:=Branch.wide_original_source_rows (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) («p»:=p) («R»:=R) (radix:=ordinary.radix) (r:=(cert).choose) (c:=c) X G S b positive base width template sitesPositive
    rawWords headerRows V I_ R_ start head short literal rawSize seed lo clockCap packWidth steps all payloadBits post
    original valid actualEarly space positiveWord pack full homeLow homeRead heap rfl rect emptyCode rfl retainedBoot
  let enterAt := paidApply% (@normalized_reel_entering) [F, (inferInstance : Field F), cp, P, X, G, S,
    k, cut, tail, n, h, C, f, g, W, q, piece, ordinary, reset, branch, positive, room, shorten,
    c, j, rest, base, width, age, wFit, qFit, qh, cfg, pool, raw, w, K, headerRows, paidRows,
    begin_, rom, codes, front, peer, old, org, homes, other, arity, groups, stride, oldTags, codec, head, short]
  let enterMemory := paidApply% enterAt [primitive, m, post, paid, actors, boot, romTop, full, space,
    rowCount, allRows, size, (rfl : (cfg).sites = S.hostSize S.length), retained, headerLow, fence,
    firstFree, dst, prior, saved, late, ceiling, tableSide, book, pageReads]
  let enterRows := paidApply% enterMemory [occ, oldCells, bankSet,
    (paint ∘ Sum.inr : RowBit (cfg).terminal.plane.rawRows (q*p) → Bool), payloadOut original, headers]
  have entering := paidApply% enterRows [sourceData]
  have originals:=DescentTerminalFullPins.wideRetained_ranges X S.copies rawSize payloadBits w seed lo clockCap
    packWidth steps count₀ codes original all post retainedBoot
  have earlier : front+DescentTerminalPaidBoot.total K W q piece codes rawWords≤ start := by
    have edge : DescentTerminalPaidBoot.total K W q piece codes rawWords≤extra := Nat.le_add_right ..
    exact (Nat.add_le_add_left edge _).trans full
  exact AddressPlan.paid_printed (cfg) leaf codec bookSeed R_ start head front B short
    ((T).value (fun _ _=>0)) post (payloadOut original) paint rfl allRows size leaves
    actualEarly space earlier originals.1 budgetHeight roleCount spare smallPage smallRows smallCircuit large
    addressBits entering

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
