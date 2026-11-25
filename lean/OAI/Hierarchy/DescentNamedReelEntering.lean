import OAI.Hierarchy.DescentTerminalPostReelRoutes
import OAI.Hierarchy.DescentNamedPreflightFormat
import OAI.Hierarchy.DescentNamedEnteringColumns
import OAI.Hierarchy.DescentTerminalPlacedRouteColumns

import OAI.Hierarchy.DescentNamedSocketDates
import OAI.Hierarchy.DescentTerminalFundedPreflight
import OAI.Hierarchy.DescentTerminalPreflightPostReel
import OAI.Hierarchy.DescentTerminalPlacedSocketMask
import OAI.Hierarchy.DescentNamedPostReelRoute

namespace OAI
/-! # Acquiring the normalized terminal leaf at its actual post-relocation date -/
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
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 3000000
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
attribute [local irreducible] Branch.archive Branch.bundleShape

variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g W q piece : ℕ}
local notation "p" => W*piece
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
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

variable (cfg : DescentTerminalCompiledPrefix.Shape)
    (pool : terminalPool X G S (W*piece) q W n h C f g ≤ cfg.terminal.pool)
    (raw : terminalRawRows X G S (W*piece) q n h C f g ≤ cfg.terminal.plane.rawRows)
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

variable {w K:ℕ} (headerRows paidRows:ℕ)
local notation "fmt" => Branch.geometryFormat G S k g p tail q R rot headerRows paidRows
local notation "pre" => Branch.preflightSpec X G S k g p tail ({fmt with binSize:=W}:Branch.PreflightFormat)
variable (begin_ rom codes front:ℕ) (peer:Bank) (old:Fin (Branch.preflightSpec X G S k g (W*piece) tail
        ({Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR)))
          (RotorSpec.ofRates reset) headerRows paidRows with binSize:=W}:Branch.PreflightFormat)).scalar.blocks →
      Fin (2*(Branch.preflightSpec X G S k g (W*piece) tail
        ({Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR)))
          (RotorSpec.ofRates reset) headerRows paidRows with binSize:=W}:Branch.PreflightFormat)).cap) → Bank)
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

variable (head : ℕ) (short : (Branch.preflightSpec X G S k g (W*piece) tail
        ({Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR)))
          (RotorSpec.ofRates reset) headerRows paidRows with binSize:=W}:Branch.PreflightFormat)).vertices * DescentTerminalVertexFields.span q
      (DescentBundleTagKeys.capacity oldTags arity groups (W*piece) stride)
      (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR))))
      (S.epochPower^S.localTokenExponent) (NativeBranch.privateSlotCapacity G S (max 1 (max reset.bitsR (C*reset.bitsR)))) (W*piece) ≤
    (Branch.preflightSpec X G S k g (W*piece) tail
        ({Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR)))
          (RotorSpec.ofRates reset) headerRows paidRows with binSize:=W}:Branch.PreflightFormat)).pageBits)
local notation "literal" => ScalarLiterals.data q (V).roles (V).privateWords (V).nodes (V).addresses grain (pre).vertices W B
  cfg.terminal.pool qh ((T).columns A_ (J_).sources) ((T).value (fun _ _=>0))
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
local notation "memAt" mu:arg => DescentTerminalEmitter.issued cfg.terminal (plan_).emit (plan_).directory
  (maskedMem (C_).layout (plan_).directory (S.hostSize S.length) (onBoard mu))

open Lean Elab Term in
local elab "reelApply% " fn:term:arg "[" args:term,* "]" : term => do
  let e ← elabTerm fn none
  return mkAppN e (← args.getElems.mapM fun arg => elabTerm arg none)

/-- The post-reel scan reconstructs all of the directory controls at the normalized host sites. -/
private theorem normalizedReelControls (m post:Memory w) (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes cfg.terminal.plane.rawRows cfg.packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w) (rowCount:cfg.terminal.rows=paidRows)
    (allRows:cfg.terminal.rows=K*W) (size:cfg.terminal.pool=K*W) (siteCount:cfg.sites=S.hostSize S.length)
    (fence firstFree dst:ℕ)
    (saved:∀u,u<fence→(u<firstFree ∨ dst<u)→post u=out_ ((X_).after values expr m) u)
    (late:dst<(pre).cohortEnd begin_) (ceiling:start≤fence) (tableSide:dst<org)
    (book:Book.Issued ((pre).parts begin_) (fun i:Fin cfg.sites=>
      let u:=i.cast siteCount
      issue (sites u) (box u) (rowNames u) (argNames u)) m)
    (pageReads:(pages₀).Reads m)
    : Controls («B»:=B) (n:=cfg.terminal.pool) (plan_).directory (onBoard post) sites (leaf).fit
      (fun i => DescentTerminalSiteShelves.actual (w:=p) (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i)
        (fun _ _ => le_refl p) ((leaf).vertsFit i) (arityCap i)) := by
  have side := (pre).scan_reel_side org q dst tableSide
  have countWords := pageReads.counts
  have boundaryWords (j:Fin (cfg.terminal.rows+1)) :
      m (boundary+j.val)=(DescentTerminalBinPackCheap.boundaries w W cfg.terminal.rows)[j.val]'j.isLt := by
    have hit:=pageReads.nextRow (j.cast (congrArg (·+1) rowCount))
    have widthEq : (pages₀).binWidth = W := rfl
    simpa only [DescentTerminalBinPackCheap.boundaries, Vector.getElem_ofFn, Fin.val_cast, widthEq] using hit
  have capacity : DescentTerminalBinPack.purchased W (DescentTerminalRecipeRows.counts (q:=q) sites) ≤ cfg.terminal.rows := ((leaf).space).trans (le_of_eq (size.trans allRows.symm))
  have poolRows : cfg.terminal.pool ≤ cfg.terminal.rows := le_of_eq (size.trans allRows.symm)
  have positiveWord : 0<w := by
    have bound:=(pre).reel_counter begin_ rom q piece K codes front peer old total modulo homes boundary
      cfg V other space
    change cfg.terminal.rows+W<2^w at bound
    have one : 1 ≤ cfg.terminal.rows + W := Nat.le_trans (show 1 ≤ W from (leaf).wp) (Nat.le_add_left ..)
    apply Nat.pos_of_ne_zero
    intro hw
    rw [hw, pow_zero] at bound
    exact (Nat.not_lt_of_ge one) bound
  have fit_ := (leaf).fit
  have wp_ := (leaf).wp
  let inputs_ := fun i : Fin (S.hostSize S.length) =>
    DescentTerminalSiteShelves.actual (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) («V»:=venues)
      (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i) (fun _ _ => le_refl p)
      ((leaf).vertsFit i) (arityCap i)
  have population_ : ∀ i, (inputs_ i).1.val = (sites i).nodes := fun _ => rfl
  cases cfg with
  | mk ns batch bw nh live term =>
    change nh=S.hostSize S.length at siteCount
    subst nh
    exact ((pre).reel_controls (w:=w) (t:=tagCount) («hN»:=cap) (nN:=nodeCap) (aN:=cap) (wid:=p) begin_ rom q piece K codes front peer old total modulo homes boundary
      (⟨ns,batch,bw,S.hostSize S.length,live,term⟩ : DescentTerminalCompiledPrefix.Shape)
      V other T qh wp_ sites box (fun i z => rowNames i z) (fun i z => argNames i z) fit_ inputs_ head short m paid actors boot
      romTop full space positiveWord rfl rowCount capacity poolRows book countWords boundaryWords
      population_ post fence firstFree dst saved late ceiling (.inr side.1) (.inr side.2.2)).2.2.1


set_option maxHeartbeats 6500000 in
/-- All scalar, route, mask and original primitive operands are read on the same
post-reel memory. Only the actual two row emitters and their original sources
supply the remaining header and cable data. -/
def normalized_reel_entering (primitive m post:Memory w) (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes cfg.terminal.plane.rawRows cfg.packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w) (rowCount:cfg.terminal.rows=paidRows)
    (allRows:cfg.terminal.rows=K*W) (size:cfg.terminal.pool=K*W) (siteCount:cfg.sites=S.hostSize S.length)
    (retained : j≤S.groupWidth k tail S.length+k) (headerLow:head<start)
    (fence firstFree dst:ℕ)
    (prior:∀u<(pre).weights begin_,out_ ((X_).after values expr m) u=primitive u)
    (saved:∀u,u<fence→(u<firstFree ∨ dst<u)→post u=out_ ((X_).after values expr m) u)
    (late:dst<(pre).cohortEnd begin_) (ceiling:start≤fence) (tableSide:dst<org)
    (book:Book.Issued ((pre).parts begin_) (fun i:Fin cfg.sites=>
      let u:=i.cast siteCount
      issue (sites u) (box u) (rowNames u) (argNames u)) m)
    (pageReads:(pages₀).Reads m)
    (occ : ∀ (i : Fin (S.hostSize S.length)) (c' : Fin (groupsAt*2^k)),
      blankAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
        (measured (C_).layout (onBoard primitive) (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap)
      (A:=cap) (w:=p) (groups:=groupsAt) i) c' ≠ 0 ↔ ∃u,(b).target.chart ord rfl i u=c')
    (oldCells : ∀i u,PrimitiveReceipts (q:=q) (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i)
      u (venueField (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p)
        (cellAt (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) (blocks:=2^k)
          (measured (C_).layout (onBoard primitive) (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) (groups:=groupsAt) i)
        ((b).target.rawResident ord rfl i u))))
    (banks:Banks) (pay:RowBit cfg.terminal.plane.rawRows (q*p)→Bool)
    (outer:Ports (fun _ : Σ _:Fin S.copies,Fin (Fintype.card (Port P X.width))=>s*1))
    (headers:ControlColumns cfg.terminal (plan_).emit (memAt post) hostGraph (leaf).home (leaf).native
      (leaf).external (leaf).nodes (leaf).ops rsite positive (leaf).birth (leaf).wp qh
      ((leaf).binsFit cfg size) banks)
    (source:SourceRows (W:=W) (q:=q) (piece:=piece) cfg.terminal (plan_).emit (memAt post)
      (leaf).external pay outer banks) :
    (leaf).Entering cfg (arity:=arity) (groups:=groups) (stride:=stride) codec plan_ (C_).layout
      (nativeCandidate post) banks pay outer size short := by
  let atPorts := out_ ((X_).after values expr m)
  have early := (pre).earlier begin_ rom q piece W K codes front peer old total modulo homes boundary
    cfg V other T (pre).vertices B paid actors boot romTop full space
  have pair_ := reelApply% (@normalized_reel_socket_dates) [F, (inferInstance : Field F), cp, P, X, G, S, k, cut, tail, n, h, C, f, g, W, q, piece,
    ordinary, reset, branch, positive, room, shorten, c, j, rest, base, width, age, wFit, qFit,
    qh, cfg, pool, raw, arity, groups, stride, oldTags,
    B, w, codec, ({fmt with binSize:=W}:Branch.PreflightFormat), begin_, head, short, rom, K, codes,
    front, peer, old, total, modulo, homes, boundary, other, T, literal, primitive, atPorts,
    post, prior, fence, firstFree, dst, saved, late, ceiling, early, space, occ, oldCells]
  have shared_ := AddressPlan.sockets_mask V cfg I_ R_ start head short literal post
    ((pre).channels_before begin_) headerLow early space
  have side := (pre).scan_reel_side org q dst tableSide
  have countWords := pageReads.counts
  have boundaryWords (j:Fin (cfg.terminal.rows+1)) :
      m (boundary+j.val)=(DescentTerminalBinPackCheap.boundaries w W cfg.terminal.rows)[j.val]'j.isLt := by
    have hit:=pageReads.nextRow (j.cast (congrArg (·+1) rowCount))
    have widthEq : (pages₀).binWidth = W := rfl
    simpa only [DescentTerminalBinPackCheap.boundaries, Vector.getElem_ofFn, Fin.val_cast, widthEq] using hit
  have remainderWords (i:Fin cfg.terminal.rows) := pageReads.remainder (i.cast rowCount)
  have router : DescentTerminalRouteIssue.Reads (q:=q) (plan_).emit.route
      (DescentTerminalLocalPortBook.rows (q:=q) (K₀:=K) sites (leaf).wp box rowNames argNames)
      (DescentTerminalEmitter.named cfg.terminal (plan_).emit (routerMem post)) := by
    exact normalized_reel_route_columns (X:=X) (G:=G) (S:=S) (ordinary:=ordinary)
      (reset:=reset) (branch:=branch) (positive:=positive) (room:=room) (shorten:=shorten)
      (c:=c) (base:=base) (width:=width) (age:=age) (wFit:=wFit) (qFit:=qFit) (qh:=qh)
      (cfg:=cfg) (pool:=pool) (raw:=raw) (headerRows:=headerRows) (paidRows:=paidRows)
      (begin_:=begin_) (rom:=rom) (codes:=codes) (front:=front) (peer:=peer) (old:=old)
      («total»:=total) («modulo»:=modulo) (homes:=homes) («boundary»:=boundary) («V»:=V)
      (other:=other) (head:=head) (short:=short)
      m post paid actors boot romTop full space rowCount allRows size siteCount fence firstFree dst
      saved late ceiling (.inr side.1) (.inr side.2.2) (.inr side.2.1)
      book countWords boundaryWords remainderWords
  have memoryEq : routerMem post = memAt post :=
    congrArg (fun count => DescentTerminalEmitter.issued cfg.terminal (plan_).emit (plan_).directory
      (maskedMem (C_).layout (plan_).directory count (onBoard post))) siteCount
  have routerAtHost := (congrArg (fun memory => DescentTerminalRouteIssue.Reads (q:=q) (plan_).emit.route
      (DescentTerminalLocalPortBook.rows (q:=q) (K₀:=K) sites (leaf).wp box rowNames argNames)
      (DescentTerminalEmitter.named cfg.terminal (plan_).emit memory)) memoryEq).mp router
  have acquiredWitness : Controls («B»:=B) (n:=cfg.terminal.pool) (plan_).directory (onBoard post) sites (leaf).fit
      (fun i => DescentTerminalSiteShelves.actual (q:=q) (t:=tagCount) (H:=cap) (N:=nodeCap) (A:=cap) (w:=p) («V»:=venues)
        (sites i) (recipes i) (ranks i) (hH i) (hN i) (hA i) (fun _ _ => le_refl p) ((leaf).vertsFit i) (arityCap i)) := reelApply% (@normalizedReelControls) [
    F, (inferInstance : Field F), cp, P, X, G, S, k, cut, tail, n, h, C, f, g, W, q, piece, ordinary,
    reset, branch, positive, room, shorten, c, j, rest, base, width, age, wFit, qFit, qh, cfg, pool,
    raw, w, K, headerRows, paidRows, begin_, rom, codes, front, peer, old, org, homes, other, arity,
    groups, stride, oldTags, codec, head, short, m, post, paid, actors, boot, romTop, full, space,
    rowCount, allRows, size, siteCount, fence, firstFree, dst, saved, late, ceiling, tableSide, book,
    pageReads]
  exact reelApply% (@normalized_entering) [F, (inferInstance : Field F), cp, P, X, G, S, k, cut, tail, n, h, C, f, g, W, q, piece,
    ordinary, reset, branch, positive, room, shorten, c, j, rest, base, width, age, wFit, qFit,
    qh, cfg, pool, raw, arity, groups, stride, oldTags,
    K, B, w, codec, plan_, (C_).layout, (nativeCandidate post), banks, pay, outer, size, short,
    retained, pair_.1, pair_.2, shared_, acquiredWitness, headers, source, routerAtHost]
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
attribute [local irreducible] Branch.archive Branch.bundleShape
