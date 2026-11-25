import OAI.Hierarchy.DescentTerminalPostReelRoutes
import OAI.Hierarchy.DescentNamedPreflightFormat
import OAI.Hierarchy.DescentNamedEnteringColumns
import OAI.Hierarchy.DescentTerminalPlacedRouteColumns

namespace OAI
/-! # The normalized leaf route expression at the final exterior reel -/
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
set_option maxHeartbeats 1300000
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
    (total modulo homes:Bank) (boundary:ℕ) (V:Home.Format) (other:AddressPlan.Input)
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
local notation "a" => Book.tokenBits (venues*NativeBranch.localLimit G S)
local notation "M" => venues*NativeBranch.localLimit G S

variable (head : ℕ) (short : (Branch.preflightSpec X G S k g (W*piece) tail
        ({Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR)))
          (RotorSpec.ofRates reset) headerRows paidRows with binSize:=W}:Branch.PreflightFormat)).vertices * DescentTerminalVertexFields.span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece ≤
    (Branch.preflightSpec X G S k g (W*piece) tail
        ({Branch.geometryFormat G S k g (W*piece) tail q (max 1 (max reset.bitsR (C*reset.bitsR)))
          (RotorSpec.ofRates reset) headerRows paidRows with binSize:=W}:Branch.PreflightFormat)).pageBits)
local notation "literal" => ScalarLiterals.data q V.roles V.privateWords V.nodes V.addresses grain (pre).vertices W B
  cfg.terminal.pool qh ((T).columns A_ (J_).sources) ((T).value (fun _ _=>0))
local notation "O_" => registers V cfg R_ start head
local notation "plan_" => AddressPlan.layout cfg I_ base_ O_
local notation "loaded" => input V cfg I_ R_ start head short literal
local notation "values" => portTable (G:=4) (V:=(pre).vertices) («M»:=M) (A:=(pre).arguments) («a»:=a) q
local notation "expr" => Book.expression ((pre).parts begin_)
local notation "out_" => (pre).afterSiteControls begin_ q grain peer old total modulo homes boundary
local notation "afterCode" => (pre).afterSiteProgram begin_ q grain peer old total modulo homes boundary
local notation "afterTime" => (pre).afterSiteTime begin_ q grain peer old total modulo homes boundary



local notation "routerMem" => fun post:Memory w=>Suffix.events cfg plan_ (C_).layout ((A_).mount (loaded post))

theorem normalized_reel_route_columns (m post:Memory w) (paid actors:Fin (pre).scalar.blocks→Bank)
    (boot:(pre).Before begin_ paid actors old peer total modulo homes boundary)
    (romTop:rom+DescentTerminalDenseHeaderBoot.extent q p≤(pre).literalBase begin_)
    (full:front+DescentTerminalPublicIdentity.total K W q piece codes cfg.terminal.plane.rawRows cfg.packets≤ start)
    (space:AddressPlan.last V cfg I_ R_ start<2^w) (rowCount:cfg.terminal.rows=paidRows)
    (allRows:cfg.terminal.rows=K*W) (size:cfg.terminal.pool=K*W) (siteCount:cfg.sites=S.hostSize S.length)
    (fence firstFree dst:ℕ)
    (saved:∀u,u<fence→(u<firstFree ∨ dst<u)→post u=out_ ((X_).after values expr m) u)
    (late:dst<(pre).cohortEnd begin_) (ceiling:start≤fence)
    (countSide:total.base+total.size≤firstFree ∨ dst<total.base)
    (boundSide:boundary+(paidRows+1)≤firstFree ∨ dst<boundary)
    (moduloSide:modulo.base+modulo.size≤firstFree ∨ dst< modulo.base)
    (book:Book.Issued ((pre).parts begin_) (fun i:Fin cfg.sites=>
      let u:=i.cast siteCount
      issue (sites u) (box u) (rowNames u) (argNames u)) m)
    (countWords:∀j:Fin (Book.Bytes 4 venues M (NativeBranch.localLimit G S) a),
      total.read m (j.val:Computability.VPVNP.BurstRAM.Word w)=countTable q j)
    (boundaryWords:∀j:Fin (cfg.terminal.rows+1),m (boundary+j.val)=(DescentTerminalBinPackCheap.boundaries w W cfg.terminal.rows)[j.val])
    (modWords:∀i:Fin cfg.terminal.rows,modulo.read m (i.val:Computability.VPVNP.BurstRAM.Word w)=((i.val%W:ℕ):Computability.VPVNP.BurstRAM.Word w)) :
    DescentTerminalRouteIssue.Reads (q:=q) (plan_).emit.route
      (DescentTerminalLocalPortBook.rows (q:=q) (K₀:=K) sites (leaf).wp box rowNames argNames)
      (DescentTerminalEmitter.named cfg.terminal (plan_).emit (routerMem post)) := by
  have fit_:=(leaf).fit
  have positiveW:=(leaf).wp
  have accounted:=(leaf).space.trans (le_of_eq (size.trans allRows.symm))
  cases cfg with
  | mk ns batchSize bitWidth siteN sitePositive term =>
    change siteN=S.hostSize S.length at siteCount
    subst siteN
    exact (pre).reel_routes begin_ rom q piece K codes front peer old total modulo homes boundary
      _ V other qh head short m post paid actors boot romTop full space rowCount allRows positiveW
      fence firstFree dst saved late ceiling countSide boundSide moduloSide sites box rowNames argNames fit_ accounted
      book countWords boundaryWords modWords

end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
attribute [local irreducible] Branch.archive Branch.bundleShape
