import OAI.Computability.BorderVNP.DiagonalFrozenPinnedArgumentData
import OAI.Computability.BorderVNP.DiagonalBootLookupOwnership

/-! # The native sparse argument window on a returned ownership handoff -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing PackedHistoryCircuit
open BorderVNP.Cube Cube.Physical Cube.Scatter Cube.TeamRows Scatter.Assignment DiagonalTallyPacketEmit
open FiniteEvaluator Evaluator SignedPrep Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit
open Packing.Directory CellAddressPhysical Cube.MeanChoice Cube.LabelIndex Cube.NativeIntervals Cube.HostScatter
open TeamContraction.JointHeader CubeHeaderInstall LocalRow Physical.NativeAssignments
open Diagonal.ExternalSew.Fragments
open RoutingISA.Evaluator.ScheduleClock FiniteEvaluator.OpenSuffix DiagonalTallyCellReports CellMacro.Generator CellDispatch
open scoped Classical
set_option maxHeartbeats 4200000
set_option maxRecDepth 5500

variable {R r t pins₀ link inner e₀ w : ℕ} {Edge : Type} {G : Wiring R r t pins₀ link inner e₀ Edge}
variable {pin : Fin pins₀ → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
variable (u : Fin (R+1))
variable {D s n d k b : ℕ} {P σ : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}
    {task : SignedTaskArena.Layout} (dir : Directory.Layout) (N : Network D P bits) (cell : N.Site → Fin task.cube.cells)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin n)
    (F : Fields s task.cube.cables n task.cube.cells d k b σ) (x : σ → Bool)
    (net : Represents N cell aux siteID edgeID portID F x) (ids : ∀ c,(F.cells c).val=c.val)
    (wireFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k ≤ b) (wordFit : b ≤ w) (positive : 0<task.cube.cells)
    (original : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (liveWidth : ∀ j,bits (live j)=dir.block) (bounds : dir.DestinationBounds)
    (base origin gap : ℕ) (before mid : Memory w)
variable (U : Fin (R+1) → PinStart SparseExterior.driver e₀ w)
    (active : PinStart.JointPrefix task.id U)
variable (incoming : Arg → Word w) (runtime : TeamOpcode.Macros w 8)
local notation3 (prettyPrint := false) "pub" => incoming
local notation3 (prettyPrint := false) "lib" => runtime
local notation3 (prettyPrint := false) "head" => (pub 0).val
local notation3 (prettyPrint := false) "pr" => privateLayout head origin task.cube.cables task.cube.cells dir.entries dir.description gap
local notation3 (prettyPrint := false) "tables" => bases origin task.cube.cables task.cube.cells dir.entries
local notation3 (prettyPrint := false) "placedOriginal" => ISA.placement (readings mid) (pr).raw
local notation3 (prettyPrint := false) "placedLive" => ISA.placement (readings mid) (tables).livePairs
local notation3 (prettyPrint := false) "rows" => dir.directory placedOriginal placedLive
local notation3 (prettyPrint := false) "published" => readings (ISA.publish mid head base rows)
local notation3 (prettyPrint := false) "geometry" => LabelIndex.layout head published
local notation3 (prettyPrint := false) "list" => NativeDemands.rows N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "recv" => NativeDemands.receiver N cell edgeID portID dir original live gap bounds

local notation3 (prettyPrint := false) "width₀" => fun i : Fin (list).length => list[i.val].width

variable {decl : LengthDeclaration task.cube.n task.cube.header.d}
variable {template : DiagonalTallyPacketEmit.Frame} {count : ℕ}
    {common : List Bool} {publicAt : HeaderExterior L common → Fin (R+1) → Arg → Word w}
    {macroAt : HeaderExterior L common → Fin (R+1) → TeamOpcode.Macros w 8}
    {regAt : HeaderExterior L common → Fin (R+1) → Bank w}
    {memAt : HeaderExterior L common → Fin (R+1) → Memory w}
    (frame : PreparationFrame G L task.cube decl common pin publicAt macroAt regAt memAt)
    (seen : HeaderExterior L common)
local notation3 (prettyPrint := false) "owned" => PinStart.ownedVisits (ar:=task.cube) U active
local notation3 (prettyPrint := false) "v" => PinStart.visits task.id U (active u)
local notation3 (prettyPrint := false) "il" => signedChooserLayout task.cube head origin
variable (alphabet : 0<task.cube.header.d)
local notation3 (prettyPrint := false) "lab" => meanPackedLabel N cell recv width₀ (List.finRange task.cube.cells) task.cube.n task.cube.header.d alphabet
local notation3 (prettyPrint := false) "who" => greedyOwner (blocks:=task.cube.header.blocks) (K:=task.cube.K) (h:=task.cube.h) R task.cube.b task.cube.s lab recv width₀
local notation3 (prettyPrint := false) "entryMem" => Packing.Directory.ISA.publish mid head base rows

local notation3 (prettyPrint := false) "nativePub" => (U u).pub
local notation3 (prettyPrint := false) "nativeHead" => (nativePub 0).val
local notation3 (prettyPrint := false) "afterArg" => (v).reports.val.2.2
local notation3 (prettyPrint := false) "parts" => (argumentVisitsEquiv nativePub (CompactMachine.install SparseExterior.driver e₀ (U u).routines) (v).reports.val.2.1 afterArg).symm (v).arguments

/-- The argument-window specification for one public bank and one macro
bank. Native visits, including the reported and emitted memories in the
window, are fixed independently of these two parameters. -/
def PreparationFrame.IssuedArgumentWindows : Prop :=
    ∀ {I : Type} [Fintype I] {sc : I → Fin task.cube.cells} {sid : I ↪ ℕ} {sw : I → ℕ} {sourcePins}
    (_ : SlottedWriter task.cube dir placedOriginal placedLive sourcePins pub mid base sc sid sw)
    (_ : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings before))
    (_ : (pr).Image (readings before) dir.entries (readings mid)) (_ : (pr).Fits w (readings before))
    (_ : Header head origin task.cube.cables task.cube.cells dir.entries (readings before))
    (_ : base+7*dir.candidates≤origin) (_ : origin<2^w)
    (_ : dir.teams≤2^w) (_ : dir.processors≤2^w) (_ : dir.fields≤2^w) (_ : dir.literal<2^w)
    (_ : task.cube.cells≤2^w) (_ : task.cube.cellStride≤2^w) (_ : origin+3*task.cube.cables≤task.cube.header.header)
    {bf : BroadcastFrame} {old : Fin 81 → Word w} {fresh gates outputs width off ell controls X : ℕ}
    {inputBits : List Bool} {claims : List (List Bool)} {pad : ℕ} {raw : Broadcast task.cube.n task.cube.header.d task.cube.header.cap}
    (_ : PinnedRawInput (ar:=task.cube) (D:=dir) (pp:=placedOriginal) (lp:=placedLive) («pub»:=pub) (slotted:=mid) (base:=base)
      bf old fresh gates outputs width off ell controls inputBits claims pad raw R X)
    (_ : (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) raw.1),
      fun pair j => readCode (task.cube.header.cap+1) (raw.2 pair j))=decl)
    {initial : Memory w} (_ : initial=entryMem)
    {reg rt : Bank w} {last : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory task.cube.n (Cube.Tally.selectorWidth task.cube.n task.cube.K task.cube.h) pub lib reg initial es rt last)
    (_ : DataReady pub W.dataInput) (_ : (DataWriter.layout (readings pub) (readings W.dataInput)).output=task.cube.records)
    (_ : frame.source seen u=readings W.sharedInput)
    (_ : LocalRow.templateLimit task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s<2^w)
    (_ : bf.team=u.val)
    (_ : ∀ pair, load (cablePair (NativeDemands.cableOrder N cell edgeID) (crossSrc N cell) (crossDst N cell) lab)
      (crossWidth N cell ∘ (NativeDemands.cableOrder N cell edgeID).symm) pair ≤ task.cube.header.blocks*(task.cube.h*task.cube.b)),
    ∃ z : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub lib reg initial,
      ∃ assigned : ℕ → ℕ,
      let prof := powerHeaderImage task.cube bf.dst (readings z.val.2.2)
      let sizes := LabelIndex.layout nativeHead published
      (sizes.cells=task.cube.cells ∧ sizes.cableCount=task.cube.cables ∧ sizes.deliveryCount=(rows).length ∧ sizes.labels=task.cube.alphabet) ∧
      CubeArena.DirectoryImage task.cube nativeHead controls decl.1 R prof assigned (readings W.dataInput) ∧
      ∀ (packetBits depthP depthD originalTeams parameters expBits fixedTicks : ℕ)
          (box : Fin dir.entries → Fin task.cube.cells) (body : Fin dir.entries → BottomReports.BundleHeader),
          let stage := task.openInputs u.val nativeHead (tables).ends controls (tables).livePairs
            (dir.teams*dir.sites) dir.entries packetBits box body
          1≤task.cube.K → 0<w → 1≤dir.description → ((CubeConstants.install task.id).slots ≤ fixedTicks) →
          Ready stage nativeHead (readings (v).owned.val.2.2) w →
          ∀ fr : FragmentDirectoryInput nativePub afterArg,
            fr.layout.host.count=task.cube.cables → fr.layout.count ≤ sizes.deliveryCount → fr.layout.cells ≤ sizes.cells →
            ∀ (emitted : ℕ → ℕ) (budget : ℕ), emitted=readings (parts).1.val.2.2 →
              let amount := fixedTicks+
                argumentDirectory task.cube.cells dir.entries+
                32*descriptorTicks sizes published (task.cube.alphabet-1) (task.cube.n+1)
                  (weightLayout task.cube nativeHead decl.1.val) (teamLayout task.cube R)+
                (82*sizes.cableCount+cubeCoefficient task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s
                  (Cube.Tally.argumentWidth task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s)*(task.cube.alphabet^2+X+1))+
                cellWork w (2^depthP+2^depthD) (originalTeams*(parameters*expBits)) X
              amount≤budget →
                ∃ window : PinStart.PublishedArgumentWindow task task.id U (u:=u) (active u) decl lab recv width₀ X dir.description depthP depthD
                  originalTeams parameters expBits (FragmentRows.Layout.fromFrame nativeHead (readings afterArg)) stage.control emitted budget,
                  window.profile=prof ∧ window.assigned=assigned

local notation3 (prettyPrint := false) "windowsFor" "(" bank "," macros ")" =>
  PreparationFrame.IssuedArgumentWindows (u:=u) (dir:=dir) (N:=N) (cell:=cell) (siteID:=siteID) (edgeID:=edgeID)
    (portID:=portID) (F:=F) (x:=x) (original:=original) (live:=live) (bounds:=bounds) (base:=base)
    (origin:=origin) (gap:=gap) (before:=before) (mid:=mid) (U:=U) (active:=active) (incoming:=bank)
    (runtime:=macros) (frame:=frame) (seen:=seen) (alphabet:=alphabet)

include net ids wireFit hk wordFit positive liveWidth in
/-- Recover the actual public and macro banks by the same returned handoff
that identifies the physical owner route. Its writer and its published
program can now feed the original sparse visit's argument window. -/
theorem PreparationFrame.ReturnedOwnershipAt.pinned_argument_window
    (q : NativeAssignments.Routed (b:=task.cube.b) (s:=task.cube.s) who)
    (returned : frame.ReturnedOwnershipAt task seen ext template count q owned) :
    windowsFor((U u).pub,CompactMachine.install SparseExterior.driver e₀ (U u).routines) := by
  obtain ⟨H,f,writers,_,handoff,obs⟩ := returned
  let provide (bank : Arg → Word w) (macros : TeamOpcode.Macros w 8) := windowsFor(bank,macros)
  have staged : provide (H u).pub (H u).macros := by
    intro I _ sc sid sw sourcePins write img place fit hdr scratch originFits teams procs fields literal cells stride below
      bf old fresh gates outputs width off ell controls X inputBits claims pad raw room decoded initial publishedAt
      reg rt last es W ready records source templateFit site cap
    subst initial
    exact writers.frozen_pinned_argument_data u dir N cell aux siteID edgeID portID F x net ids wireFit hk wordFit
      positive original live liveWidth bounds base origin gap before mid U active alphabet write img place fit hdr
      scratch originFits teams procs fields literal cells stride below room (frame.frame seen) handoff q obs decoded
      W ready records source templateFit site cap
  have align : provide ((U u).pub) (CompactMachine.install SparseExterior.driver e₀ (U u).routines) =
      provide (H u).pub (H u).macros := congrArg₂ provide (handoff.pub u) (handoff.macros u)
  change provide ((U u).pub) (CompactMachine.install SparseExterior.driver e₀ (U u).routines)
  rw [align]
  exact @staged

end TeamContraction

end BorderVNP
end Computability
end OAI
