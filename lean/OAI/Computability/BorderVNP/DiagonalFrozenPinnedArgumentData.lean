import OAI.Computability.BorderVNP.DiagonalSignedPinnedArgumentCharge
import OAI.Computability.BorderVNP.DiagonalPinnedArgumentWindowData

/-! # The elected argument window at the actual signed publication -/

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
variable {histDir : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {ownedOrigin ownedStride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {f : ReturnedDelivery G pin ext L histDir pp lp owner ownedOrigin ownedStride H pins} {g : SharedRows.Layout}
variable {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
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

local notation3 (prettyPrint := false) "pub" => (H u).pub
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
variable {group : Fin task.cube.header.d → Fin (R+1)}

variable {template : DiagonalTallyPacketEmit.Frame} {id : TableEntry task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s → ℕ} {count : ℕ}

variable (U : Fin (R+1) → PinStart SparseExterior.driver e₀ w)
    (active : PinStart.JointPrefix id U)
local notation3 (prettyPrint := false) "owned" => PinStart.ownedVisits (ar:=task.cube) U active
local notation3 (prettyPrint := false) "v" => PinStart.visits id U (active u)
local notation3 (prettyPrint := false) "il" => signedChooserLayout task.cube head origin
variable (alphabet : 0<task.cube.header.d)
local notation3 (prettyPrint := false) "lab" => meanPackedLabel N cell recv width₀ (List.finRange task.cube.cells) task.cube.n task.cube.header.d alphabet
local notation3 (prettyPrint := false) "who" => greedyOwner (blocks:=task.cube.header.blocks) (K:=task.cube.K) (h:=task.cube.h) R task.cube.b task.cube.s lab recv width₀
local notation3 (prettyPrint := false) "entryMem" => Packing.Directory.ISA.publish mid head base rows

local notation3 (prettyPrint := false) "nativePub" => (U u).pub
local notation3 (prettyPrint := false) "nativeHead" => (nativePub 0).val
local notation3 (prettyPrint := false) "afterArg" => (v).reports.val.2.2
local notation3 (prettyPrint := false) "lib" => CompactMachine.install SparseExterior.driver e₀ (U u).routines
local notation3 (prettyPrint := false) "parts" => (argumentVisitsEquiv nativePub lib (v).reports.val.2.1 afterArg).symm (v).arguments

include net ids wireFit hk wordFit positive liveWidth in
/-- Materialize a window on the exact memory returned by the sparse emitter,
while retaining the particular profile and assigned owner table used by all
subsequent report and tally phases. Its budget comparison is purely arithmetic. -/
theorem SharedWriters.frozen_pinned_argument_data
    {I : Type} [Fintype I] {sc : I → Fin task.cube.cells} {sid : I ↪ ℕ} {sw : I → ℕ} {sourcePins}
    (write : SlottedWriter task.cube dir placedOriginal placedLive sourcePins pub mid base sc sid sw)
    (img : Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings before))
    (place : (pr).Image (readings before) dir.entries (readings mid)) (fit : (pr).Fits w (readings before))
    (hdr : Header head origin task.cube.cables task.cube.cells dir.entries (readings before))
    (scratch : base+7*dir.candidates≤origin) (originFits : origin<2^w)
    (teams : dir.teams≤2^w) (procs : dir.processors≤2^w) (fields : dir.fields≤2^w) (literal : dir.literal<2^w)
    (cells : task.cube.cells≤2^w) (stride : task.cube.cellStride≤2^w) (below : origin+3*task.cube.cables≤task.cube.header.header)
    {bf : BroadcastFrame} {old : Fin 81 → Word w} {fresh gates outputs width off ell controls X : ℕ}
    {inputBits : List Bool} {claims : List (List Bool)} {pad : ℕ} {raw : Broadcast task.cube.n task.cube.header.d task.cube.header.cap}
    (room : PinnedRawInput (ar:=task.cube) (D:=dir) (pp:=placedOriginal) (lp:=placedLive) («pub»:=pub) (slotted:=mid) (base:=base)
      bf old fresh gates outputs width off ell controls inputBits claims pad raw R X)
    (writer : SharedWriters f g src) (symbols : SymbolFrame g (src anchor) task.cube.header.blocks task.cube.K task.cube.h decl group)
    (handoff : OwnedHandoff f g src task.cube decl group template id count owned)
    (q : NativeAssignments.Routed (b:=task.cube.b) (s:=task.cube.s) who)
    (receipt : ObservedOwned task.cube decl group owned who (f.receivedRows g group) q)
    (decoded : (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) raw.1),
      fun pair j => readCode (task.cube.header.cap+1) (raw.2 pair j))=decl)
    {reg rt : Bank w} {last : Memory w} {es : List (TeamRAM.Event w)}
    (W : WriterHistory task.cube.n (Cube.Tally.selectorWidth task.cube.n task.cube.K task.cube.h) pub (H u).macros reg entryMem es rt last)
    (ready : DataReady pub W.dataInput) (records : (DataWriter.layout (readings pub) (readings W.dataInput)).output=task.cube.records)
    (source : src u=readings W.sharedInput)
    (templateFit : LocalRow.templateLimit task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s<2^w)
    (site : bf.team=u.val)
    (cap : ∀ pair, load (cablePair (NativeDemands.cableOrder N cell edgeID) (crossSrc N cell) (crossDst N cell) lab)
      (crossWidth N cell ∘ (NativeDemands.cableOrder N cell edgeID).symm) pair ≤ task.cube.header.blocks*(task.cube.h*task.cube.b)) :
    ∃ z : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub (H u).macros reg entryMem,
      ∃ assigned : ℕ → ℕ,
      let prof := powerHeaderImage task.cube bf.dst (readings z.val.2.2)
      let sizes := LabelIndex.layout nativeHead published
      (sizes.cells=task.cube.cells ∧ sizes.cableCount=task.cube.cables ∧ sizes.deliveryCount=(rows).length ∧ sizes.labels=task.cube.alphabet) ∧
      CubeArena.DirectoryImage task.cube nativeHead controls decl.1 R prof assigned (readings W.dataInput) ∧
      ∀ (packetBits depthP depthD originalTeams parameters expBits fixedTicks : ℕ)
          (box : Fin dir.entries → Fin task.cube.cells) (body : Fin dir.entries → BottomReports.BundleHeader),
          let stage := task.openInputs u.val nativeHead (tables).ends controls (tables).livePairs
            (dir.teams*dir.sites) dir.entries packetBits box body
          1≤task.cube.K → 0<w → 1≤dir.description → ((CubeConstants.install id).slots ≤ fixedTicks) →
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
                ∃ window : PinStart.PublishedArgumentWindow task id U (u:=u) (active u) decl lab recv width₀ X dir.description depthP depthD
                  originalTeams parameters expBits (FragmentRows.Layout.fromFrame nativeHead (readings afterArg)) stage.control emitted budget,
                  window.profile=prof ∧ window.assigned=assigned := by
  obtain ⟨z,image,shape,assigned,schedule,dirs,pass,charge⟩ :=
    writer.signed_pinned_argument_bound u dir N cell aux siteID edgeID portID F x net ids wireFit hk wordFit positive
      original live liveWidth bounds base origin gap before mid U active alphabet write img place fit hdr scratch originFits teams
      procs fields literal cells stride below room symbols handoff q receipt decoded W ready records source templateFit site cap
  refine ⟨z,assigned,shape,dirs,?_⟩
  intro packetBits depthP depthD originalTeams parameters expBits fixedTicks box body stage copies hw descPositive idsBound
    openReady fr frCables frRows frCells emitted budget equal amount paid
  refine PinStart.PublishedArgumentWindow.of_emitted (A:=Fin (list).length) task id U u (active u) decl _ _ _
    X dir.description depthP depthD originalTeams parameters expBits stage.control emitted _ budget equal fr
    _ assigned schedule image pass ?_
  intro Site E I P finiteP native S production cursor seed
  have measured := charge packetBits depthP depthD originalTeams parameters expBits fixedTicks box body copies hw descPositive
    idsBound openReady fr frCables frRows frCells Site E I P native S production cursor seed
  exact measured.trans paid

end TeamContraction

end BorderVNP
end Computability
end OAI
