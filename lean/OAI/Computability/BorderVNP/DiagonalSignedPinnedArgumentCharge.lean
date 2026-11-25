import OAI.Computability.BorderVNP.DiagonalSignedPinnedArgumentRows
import OAI.Computability.BorderVNP.DiagonalJointArgumentAssembly

/-! # Select the genuine public schedule before charging a signed sparse call -/

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
set_option maxHeartbeats 1800000
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
/-- Choose the public schedule first on this prefix. The cost law then holds
for every private sparse source and authentic report on that same ownership
table, including sources that later fail the private test. -/
theorem SharedWriters.signed_pinned_argument_bound
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
      let prof := powerHeaderImage task.cube bf.dst (readings z.val.2.2)
      let ws := weightLayout task.cube nativeHead decl.1.val
      let ts := teamLayout task.cube R
      let sizes := LabelIndex.layout nativeHead published
      GroupWeights.PhysicalImage ws prof task.cube.header.blocks task.cube.b task.cube.K task.cube.h decl lab recv width₀ ∧
      (sizes.cells=task.cube.cells ∧ sizes.cableCount=task.cube.cables ∧ sizes.deliveryCount=(rows).length ∧ sizes.labels=task.cube.alphabet) ∧
      ∃ scheduled, GroupWeights.ScheduleResult ws ts prof scheduled ∧
        CubeArena.DirectoryImage task.cube nativeHead controls decl.1 R prof scheduled (readings W.dataInput) ∧
        (TeamBudget.Layout.mk (R+1) X task.cube.teamTotals).Passes scheduled ∧
        ∀ (packetBits depthP depthD originalTeams parameters expBits fixedTicks : ℕ)
          (box : Fin dir.entries → Fin task.cube.cells) (body : Fin dir.entries → BottomReports.BundleHeader),
          let stage := task.openInputs u.val nativeHead (tables).ends controls (tables).livePairs
            (dir.teams*dir.sites) dir.entries packetBits box body
          1≤task.cube.K → 0<w → 1≤dir.description → ((CubeConstants.install id).slots ≤ fixedTicks) →
          Ready stage nativeHead (readings (v).owned.val.2.2) w →
          ∀ fr : FragmentDirectoryInput nativePub afterArg,
            fr.layout.host.count=task.cube.cables → fr.layout.count ≤ sizes.deliveryCount → fr.layout.cells ≤ sizes.cells →
            ∀ (Site E I P : Type) [Fintype P] (native : PinStart.SparseSource id U (active u))
              (S : SparseReportSources Site E I P task.cube decl lab recv width₀ scheduled u.val dir.description
                depthP depthD originalTeams parameters expBits native.source fr.layout (readings afterArg) stage.control (readings (parts).1.val.2.2)),
              ProducedRoster task stage.control (readings (parts).1.val.2.2) S.places S.geometry S.extra native.source →
              ∀ cursor : ReportCursor, PreparedReportInput nativePub (v).controls.val.2.2 S.reportRows cursor dir.description →
              let input := PinStart.afterRoute id U (active u)
              traceCost input.val.1+privateDirectoryTicks nativePub input.val.2.2 ≤
                fixedTicks+
                argumentDirectory task.cube.cells dir.entries+
                32*descriptorTicks sizes published (task.cube.alphabet-1) (task.cube.n+1) ws ts+
                (82*sizes.cableCount+cubeCoefficient task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s
                  (Cube.Tally.argumentWidth task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s)*(task.cube.alphabet^2+X+1))+
                cellWork w (2^depthP+2^depthD) (originalTeams*(parameters*expBits)) X := by
  obtain ⟨z,image,⟨scheduled,sched,dirs,pass⟩,padding,occupied⟩ :=
    writer.signed_pinned_argument_rows u dir N cell aux siteID edgeID portID F x net ids wireFit hk wordFit positive
      original live liveWidth bounds base origin gap before mid U active alphabet write img place fit hdr scratch originFits
      teams procs fields literal cells stride below room symbols handoff q receipt decoded W ready records source templateFit site cap
  have frame : nativeHead=head := congrFun (congrArg readings (handoff.pub u)) 0
  obtain ⟨_,edges,_,_,cellsAt,_⟩ := signed_published_cable_rows task.cube dir N cell aux siteID edgeID portID F x
      net ids wireFit hk wordFit positive original live liveWidth bounds pub base origin gap before mid write img place fit hdr scratch originFits
      teams procs fields literal cells stride
  have largest : task.cube.alphabet<2^w := by
    have big : task.cube.alphabet ≤ task.cube.alphabet^2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right _ (pow_pos alphabet _)
    have limit := room.arena
    obtain ⟨_,_,_,_,_,_,_,_⟩ := task.cube.writer_order
    omega
  have labels := room.boot.arenaOperand task.cube old fresh inputBits.length gates outputs width off ell
    (k:=56) (value:=task.cube.alphabet) rfl largest
  have shape : (LabelIndex.layout nativeHead published).cells=task.cube.cells ∧
      (LabelIndex.layout nativeHead published).cableCount=task.cube.cables ∧
      (LabelIndex.layout nativeHead published).deliveryCount=(rows).length ∧
      (LabelIndex.layout nativeHead published).labels=task.cube.alphabet := by
    rw [frame]
    refine ⟨cellsAt,edges,?_,labels⟩
    change (Packing.Directory.ISA.publish mid head base rows (head+9)).val=(rows).length
    rw [Packing.Directory.ISA.publish,Function.update_self]
    have lengthBound := dir.directory_length_le placedOriginal placedLive
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨z,image,shape,scheduled,sched,dirs,pass,?_⟩
  intro packetBits depthP depthD originalTeams parameters expBits fixedTicks box body stage copies hw descPositive bound
    openReady fr fc frRows frCells Site E I P instanceP native S roster cursor seed
  exact SharedWriters.arguments_on_joint_prefix (a:=task) (f:=f) (q:=q)
    (width:=Cube.Tally.argumentWidth task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s) U active u
    writer symbols handoff receipt sched image pass copies hw descPositive bound _ padding occupied openReady fr
    (LabelIndex.layout nativeHead published) published (task.cube.alphabet-1) (task.cube.n+1)
    shape.2.1 fc frRows frCells native roster S cursor seed

end TeamContraction

end BorderVNP
end Computability
end OAI
