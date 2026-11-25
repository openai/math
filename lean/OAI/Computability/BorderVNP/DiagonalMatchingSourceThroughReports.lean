import OAI.Computability.BorderVNP.DiagonalCanonicalFragmentPlacements
import OAI.Computability.BorderVNP.DiagonalMatchingHostTables
import OAI.Computability.BorderVNP.DiagonalOwnedWriterCellWord
import OAI.Computability.BorderVNP.DiagonalPinnedPlacementKeys
import OAI.Computability.BorderVNP.DiagonalOwnedReportSourceWords
import OAI.Computability.BorderVNP.DiagonalExternalFragmentNativeWords

/-! # The actual signed source words before the argument writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing PackedHistoryCircuit
open BorderVNP.Cube Cube.Physical Cube.Scatter Cube.TeamRows Scatter.Assignment DiagonalTallyPacketEmit
open FiniteEvaluator Evaluator SignedPrep Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit
open Packing.Directory CellAddressPhysical Cube.MeanChoice Cube.LabelIndex Cube.NativeIntervals Cube.HostScatter
open TeamContraction.JointHeader CubeHeaderInstall LocalRow Physical.NativeAssignments
open Diagonal.ExternalSew Diagonal.ExternalSew.Fragments Cube.HostAddress DiagonalTallyCellReports DiagonalTallyAllocation
open CellMacro.Generator CompactMachine
open scoped Classical
set_option maxHeartbeats 1800000
set_option maxRecDepth 5500

variable {R r t pins₀ link inner n w V wordSize entries desc D sz np d k b : ℕ}
    {Edge : Type} {G : Wiring R r t pins₀ link inner n Edge}
    {pin : Fin pins₀ → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
    {H : Fin (R+1) → TeamHistory w} {ib hb sb : Fin (R+1) → ℕ}
    {owner : ℕ → Fin (R+1)} (task : SignedTaskArena.Layout)
    {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
    {σ : Type} [Fintype σ]
local notation3 (prettyPrint := false) "dir" => freeDirectory R r (G.program.length+t) link V wordSize entries desc
local notation3 (prettyPrint := false) "pinRows" => fun u => G.pinLayout u (ib u) (hb u) (sb u)
variable    (N : Network D (FreeBlock R V) (fun _ => wordSize)) (cell : N.Site → Fin task.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin sz) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : FreeBlock R V ↪ Fin np)
    (F : Fields sz task.cube.cables np task.cube.cells d k b σ) (x : Fin (R+1) → σ → Bool)
    (original : Fin entries ↪ N.Site)
    (bounds : (freeDirectory R r (G.program.length+t) link V wordSize entries desc).DestinationBounds)
    (base geo gap : ℕ) (profile mid : Fin (R+1) → Memory w)
    {decl : LengthDeclaration task.cube.n task.cube.header.d} {group : Fin task.cube.header.d → Fin (R+1)}
    {template : Frame} {id : TableEntry task.cube.n task.cube.b task.cube.h task.cube.K task.cube.s → ℕ} {count : ℕ}
    (alphabet : 0<task.cube.header.d)
    (owned : TeamRows.Returns (Fin (R+1)) task.cube w)
    (scan : ∀ u, ReportsThrough (owned.pub u) (owned.macros u) (owned.finalRegs u) (owned.output u))
local notation3 (prettyPrint := false) "live" => (Function.Embedding.refl (FreeBlock R V))
local notation3 (prettyPrint := false) "privateRows" => NativeDemands.privatePair N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "liveRows" => NativeDemands.livePair N cell edgeID portID dir original live gap
variable {f : ReturnedDelivery G pin ext L (freeDirectory R r (G.program.length+t) link V wordSize entries desc)
  (NativeDemands.privatePair N cell edgeID portID (freeDirectory R r (G.program.length+t) link V wordSize entries desc)
    original (Function.Embedding.refl (FreeBlock R V)) gap)
  (NativeDemands.livePair N cell edgeID portID (freeDirectory R r (G.program.length+t) link V wordSize entries desc)
    original (Function.Embedding.refl (FreeBlock R V)) gap)
  owner task.cube.cellBank task.cube.cellStride H (fun u => G.pinLayout u (ib u) (hb u) (sb u))}
local notation3 (prettyPrint := false) "head(" u ")" => ((H u).pub 0).val
local notation3 (prettyPrint := false) "pr(" u ")" => privateLayout (head(u)) geo task.cube.cables task.cube.cells (dir).entries (dir).description gap
local notation3 (prettyPrint := false) "tabs" => bases geo task.cube.cables task.cube.cells (dir).entries
local notation3 (prettyPrint := false) "p₀(" u ")" => ISA.placement (readings (mid u)) (pr(u)).raw
local notation3 (prettyPrint := false) "l₀(" u ")" => ISA.placement (readings (mid u)) (tabs).livePairs
local notation3 (prettyPrint := false) "published(" u ")" => ISA.publish (mid u) (head(u)) base ((dir).directory (p₀(u)) (l₀(u)))
local notation3 (prettyPrint := false) "canonical(" u ")" => ISA.publish (mid u) (head(u)) base ((dir).directory privateRows liveRows)
local notation3 (prettyPrint := false) "dataRows" => NativeDemands.rows N cell edgeID portID dir original live gap
local notation3 (prettyPrint := false) "recv" => NativeDemands.receiver N cell edgeID portID dir original live gap bounds
local notation3 (prettyPrint := false) "amount" => fun i : Fin (dataRows).length => dataRows[i.val].width
local notation3 (prettyPrint := false) "labels" => meanPackedLabel N cell recv amount (List.finRange task.cube.cells) task.cube.n task.cube.header.d alphabet
local notation3 (prettyPrint := false) "ownerMap" => greedyOwner (blocks:=task.cube.header.blocks) (K:=task.cube.K) (h:=task.cube.h) R task.cube.b task.cube.s labels recv amount

local notation3 (prettyPrint := false) "edgeOrder" => NativeDemands.cableOrder N cell edgeID

private theorem mean_host_capacity {depth cables C : ℕ} {Port Data : Type} [Fintype Data] {bit : Port → ℕ}
    (a : CubeArena.Layout) (model : Network depth Port bit) (tile : model.Site → Fin C)
    (ord : model.CrossingEdge tile ≃ Fin cables) (toCell : Data → Fin C) (size : Data → ℕ)
    (positive : 0<a.header.d) {volume : ℝ} {mass : ℕ}
    (budget : PackedLabelBudget model tile toCell size volume mass (a.header.d^(a.n+1)))
    (lane : 0<a.h*a.b) (blocks : a.header.blocks=blocksFor volume (a.h*a.b) (a.header.d^(a.n+1))) :
    let label := meanPackedLabel model tile toCell size (List.finRange C) a.n a.header.d positive
    ∀ u,load (cablePair ord (crossSrc model tile) (crossDst model tile) label)
      (crossWidth model tile ∘ ord.symm) u ≤ a.header.blocks*(a.h*a.b) := by
  intro label u
  rw [blocks]
  exact load_le_blocks ord (crossSrc model tile) (crossDst model tile) (crossWidth model tile) label
    (fun e => e.2) ((Nat.cast_nonneg _).trans budget.dataVolume) lane (pow_pos positive _)
    (meanPackedLoads model tile toCell size (List.finRange C) (List.nodup_finRange _)
      (by ext; simp) a.n a.header.d positive budget).1 u

include G owned task N cell aux siteID edgeID portID F x original bounds base geo gap profile mid alphabet in
/-- The native writer recovers both endpoint and literal source words in the physical
host-scatter image at the original compact owner of each cell. -/
theorem SharedWriters.matching_source_at_hosts
    (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) task.cube.header.blocks task.cube.K task.cube.h decl group)
    (handoff : OwnedHandoff f g src task.cube decl group template id count owned)
    (matchQ : Matching task.cube ownerMap decl (f.receivedRows g group))
    (observed : ObservedOwned task.cube decl group owned ownerMap (f.receivedRows g group) matchQ.val)
    (net : ∀ u, Represents N cell aux siteID edgeID portID F (x u)) (ids : ∀ c,(F.cells c).val=c.val)
    (fieldRoom : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k≤b) (wordFit : b≤w) (positive : 0<task.cube.cells)
    (img : ∀ u, Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) (x u) geo (readings (profile u)))
    (place : ∀ u,(pr(u)).Image (readings (profile u)) (dir).entries (readings (mid u)))
    (fit : ∀ u,(pr(u)).Fits w (readings (profile u)))
    (hdr : ∀ u,Header (head(u)) geo task.cube.cables task.cube.cells (dir).entries (readings (profile u)))
    (reserve : base+7*(dir).candidates≤geo) (endGeo : geo+5*task.cube.cables≤task.cube.header.header)
    (geoFit : geo<2^w) (teams : (dir).teams≤2^w) (procs : (dir).processors≤2^w) (fields : (dir).fields≤2^w)
    (literal : (dir).literal<2^w) (cells : task.cube.cells≤2^w) (stride : task.cube.cellStride≤2^w)
    (capacity : ∀ c,suppliedSize N cell c+gap+(∑ j,if cell (original j)=c then (dir).description else 0)≤task.cube.cellStride)
    {I : Type} [Fintype I] {sc : I → Fin task.cube.cells} {sid : I ↪ ℕ} {sw : I → ℕ}
    (B : Fin (R+1) → BroadcastFrame) (processor : ∀ u,Pins.ProcessorFields ((pinRows) u))
    {guess : Fin (R+1) → ℕ → Bool} (source : ∀ u,ProfileRouteInputs (processor u) (B u) (H u).pub (guess u) (canonical(u)))
    (team : ∀ u,(B u).team=u.val)
    (write : ∀ u,SlottedWriter task.cube dir privateRows liveRows ((pinRows) u) (H u).pub (mid u) base sc sid sw)
    {old : Fin (R+1) → Fin 81 → Word w} {fresh gates outputs width off ell controls X : ℕ}
    {Gbits : Fin (R+1) → List Bool} {claims : Fin (R+1) → List (List Bool)} {pad : Fin (R+1) → ℕ}
    {raw : Broadcast task.cube.n task.cube.header.d task.cube.header.cap}
    (room : ∀ u,PinnedRawInput (ar:=task.cube) (D:=dir) (pp:=privateRows) (lp:=liveRows) (pub:=(H u).pub)
      (slotted:=mid u) (base:=base) (B u) (old u) fresh gates outputs width off ell controls
      (Gbits u) (claims u) (pad u) raw R X)
    (decoded : (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) raw.1),
      fun row j => readCode (task.cube.header.cap+1) (raw.2 row j))=decl)
    (history : ∀ u, ∃ (regs lastReg : Bank w) (events : List (TeamRAM.Event w)) (last : Memory w)
      (W : WriterHistory task.cube.n (Cube.Tally.selectorWidth task.cube.n task.cube.K task.cube.h)
        (H u).pub (H u).macros regs (canonical(u)) events lastReg last),
      DemandInput task.cube dir privateRows liveRows owner (H u).pub W.dataInput ∧
      src u=readings W.sharedInput)
    {volume : ℝ} {mass : ℕ}
    (budget : PackedLabelBudget N cell recv amount volume mass (task.cube.header.d^(task.cube.n+1)))
    (lane : 0<task.cube.h*task.cube.b)
    (blocks : task.cube.header.blocks=blocksFor volume (task.cube.h*task.cube.b) (task.cube.header.d^(task.cube.n+1)))
    (hg : 0<wordSize) (roomFree : r*(2*(G.program.length+t)+R*link)≤V*wordSize)
    (input : Fin pins₀ → Bool) (subst : ∀ u,Pins.SubstitutionAt ((pinRows) u) (Pins.extendGuess input) (H u).initial)
    {reports : Fin (R+1) → ReportLayout} (roster : ReceivedRows reports task.cube.cells)
    (sections : Fin (R+1) → OpenSuffix.Inputs)
    {beforeTasks : Fin (R+1) → BeforeTasks}
    (served : (∀ u (i : Fin (roster.cells u).length),
      readings (owned.output u) (task.cube.hostDirectory+2*(roster.order ⟨u,i⟩).val)=u.val) ∨
      ∀ u (i : Fin (roster.cells u).length), ownerMap matchQ.val.1
        (labels (roster.order ⟨u,i⟩) (chosen task.cube.b task.cube.s matchQ.val.1))=u)
    (opened : ∀ u, OpenSuffix.Placement (sections u) task.cube (beforeTasks u) (owned.pub u 0).val
      (readings (owned.output u))) :
    let slot := packedSlotEmbedding N cell edgeOrder labels task.cube.header.blocks (task.cube.h*task.cube.b)
      (mean_host_capacity task.cube N cell edgeOrder recv amount alphabet budget lane blocks)
    SourceWords N cell edgeID portID hg roomFree liveRows task.cube.cellBank task.cube.cellStride (freeBits G input)
      (routedEnds N cell ownerMap slot matchQ.val)
      (fun c => OpenSuffix.hostImage (owned.pub (roster.order.symm c).1 0).val
        (readings (owned.output (roster.order.symm c).1))) := by
  intro slot
  choose regs lastReg events last W demand shared using history
  have keys (u : Fin (R+1)) (j : (dir).DestinationKey) :
      (dir).keyPlacement privateRows liveRows j=(dir).keyPlacement (p₀(u)) (l₀(u)) j :=
    NativeDemands.returned_key_placements N cell edgeID portID dir original live gap (fun _ => rfl)
      aux siteID F (x u) (net u) ids fieldRoom (head(u)) geo (readings (profile u)) (readings (mid u))
      (img u) (place u) (fit u) j
  have rowsEq (u : Fin (R+1)) : (dir).directory privateRows liveRows=(dir).directory (p₀(u)) (l₀(u)) :=
    (dir).directory_congr_keys _ _ _ _ bounds (keys u)
  have images (u : Fin (R+1)) : canonical(u)=published(u) := congrArg (ISA.publish (mid u) (head(u)) base) (rowsEq u)
  have tables := writer.matching_host_tables task dir N cell aux siteID edgeID portID F x original live bounds
    base geo gap profile mid alphabet symbols handoff matchQ observed net ids fieldRoom hk wordFit positive
    (fun _ => rfl) img place fit hdr reserve endGeo geoFit teams procs fields literal cells stride capacity
    B processor (fun u => images u ▸ source u) team (fun u => (write u).withKeyPlacements (keys u))
    (fun u => (room u).commonPlacement (rowsEq u)) decoded (fun u => by
      rw [←images u]
      exact ⟨regs u,lastReg u,events u,last u,W u,(demand u).ready,(demand u).records,shared u⟩)
  obtain ⟨pointers,intervalMem,earlier,row,tab⟩ := tables
  have stored : LivePlacement N cell edgeID portID (l₀(0)) := live_placement_of_image N cell edgeID portID aux siteID F
    (net 0) ids fieldRoom original (head(0)) geo (dir).description gap (readings (profile 0)) (readings (mid 0))
    (img 0) (place 0)
  have placement : LivePlacement N cell edgeID portID liveRows := fun a => (keys 0 (.inr a)).trans (stored a)
  have pointer (u : Fin (R+1)) : (hostLayout (owned).pub (owned).output u).cells=task.cube.hostDirectory :=
    (opened u).pointer
  have freeOwner (z : FreePort R r (G.program.length+t)) :
      let c := cell (N.attach (freeLane hg roomFree z).1)
      owner c.val=group (labels c (chosen task.cube.b task.cube.s matchQ.val.1)) := by
    intro c
    have rawOwner := free_owner_on_writer N cell edgeID portID hg roomFree privateRows liveRows (demand 0) placement z
    have same := writer.data_owner_after_owned symbols handoff observed 0 (W 0) (demand 0).ready (demand 0).records
      (shared 0) (pointer 0) c
    exact Fin.ext (rawOwner.symm.trans (same.trans (tab.cellOwner 0 c)))
  have rosterOwner (u : Fin (R+1)) (i : Fin (roster.cells u).length) :
      group (labels (roster.order ⟨u,i⟩) (chosen task.cube.b task.cube.s matchQ.val.1))=u := by
    rcases served with raw | logical
    · have word := tab.cellOwner u (roster.order ⟨u,i⟩)
      rw [pointer u] at word
      exact Fin.ext (word.symm.trans (raw u i))
    · exact (congrFun observed.allocation (labels (roster.order ⟨u,i⟩) (chosen task.cube.b task.cube.s matchQ.val.1))).symm.trans (logical u i)
  have before := native_source_words_at_inputs writer symbols handoff observed N cell edgeID portID edgeOrder labels tab
    (mean_host_capacity task.cube N cell edgeOrder recv amount alphabet budget lane blocks) hg roomFree placement input subst
    freeOwner pointers rfl rfl le_rfl
  have index (c : Fin task.cube.cells) :
      group (labels c (chosen task.cube.b task.cube.s matchQ.val.1))=(roster.order.symm c).1 := by
    obtain ⟨⟨u,i⟩,rfl⟩ := roster.order.surjective c
    exact (rosterOwner u i).trans (congrArg Sigma.fst (roster.order.symm_apply_apply ⟨u,i⟩)).symm
  have memories : hostWords labels (chosen task.cube.b task.cube.s matchQ.val.1) group owned.pub owned.output =
      (fun c => OpenSuffix.hostImage (owned.pub (roster.order.symm c).1 0).val
        (readings (owned.output (roster.order.symm c).1))) := by
    funext c
    change OpenSuffix.hostImage _ (readings (owned.output (group _)))=_
    rw [index c]
  rw [memories] at before
  exact before

include G owned scan task N cell aux siteID edgeID portID F x original bounds base geo gap profile mid alphabet in
/-- The actual owned output and its control and report successors suffice to read both
routed endpoints and the original free inputs, before any sparse argument is fitted. -/
theorem SharedWriters.matching_source_through_reports
    (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) task.cube.header.blocks task.cube.K task.cube.h decl group)
    (handoff : OwnedHandoff f g src task.cube decl group template id count owned)
    (matchQ : Matching task.cube ownerMap decl (f.receivedRows g group))
    (observed : ObservedOwned task.cube decl group owned ownerMap (f.receivedRows g group) matchQ.val)
    (net : ∀ u, Represents N cell aux siteID edgeID portID F (x u)) (ids : ∀ c,(F.cells c).val=c.val)
    (fieldRoom : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (hk : k≤b) (wordFit : b≤w) (positive : 0<task.cube.cells)
    (img : ∀ u, Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) (x u) geo (readings (profile u)))
    (place : ∀ u,(pr(u)).Image (readings (profile u)) (dir).entries (readings (mid u)))
    (fit : ∀ u,(pr(u)).Fits w (readings (profile u)))
    (hdr : ∀ u,Header (head(u)) geo task.cube.cables task.cube.cells (dir).entries (readings (profile u)))
    (reserve : base+7*(dir).candidates≤geo) (endGeo : geo+5*task.cube.cables≤task.cube.header.header)
    (geoFit : geo<2^w) (teams : (dir).teams≤2^w) (procs : (dir).processors≤2^w) (fields : (dir).fields≤2^w)
    (literal : (dir).literal<2^w) (cells : task.cube.cells≤2^w) (stride : task.cube.cellStride≤2^w)
    (capacity : ∀ c,suppliedSize N cell c+gap+(∑ j,if cell (original j)=c then (dir).description else 0)≤task.cube.cellStride)
    {I : Type} [Fintype I] {sc : I → Fin task.cube.cells} {sid : I ↪ ℕ} {sw : I → ℕ}
    (B : Fin (R+1) → BroadcastFrame) (processor : ∀ u,Pins.ProcessorFields ((pinRows) u))
    {guess : Fin (R+1) → ℕ → Bool} (source : ∀ u,ProfileRouteInputs (processor u) (B u) (H u).pub (guess u) (canonical(u)))
    (team : ∀ u,(B u).team=u.val)
    (write : ∀ u,SlottedWriter task.cube dir privateRows liveRows ((pinRows) u) (H u).pub (mid u) base sc sid sw)
    {old : Fin (R+1) → Fin 81 → Word w} {fresh gates outputs width off ell controls X : ℕ}
    {Gbits : Fin (R+1) → List Bool} {claims : Fin (R+1) → List (List Bool)} {pad : Fin (R+1) → ℕ}
    {raw : Broadcast task.cube.n task.cube.header.d task.cube.header.cap}
    (room : ∀ u,PinnedRawInput (ar:=task.cube) (D:=dir) (pp:=privateRows) (lp:=liveRows) (pub:=(H u).pub)
      (slotted:=mid u) (base:=base) (B u) (old u) fresh gates outputs width off ell controls
      (Gbits u) (claims u) (pad u) raw R X)
    (decoded : (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) raw.1),
      fun row j => readCode (task.cube.header.cap+1) (raw.2 row j))=decl)
    (history : ∀ u, ∃ (regs lastReg : Bank w) (events : List (TeamRAM.Event w)) (last : Memory w)
      (W : WriterHistory task.cube.n (Cube.Tally.selectorWidth task.cube.n task.cube.K task.cube.h)
        (H u).pub (H u).macros regs (canonical(u)) events lastReg last),
      DemandInput task.cube dir privateRows liveRows owner (H u).pub W.dataInput ∧
      src u=readings W.sharedInput)
    {volume : ℝ} {mass : ℕ}
    (budget : PackedLabelBudget N cell recv amount volume mass (task.cube.header.d^(task.cube.n+1)))
    (lane : 0<task.cube.h*task.cube.b)
    (blocks : task.cube.header.blocks=blocksFor volume (task.cube.h*task.cube.b) (task.cube.header.d^(task.cube.n+1)))
    (hg : 0<wordSize) (roomFree : r*(2*(G.program.length+t)+R*link)≤V*wordSize)
    (input : Fin pins₀ → Bool) (subst : ∀ u,Pins.SubstitutionAt ((pinRows) u) (Pins.extendGuess input) (H u).initial)
    {reports : Fin (R+1) → ReportLayout} (roster : ReceivedRows reports task.cube.cells)
    (sections : Fin (R+1) → OpenSuffix.Inputs)
    {post : Fin (R+1) → AfterTasks} {beforeTasks : Fin (R+1) → BeforeTasks}
    {banks : Fin (R+1) → CellBanks.Layout} {cursor : Fin (R+1) → ReportCursor} {description : Fin (R+1) → ℕ}
    (served : (∀ u (i : Fin (roster.cells u).length),
      readings (owned.output u) (task.cube.hostDirectory+2*(roster.order ⟨u,i⟩).val)=u.val) ∨
      ∀ u (i : Fin (roster.cells u).length), ownerMap matchQ.val.1
        (labels (roster.order ⟨u,i⟩) (chosen task.cube.b task.cube.s matchQ.val.1))=u)
    (ready : ∀ u, OpenSuffix.Ready (sections u) (owned.pub u 0).val (readings (owned.output u)) w)
    (opened : ∀ u, OpenSuffix.Placement (sections u) task.cube (beforeTasks u) (owned.pub u 0).val
      (readings (owned.output u)))
    (alloc : ∀ u,ReportAllocation (beforeTasks u) (post u) (banks u) (reports u) (roster.cells u) (cursor u))
    (seed : ∀ u,PreparedReportInput (owned.pub u) (scan u).controls.val.2.2 (roster.cells u) (cursor u) (description u))
    (origins : ∀ u,(banks u).bankStart=task.cube.cellBank) (strides : ∀ u,(banks u).stride=task.cube.cellStride)
    (widths : ∀ u (i : Fin (roster.cells u).length),((roster.cells u).get i).supplied=suppliedSize N cell (roster.order ⟨u,i⟩)) :
    let slot := packedSlotEmbedding N cell edgeOrder labels task.cube.header.blocks (task.cube.h*task.cube.b)
      (mean_host_capacity task.cube N cell edgeOrder recv amount alphabet budget lane blocks)
    SourceWords N cell edgeID portID hg roomFree liveRows task.cube.cellBank task.cube.cellStride (freeBits G input)
      (routedEnds N cell ownerMap slot matchQ.val)
      (fun c => readings (scan (roster.order.symm c).1).reports.val.2.2) := by
  intro slot
  have before := writer.matching_source_at_hosts task N cell aux siteID edgeID portID F x original bounds base geo gap
    profile mid alphabet owned symbols handoff matchQ observed net ids fieldRoom hk wordFit positive img place fit
    hdr reserve endGeo geoFit teams procs fields literal cells stride capacity B processor source team write room decoded
    history budget lane blocks hg roomFree input subst roster sections served opened
  have placement : LivePlacement N cell edgeID portID liveRows :=
    Diagonal.ExternalSew.live_pair_slots N cell edgeID portID original gap
  exact roster.sourceWords_through_reports N cell edgeID portID hg roomFree liveRows task.cube.cellBank task.cube.cellStride
    (freeBits G input) (routedEnds N cell ownerMap slot matchQ.val) scan task.cube sections placement ready opened alloc seed
    origins strides widths before

end TeamContraction

end BorderVNP
end Computability
end OAI
