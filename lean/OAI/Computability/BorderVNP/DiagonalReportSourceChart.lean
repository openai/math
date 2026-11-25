import OAI.Computability.BorderVNP.DiagonalMatchingSourceThroughReports

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

variable {R r t pins₀ link inner n w V wordSize entries desc D sz ne np d k b : ℕ}
    {Edge : Type} {G : Wiring R r t pins₀ link inner n Edge}
    {pin : Fin pins₀ → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}
    {H : Fin (R+1) → TeamHistory w} {ib hb sb : Fin (R+1) → ℕ}
    {owner : ℕ → Fin (R+1)} (task : SignedTaskArena.Layout)
    {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {anchor : Fin (R+1)}
    {σ : Type} [Fintype σ]
local notation3 (prettyPrint := false) "dir" => freeDirectory R r (G.program.length+t) link V wordSize entries desc
local notation3 (prettyPrint := false) "pinRows" => fun u => G.pinLayout u (ib u) (hb u) (sb u)
variable    (N : Network D (FreeBlock R V) (fun _ => wordSize)) (cell : N.Site → Fin task.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin sz) (edgeID : N.Edge ↪ Fin ne) (portID : FreeBlock R V ↪ Fin np)
    (F : Fields sz ne np task.cube.cells d k b σ) (x : Fin (R+1) → σ → Bool)
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

open private mean_host_capacity from OAI.Computability.BorderVNP.DiagonalMatchingSourceThroughReports

include G owned task N cell aux siteID edgeID portID F x original bounds base geo gap profile mid alphabet in
/-- The original chart's chosen owner and slot recover physical host words
without requiring a local report from any team. -/
theorem SharedWriters.matching_host_in_chart
    (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) task.cube.header.blocks task.cube.K task.cube.h decl group)
    (handoff : OwnedHandoff f g src task.cube decl group template id count owned)
    (issuedOwner : (BorderVNP.Cube.Packet task.cube.n task.cube.header.d task.cube.header.blocks →
      BorderVNP.Cube.Selector task.cube.n task.cube.K task.cube.h) → Fin task.cube.header.d → Fin (R+1))
    (matchQ : Matching task.cube issuedOwner decl (f.receivedRows g group))
    (observed : ObservedOwned task.cube decl group owned issuedOwner (f.receivedRows g group) matchQ.val)
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
      ∀ u (i : Fin (roster.cells u).length), issuedOwner matchQ.val.1
        (labels (roster.order ⟨u,i⟩) (chosen task.cube.b task.cube.s matchQ.val.1))=u)
    (opened : ∀ u, OpenSuffix.Placement (sections u) task.cube (beforeTasks u) (owned.pub u 0).val
      (readings (owned.output u)))
    (cableCount : ne=task.cube.cables)
    (issuedSlot : LiveBit N cell ↪ Slot task.cube.n task.cube.header.d task.cube.header.blocks (task.cube.h*task.cube.b))
    (ownerEq : issuedOwner=ownerMap)
    (slotEq : ∀ bound : ∀ j,load (cablePair edgeOrder (crossSrc N cell) (crossDst N cell) labels)
        (crossWidth N cell ∘ (edgeOrder).symm) j≤task.cube.header.blocks*(task.cube.h*task.cube.b),
      packedSlotEmbedding N cell edgeOrder labels task.cube.header.blocks (task.cube.h*task.cube.b) bound=issuedSlot) :
    SourceWords N cell edgeID portID hg roomFree liveRows task.cube.cellBank task.cube.cellStride (freeBits G input)
      (routedEnds N cell issuedOwner issuedSlot matchQ.val)
      (fun c => OpenSuffix.hostImage (owned.pub (roster.order.symm c).1 0).val
        (readings (owned.output (roster.order.symm c).1))) := by
  subst ne
  subst issuedOwner
  have result := writer.matching_source_at_hosts task N cell aux siteID edgeID portID F x original bounds base geo gap
    profile mid alphabet owned symbols handoff matchQ observed net ids fieldRoom hk wordFit positive img place fit
    hdr reserve endGeo geoFit teams procs fields literal cells stride capacity B processor source team write room decoded
    history budget lane blocks hg roomFree input subst roster sections served opened
  simpa only [slotEq] using result

include G owned scan task N cell aux siteID edgeID portID F x original bounds base geo gap profile mid alphabet in
/-- The actual owned output and its control and report successors suffice to read both
routed endpoints and the original free inputs, before any sparse argument is fitted. -/
theorem SharedWriters.matching_source_through_chart
    (writer : SharedWriters f g src)
    (symbols : SymbolFrame g (src anchor) task.cube.header.blocks task.cube.K task.cube.h decl group)
    (handoff : OwnedHandoff f g src task.cube decl group template id count owned)
    (issuedOwner : (BorderVNP.Cube.Packet task.cube.n task.cube.header.d task.cube.header.blocks →
      BorderVNP.Cube.Selector task.cube.n task.cube.K task.cube.h) → Fin task.cube.header.d → Fin (R+1))
    (matchQ : Matching task.cube issuedOwner decl (f.receivedRows g group))
    (observed : ObservedOwned task.cube decl group owned issuedOwner (f.receivedRows g group) matchQ.val)
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
      ∀ u (i : Fin (roster.cells u).length), issuedOwner matchQ.val.1
        (labels (roster.order ⟨u,i⟩) (chosen task.cube.b task.cube.s matchQ.val.1))=u)
    (ready : ∀ u, OpenSuffix.Ready (sections u) (owned.pub u 0).val (readings (owned.output u)) w)
    (opened : ∀ u, OpenSuffix.Placement (sections u) task.cube (beforeTasks u) (owned.pub u 0).val
      (readings (owned.output u)))
    (alloc : ∀ u,ReportAllocation (beforeTasks u) (post u) (banks u) (reports u) (roster.cells u) (cursor u))
    (seed : ∀ u,PreparedReportInput (owned.pub u) (scan u).controls.val.2.2 (roster.cells u) (cursor u) (description u))
    (origins : ∀ u,(banks u).bankStart=task.cube.cellBank) (strides : ∀ u,(banks u).stride=task.cube.cellStride)
    (widths : ∀ u (i : Fin (roster.cells u).length),((roster.cells u).get i).supplied=suppliedSize N cell (roster.order ⟨u,i⟩))
    (cableCount : ne=task.cube.cables)
    (issuedSlot : LiveBit N cell ↪ Slot task.cube.n task.cube.header.d task.cube.header.blocks (task.cube.h*task.cube.b))
    (ownerEq : issuedOwner=ownerMap)
    (slotEq : packedSlotEmbedding N cell edgeOrder labels task.cube.header.blocks (task.cube.h*task.cube.b)
      (mean_host_capacity task.cube N cell edgeOrder recv amount alphabet budget lane blocks)=issuedSlot) :
    SourceWords N cell edgeID portID hg roomFree liveRows task.cube.cellBank task.cube.cellStride (freeBits G input)
      (routedEnds N cell issuedOwner issuedSlot matchQ.val)
      (fun c => readings (scan (roster.order.symm c).1).reports.val.2.2) := by
  subst ne
  subst issuedOwner
  subst issuedSlot
  exact writer.matching_source_through_reports task N cell aux siteID edgeID portID F x original bounds base geo gap
    profile mid alphabet owned scan symbols handoff matchQ observed net ids fieldRoom hk wordFit positive img place fit
    hdr reserve endGeo geoFit teams procs fields literal cells stride capacity B processor source team write room decoded
    history budget lane blocks hg roomFree input subst roster sections served ready opened alloc seed origins strides widths

end TeamContraction

end BorderVNP
end Computability
end OAI
