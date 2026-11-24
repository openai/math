import OAI.Computability.VPVNP.PairRefreshTraversalCanonical
import OAI.Computability.VPVNP.PairRefreshResidentReads
import OAI.Computability.VPVNP.PairRefreshResidentMapExact
import OAI.Computability.VPVNP.PairSimulationFieldReadSafety

/-!
# The chronological refresh action and its upper scratch state

The event list of a successful local visit depends on the actual node halves, the
selected term, the published level headers and the four-word geometry reload.
Its private scratch update acts on the incoming scratch independently of unrelated
host registers or private memory below the DFS boundary.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TraversalPlan

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe PairSimulation VertexImage NodeArguments NewSlots RefreshMapOperands NetworkKernel
open MotifConversion MotifEntry MotifDemandPadding MotifSelector LocalHistory
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) {t hist bits g : ℕ}
  (ties : Fin t ≃ Tie (2 ^ S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)
  (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2 ^ S.portExponent)) (degree n rowEnd child parent : ℕ)

local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "hd" => And.right S.degree_bounds
local notation "T" => plan B ties stride order
local notation "Y" =>
  dyadicRefreshNext X S.graph (Nat.two_pow_pos _) hc B.refresh S.port_order hd choice
local notation "R" => TerminalLayout.privateRegions degree n rowEnd hist
local notation "A" => LeafArena.Regions.arguments R
local notation "hb" => LeafArena.Regions.histBase R
local notation "dir" => hb + hist + 12 + 2 * n
local notation "K" => MapCallWords.headCapacity (2 ^ S.portExponent) (2 ^ S.expanderExponent)
local notation "demand" =>
  blockDemandWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) (Prod.fst v)
local notation "copies" => repetitions B.refresh demand
local notation "O" => sites (D := 2 ^ S.portExponent) X.baseIndex (bitWordFinEquiv g)

/-- The selected physical fit conditions needed by the terminal private arena.
All conditions hold or fail independently of the particular guessed old half. -/
structure Room (hist bits : ℕ) : Prop where
  childBound : child < rowEnd
  parentBound : parent < rowEnd
  oldDegree : 2 ^ S.portExponent ≤ degree
  newDegree : 2 ^ (S.degreeExponent 0) ≤ degree
  oldWidth : X.maxWireWidth ≤ n
  newWidth : (Y).maxWireWidth ≤ n
  copyBound : copies ≤ n
  large : K + 12 ≤ n
  five : 5 ≤ n
  capacity : MapWorkspace.Capacity B.refresh bits n
    (TerminalLayout.privateRegions degree n rowEnd hist).cacheBase
  tableWidth : MapConstants.widthThreshold B.refresh ≤ bits

variable (room : Room B X choice v degree n rowEnd child parent hist bits)
  (old : X.network.Half (oldSite X v))
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order))
    B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites v))
  (m : Memory bits) (oldHead newHead : ℕ) (G : W bits)

/-- Canonical successful traversal trace consisting of four geometry-reload ticks and the
resident plan's selected refresh events. -/
noncomputable def canonicalEvents : List (Event bits) :=
  List.replicate 4 .tick ++ (T).successEvents X choice v m old new room.tableWidth
    (operands (O v).val parent newHead hb G) (word oldHead)

set_option maxHeartbeats 1200000 in
-- Constructing the scratch update elaborates the size witnesses for both node frames.
/-- Private scratch image after the selected refresh map executes with the bounded child and
parent frames, copy buffers, and histogram. -/
noncomputable def canonicalUpper {endAddr : ℕ}
    (s : DFS.Scratch bits endAddr) : DFS.Scratch bits endAddr :=
  (T).mapUpper X choice v A child parent old new hb n dir hb
    (TraversalGeometry.argument_end degree n rowEnd hist X (oldSite X v) old child room.childBound
      room.oldDegree room.oldWidth)
    (TraversalGeometry.argument_end degree n rowEnd hist Y (promotedSites v) new parent
      room.parentBound room.newDegree room.newWidth)
    room.oldWidth room.newWidth (by omega) (by omega)
    (TraversalGeometry.workspace_before_cache degree n rowEnd hist K copies room.large room.five
      room.copyBound).2
    room.capacity room.copyBound room.tableWidth endAddr s

local notation "events" =>
  canonicalEvents B ties stride order X choice v degree n rowEnd child parent room old new
    m oldHead newHead G
local notation "upper" =>
  canonicalUpper B ties stride order X choice v degree n rowEnd child parent room old new

/-- The traversal action combines the diagonal and map result with its canonical successful
events and private scratch update. -/
noncomputable def canonicalAction {endAddr : ℕ} (s : DFS.Scratch bits endAddr) :
    Option (List (Event bits) × DFS.Scratch bits endAddr) :=
  if (emitted B order X choice v old new).isSome then some (events, upper s) else none

variable (U V : IncidenceDirectory bits) (start listHead : ℕ)

local notation "Pl" =>
  Allocation.plan X (S.degreeExponent 0) (2 ^ S.expanderExponent) t stride start
local notation "pub" => operands (Fin.val (O v)) parent newHead hb G
local notation "st" => word (bits := bits) oldHead
local notation "I" => entryInput B X choice v old new
local notation "z" => demandGrid B.refresh (fun _ => zero_lt_one) (EntryInput.demand I)

set_option maxHeartbeats 1400000 in
-- The trace bound instantiates the three dependent field-read families at the terminal.
/-- All external reads of the exact event list avoid the scheduler's two control
cells in the fitting terminal header. -/
theorem canonical_worker_reads {fit :
    Fintype.card X.Base * 2 ^ S.portExponent * 2 ^ g * 2 ^ S.portExponent ≤ 2 ^ bits}
    (header : TraversalHeaders.Geometry (Fintype.card X.Base) g oldHead newHead start A U V m)
    (row : DFS.Row m parent listHead [word child]) (lanes : 2 ^ g < 2 ^ bits)
    (oldCols : U.ActualColumns X m) (newCols : V.ActualColumns Y m)
    (terminal : W bits) (terminalFit : terminal.val + 31 < 2 ^ bits)
    (oldBefore : oldHead + 60 < terminal.val) (newBefore : newHead + 59 < terminal.val)
    (parentBefore : parent < terminal.val) (listBefore : listHead < terminal.val)
    (area : (Pl).supply ≤ terminal.val)
    (oldIn : U.actualIn.val + Fintype.card X.Base * 2 ^ (S.portExponent + g) * 2 ^ S.portExponent ≤
      terminal.val)
    (oldWidth : U.width.val + Fintype.card X.Base * 2 ^ (S.portExponent + g) * 2 ^ S.portExponent ≤
      terminal.val)
    (newIn : V.actualIn.val + Fintype.card (State.Base Y) * 2 ^ g * 2 ^ (S.degreeExponent 0) ≤
      terminal.val)
    (newWidth : V.width.val + Fintype.card (State.Base Y) * 2 ^ g * 2 ^ (S.degreeExponent 0) ≤
      terminal.val)
    (wide : 2 ^ S.portExponent < 2 ^ bits)
    (enough : 2 + 2 ^ S.portExponent * 2 ^ S.expanderExponent ≤ stride) :
    SourceTransport.Reads (TerminalLink.workerCell terminal) events := by
  obtain ⟨dia, route, directory, fields⟩ :=
    canonical_reads B ties stride order X choice v A U V m start parent child listHead oldHead
      newHead hb G (fit := fit) header row lanes oldCols newCols terminal.val terminal.isLt.le
      oldBefore newBefore parentBefore listBefore area oldIn oldWidth newIn newWidth wide enough
  have allowed : SourceTransport.Reads (· < terminal.val)
      ((T).successEvents X choice v m old new room.tableWidth pub st) := by
    apply (T).successEvents_readsFrom X choice v m old new room.tableWidth pub st _ dia route
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [MapArgumentWriter.recipes, Fin.snoc_last] using directory
    · simpa only [MapArgumentWriter.recipes, Fin.snoc_castSucc] using fields (z, v.2) j
  intro a value ha
  rcases List.mem_append.mp ha with tick | cell
  · cases List.eq_of_mem_replicate tick
  · exact TerminalLink.workerCell_of_lt terminalFit (allowed a value cell)

end CompressorRecords.PortRefresh.TraversalPlan

end VPVNP
end Computability
end OAI
