import OAI.Computability.VPVNP.LiveCompressedPairTerminalAssembly
import OAI.Computability.VPVNP.PairSimulationPhysicalScanData
import OAI.Computability.VPVNP.PairVertexOrdinalPhase
import OAI.Computability.VPVNP.PairVertexAscendingCosts

/-!
# Building a terminal branch from the actual wire scan and site table

For a selected compression state, the shared-bit worker traverses the
ordered payload bank and the fixed vertex program runs one burst for each
site ordinal, followed by the final closing call. The constructor uses the
source-to-physical replay at the two controller words and leaves exactly
the selected sum of site exponents at each motif counter.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair
open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords SourceTransport NetworkKernel
open PairSimulation LocalHistory TerminalLink
open scoped Fin.CommRing

attribute [local irreducible] VertexImage.template VertexImage.segments TerminalProgram.workers PhysicalScanData.physical stateScanPhase

variable {a g v p r k : ℕ} (X : State a g) (M : Machine v p r k)
  (pc : Fin 10 → Fin p) (reg : Fin 2 ↪ Fin r) (bank : Fin k) (done : Fin p)
  (hl : FinalBits.Linked M pc reg bank done) (he : M.entry=pc 0)
  (oldLow : ℕ) (bankAddr : M.publicData bank = FinalBits.cursor v oldLow 0) (oldMem : Memory v)
  (extra : ℕ) (oldFit : oldLow + X.totalWidth < 2^v)

local notation "scan₀" => stateScanPhase X M pc reg bank done hl he oldLow bankAddr oldMem extra oldFit

variable {w cap ns labels : ℕ} {R : Type*} [CommRing R] {Label : Type} [Fintype Label] {κ : Label → R}
  (parsers : SiteParsers κ X.network) (order : Fin ns ≃ X.network.Site) (names : Fin labels ≃ Label)
  (shape : DescriptorSpace.Shape) (limit : ℕ) {geometry rootFields leaf shrink refresh : VertexImage.Segment}
  (ports : Fin 11 → Word w)

local notation "code" => VertexImage.segments geometry rootFields leaf shrink refresh
local notation "workers₀" => TerminalProgram.workers shape limit code

variable {mem : Memory w} (q : QuietPrefix (TerminalProgram.workers shape limit (VertexImage.segments geometry rootFields leaf shrink refresh)) ports cap mem)
  (lo : ℕ) (beforeBits : Memory w) (wireLayout : FinalBits.Worker.Layout ports beforeBits lo X.totalWidth)
  (clockRoom : 54 ≤ cap) (headerRoom : (header ports).val + 32 ≤ 2^w)
  (below : lo + X.totalWidth ≤ (header ports).val)
  (readAgree : Agree (workerCell (header ports)) beforeBits q.traversalRows.val.memory)

local notation "shared" => PhysicalScanData.physical X M pc reg bank done hl he oldLow bankAddr oldMem extra oldFit
  shape limit code ports cap beforeBits q.traversalRows.val.memory lo wireLayout clockRoom headerRoom below readAgree

variable (counter grammar : ℕ)
local notation "siteFields" x => WireTensor.edgeAssignment X.network.src X.network.dst (ScanPhase.payload scan₀ x)
local notation "ordinal" x => VertexImage.siteOrdinals parsers order names (siteFields x)
local notation "machine₀" => Machine.program (Template.instantiate (VertexImage.template code) w ports)

/-- Local physical facts still needed for each single active site burst.
The ascending traversal, source-to-controller replay and wire assignment
are constructed by the terminal branch below. -/
structure SelectedSites (x : (scan₀).Path) where
  /-- Memory against which the worker checks the unchanged descriptor cells. -/
  reference : Memory w
  /-- Memory from which the unlinked ascending vertex worker starts. -/
  sourceMem : Memory w
  active : VertexImage.ActiveCalls (ordinal x) machine₀ cap counter grammar
    (VertexFrame.Linked (header ports) counter grammar labels reference)
  stored : ∀ m, VertexFrame.Linked (header ports) counter grammar labels reference ns m →
    m (TerminalSiteStart.headerWord ports + 7).val = (ns : Word w)
  checks : ∀ (i : Fin ns) (m : Memory w), VertexFrame.Linked (header ports) counter grammar labels reference i.val m →
    ∀ (y : (ordinal x).Choice i) (rep : Report w),
      execute machine₀ cap ((machine₀).start (i.val : Word w)) m ((ordinal x).encode i y) = some rep →
        Reads (workerCell (header ports)) rep.events ∧ rep.events.length+1 ≤ cap-30
  sourceReady : VertexFrame.Linked (header ports) counter grammar labels reference 0 sourceMem
  physicalReady : VertexFrame.Linked (header ports) counter grammar labels reference 0 (shared x).val.memory
  agree : Agree (workerCell (header ports)) sourceMem (shared x).val.memory

variable (visit : ∀ x : (stateScanPhase X M pc reg bank done hl he oldLow bankAddr oldMem extra oldFit).Path,
  SelectedSites X M pc reg bank done hl he oldLow bankAddr oldMem extra oldFit
    parsers order names shape limit ports q lo beforeBits wireLayout clockRoom headerRoom below readAgree counter grammar x)

private theorem siteReplay (x : (scan₀).Path) :
    WorkerFrame workers₀ ports cap (.resume TerminalLink.Stage.vertices 0) (visit x).sourceMem (shared x).val.memory :=
  VertexImage.ordinalWorkerFrame (D := ordinal x) (cap := cap) (base := counter) (grammar := grammar)
    (geometry := geometry) (rootFields := rootFields) (leaf := leaf) (shrink := shrink) (refresh := refresh) shape limit (visit x).reference (visit x).sourceMem (shared x).val.memory
    (visit x).active (VertexImage.template_closes (geometry := geometry) (rootFields := rootFields) (leaf := leaf) (shrink := shrink) (refresh := refresh) (pub := ports) (by omega : 15 ≤ cap) (visit x).stored) headerRoom
    (by omega : 45 ≤ cap) (visit x).checks (visit x).sourceReady (visit x).physicalReady (visit x).agree

local notation "replay" => siteReplay X M pc reg bank done hl he oldLow bankAddr oldMem extra oldFit
  parsers order names shape limit ports q lo beforeBits wireLayout clockRoom headerRoom below readAgree counter grammar visit

/-- The two nondeterministic phases of the fixed finite terminal program,
with every wire bit and site witness interpreted on its selected memory. -/
noncomputable def selectedTerminalBranch : TerminalBranchData workers₀ ports cap mem scan₀ parsers where
  setup := q
  bitPaths := shared
  vertexPaths x := VertexImage.sitePhysical (Frame := VertexFrame.Linked (header ports) counter grammar labels (visit x).reference) parsers order names (siteFields x) shape limit
    (visit x).sourceMem (shared x).val.memory (visit x).active (by omega : 15 ≤ cap)
    (visit x).sourceReady (visit x).stored (replay x)

local notation "branch" => selectedTerminalBranch X M pc reg bank done hl he oldLow bankAddr oldMem extra oldFit
  parsers order names shape limit ports q lo beforeBits wireLayout clockRoom headerRoom below readAgree counter grammar visit

theorem selectedTerminalBranch_tapes (x : (scan₀).Path)
    (ys : ∀ v, (parsers.witnesses v ((siteFields x) v)).Choice) :
    ((branch).bitPaths x).val.choices = (scan₀).calls x ++ [[]] ∧
    ((branch).vertexPaths x ys).val.choices =
      (List.ofFn fun j => (parsers.read (order j) ((siteFields x) (order j))).encode (ys (order j))) ++ [[]] :=
  ⟨PhysicalScanData.physical_choices ..,rfl⟩

theorem selectedTerminalBranch_readback (x : (scan₀).Path)
    (ys : ∀ v, (parsers.witnesses v ((siteFields x) v)).Choice) :
    Agree (workerCell (header ports)) ((ordinal x).finalMemory counter grammar (visit x).sourceMem
      (fun j => ys (order j))) ((branch).vertexPaths x ys).val.memory :=
  VertexImage.physicalSite_memory parsers order names (siteFields x) shape limit (visit x).sourceMem
    (shared x).val.memory (visit x).active (by omega : 15 ≤ cap) (visit x).sourceReady (visit x).stored (replay x) ys

/-- The gadget-label counter is updated by the sum of the powers of the
chosen terminal site witnesses. Its incoming value is the actual source word. -/
theorem selectedTerminalBranch_counter (x : (scan₀).Path)
    (ys : ∀ v, (parsers.witnesses v ((siteFields x) v)).Choice) (l : Fin labels)
    (cell : workerCell (header ports) (counter + grammar + l)) :
    ((branch).vertexPaths x ys).val.memory (counter + grammar + l) =
      (visit x).sourceMem (counter + grammar + l) +
        ((∑ v, (parsers.witnesses v ((siteFields x) v)).exponents (ys v) (names l) : ℕ) : Word w) :=
  VertexImage.physicalSite_histogram parsers order names (siteFields x) shape limit (visit x).sourceMem
    (shared x).val.memory (visit x).active (by omega : 15 ≤ cap) (visit x).sourceReady (visit x).stored (replay x) ys l cell

/-- The last two native stages contain one scan report per shared bit and
one charged vertex report per ordinal, followed by their respective guards.
The bound for a vertex can depend on its selected occurrence tree. -/
theorem selectedTerminalBranch_rows (x : (scan₀).Path)
    (ys : ∀ v, (parsers.witnesses v ((siteFields x) v)).Choice)
    (ok : X.network.Site → Report w → Prop)
    (checks : ∀ i m, VertexFrame.Linked (header ports) counter grammar labels (visit x).reference i.val m →
      ∀ (y : (ordinal x).Choice i) r, execute machine₀ cap ((machine₀).start (i.val : Word w)) m
        ((ordinal x).encode i y) = some r → ok (order i) r) :
    let bits := PhysicalScanData.assignment X M pc reg bank done hl he oldLow bankAddr oldMem extra oldFit x
    let last := (ordinal x).finalMemory counter grammar (visit x).sourceMem (fun i => ys (order i))
    ((branch).bitPaths x).val.logs.map Prod.snd = FinalBits.Worker.reports ports 0 beforeBits bits ∧
      ∃ reps : X.network.Site → Report w, (∀ v, ok v (reps v)) ∧
        ((branch).vertexPaths x ys).val.logs.map Prod.snd = (List.ofFn fun i => reps (order i)) ++
          [VertexImage.closingReport ports last] := by
  intro bits last
  refine ⟨?_,?_⟩
  · unfold selectedTerminalBranch PhysicalScanData.physical
    exact stageLogs_raw (.resume TerminalLink.Stage.sharedBits 0) _
  · exact VertexImage.physicalSite_rows parsers order names (siteFields x) shape limit (visit x).sourceMem
      (shared x).val.memory (visit x).active (by omega : 15 ≤ cap) (visit x).sourceReady (visit x).stored
      (replay x) ys ok checks

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
