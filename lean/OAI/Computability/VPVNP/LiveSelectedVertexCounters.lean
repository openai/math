import OAI.Computability.VPVNP.LiveCompressedPairVertexAssembly
import OAI.Computability.VPVNP.LiveVertexJobDeposits

/-! # Deposits of the actual selected terminal branch on its input counters -/

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

variable (visit : ∀ x : (stateScanPhase X M pc reg bank done hl he oldLow bankAddr oldMem extra oldFit).Path,
  SelectedSites X M pc reg bank done hl he oldLow bankAddr oldMem extra oldFit
    parsers order names shape limit ports q lo beforeBits wireLayout clockRoom headerRoom below readAgree counter grammar x)

local notation "branch" => selectedTerminalBranch X M pc reg bank done hl he oldLow bankAddr oldMem extra oldFit
  parsers order names shape limit ports q lo beforeBits wireLayout clockRoom headerRoom below readAgree counter grammar visit

/-- On every counter cell the genuine last block writes exactly the
selected jobs' deposits on the nominated pair memory. The shared-bit
phase and the earlier metadata stages need only preserve the incoming
word at this particular cell. -/
theorem selectedTerminalBranch_deposited (x : TerminalData scan₀ parsers)
    (trees : X.network.Site → DFS.VertexTree) (jobs : JobsFor parsers) (valid : JobsSpec parsers trees jobs)
    (input : Memory w) (a : ℕ) (cell : workerCell (header ports) a)
    (before : (visit x.arcs).sourceMem a = input a) :
    ((branch).vertexPaths x.arcs x.choices).val.memory a =
    Counters.visit counter grammar (fun v l => ((x.jobs jobs v).map (fun j => j.increment (names l))).sum)
      (List.ofFn order) input a := by
  have read := selectedTerminalBranch_readback X M pc reg bank done hl he oldLow bankAddr oldMem extra oldFit
    parsers order names shape limit ports q lo beforeBits wireLayout clockRoom headerRoom below readAgree
    counter grammar visit x.arcs x.choices
  exact (read a cell).symm.trans (x.deposits order names trees jobs valid counter grammar (visit x.arcs).sourceMem input a before)

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
