import OAI.Computability.VPVNP.LiveCompressedPairVertexAssembly
import OAI.Computability.VPVNP.PairTerminalProgramControl
import OAI.Computability.VPVNP.PairTerminalFootprint

/-! # Address protection on every prefix of the selected terminal traversal -/

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

include visit in
/-- At every reached terminal call, including a last accepting report and
any partial run without an accepting extension, an address before the
wire bank and outside the motif counters retains its physical value. -/
theorem selectedTerminalBranch_word (address : ℕ) (wireLow : address < lo)
    (outside : address < counter+grammar ∨ counter+grammar+labels ≤ address)
    (replayed : ReplayFrame address mem q.reportList)
    (valid : (Entry.resume TerminalLink.Stage.sharedBits (0 : Word w)).Valid (header ports) q.traversalRows.val.memory) :
    BurstRAM.PreservesCell (TerminalLink.program workers₀ ports) cap 0 mem address := by
  have low : address < (header ports).val := by omega
  have cell : workerCell (header ports) address := TerminalFootprint.below _ (by omega) low
  intro st now tape out reached ran
  exact TerminalProgram.preservesCell shape limit ports mem q shared address (by omega) (by omega) replayed valid
    beforeBits wireLayout headerRoom readAgree (Or.inl wireLow) cell (fun x => ordinal x)
    (fun x => (visit x).reference) (fun x => (visit x).active)
    (fun x => (visit x).stored) (fun x => (visit x).physicalReady) outside reached ran

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
