import OAI.Computability.VPVNP.PairVertexAscendingPaths
import OAI.Computability.VPVNP.PairSimulationTraceJobs
import OAI.Computability.VPVNP.LiveVirtualPairJobCounters

/-!
# Equality of native vertex deposits and local job increments

The final counter memory of the physical site traversal is a fold over its
site ordinals. The jobs of each selected local parser have the same exponent
vector. This includes the grammar prefix, which every site visit preserves.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.Counters

open BurstRAM

theorem visit_congr_at {w g : ℕ} {X : Type*} (base grammar : ℕ) (h : X → Fin g → ℕ) (vs : List X)
    {m₁ m₂ : Memory w} (a : ℕ) (same : m₁ a=m₂ a) : visit base grammar h vs m₁ a = visit base grammar h vs m₂ a := by
  by_cases inside : base+grammar ≤ a ∧ a < base+grammar+g
  · let j : Fin g := ⟨a-(base+grammar),by omega⟩
    have eq : a = base+grammar+j.val := by dsimp [j]; omega
    rw [eq,visit_at,visit_at]
    exact congrArg (· + _) (eq ▸ same)
  · have outside : a < base+grammar ∨ base+grammar+g ≤ a := by omega
    rw [visit_outside _ _ _ _ _ _ outside,visit_outside _ _ _ _ _ _ outside]
    exact same

end PairSimulation.Counters

namespace PairSimulation.LocalHistory

open BurstRAM NetworkKernel CompressorRecords VertexImage

variable {A : Type*} [CommRing A] {L : Type} [Fintype L] {κ : L → A} {N : Network}
    {scan : ScanPhase N} {P : SiteParsers κ N} (x : TerminalData scan P)
    {n g w : ℕ} (order : Fin n ≃ N.Site) (labels : Fin g ≃ L)
    (trees : N.Site → DFS.VertexTree) (jobs : JobsFor P) (valid : JobsSpec P trees jobs)

local notation "incident" => WireTensor.edgeAssignment N.src N.dst (scan.payload x.arcs)

include valid in
/-- Read any physical address after all selected vertices. Equality of the
incoming words at that single address suffices, even when the other source
memory cells differ from those of the actual prepared pair. -/
theorem TerminalData.deposits (base grammar : ℕ) (source input : Memory w) (a : ℕ) (before : source a=input a) :
    (siteOrdinals P order labels incident).finalMemory base grammar source (fun i => x.choices (order i)) a =
    Counters.visit base grammar (fun v l => ((x.jobs jobs v).map (fun j => j.increment (labels l))).sum)
      (List.ofFn order) input a := by
  let F := fun (v : N.Site) (l : Fin g) => ((x.jobs jobs v).map (fun j => j.increment (labels l))).sum
  have stored : (siteOrdinals P order labels incident).finalMemory base grammar source (fun i => x.choices (order i)) =
      Counters.visit base grammar F (List.ofFn order) source := by
    unfold IndexedSites.finalMemory
    apply Counters.visit_eq_of_sums
    intro l
    rw [List.map_ofFn,List.map_ofFn,List.sum_ofFn,List.sum_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    exact (valid.increments (order i) (incident (order i)) (x.choices (order i)) (labels l)).symm
  rw [stored]
  exact Counters.visit_congr_at base grammar F (List.ofFn order) a before

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
