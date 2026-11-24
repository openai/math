import OAI.Computability.VPVNP.PairSimulationLeafSegment
import OAI.Computability.VPVNP.PairSimulationLeafRealization
import OAI.Computability.VPVNP.PairSimulationLeafImageFrame

/-! # The selected cursor occurrence on the terminal vertex's native leaf role -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafRole

open BurstRAM PrivateRAM CursorRouting CursorNetwork LeafStartup DFS
open LocalHistory LeafHandler
open scoped Fin.CommRing

variable {w : ℕ} {L : PrimedInputRAM.Lengths} {n a H s : ℕ} {Q : PrimedInputRAM.Layout L n a H w}
  (D : PrimedCounter.Data Q s) {b l e degree pad endAddr : ℕ} [NeZero (b+l)]
  (hD : 1 < b+l) (hd : 2+pad=2^degree) (budget : ProcessorBudget n (b+l) e w)
  {K : Type*} [CommRing K] {Label : Type} [Fintype Label] (f : Label → K)
  (clock : ℕ) (bound : NominationClock D budget.tags budget.capFits clock)
  (data : Fin 10 → Word w) (R : LeafArena.Regions) (cap : ℕ)
  (fit : R.stackBase + Fintype.card ScalarPort * n^40 < 2^w)
  (m : Memory w) (node : Word w) (saved : Scratch w endAddr)
  (v : Position (b+l)) (z : (LeafArguments.state hD hd (2^e) w).network.Half
    (lanePositions (cursorCoordinateLabels b l) v))
  (row : StoredCursorRow hD hd (addressFields data) R.arguments node saved cap v z)

include row in
/-- Each selected source occurrence is accepted by the actual role reader
with the same code and suffix. The reload is deterministic and the physical
histogram retains every component, including nonzero incoming counts. -/
theorem selected_job (cell : Label → {a : Word w // endAddr ≤ a.val})
    (below : ∀ i, (cell i).val.val < R.stackBase)
    (room : ∀ j, (auxiliaryBank D budget.tags budget.capFits v (LeafArguments.buffers hD hd v z) j).length
      + clock ≤ n^40) (code suffix : List Bool)
    (selected : ∃ x, code = (cursorSiteReader hD hd D budget.tags budget.capFits f clock bound v z).encode x) :
    ∃ actual, (parser data D budget R fit m clock).read node saved (code++suffix) = some (actual,suffix) ∧
      actual.enabled saved ∧ RealizesJob (fun old i => (old (cell i)).val) ⟨node.val,code,fun _ => 0⟩ actual := by
  let L := LeafVisit.storage R fit
  let fld := addressFields data
  let inp := LeafVisit.loaded (endAddr := endAddr) D budget R fit fld m
  let tr := fun n s => (inp n s).trace
  let prep := fun n s => (inp n s).prepared
  have away (i : Label) (j : ScalarPort) : (cell i).val.val < L.base j ∨ L.base j+L.capacity ≤ (cell i).val.val :=
    Or.inl ((below i).trans_le (R.stack_above _ _ fit j))
  obtain ⟨j,hit,en,real⟩ := cursorHook_realizes D budget.tags L clock node saved hD hd f budget.capFits
    bound fld R.arguments tr prep cap v z row cell away
    (LeafVisit.trace_bits D budget m fld _ _) (fun i => LeafVisit.loaded_below D budget R fit m fld node saved
      (cell i) (below i)) room code suffix selected
  let extended : VisitPath w endAddr :=
    ⟨j.node,List.replicate 21 .tick ++ j.trace,fun s => s = saved ∧ j.enabled s,j.update⟩
  change (LeafHandler.parser D budget.tags budget.capFits L inp clock).read node saved (code++suffix) =
    some (j,suffix) at hit
  refine ⟨extended,?_,⟨rfl,en⟩,⟨real.address,?_,fun s h i => real.counts s h.2 i⟩⟩
  · change ((LeafHandler.parser D budget.tags budget.capFits L inp clock).read node saved (code++suffix)).map _ = _
    rw [hit]; rfl
  · exact real.bits

/-- Every successful physical leaf, independently of its chosen occurrence,
preserves all sibling packets, geometry and histogram cells before the stacks. -/
theorem below_stack (bits tail : List Bool) (job : VisitPath w endAddr)
    (hit : (parser data D budget R fit m clock).read node saved bits = some (job,tail))
    (room : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) j,
      (auxiliaryBank D budget.tags budget.capFits v buf j).length + clock ≤ n^40)
    (i : {a : Word w // endAddr ≤ a.val}) (before : i.val.val < R.stackBase) :
    job.update saved i = saved i := by
  let source : HookParser w endAddr := LeafHandler.parser D budget.tags budget.capFits (LeafVisit.storage R fit)
    (LeafVisit.loaded D budget R fit (addressFields data) m) clock
  obtain ⟨old,read,_,upd,_,_,_⟩ := reload_read source node saved bits tail job hit
  let measure : Machine w 1 0 10 := ⟨0,fun _ => .reject,data⟩
  rw [upd]
  exact LeafVisit.read_below (M := measure) D budget R fit LeafGeometryLoad.slot m clock node saved bits read room i before

end PairSimulation.LeafRole

end VPVNP
end Computability
end OAI
