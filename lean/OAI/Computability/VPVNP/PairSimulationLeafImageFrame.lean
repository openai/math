import OAI.Computability.VPVNP.PairSimulationLeafImageHandler
import OAI.Computability.VPVNP.PairSimulationLeafFrame

/-! # Preserving the other descriptor inputs, histogram and geometry at a leaf -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafVisit

open BurstRAM PrivateRAM LeafHandler LeafStartup DFS CursorNetwork
open scoped Fin.CommRing

variable {w p r k : ℕ} {A : PrimedInputRAM.Lengths} {n a H s : ℕ}
    {Q : PrimedInputRAM.Layout A n a H w} (D : PrimedCounter.Data Q s)
    {b l e endAddr : ℕ} [NeZero (b+l)] (budget : ProcessorBudget n (b+l) e w)
    (R : LeafArena.Regions) (fit : R.stackBase + Fintype.card ScalarPort*n^40 < 2^w)
    {M : Machine w p r k} (pub : LeafImage.Pub → Fin k) (m : Memory w)

theorem loaded_below (f : LeafAddress.Field → Word w) (node : Word w) (saved : Scratch w endAddr)
    (i : {a : Word w // endAddr ≤ a.val}) (below : i.val.val < R.stackBase) :
    (loaded D budget R fit f m node saved).prepared i = saved i := by
  let L := storage R fit
  let x := loaded D budget R fit f m node saved
  let bank := auxiliaryBank D budget.tags budget.capFits x.pos x.buffers
  have h : ¬ ∃ j, LeafLoadedBank.occupies L bank i.val j := by
    rintro ⟨j,bot,_⟩
    exact (not_le_of_gt (below.trans_le (R.stack_above _ _ fit j))) bot
  change (if x.pos.1 = 0 then LeafLoadedBank.scratch L bank saved else saved) i = _
  split
  · simp only [LeafLoadedBank.scratch,LeafLoadedBank.readCell,dite_eq_right h,Option.getD_none]
  · rfl

/-- A successful physical leaf leaves every word below its allocated stacks
unchanged. This includes the cache of 38 actual auxiliary operands, the
geometry pointer and descriptors, the parent and sibling argument packets,
and the label histogram. -/
theorem read_below (clock : ℕ) (node : Word w) (saved : Scratch w endAddr)
    (bits : List Bool) {job : VisitPath w endAddr} {tail : List Bool}
    (read : (leafParser (M := M) D budget R fit pub m clock).read node saved bits = some (job,tail))
    (room : ∀ (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w) j,
      (auxiliaryBank D budget.tags budget.capFits v buf j).length + clock ≤ n^40)
    (i : {a : Word w // endAddr ≤ a.val}) (below : i.val.val < R.stackBase) :
    job.update saved i = saved i := by
  let f := fields (M := M) pub
  let input := loaded (endAddr := endAddr) D budget R fit f m
  obtain ⟨_,_,_,frame⟩ := parser_observations D budget.tags budget.capFits (storage R fit) input clock
    node saved bits tail job read (trace_bits D budget m f _ _) (room _ _)
  exact (frame i fun j => Or.inl (below.trans_le (R.stack_above _ _ fit j))).trans
    (loaded_below D budget R fit m f node saved i below)

end PairSimulation.LeafVisit

end VPVNP
end Computability
end OAI
