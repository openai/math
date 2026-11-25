import OAI.Computability.BorderVNP.CellSparseExteriorNativeArena
import OAI.Computability.BorderVNP.CellSparseExteriorBatchRun
import OAI.Computability.BorderVNP.RoutingISASignedTaskArena

/-! # Independence of all sparse exterior writes in the genuine task arena -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open DiagonalTallyAllocation VPVNP.BurstRAM

/-- Actual task and six-word directories, together with the controller's
published fragment arenas and the run-time number of owned cells. -/
noncomputable def batchLayout (a : SignedTaskArena.Layout) (frame control count : ℕ) : Layout :=
  ⟨frame,control,count,(a.tasks 0 0 0 0).tasks,a.before.six,a.fragments.pairs,a.fragments.triples,
    a.fragments.external,a.fragments.stride,a.fragments.counts⟩

/-- Both the true compact six-word and seven-word source headers lie above
all sparse outputs. Each later task begins beyond every earlier task row. -/
private theorem batch_regions (a : SignedTaskArena.Layout) :
    a.fragments.limit ≤ a.before.six ∧ a.before.six+6*a.p.report.cells ≤ (a.tasks 0 0 0 0).tasks := by
  constructor
  · dsimp only [SignedTaskArena.Layout.before,BeforeTasks.six,BeforeTasks.four,BeforeTasks.merged,
      BeforeTasks.counters,BeforeTasks.supplement,BeforeTasks.tailWidths]; omega
  · change a.before.six+6*a.before.bound.cells ≤ a.before.limit+3*a.cube.cells
    dsimp only [BeforeTasks.limit,BeforeTasks.bundleTable,BeforeTasks.ranges]; omega

/-- The previously serialized compact fields, count words and task updates
are disjoint from the complete read footprint of each subsequent owned task. -/
theorem batch_independent (a : SignedTaskArena.Layout) (frame ctl count : ℕ) (owned : ℕ → Owned)
    (bounded : count ≤ a.p.report.cells) (global : ∀ i < count, (owned i).global<a.fragments.cells)
    (tables : ∀ i < count, (owned i).first+(owned i).field.spans.length≤a.fragments.capacity)
    (outputs : ∀ i < count, (owned i).field.bytes.length≤a.fragments.stride)
    (reports : ∀ i < count, (owned i).dense+(owned i).field.width+(owned i).field.tail.length≤a.fragments.start)
    (data : ∀ i < count, ∀ r ∈ (owned i).field.spans, r.source+r.bits.length≤a.fragments.start) :
    let l := batchLayout a frame ctl count
    ∀ i < count, ∀ j < i, ∀ addr, (owned i).Source l i addr → (owned j).Outside l j addr := by
  intro l i hi j hj addr source
  have hjc := hj.trans hi
  have gc := global i hi
  have gj := global j hjc
  have size := outputs j hjc
  have rowBound := Nat.mul_le_mul_left 3 (tables i hi)
  rw [Nat.mul_add] at rowBound
  have limit := batch_regions a
  have actual : (owned j).dest l=a.fragments.external+(owned j).global*a.fragments.stride := rfl
  have dstLow : a.fragments.external≤(owned j).dest l := by rw [actual]; omega
  have dstHigh : (owned j).dest l+(owned j).field.bytes.length≤a.fragments.counts := by
    have h := Nat.mul_le_mul_right a.fragments.stride (Nat.succ_le_of_lt gj)
    rw [Nat.succ_mul] at h
    rw [actual,FragmentArena.Layout.counts]; omega
  have high : a.fragments.counts+(owned j).global < a.fragments.limit := by
    rw [FragmentArena.Layout.limit]; omega
  have early : a.fragments.start≤a.fragments.external := by
    simp only [FragmentArena.Layout.external,FragmentArena.Layout.cursors,FragmentArena.Layout.triples,
      FragmentArena.Layout.pairs,FragmentArena.Layout.quads]; omega
  have middle : a.fragments.triples+3*a.fragments.capacity ≤ a.fragments.external := by
    simp only [FragmentArena.Layout.external,FragmentArena.Layout.cursors]; omega
  have pair : a.fragments.pairs+2*a.fragments.cells≤a.fragments.triples := le_rfl
  have later : a.fragments.external≤a.fragments.counts := by rw [FragmentArena.Layout.counts]; omega
  change (_ ∨ _) ∧ addr≠(a.tasks 0 0 0 0).tasks+7*j+2 ∧ addr≠(a.tasks 0 0 0 0).tasks+7*j+3 ∧
    addr≠a.fragments.counts+(owned j).global
  rcases source with keys | triples | report | ⟨r,mem,lower,upper⟩
  · simp only [Owned.addresses,List.mem_cons,List.not_mem_nil,or_false] at keys
    change addr=a.before.six+6*i ∨ addr=a.before.six+6*i+2 ∨ addr=(a.tasks 0 0 0 0).tasks+7*i+2 ∨
      addr=(a.tasks 0 0 0 0).tasks+7*i+3 ∨ addr=a.fragments.pairs+2*(owned i).global ∨
      addr=a.fragments.pairs+2*(owned i).global+1 at keys
    rcases keys with h|h|h|h|h|h <;> omega
  · change _ ∧ addr<a.fragments.triples+3*((owned i).first+(owned i).field.spans.length) at triples
    rw [Nat.mul_add] at triples
    omega
  · have := reports i hi; omega
  · have := data i hi r mem; omega

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
