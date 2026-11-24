import OAI.Computability.VPVNP.PairVertexActiveGeometry
import OAI.Computability.VPVNP.PairSimulationTerminalSplice

/-! # Source reads outside the two online terminal-controller cells -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalFootprint

open BurstRAM PrivateRAM CompressorRecords.SourceTransport TerminalLink
open scoped Fin.CommRing

variable {w : ℕ}

theorem header_val (H : Word w) (fit : H.val+31 < 2^w) {j : ℕ} (hj : j ≤ 31) :
    (H+(j : Word w)).val = H.val+j := by
  rw [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (by omega : j < 2^w),Nat.mod_eq_of_lt (by omega)]

theorem below (H : Word w) (fit : H.val+31 < 2^w) {i : ℕ} (before : i < H.val) : workerCell H i := by
  change i ≠ H.val ∧ i ≠ (H+(31 : Word w)).val
  rw [show (H+(31 : Word w)).val = H.val+31 from header_val H fit (j := 31) le_rfl]; omega

theorem headerField (H : Word w) (fit : H.val+31 < 2^w) {j : ℕ} (lo : 0 < j) (hi : j < 31) :
    workerCell H (H+(j : Word w)).val := by
  unfold workerCell
  rw [header_val H fit hi.le,show (H+(31 : Word w)).val = H.val+31 from header_val H fit (j := 31) le_rfl]
  omega

theorem reads_append {allow : ℕ → Prop} {es fs : List (Event w)} (left : Reads allow es) (right : Reads allow fs) :
    Reads allow (es++fs) := fun a v h => (List.mem_append.mp h).elim (left a v) (right a v)

theorem reads_ticks (allow : ℕ → Prop) (n : ℕ) : Reads allow (List.replicate n (.tick : Event w)) := by
  intro a v h
  have eq : (.read a v : Event w) = .tick := List.eq_of_mem_replicate h
  cases eq

theorem reads_mono {allow allow' : ℕ → Prop} {es : List (Event w)}
    (reads : Reads allow es) (h : ∀ i, allow i → allow' i) : Reads allow' es :=
  fun a v read => h a.val (reads a v read)

private theorem field (H : Word w) (fit : H.val+31 < 2^w) (m : Memory w) {j : ℕ}
    (lo : 0 < j) (hi : j < 31) : Reads (workerCell H) (TerminalSiteStart.fieldTrace m H j) := by
  intro a v h
  simp only [TerminalSiteStart.fieldTrace,List.mem_cons,List.not_mem_nil,reduceCtorEq,false_or,or_false,
    Event.read.injEq] at h
  exact h.1 ▸ headerField H fit lo hi

end PairSimulation.TerminalFootprint

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM CompressorRecords.SourceTransport TerminalFootprint TerminalLink TerminalSiteStart
open scoped Fin.CommRing

variable {w : ℕ}

/-- All fifteen reads of the active ordinal guard and the geometry initializer
avoid the phase word and the worker-state word. -/
theorem active_geometry_reads (m : Memory w) (H : Word w) (degree t : ℕ) (fit : H.val+31 < 2^w) :
    Reads (workerCell H) (startTrace m H ++ (NativeFrame.events degree H m ++ List.replicate (t+2) .tick)) := by
  apply reads_append
  · apply reads_append
    · exact reads_append (reads_append (reads_ticks _ 10) (TerminalFootprint.field H fit m (by decide) (by decide)))
        (reads_ticks _ 2)
    · apply reads_append
      · intro a v h
        obtain ⟨j,member,read⟩ := List.mem_flatMap.mp h
        have lo : 0 < j := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          omega
        have hi : j < 31 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          omega
        exact TerminalFootprint.field H fit m lo hi a v read
      · exact reads_ticks _ 5
  · refine reads_append (es := NativeFrame.events degree H m) ?_ (reads_ticks _ (t+2))
    refine reads_mono (NativeFrame.events_reads degree H m) ?_
    rintro i ⟨j,rfl⟩
    exact headerField H fit (by fin_cases j <;> decide) (by fin_cases j <;> decide)

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
