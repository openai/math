import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherLayout
import OAI.Computability.VPVNP.CompressorSourceTransport

/-! # External read addresses of the terminal endpoint gather -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SourceTransport

open BurstRAM

theorem Reads.append {w : ℕ} {P : ℕ → Prop} {xs ys : List (Event w)}
    (hx : Reads P xs) (hy : Reads P ys) : Reads P (xs ++ ys) :=
  fun a v read ↦ (List.mem_append.mp read).elim (hx a v) (hy a v)

theorem Reads.replicate_tick {w : ℕ} (P : ℕ → Prop) (n : ℕ) :
    Reads P (List.replicate n (.tick : Event w)) := by
  intro a v read
  cases List.eq_of_mem_replicate read

end CompressorRecords.SourceTransport

namespace PairSimulation.TerminalRootGather

open BurstRAM CompressorRecords.SourceTransport
open scoped Fin.CommRing

/-- Allowed external addresses for this vertex's incoming-edge lookup, outgoing
edge metadata and shared bit intervals. The incoming lookup precedes the width
and prefix reads, so those two bounds depend on the actual entry memory. -/
structure Layout.Readable {w : ℕ} (L : Layout) (m : Memory w) (P : ℕ → Prop) : Prop where
  incoming : ∀ j < L.degree, P (L.incomingHead + L.index j)
  widths : ∀ d j, j < L.degree → P (L.widthHead + L.edge m d j)
  prefixes : ∀ d j, j < L.degree → P (L.prefixHead + L.edge m d j)
  wire : ∀ d j, j < L.degree → ∀ i < L.width m d j, P (L.start m d j + i)

theorem Layout.readable_true {w : ℕ} (L : Layout) (m : Memory w) : L.Readable m (fun _ ↦ True) :=
  ⟨fun _ _ ↦ trivial, fun _ _ _ ↦ trivial, fun _ _ _ ↦ trivial, fun _ _ _ _ _ ↦ trivial⟩

/-- The bit-copy loop reads exactly within the chosen source interval. -/
theorem arc_reads {w : ℕ} (m : Memory w) (P : ℕ → Prop) (s n : ℕ)
    (fit : s+n < 2^w) (allowed : ∀ i < n, P (s+i)) :
    Reads P (EndpointBits.events m s n) := by
  induction n generalizing s with
  | zero => exact Reads.replicate_tick P 1
  | succ n ih =>
    apply Reads.append _ (ih (s+1) (by omega) (fun i hi ↦ by
      simpa only [Nat.add_assoc, Nat.add_comm 1 i] using allowed (i+1) (by omega)))
    intro a v h
    simp only [List.mem_cons,List.not_mem_nil,Event.read.injEq,reduceCtorEq,false_or,or_false] at h
    rw [h.1, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simpa using allowed 0 (by omega)

end PairSimulation.TerminalRootGather

end VPVNP
end Computability
end OAI
