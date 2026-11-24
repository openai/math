import OAI.Computability.VPVNP.PairSimulationDFS
import OAI.Computability.VPVNP.PairTerminalFootprint

/-! # External read addresses of the native placement-tree traversal -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation

open BurstRAM TerminalFootprint CompressorRecords.SourceTransport
open private headerEvents from OAI.Computability.VPVNP.PairSimulationDFS

variable {w : ℕ}

/-- A descriptor's child pointers occupy consecutive words. -/
theorem EndpointBits.events_reads {src n : ℕ} (m : Memory w) (fit : src+n < 2^w)
    {allow : ℕ → Prop} (cells : ∀ i : Fin n, allow (src+i.val)) : Reads allow (events m src n) := by
  induction n generalizing src with
  | zero =>
    intro a v read
    simp [events] at read
  | succ n ih =>
    intro a v read
    rcases List.mem_append.mp read with head | rest
    · simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, Event.read.injEq, false_or, or_false] at head
      have eq : a.val = src := (congrArg Fin.val head.1).trans (Nat.mod_eq_of_lt (by omega))
      rw [eq]
      exact cells 0
    · refine ih (src := src+1) (by omega) ?_ a v rest
      intro i
      have h := cells ⟨i.val+1, by omega⟩
      simpa only [Nat.add_assoc, Nat.add_comm 1] using h

/-- Read addresses use the stored count and pointer of the current row.
Only rows visited by the selected preorder need to lie below the bound. -/
theorem DFS.Visits.reads_of_row_bounds {m : Memory w} {endAddr limit : ℕ}
    {pending nodes : List (Word w)} {es : List (Event w)} (walk : DFS.Visits m endAddr pending nodes es)
    (bounds : ∀ node ∈ nodes, node.val+2 ≤ limit ∧ (m node.val).val+(m (node.val+1)).val ≤ limit) :
    Reads (· < limit) es := by
  induction walk with
  | nil =>
    intro a v read
    simp at read
  | @cons node pending kids nodes src es row fits rest ih =>
    have current := bounds node List.mem_cons_self
    have ha : node.val+1 < 2^w := row.1
    have hs : src+kids.length < 2^w := row.2.1
    have hptr : (m node.val).val = src := (congrArg Fin.val row.2.2.1).trans (Nat.mod_eq_of_lt (by omega))
    have hlen : (m (node.val+1)).val = kids.length :=
      (congrArg Fin.val row.2.2.2.1).trans (Nat.mod_eq_of_lt (by omega))
    refine reads_append (es := _ ++ _ ++ _) ?_ (ih (fun v hv => bounds v (List.mem_cons_of_mem _ hv)))
    refine reads_append (es := _ ++ _) ?_ (EndpointBits.events_reads m hs ?_)
    · refine reads_append (es := [.tick,.tick,.tick]) (reads_ticks _ 3) ?_
      intro a v read
      simp only [headerEvents, List.mem_cons, List.not_mem_nil, reduceCtorEq, Event.read.injEq,
        false_or, or_false] at read
      rcases read with h | h
      · have eq : a.val = node.val := (congrArg Fin.val h.1).trans (Nat.mod_eq_of_lt node.isLt)
        omega
      · have eq : a.val = node.val+1 := (congrArg Fin.val h.1).trans (Nat.mod_eq_of_lt ha)
        omega
    · intro i
      have := i.isLt
      omega

end PairSimulation

end VPVNP
end Computability
end OAI
