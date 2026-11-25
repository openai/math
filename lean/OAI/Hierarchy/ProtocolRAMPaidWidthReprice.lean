import OAI.Hierarchy.ProtocolRAMCalendarPrefixWidths

namespace OAI
/-! # Replaying any dated prefix costs at most one copy of its full sparse reporter -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.PrefixWidths
open Computability.VPVNP.BurstRAM PrivateRAM PaidWidths
open ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators

/-- Repositioning the width vector changes only a destination literal in the emitted
expression. It preserves its literal expression-tree work for every possible slice. -/
theorem pair_work_bank (s : Slice) (edges : ℕ) (left right : Bank) :
    (RepairHistogram.pair (s.columns left edges)).work=(RepairHistogram.pair (s.columns right edges)).work := rfl

private theorem prefix_charge (es : List Event) (compile : Event→List Slice) (charge : Slice→ℕ) (j : ℕ) :
    ((prefixRows es compile j).map charge).sum≤((es.flatMap compile).map charge).sum := by
  have whole : es.flatMap compile=prefixRows es compile j ++ (es.drop j).flatMap compile := by
    unfold prefixRows
    rw [←List.flatMap_append,List.take_append_drop]
  rw [whole,List.map_append,List.sum_append]
  exact Nat.le_add_right ..

/-- Includes both the initialization pass at every date and all edge scatters on
the complete initial segment, including repeated occurrences of the same slice. -/
theorem time_prefix_le {edges : ℕ} (L : Layout edges) (es : List Event) (compile : Event→List Slice)
    (origin : Bank) (last : ℕ) :
    time L (prefixRows es compile) last≤(last+1)*PaidWidths.clock origin edges (es.flatMap compile) := by
  apply time_le
  intro j _
  rw [PaidWidths.clock_eq (L.bank j) edges (prefixRows es compile j),
    PaidWidths.clock_eq origin edges (es.flatMap compile)]
  let toll (s : Slice) := 7+s.count*(4*(RepairHistogram.pair (s.columns origin edges)).work+20)
  change 8+6*edges+((prefixRows es compile j).map toll).sum≤8+6*edges+((es.flatMap compile).map toll).sum
  exact Nat.add_le_add_left (prefix_charge es compile toll j) _

/-- The source port and the dated destination base do not affect the compiled
text tariff. Every term is the literal native reporter cost on the original list. -/
theorem text_prefix_le (W : ℕ) {edges : ℕ} (L : Layout edges) (es : List Event) (compile : Event→List Slice)
    (origin : Bank) (src last : ℕ) :
    text (program L (prefixRows es compile) W last)≤
      (last+1)*text (PaidWidths.native W edges src origin (es.flatMap compile)) := by
  rw [text_sum (W:=W) L (prefixRows es compile) last, paid_text W edges src origin (es.flatMap compile)]
  let size (s : Slice) := rowText (RepairHistogram.pair (s.columns origin edges))+22
  change (∑ j : Fin (last+1), (30+((prefixRows es compile j.val).map size).sum))≤
    (last+1)*(30+((es.flatMap compile).map size).sum)
  calc
    _ ≤ ∑ _j : Fin (last+1), (30+((es.flatMap compile).map size).sum) :=
      Finset.sum_le_sum (fun j _=>Nat.add_le_add_left (prefix_charge es compile size j.val) _)
    _ = _ := by simp [Finset.sum_const]


end Hierarchy.ProtocolRAM.Calendar.PrefixWidths
end

end OAI
