import OAI.Hierarchy.ProtocolRAMCalendarPaidWhole
import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices

namespace OAI
/-! # Bytecode price of the actual full calendar and paid terminal width scan -/

namespace Hierarchy.ProtocolRAM.Calendar.Whole.Priced.Paid
open ProbeStage ProbeStage.Native AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {z d k q goods r edges : ℕ}
variable (c : Mesh) (finish : ℝ) (prices : PhasePrice) (format : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (s : Sink r edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
local notation "C" => pricedInstalled c finish prices format feeds s idBase role ids

theorem text_eq (flag src : ℕ) (ss : List PaidWidths.Slice) (a : ReserveUse.Archive) (count n reserve : ℕ) :
    text (program c finish prices format feeds s idBase role ids flag src ss a count n reserve)=
      text (subdivisionProgram z d)+(15+((events (C).mesh).map (eventText C)).sum+
        rowText (historyFlag C (events (C).mesh))+(30+(ss.map
          (fun t=>rowText (RepairHistogram.pair (t.columns s.banks.width edges))+22)).sum)+
        (listText (ReserveUse.columns a s.banks count n reserve)+22)+sinkText s) := by
  rw [program,text_seq,paidReporter_text]

/-- The archive scan is linear in the sum of the actual sparse slice
extents. In particular repeated occurrences of an edge remain charged.
Its bytecode is independent of those extents. -/
theorem archive_bill (slices : List PaidWidths.Slice) (bank : Bank) (edges B : ℕ)
    (work : ∀ t∈slices,(RepairHistogram.pair (t.columns bank edges)).work≤B) :
    PaidWidths.clock bank edges slices ≤
        8+6*edges+7*slices.length+(slices.map PaidWidths.Slice.count).sum*(4*B+20) ∧
      (slices.map (fun t=>rowText (RepairHistogram.pair (t.columns bank edges))+22)).sum ≤
        slices.length*(33+4*B) := by
  rw [PaidWidths.clock_eq]
  have per :
      (slices.map (fun t=>7+t.count*(4*(RepairHistogram.pair (t.columns bank edges)).work+20))).sum ≤
        7*slices.length+(slices.map PaidWidths.Slice.count).sum*(4*B+20) ∧
      (slices.map (fun t=>rowText (RepairHistogram.pair (t.columns bank edges))+22)).sum ≤
        slices.length*(33+4*B) := by
    induction slices with
    | nil => simp
    | cons t ts ih =>
      have h := work t (by simp)
      obtain ⟨ht,hn⟩ := ih (fun u hu=>work u (by simp [hu]))
      have times := Nat.mul_le_mul_left t.count
        (show 4*(RepairHistogram.pair (t.columns bank edges)).work+20≤4*B+20 by omega)
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      constructor
      · rw [Nat.mul_succ 7 ts.length, Nat.add_mul t.count]
        omega
      · have head : rowText (RepairHistogram.pair (t.columns bank edges)) + 22 ≤ 33 + 4*B := by
          rw [rowText]
          omega
        rw [Nat.succ_mul ts.length]
        omega
  obtain ⟨time,code⟩ := per
  exact ⟨by omega,code⟩

end
end Hierarchy.ProtocolRAM.Calendar.Whole.Priced.Paid

end OAI
