import OAI.Hierarchy.ProtocolRAMPaidWidthCore

namespace OAI
/-! # Size of a scratch vector reused by serial paid-width scans -/

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

/-- The temporary vectors are reused by each serial scan. -/
def wideSliceBound : List PaidWidths.Slice → ℕ
  | [] => 0
  | s :: ss => max s.count (wideSliceBound ss)

theorem wideSliceBound_spec (ss : List PaidWidths.Slice) : ∀s∈ss,s.count ≤ wideSliceBound ss := by
  induction ss with
  | nil => simp
  | cons a tail ih =>
    intro s hs
    rcases List.mem_cons.mp hs with same | member
    · subst s
      exact le_max_left ..
    · exact (ih s member).trans (le_max_right ..)

theorem wideSliceBound_le (ss : List PaidWidths.Slice) (cap : ℕ)
    (fits : ∀s∈ss,s.count ≤ cap) : wideSliceBound ss ≤ cap := by
  induction ss with
  | nil => exact Nat.zero_le _
  | cons a tail ih =>
    exact max_le (fits a (List.mem_cons_self ..)) (ih (fun s hs => fits s (List.mem_cons_of_mem _ hs)))

theorem wideSliceBound_le_sum (ss : List PaidWidths.Slice) :
    wideSliceBound ss ≤ (ss.map PaidWidths.Slice.count).sum := by
  induction ss with
  | nil => rfl
  | cons a tail ih =>
    change max a.count (wideSliceBound tail) ≤ a.count+(tail.map PaidWidths.Slice.count).sum
    exact max_le (Nat.le_add_right _ _) (ih.trans (Nat.le_add_left _ _))

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end OAI
