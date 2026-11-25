import OAI.Hierarchy.ProtocolRAMPaidWidthReplay
import OAI.Hierarchy.ProtocolRAMPaidWidthUpper
import OAI.Hierarchy.ProtocolRAMReservePrefixReplay

namespace OAI
/-! # The upper memory frame of the dated width and reserve reporters -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM

namespace PrefixWidths

theorem image_above {W edges : ℕ} (L : Layout edges) (rows : ℕ → List PaidWidths.Slice)
    (m : Memory W) (last maxRows x : ℕ)
    (fit : ∀ j ≤ last, ∀ s ∈ rows j, s.Fits (L.bank j) edges L.scratch W)
    (pages : ∀ j ≤ last, (L.bank j).base+edges < L.scratch)
    (count : ∀ j ≤ last, ∀ s ∈ rows j, s.count ≤ maxRows) (high : L.scratch+2*maxRows ≤ x) :
    image L rows m last x = m x := by
  have one (j : ℕ) (hj : j ≤ last) (u : Memory W) :
      PaidWidths.output (L.bank j) edges L.scratch (rows j) u x = u x := by
    apply PaidWidths.output_above _ _ _ _ _ _ (fit j hj)
    · exact (pages j hj).trans_le ((Nat.le_add_right _ _).trans high)
    · intro s hs
      exact (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (count j hj s hs)) _).trans high
  have atDate (j : ℕ) (hj : j ≤ last) : image L rows m j x = m x := by
    induction j with
    | zero => exact one 0 hj m
    | succ j ih => exact (one (j+1) hj _).trans (ih (Nat.le_trans (Nat.le_succ j) hj))
  exact atDate last le_rfl

end PrefixWidths

namespace PrefixReserve

theorem image_above {W count N : ℕ} (L : PrefixWidths.Layout count) (old : RouteSettlement.Banks)
    (a : ReserveUse.Archive) (size : ℕ → Fin (N+1)) (reserve : ℕ) (owner : Fin N → Fin count)
    (amount : Fin N → ℕ) (m : Memory W) (last x : ℕ)
    (pages : ∀ j ≤ last, (L.bank (2*j+1)).base+count ≤ x) (high : a.scratch+2*N ≤ x) :
    image L old a size reserve owner amount m last x = m x := by
  have one (j : ℕ) (hj : j ≤ last) (u : Memory W) :
      ReserveUse.output a (banks L old j) reserve (PrefixReserve.prefix (size j) owner) (PrefixReserve.prefix (size j) amount) u x = u x := by
    apply ReserveUse.frame
    · apply Or.inr
      exact (L.before (Nat.lt_succ_self (2*j))).le.trans
        ((Nat.le_add_right _ count).trans (pages j hj))
    · exact Or.inr (pages j hj)
    · exact Or.inr ((Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.le_of_lt_succ (size j).isLt)) _).trans high)
  have atDate (j : ℕ) (hj : j ≤ last) : image L old a size reserve owner amount m j x = m x := by
    induction j with
    | zero => exact one 0 hj m
    | succ j ih => exact (one (j+1) hj _).trans (ih (Nat.le_trans (Nat.le_succ j) hj))
  exact atDate last le_rfl

/-- Both complete replay images preserve the entire high suffix at the common
public scratch bound. Dated pages and repeated occurrences use the same memory. -/
theorem after_widths_above {W edges count N : ℕ} (lw : PrefixWidths.Layout edges)
    (lr : PrefixWidths.Layout count) (rows : ℕ → List PaidWidths.Slice) (old : RouteSettlement.Banks)
    (a : ReserveUse.Archive) (size : ℕ → Fin (N+1)) (reserve : ℕ) (owner : Fin N → Fin count)
    (amount : Fin N → ℕ) (m : Memory W) (last maxRows x : ℕ)
    (ready : PrefixWidths.Ready lw rows m last)
    (widthPages : ∀ j ≤ last, (lw.bank j).base+edges < lw.scratch)
    (counts : ∀ j ≤ last, ∀ s ∈ rows j, s.count ≤ maxRows)
    (reservePages : ∀ j ≤ last, (lr.bank (2*j+1)).base+count ≤ lr.scratch)
    (widthScratch : lw.scratch ≤ lr.scratch) (reserveScratch : a.scratch ≤ lr.scratch)
    (high : lr.scratch+2*max maxRows N ≤ x) :
    image lr old a size reserve owner amount (PrefixWidths.image lw rows m last) last x = m x := by
  have above : lr.scratch ≤ x := (Nat.le_add_right _ _).trans high
  refine (image_above lr old a size reserve owner amount _ last x
    (fun j hj => (reservePages j hj).trans above) ?_).trans ?_
  · exact (Nat.add_le_add reserveScratch (Nat.mul_le_mul_left 2 (Nat.le_max_right maxRows N))).trans high
  · exact PrefixWidths.image_above lw rows m last maxRows x (fun j hj s hs => (ready.mounted j hj s hs).1)
      widthPages counts ((Nat.add_le_add widthScratch (Nat.mul_le_mul_left 2 (Nat.le_max_left maxRows N))).trans high)

end PrefixReserve
end Hierarchy.ProtocolRAM.Calendar

end
end OAI
