import OAI.Hierarchy.ProtocolRAMCatalystArchiveDirectory
import OAI.Hierarchy.ProtocolRAMCalendarRemainders

namespace OAI
/-! # Reading the physical debit and expression at an event before checkout -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {w q d : ℕ}

/-- The word written at this event is in its own stride. Chronological ordering
places all later output ranges strictly beyond it. The last single-word write is
the verdict at `flag`. -/
theorem dated_word (C : Chart w q d) (A : Arena) (initial : Memory w) (flag : ℕ)
    (mounted : Calendar.mounted C (events C.mesh) initial)
    (floor : ∀ t x,x<A.base C.mesh t → protected C x t)
    (i : Fin (events C.mesh).length) (x : ℕ)
    (fits : x<A.base C.mesh ((events C.mesh).get i)+A.stride) (off : x≠flag) :
    checkedOut C flag initial x=after C ((events C.mesh).get i)
      (run C ((events C.mesh).take i.val) initial) x := by
  have cut := ordinal_slot C initial i mounted
  have apart : x<flag ∨ flag+1≤x := by omega
  rw [checkedOut,ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ apart]
  apply cut.word
  intro t ht
  exact floor t x (fits.trans_le (A.apart C.mesh (cut.later t ht)))

/-- Re-evaluating a row decoder at checkout reads precisely the old CT columns,
public port row and retained birth shelf it read upon entering the event. -/
theorem dated_expr (C : Chart w q d) (A : Arena) (initial : Memory w) (flag : ℕ)
    (mounted : Calendar.mounted C (events C.mesh) initial)
    (floor : ∀ t x,x<A.base C.mesh t → protected C x t)
    (i : Fin (events C.mesh).length) (expr : Expr) (row : Word w)
    (fits : expr.Fits w (A.base C.mesh ((events C.mesh).get i)))
    (high : A.base C.mesh ((events C.mesh).get i)≤flag) :
    expr.eval (checkedOut C flag initial) row=
      expr.eval (run C ((events C.mesh).take i.val) initial) row := by
  apply eval_below _ _ _ _ fits
  intro x hx
  rw [dated_word C A initial flag mounted floor i x (hx.trans_le (Nat.le_add_right ..))
    (ne_of_lt (hx.trans_le high))]
  exact after_frame C _ _ _ (ordinal_slot C initial i mounted).currentReady (floor _ _ hx)

/-- Flatten the genuine historical widths using the same ordinal as the pointer
ROM. In particular, there are no reserve entries at feed events. -/
theorem checked_amount {count payload : ℕ} (C : Chart w q d) (A : Arena) (initial : Memory w)
    (flag : ℕ) (issued : Attempt→Entry count payload) (base : Event→ℕ) (history : Bank)
    (mounted : Calendar.mounted C (events C.mesh) initial)
    (floor : ∀ t x,x<A.base C.mesh t → protected C x t)
    (span : ∀ t : Fin (events C.mesh).length, ∀ h : Fin (atTime C.mesh issued t).rows,
      history.base+base ((events C.mesh).get t)+h.val<A.base C.mesh ((events C.mesh).get t)+A.stride)
    (high : A.endAddress C.mesh≤flag)
    (cash : ∀ t : Fin (events C.mesh).length, ∀ h : Fin (atTime C.mesh issued t).rows,
      after C ((events C.mesh).get t) (run C ((events C.mesh).take t.val) initial)
        (history.base+base ((events C.mesh).get t)+h.val)=((atTime C.mesh issued t).bits h:Word w))
    (i : Fin (recordCount C.mesh issued)) :
    checkedOut C flag initial (history.base+sourceAt C.mesh issued base i)=(debit C.mesh issued i:Word w) := by
  let z := (rank C.mesh issued).symm i
  let t := (events C.mesh).get z.1
  have range := span z.1 z.2
  have limit := A.within C.mesh t (List.get_mem ..)
  change checkedOut C flag initial (history.base+(base t+z.2.val))=_
  rw [←Nat.add_assoc,dated_word C A initial flag mounted floor z.1 _ range (ne_of_lt (range.trans_le (limit.trans high)))]
  exact cash z.1 z.2


end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
