import OAI.Hierarchy.ProtocolRAMCatalystDatedReads
import OAI.Hierarchy.ProtocolRAMCalendarPrevious

namespace OAI
/-! # Retired debit words and owner keys at every later calendar prefix -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {w q d : ℕ}

/-- The cell published at the retired event is still present at each
subsequent prefix. The final verdict writes only its single flag word. -/
theorem prefix_word (C : Chart w q d) (A : Arena) (initial : Memory w) (flag : ℕ)
    (mounted : Calendar.mounted C (events C.mesh) initial)
    (floor : ∀ t x,x< A.base C.mesh t → protected C x t)
    (t : Fin (events C.mesh).length) (j : ℕ) (past : t.val<j) (endAt : j≤(events C.mesh).length)
    (x : ℕ) (fits : x< A.base C.mesh ((events C.mesh).get t)+A.stride) (off : x≠flag) :
    run C ((events C.mesh).take j) initial x=checkedOut C flag initial x := by
  induction j with
  | zero => omega
  | succ j ih =>
    have inside : j<(events C.mesh).length := by omega
    rw [List.take_succ_eq_append_getElem inside,run_append]
    change after C ((events C.mesh)[j]) (run C ((events C.mesh).take j) initial) x=_
    by_cases exactDate : t.val=j
    · subst j
      exact (dated_word C A initial flag mounted floor t x fits off).symm
    · have older : t.val<j := by omega
      have order : position C.mesh ((events C.mesh).get t)<position C.mesh ((events C.mesh)[j]) := by
        change position C.mesh ((events C.mesh)[t.val])<_
        rw [position_at C.mesh t.isLt,position_at C.mesh inside]
        exact older
      have receipt := ordinal_slot C initial ⟨j,inside⟩ mounted
      rw [after_frame C _ _ _ receipt.currentReady (floor _ _ (fits.trans_le (A.apart C.mesh order)))]
      exact ih older (by omega)

/-- An owner decoder can be dynamic. Every cell it can read is below its
own birth slab, so it returns the same owner at every later prefix. -/
theorem prefix_expr (C : Chart w q d) (A : Arena) (initial : Memory w) (flag : ℕ)
    (mounted : Calendar.mounted C (events C.mesh) initial)
    (floor : ∀ t x,x< A.base C.mesh t → protected C x t)
    (t : Fin (events C.mesh).length) (j : ℕ) (past : t.val<j) (endAt : j≤(events C.mesh).length)
    (expr : Expr) (row : Word w) (fits : expr.Fits w (A.base C.mesh ((events C.mesh).get t)))
    (high : A.base C.mesh ((events C.mesh).get t)≤flag) :
    expr.eval (run C ((events C.mesh).take j) initial) row=expr.eval (checkedOut C flag initial) row := by
  apply eval_below expr row _ _ fits
  intro x hx
  exact prefix_word C A initial flag mounted floor t j past endAt x (hx.trans_le (Nat.le_add_right ..))
    (ne_of_lt (hx.trans_le high))

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
