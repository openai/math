import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn

namespace OAI
/-! Reading the word at its original finite bit index after conversion to a list. -/
namespace Hierarchy

theorem finiteWord_read {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) (fallback : α) :
    (List.ofFn f).getD i.val fallback=f i := by
  rw [List.getD_eq_getElem (List.ofFn f) fallback (by simpa only [List.length_ofFn] using i.isLt),
    List.getElem_ofFn]

end Hierarchy

end OAI
