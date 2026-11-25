import OAI.Computability.BorderVNP.CellRecordGuardsBudget
import OAI.Computability.BorderVNP.CellProfileDepth

/-! # A fixed generator depth for all public directory records

The number of descriptors and the number of copies per cable may grow. The
generator's lexical and arithmetic depth remain bounded at three and eight.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro.Address (depth)

/-- The two scratch-management loops require just one control level;
neither wraps the profile checker in another loop. -/
theorem localFlags_fitsDepth {d h : ℕ} (len : ℕ) (s : Stmt) (hs : s.FitsDepth d h) (hh : 0 < h) :
    (localFlags len s).FitsDepth d h := by
  simpa only [localFlags, Stmt.FitsDepth, depth, Nat.zero_le, true_and, and_true, hh] using hs

/-- A single record has uniform depth for the fixed cell decoder. -/
theorem recordGuard_fitsDepth (boxes : List (List Factor)) (r : Record) :
    (recordGuard boxes r).FitsDepth 8 3 := by
  cases r with
  | zero c l p =>
    refine ⟨by decide, by simp [depth], by decide, by simp [depth], Term.guard_fitsDepth _ ?_ _⟩
    simp [Term.FitsAddr, Port.expr, depth]
  | equal c l p q =>
    refine ⟨by decide, by simp [depth], by decide, by simp [depth], Term.guard_fitsDepth _ ?_ _⟩
    simp [Term.equal_fitsAddr, Term.FitsAddr, Port.expr, depth]
  | profile c p w hist routes =>
    exact localFlags_fitsDepth _ _ (Profile.profileGen_fitsDepth ..) (by decide)
  | box id base copies stride => exact Term.guard_fitsDepth (.lit _) trivial _

/-- Sequential composition of arbitrarily many public records preserves the
fixed decoder depths, including each profile's flag initialization and disposal. -/
theorem Directory.recordGuards_fitsDepth (D : Directory) :
    D.recordGuards.FitsDepth 8 3 := by
  apply sequence_fitsDepth
  intro s hs
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hs
  exact recordGuard_fitsDepth D.boxes r

end CellSparse

end BorderVNP
end Computability
end OAI
