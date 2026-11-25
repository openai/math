import OAI.Computability.BorderVNP.CellBoxLexical
import OAI.Computability.BorderVNP.CellDirectoryDepth
import OAI.Computability.BorderVNP.CellProfileLexical

/-! # Lexical index bound for the complete sparse cell generator

Absolute positions, widths and counts use binary literal fields. Only lexical
loop references contribute to the unary index length in the address evaluator.
No command in the complete cell generator refers to an index larger than two.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

private theorem all_lexical (l : List Term) {bound : ℕ} (h : ∀ t ∈ l, t.lexical ≤ bound) :
    (Term.all l).lexical ≤ bound := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons t ts ih => exact max_le (h t List.mem_cons_self) (ih (fun u hu => h u (.tail _ hu)))

/-- Scratch allocation and disposal contain only a binary bound and fixed opcodes. -/
theorem localFlags_lexical (len : ℕ) (s : Stmt) : (localFlags len s).lexical = s.lexical := by
  simp [localFlags, Stmt.lexical, NatExpr.lexical]

/-- Every public record uses at most three nested counter positions, indexed from zero. -/
theorem recordGuard_lexical_le (boxes : List (List Factor)) (r : Record) :
    (recordGuard boxes r).lexical ≤ 2 := by
  cases r with
  | zero c l p => simp [recordGuard, zeroRow, Stmt.lexical, Term.lexical, NatExpr.lexical]
  | equal c l p q => simp [recordGuard, equalRow, Stmt.lexical, Term.lexical, NatExpr.lexical]
  | profile c s w hist routes =>
    rw [recordGuard, profileRow, localFlags_lexical]
    exact Profile.profileGen_lexical_le ..
  | box id base c stride => simp [recordGuard, Term.lexical]

/-- The whole stream of public guards preserves the absolute index bound. -/
theorem Directory.recordGuards_lexical_le (D : Directory) : D.recordGuards.lexical ≤ 2 := by
  apply sequence_lexical_le
  intro s hs
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hs
  exact recordGuard_lexical_le D.boxes r

/-- The comparison to each supplied count bit uses the innermost lexical counter. -/
theorem finishCount_lexical_le (base off cap : ℕ) (bits : List ℕ) :
    (finishCount base off cap bits).lexical ≤ 2 := by
  have hb : (digitChecks off bits (.index 0)).lexical ≤ 2 := by
    apply all_lexical
    intro t ht
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp ht
    simp [Term.lexical, NatExpr.lexical]
  simpa [finishCount, Stmt.lexical, NatExpr.lexical, Term.lexical] using hb

/-- Complete subtotal rows retain the bound, including their signed-box traversal. -/
theorem Gadget.row_lexical_le (D : Directory) (id : ℕ) (bits : List ℕ) :
    (Gadget.row D id bits).lexical ≤ 2 := by
  rw [Gadget.row, localFlags_lexical]
  simp only [Gadget.checker, Stmt.lexical, max_le_iff]
  exact ⟨by simp, Gadget.steps_lexical_le D _ _ id, finishCount_lexical_le 0 _ _ bits⟩

/-- At most two is stored in any unary lexical-reference field in a full
cell program, independently of all loop trip counts and private data. -/
theorem Directory.program_lexical_le (D : Directory) (privateWires : ℕ) :
    (D.program privateWires).lexical ≤ 2 := by
  simp only [Directory.program, Directory.checkAssignment, Directory.countGuards,
    Stmt.lexical, NatExpr.lexical, max_le_iff]
  refine ⟨⟨by decide, by decide⟩, D.recordGuards_lexical_le, factorSweep_lexical_le D 0,
    D.rangeGuard_lexical_le, sequence_lexical_le _ ?_⟩
  intro s hs
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hs
  exact Gadget.row_lexical_le D z.2 z.1

end CellSparse

end BorderVNP
end Computability
end OAI
