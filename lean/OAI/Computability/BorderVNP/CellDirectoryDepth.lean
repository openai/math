import OAI.Computability.BorderVNP.CellBoxDepth
import OAI.Computability.BorderVNP.CellRecordGuardsDepth
import OAI.Computability.BorderVNP.CellSparseCompiled

/-! # A single bounded-depth decoder for complete cell programs

Local subtotal flags and copy loops reuse the same control levels. The
outer private-wire guessing loop ends before any checking begins.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro.Address (depth)

private theorem allFits (l : List Term) (d : ℕ) (h : ∀ t ∈ l, t.FitsAddr d) :
    (Term.all l).FitsAddr d := by
  induction l with
  | nil => trivial
  | cons t ts ih => exact ⟨h t List.mem_cons_self, ih (fun u hu => h u (.tail _ hu))⟩

/-- Comparing the announced binary subtotal to the selected final count
uses a loop followed by one bounded conditional. -/
theorem finishCount_fitsDepth (base off cap : ℕ) (bits : List ℕ) :
    (finishCount base off cap bits).FitsDepth 8 3 := by
  have hflag : (Prefix.flagTerm base cap (.lit cap) (.index 0)).FitsAddr 8 := by
    simp [Prefix.flagTerm, Term.FitsAddr, depth]
  have hbits : (digitChecks off bits (.index 0)).FitsAddr 8 := by
    apply allFits
    intro t ht
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp ht
    simp [Term.equal_fitsAddr, Term.FitsAddr, depth]
  refine ⟨by decide, by simp [depth], by decide, by simp [depth], Term.guard_fitsDepth _ ?_ _,
    Term.guard_fitsDepth (Term.not _) hflag _⟩
  exact ⟨hflag,hbits⟩

/-- Each subtotal row uses the same finite-depth decoder as the original
signed and Boolean factor scans, independently of its copy count. -/
theorem Gadget.row_fitsDepth (D : Directory) (id : ℕ) (bits : List ℕ) :
    (Gadget.row D id bits).FitsDepth 8 3 := by
  apply localFlags_fitsDepth _ _ _ (by decide)
  exact ⟨Prefix.initGen_fitsDepth 0 D.visitCount 8 3 (by decide) (by decide),
    Gadget.steps_fitsDepth D _ _ id, finishCount_fitsDepth 0 _ _ bits⟩

/-- Full program depth bound, covering physical wire guesses, public records,
the signed factor sweep, range tests, and every announced gadget subtotal. -/
theorem Directory.program_fitsDepth (D : Directory) (privateWires : ℕ) :
    (D.program privateWires).FitsDepth 8 3 := by
  refine ⟨⟨by decide, by simp [depth], trivial⟩, D.recordGuards_fitsDepth,
    factorSweep_fitsDepth D 0, D.rangeGuard_fitsDepth, sequence_fitsDepth _ ?_⟩
  intro s hs
  obtain ⟨z, _, rfl⟩ := List.mem_map.mp hs
  exact Gadget.row_fitsDepth D z.2 z.1

end CellSparse

end BorderVNP
end Computability
end OAI
