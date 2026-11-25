import OAI.Computability.BorderVNP.DiagonalCheckedCellReport
import OAI.Computability.BorderVNP.FiniteDiagonalCellTraceUnsigned

/-! # Unique real report and auxiliary return tape for one fixed passing cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open CellSparse Packing.BottomReports FiniteDiagonal.CellTrace
open scoped Classical

variable {l : ReportLayout}

/-- Feeding a finite native choice vector to the true decoder reconstructs
exactly that vector in the cell's count-and-use report section. -/
theorem ReportCell.finiteTape_bits (c : ReportCell l) (x : Fin c.tailWidth → Bool) :
    (c.withTape (lookup (List.ofFn x)) 0).bits = List.ofFn x := by
  rw [ReportCell.withTape_bits,reportSlice]
  apply congrArg List.ofFn
  funext i
  simpa only [List.append_nil,Nat.zero_add] using CellSparse.lookup_prefix x [] i

private theorem exists_spelling {xs : List Bool} {n : ℕ} (h : xs.length=n) :
    ∃ x : Fin n → Bool, List.ofFn x=xs := by
  subst n
  exact ⟨xs.get,by simp⟩

/-- The original report vector and the genuine residual bytecode choices
are both forced. Every surviving native choice has positive sign. This
statement classifies every candidate tape, including all malformed reports. -/
theorem fixed_native_cell {w order privateWires : ℕ} (c : ReportCell l) (D : Directory)
    (g : Fin privateWires → Bool) (boundary : List Bool) (bs : List Bundle)
    (obs : List (Bool × Option ℕ)) (unsigned : D.SignFree)
    (layout : D.reportedCounts=countFields (privateWires+boundary.length) l.gadgets l.countWidth)
    (seen : ∀ t, D.guardedObservations (lookup (List.ofFn g ++ boundary ++ t))=some obs)
    (core : ∀ b ∈ bs, b.CorePass (List.ofFn g ++ boundary))
    (width : (c.bundles.map ReportBundle.useCount).sum=(bs.map Bundle.useBits).sum)
    (range : ∀ i ∈ obs.filterMap Prod.snd, i < l.gadgets)
    (fit : ∀ i : Fin l.gadgets, (obs.filterMap Prod.snd).count i.val < 2^l.countWidth)
    (positiveWord : 0<w) (profile : D.ProfileWidths)
    (clock : ∀ x : Fin c.tailWidth → Bool,
      Copied.FitsClock (appendRows D (supplements (privateWires+boundary.length+l.gadgets*l.countWidth) bs))
        w order privateWires (boundary++List.ofFn x)) :
    let pre := List.ofFn g ++ boundary
    let result := appendRows D (supplements (privateWires+boundary.length+l.gadgets*l.countWidth) bs)
    ∃ u : List Bool, ∀ (x : Fin c.tailWidth → Bool) (tail : List Bool) (sg : Bool),
      Copied.Accepted result w order g (boundary++List.ofFn x) tail sg ↔
        List.ofFn x=canonicalTail obs l.gadgets l.countWidth pre bs ∧ tail=u ∧ sg=false := by
  let pre := List.ofFn g ++ boundary
  let start := privateWires+boundary.length+l.gadgets*l.countWidth
  let extra := supplements start bs
  let result := appendRows D extra
  let correct := canonicalTail obs l.gadgets l.countWidth pre bs
  let tails := fun x : Fin c.tailWidth → Bool => Compact.assignmentTails result [] (List.ofFn g) (boundary++List.ofFn x)
  have plen : pre.length=privateWires+boundary.length := by simp [pre]
  have clen : correct.length=c.tailWidth := by
    simp only [correct,canonicalTail,List.length_append,countPart_length,useTape_length,ReportCell.tailWidth,width]
  have actualUnsigned : result.SignFree := unsigned
  have fits := append_profile profile extra (supplements_wiring start bs)
  have accept (x : Fin c.tailWidth → Bool) (t : List Bool) (sg : Bool) :
      Copied.Accepted result w order g (boundary++List.ofFn x) t sg ↔ (t,sg) ∈ tails x :=
    Compact.typed_native_assignment result _ _ positiveWord fits (clock x) g t sg
  have weight (x : Fin c.tailWidth → Bool) : ((tails x).card : ℤ) = if List.ofFn x=correct then 1 else 0 := by
    let row := c.withTape (lookup (List.ofFn x)) 0
    have bits : row.bits=List.ofFn x := c.finiteTape_bits x
    have widths : (row.bundles.map ReportBundle.useCount).sum=(bs.map Bundle.useBits).sum := by
      simpa only [row,ReportCell.withTape,tapeBundles_useCount] using width
    have obs0 : D.guardedObservations (lookup (pre++row.bits)) = some obs := seen row.bits
    have h := checked_report_weight row D pre bs obs unsigned (plen ▸ layout) obs0 core widths range fit
    dsimp only at h
    rw [plen,bits] at h
    rw [unsigned_card result actualUnsigned]
    simpa only [pre,List.append_assoc,correct,result,extra,start] using h
  obtain ⟨x₀,hx₀⟩ := exists_spelling clen
  have size : (tails x₀).card=1 := by
    have he := weight x₀
    rw [ite_eq_left_iff.mpr (by intro no; exact False.elim (no hx₀))] at he
    exact_mod_cast he
  obtain ⟨u,hu⟩ := Finset.card_eq_one.mp size
  have huMem : u ∈ tails x₀ := by simp [hu]
  have plus : u.2=false := unsigned_positive result actualUnsigned [] (List.ofFn g) (boundary++List.ofFn x₀) u.1 u.2 huMem
  refine ⟨u.1,fun x t sg => ?_⟩
  change Copied.Accepted result w order g (boundary++List.ofFn x) t sg ↔ List.ofFn x=correct ∧ t=u.1 ∧ sg=false
  rw [accept]
  by_cases hx : List.ofFn x=correct
  · have ex : x=x₀ := List.ofFn_injective (hx.trans hx₀.symm)
    subst x
    rw [hu,Finset.mem_singleton]
    simp only [hx₀,true_and]
    constructor
    · rintro rfl
      exact ⟨rfl,plus⟩
    · rintro ⟨rfl,hsg⟩
      exact Prod.ext rfl (hsg.trans plus.symm)
  · have eq := weight x
    simp only [hx,ite_false] at eq
    have empty : tails x=∅ := Finset.card_eq_zero.mp (show (tails x).card=0 by exact_mod_cast eq)
    simp [empty,hx]

/-- A failing fixed core has no accepted native report or residual choice tape.
This excludes every positive and negative return without a cancellation argument. -/
theorem fixed_native_absent {w order privateWires : ℕ} (c : ReportCell l) (D : Directory)
    (g : Fin privateWires → Bool) (boundary : List Bool) (bs : List Bundle) (unsigned : D.SignFree)
    (absent : ∀ t, D.guardedObservations (lookup (List.ofFn g++boundary++t))=none)
    (positiveWord : 0<w) (profile : D.ProfileWidths)
    (clock : ∀ x : Fin c.tailWidth → Bool,
      Copied.FitsClock (appendRows D (supplements (privateWires+boundary.length+l.gadgets*l.countWidth) bs))
        w order privateWires (boundary++List.ofFn x)) :
    let result := appendRows D (supplements (privateWires+boundary.length+l.gadgets*l.countWidth) bs)
    ∀ (x : Fin c.tailWidth → Bool) (t : List Bool) (sg : Bool),
      ¬ Copied.Accepted result w order g (boundary++List.ofFn x) t sg := by
  let pre := List.ofFn g++boundary
  let extra := supplements (privateWires+boundary.length+l.gadgets*l.countWidth) bs
  let result := appendRows D extra
  dsimp only
  intro x t sg accepted
  let row := c.withTape (lookup (List.ofFn x)) 0
  have bits : row.bits=List.ofFn x := c.finiteTape_bits x
  have plen : pre.length=privateWires+boundary.length := by simp [pre]
  have weight := checked_report_absent row D pre bs unsigned (absent row.bits)
  dsimp only at weight
  rw [plen,bits,List.append_assoc] at weight
  have sign : result.SignFree := unsigned
  let T := Compact.assignmentTails result [] (List.ofFn g) (boundary++List.ofFn x)
  have size : (T.card : ℤ)=0 := (unsigned_card result sign [] (List.ofFn g) (boundary++List.ofFn x)).trans weight
  have empty := Finset.card_eq_zero.mp (show T.card=0 by exact_mod_cast size)
  have mem : (t,sg) ∈ T := (Compact.typed_native_assignment result _ _ positiveWord
    (append_profile profile extra (supplements_wiring _ _)) (clock x) g t sg).mp accepted
  rw [empty] at mem
  exact Finset.notMem_empty _ mem

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
