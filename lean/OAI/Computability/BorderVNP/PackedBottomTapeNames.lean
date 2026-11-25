import OAI.Computability.BorderVNP.PackedBottomNativeNames

/-! # Native cursor binding inside the cell's actual compact report tape

The gadget count words come first. Earlier retained bundles occupy precisely
their actual marked-copy counts. The next row is read at its source-major,
copy-minor position even when an earlier bundle has no marked entries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open CellSparse DiagonalTallyCellReports

private theorem uses_length (bs : List ReportBundle) :
    (bs.flatMap (fun b => List.ofFn b.uses)).length = (bs.map ReportBundle.useCount).sum := by
  simp only [List.length_flatMap,List.length_ofFn]
  rfl

private theorem counts_length {l : ReportLayout} (c : ReportCell l) :
    ((List.ofFn fun g => List.ofFn (c.counts g)).flatten).length = l.gadgets*l.countWidth := by
  simp [List.length_flatten,List.map_ofFn,List.ofFn_const,Function.comp_def]

private theorem at_append {α : Type} (xs ys : List α) (i : ℕ) :
    (xs++ys)[xs.length+i]? = ys[i]? := by
  rw [List.getElem?_append_right (by omega : xs.length ≤ xs.length+i)]
  simp

/-- Direct indexed read of one typed operand bit from the exact cell tape. -/
theorem bundle_tape_get {l : ReportLayout} (c : ReportCell l) (before after : List ReportBundle)
    (b : ReportBundle) (order : c.bundles = before++b::after) (i : Fin b.useCount) :
    c.bits[l.gadgets*l.countWidth+(before.map ReportBundle.useCount).sum+i.val]? = some (b.uses i) := by
  rw [ReportCell.bits,order,List.flatMap_append,List.flatMap_cons,← counts_length c,← uses_length before,
    Nat.add_assoc,at_append,at_append,List.getElem?_append_left (by simpa only [List.length_ofFn,ReportBundle.useCount] using i.isLt),
    List.getElem?_eq_getElem (by simpa only [List.length_ofFn,ReportBundle.useCount] using i.isLt),List.getElem_ofFn]
  rfl

/-- Reading a compact suffix placed in the private cell bank binds every
source name at the actual cursor obtained from all preceding bundles. -/
theorem namedAt_report_tape {l : ReportLayout} (c : ReportCell l) (before after : List ReportBundle)
    (h : BundleHeader) (body original : List Factor) (bank : ℕ → Bool)
    (order : c.bundles = before++(physicalBundle h body original bank)::after)
    (unique : ((sidecar h.orig original).map Prod.fst).Nodup) (i : Fin h.copies)
    (tailAt : ∀ k < c.bits.length, bank (c.privateWires+c.supplied+k) = (c.bits[k]?).getD false) :
    NamedAt bank (bundleUse h body original bank i) h.copies i.val
      (c.privateWires+c.supplied+l.gadgets*l.countWidth+(before.map ReportBundle.useCount).sum)
      (sidecar h.orig original) := by
  rw [namedAt_iff]
  intro r
  let rank : Fin (positions h.orig original).length := ⟨r.val,by simpa using r.isLt⟩
  let k := finProdFinEquiv (rank,i)
  have hk : k.val = r.val*h.copies+i.val := by change i.val+h.copies*r.val = _; ac_rfl
  have read := bundle_tape_get c before after _ order k
  rw [hk] at read
  have bound := List.getElem?_eq_some_iff.mp read
  have hb := tailAt _ bound.choose
  rw [read] at hb
  rw [bundleUse_row h body original bank i unique r]
  calc
    _ = (physicalBundle h body original bank).uses k := by
      simpa only [Nat.add_assoc,Option.getD_some] using hb
    _ = _ := congrArg (physicalBundle h body original bank).uses (Fin.ext rfl)

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
