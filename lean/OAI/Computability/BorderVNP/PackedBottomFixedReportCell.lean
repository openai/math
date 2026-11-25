import OAI.Computability.BorderVNP.PackedBottomFixedUseTape
import OAI.Computability.BorderVNP.DiagonalTallyReportBitsRead

/-! # The native report cell's count block and canonical physical use suffix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open CellSparse DiagonalTallyCellReports

/-- Reading the actual native bundles in stable site order gives the use tape
of their original selected wires, with the full private bodies in place. -/
theorem nativeBundles_useTape {J : Type*} (pre : List Bool) (sites : List J)
    (source : J → Bundle) (body : J → List Factor) :
    ((sites.map fun j => physicalBundle (source j).header (body j) (source j).factors (lookup pre)).flatMap
      (fun b => List.ofFn b.uses)) = useTape pre (sites.map source) := by
  induction sites with
  | nil => rfl
  | cons j js ih =>
    simp only [List.map_cons,List.flatMap_cons,useTape] at ih ⊢
    exact congrArg₂ List.append ((source j).useChoice_native pre (body j)).symm ih

private theorem count_length {l : ReportLayout} (c : ReportCell l) :
    (List.ofFn fun g => List.ofFn (c.counts g)).flatten.length=l.gadgets*l.countWidth := by
  simp [List.length_flatten,List.map_ofFn,List.ofFn_const,Function.comp_def]

private theorem use_length (bs : List ReportBundle) :
    (bs.flatMap fun b => List.ofFn b.uses).length = (bs.map ReportBundle.useCount).sum := by
  simp only [List.length_flatMap,List.length_ofFn]
  rfl

/-- A candidate native report cell passes the physical supplemental rows
precisely when its guessed use suffix is the canonical list of the fixed
original assignment. Its checked count digits come before that suffix. -/
theorem reportCell_supplements_iff {l : ReportLayout} (c : ReportCell l)
    (pre : List Bool) (bs : List Bundle) (boxes : List (List Factor))
    (core : ∀ b ∈ bs, b.CorePass pre) (shape : (c.bundles.map ReportBundle.useCount).sum=(bs.map Bundle.useBits).sum) :
    (∀ row ∈ supplements (pre.length+l.gadgets*l.countWidth) bs, row.Valid boxes (lookup (pre++c.bits))) ↔
      c.bundles.flatMap (fun b => List.ofFn b.uses) = useTape pre bs := by
  have h := supplements_iff_useTape pre (List.ofFn fun g => List.ofFn (c.counts g)).flatten
    (c.bundles.flatMap fun b => List.ofFn b.uses) bs boxes core ((use_length _).trans shape)
  simpa only [count_length,ReportCell.bits,List.append_assoc] using h

/-- The checked native cell reads every little-endian count digit and every
physically forced use at its own absolute RAM address. The formal checker
indexes the same bits relative to the cell's original physical prefix. -/
theorem reportCell_read_fixed {l : ReportLayout} (c : ReportCell l) (pre : List Bool) (bs : List Bundle)
    (boxes : List (List Factor)) (core : ∀ b ∈ bs, b.CorePass pre)
    (shape : (c.bundles.map ReportBundle.useCount).sum=(bs.map Bundle.useBits).sum)
    (m : ℕ → ℕ) (words : literalBitsAt m (c.external+c.supplied) c.bits)
    (pass : ∀ row ∈ supplements (pre.length+l.gadgets*l.countWidth) bs, row.Valid boxes (lookup (pre++c.bits))) :
    (∀ g j, m (c.external+c.supplied+g.val*l.countWidth+j.val)=(c.counts g j).toNat) ∧
      literalBitsAt m (c.external+c.supplied+l.gadgets*l.countWidth) (useTape pre bs) := by
  refine ⟨(c.readBits m words).1,?_⟩
  rw [← (reportCell_supplements_iff c pre bs boxes core shape).mp pass]
  rw [literalBitsAt,ReportCell.bits,List.map_append] at words
  simpa only [literalBitsAt,List.length_map,count_length] using words.right

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
