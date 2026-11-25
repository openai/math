import OAI.Computability.BorderVNP.PackedBottomReportBundle
import OAI.Computability.BorderVNP.PackedBottomReportCursors
import OAI.Computability.BorderVNP.CellGuardedObservations

/-! # Canonical weighted use choices in a fixed physical cell prefix

A successful retained box makes its staged report equal the original unary
wire at every real copy. Its stored zero factors force the unused stage lanes.
Neither assertion uses a supplemental use guess.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open CellSparse BottomGridBank DiagonalTallyCellReports
open private mapM_present from OAI.Computability.BorderVNP.PackedGridDirectory

/-- The original unary wire selected in this source-major, copy-minor
occurrence. It is read from the fixed cell prefix before the count and use tail. -/
def Bundle.useChoice (b : Bundle) (pre : List Bool) (k : Fin b.useBits) : Bool :=
  let rc : Fin (count b.factors) × Fin b.header.copies := finProdFinEquiv.symm k
  lookup pre (b.header.boxBase+rc.2.val*b.header.stride+(selectedWires b.factors)[rc.1.val]'(by
    simpa only [selectedWires_length] using rc.1.isLt))

/-- Recover the address of the actual selected wire at its original copy. -/
theorem Bundle.useChoice_pair (b : Bundle) (pre : List Bool) (r : Fin (count b.factors)) (i : Fin b.header.copies) :
    b.useChoice pre (finProdFinEquiv (r,i)) = lookup pre
      (b.header.boxBase+i.val*b.header.stride+(selectedWires b.factors)[r.val]'(by simp)) := by
  simp only [useChoice,Equiv.symm_apply_apply]

/-- The unique use list computed from the old core, ordered by physical
bundle, original marked source and actual copy. -/
def useTape (pre : List Bool) (bs : List Bundle) := bs.flatMap fun b => List.ofFn (b.useChoice pre)

/-- The number of compact use bits is the exact sum of source-copy counts. -/
@[simp] theorem useTape_length (pre : List Bool) (bs : List Bundle) :
    (useTape pre bs).length = (bs.map Bundle.useBits).sum := by
  simp [useTape,List.length_flatMap]

/-- On the true native bundle, its physical choice list is exactly the canonical
list even when its source count or its multiplicity is zero. -/
theorem Bundle.useChoice_native (b : Bundle) (pre : List Bool) (body : List Factor) :
    List.ofFn (b.useChoice pre) =
      List.ofFn (physicalBundle b.header body b.factors (lookup pre)).uses := by
  have size : (positions b.header.orig b.factors).length = count b.factors := positions_length ..
  let castRow : Fin (count b.factors) → Fin (positions b.header.orig b.factors).length := Fin.cast size.symm
  apply List.ext_getElem
  · rw [List.length_ofFn,List.length_ofFn]
    exact congrArg (fun k => k*b.header.copies) size.symm
  · intro k hk₁ hk₂
    let z : Fin b.useBits := ⟨k,by simpa using hk₁⟩
    let rc : Fin (count b.factors) × Fin b.header.copies := finProdFinEquiv.symm z
    let w := finProdFinEquiv (castRow rc.1,rc.2)
    have hw : w.val = k := by
      change rc.2.val+b.header.copies*rc.1.val = k
      exact congrArg Fin.val (finProdFinEquiv.apply_symm_apply z)
    rw [List.getElem_ofFn,List.getElem_ofFn]
    change b.useChoice pre z = _
    rw [← finProdFinEquiv.apply_symm_apply z,b.useChoice_pair]
    exact (physicalBundle_use b.header body b.factors (lookup pre) (castRow rc.1) rc.2).symm.trans
      (congrArg (physicalBundle b.header body b.factors (lookup pre)).uses (Fin.ext hw))

/-- The declared box geometry and the observations of its original stages
and zero suffix in the fixed physical bank. -/
structure Bundle.CorePass (b : Bundle) (pre : List Bool) : Prop where
  /-- Actual distance between two copies of the physical box. -/
  stride : b.header.stride = bottomStride b.header.orig b.header.cap
  /-- The number of real marked sources fits the reserved use area. -/
  capacity : count b.factors ≤ b.header.cap
  /-- All copies lie inside the pre-report bank. -/
  extent : b.header.boxBase+b.header.copies*b.header.stride ≤ pre.length
  /-- Every staged original factor passes at its physical copy. -/
  staged : ∀ i : Fin b.header.copies, ∀ f ∈ stage b.header.orig b.factors,
    (f.observe (lookup pre) (b.header.boxBase+i.val*b.header.stride) i.val).isSome = true
  /-- The actual private zero factors force the whole unused report suffix. -/
  zero : ∀ i : Fin b.header.copies, ∀ k < b.header.cap-count b.factors,
    lookup pre (b.header.boxBase+i.val*b.header.stride+(b.header.orig+count b.factors+k)) = false

/-- Every actual factor in a referenced box is observed in each genuine copy
when the pre-supplement directory passes. -/
theorem guarded_box_factors {D : Directory} (pre : List Bool) {os : List (Bool × Option ℕ)}
    (pass : D.guardedObservations (lookup pre) = some os) {id base copies stride : ℕ}
    (row : Record.box id base copies stride ∈ D.records) (i : Fin copies) :
    ∀ f ∈ D.boxes.getD id [], (f.observe (lookup pre) (base+i.val*stride) i.val).isSome = true := by
  have hp := (Directory.guarded_some.mp pass).2
  have present : (D.observations (lookup pre)).isSome = true := by rw [hp]; rfl
  have all := (mapM_present D.occurrences (fun o => o.factor.observe (lookup pre) o.offset o.copy)).mp present
  intro f hf
  apply all (⟨f,base+i.val*stride,i.val⟩ : Occurrence)
  apply List.mem_flatMap.mpr ⟨_,row,?_⟩
  exact List.mem_flatMap.mpr ⟨i.val,List.mem_range.mpr i.isLt,List.mem_map.mpr ⟨f,hf,rfl⟩⟩

/-- The observed stored factors, including its physical zero rows, discharge
the original-stage and padding premises using the actual referenced box. -/
theorem Bundle.corePass_of_guarded (b : Bundle) (pre : List Bool) {D : Directory} {os : List (Bool × Option ℕ)}
    (pass : D.guardedObservations (lookup pre) = some os) (id : ℕ)
    (row : Record.box id b.header.boxBase b.header.copies b.header.stride ∈ D.records)
    (staged : ∀ f ∈ stage b.header.orig b.factors, f ∈ D.boxes.getD id [])
    (zeros : ∀ f ∈ reportZeros b.header.orig (count b.factors) b.header.cap, f ∈ D.boxes.getD id [])
    (hs : b.header.stride = bottomStride b.header.orig b.header.cap) (hc : count b.factors ≤ b.header.cap)
    (he : b.header.boxBase+b.header.copies*b.header.stride ≤ pre.length) : b.CorePass pre := by
  have hp := guarded_box_factors pre pass row
  refine ⟨hs,hc,he,fun i f hf => hp i f (staged f hf),?_⟩
  intro i
  apply (reportZeros_pass ..).mp
  rw [List.all_eq_true]
  exact fun f hf => hp i f (zeros f hf)

end Packing.BottomReports

end BorderVNP
end Computability
end OAI
