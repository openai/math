import OAI.Computability.BorderVNP.PackedCellSlabs
import OAI.Computability.BorderVNP.PackedDirectory

/-! # Distinct destination bits in the compacted data directory and the cell banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

open CellSlabs Function
open scoped Classical

/-- Candidate numbers retained by the positive-width compacting writer. -/
def Layout.populated (d : Layout) (pp lp : ℕ → ℕ × ℕ) : List ℕ :=
  (List.range d.candidates).filter fun i => 0 < (d.row pp lp i).width

/-- The concrete demand directory preserves the exact increasing order of the
selected candidate numbers. -/
theorem Layout.directory_eq_populated (d : Layout) (pp lp : ℕ → ℕ × ℕ) :
    d.directory pp lp = (d.populated pp lp).map (d.row pp lp) := by
  simp [Layout.directory,Layout.populated,List.filter_map,Function.comp_def]

/-- Candidate number of each actual populated row. Filtering never identifies two
indices, including when two records have the same source or target team. -/
def Layout.populatedIndex (d : Layout) (pp lp : ℕ → ℕ × ℕ) :
    Fin (d.directory pp lp).length ↪ Fin d.candidates where
  toFun i :=
    let h : i.val < (d.populated pp lp).length := by simpa only [d.directory_eq_populated,List.length_map] using i.isLt
    let n := (d.populated pp lp)[i.val]'h
    ⟨n, List.mem_range.mp (List.mem_filter.mp (List.getElem_mem h)).1⟩
  inj' := by
    intro i j e
    have same := congrArg Fin.val e
    have nd : (d.populated pp lp).Nodup := List.nodup_range.filter _
    exact Fin.ext (nd.getElem_inj_iff.mp same)

/-- Reading a compacted input record is the candidate evaluated at its true public number. -/
theorem Layout.populatedRow (d : Layout) (pp lp : ℕ → ℕ × ℕ) (i : Fin (d.directory pp lp).length) :
    (d.directory pp lp)[i.val] = d.row pp lp (d.populatedIndex pp lp i) := by
  simp only [d.directory_eq_populated,List.getElem_map]
  rfl

namespace DataSlabs

variable {A : Type*} [Fintype A] {cells : ℕ}
variable (cell : A → Fin cells) (row : A ↪ ℕ) (width : A → ℕ)

/-- Physical size of the supplied-data portion of a cell bank. -/
noncomputable def size (c : Fin cells) : ℕ := ∑ t, if cell t = c then width t else 0

/-- Within-cell displacement of the first bit of a supplied private description or
live input block. Only the widths of earlier supplied words belonging to this cell
contribute. -/
noncomputable def base (a : A) : ℕ :=
  start row (fun t => if cell t = cell a then width t else 0) a

/-- The slot interval fits into its owning bank even for an empty supplied word. -/
theorem base_end_le (a : A) : base cell row width a + width a ≤ size cell width (cell a) := by
  simpa [base,size] using end_le_capacity row (fun t => if cell t = cell a then width t else 0) a

/-- The fixed-stride absolute address used by the two-word cell-owner directory. -/
noncomputable def address (origin stride : ℕ) (x : (a : A) × Fin (width a)) : ℕ :=
  origin+(cell x.1).val*stride+base cell row width x.1+x.2.val

/-- The absolute addresses distinguish every supplied slot on every cell. Within one
cell this uses the checked row-prefix bijection. Across cells it uses the fitted stride. -/
theorem address_injective (origin stride : ℕ) (room : ∀ c, size cell width c ≤ stride) :
    Injective (address cell row width origin stride) := by
  rintro ⟨a,k⟩ ⟨b,j⟩ eq
  change origin + (cell a).val*stride + base cell row width a + k.val =
    origin + (cell b).val*stride + base cell row width b + j.val at eq
  have ha := (Nat.add_lt_add_left k.isLt _).trans_le ((base_end_le cell row width a).trans (room _))
  have hb := (Nat.add_lt_add_left j.isLt _).trans_le ((base_end_le cell row width b).trans (room _))
  have same : cell a = cell b := by
    apply Fin.ext
    rcases lt_trichotomy (cell a).val (cell b).val with hl | he | hg
    · have h := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hl)
      rw [Nat.succ_mul] at h; omega
    · exact he
    · have h := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hg)
      rw [Nat.succ_mul] at h; omega
  let wid := fun t => if cell t = cell a then width t else 0
  let ka : Fin (wid a) := ⟨k.val, by simp [wid]⟩
  let jb : Fin (wid b) := ⟨j.val, by simp [wid,same]⟩
  have val : (ordinal row wid ⟨a,ka⟩).val = (ordinal row wid ⟨b,jb⟩).val := by
    have eb : base cell row width b = start row wid b := by simp [base,wid,same]
    change base cell row width a + k.val = start row wid b + j.val
    rw [← eb]
    rw [same] at eq
    omega
  have hk := (ordinal row wid).injective (Fin.ext val)
  have eab : a = b := congrArg Sigma.fst hk
  subst b
  exact congrArg (Sigma.mk a) (Fin.ext (by omega : k.val = j.val))

end DataSlabs
end Packing.Directory

end BorderVNP
end Computability
end OAI
