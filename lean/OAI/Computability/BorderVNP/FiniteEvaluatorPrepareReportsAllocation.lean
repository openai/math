import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsParameters
import OAI.Computability.BorderVNP.DiagonalTallyReportAllocation
import OAI.Computability.BorderVNP.RoutingISACellBanks

/-! # Disjoint physical regions of the finite report preparer

Each owned global cell has one fixed-stride receiving bank, one tail width
and two supplement counters. These same allocated intervals supply all
chronological header reads, including when the field-report width is zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open RoutingISA DiagonalTallyAllocation

/-- Actual frame pointers of the finite preparer in the public pre-task allocation. -/
def allocatedLayout (pre : BeforeTasks) (frame control scalars digits : ℕ) : Layout :=
  ⟨frame,control,pre.six,pre.counters,pre.tailWidths,scalars,digits⟩

/-- This row lies in the receive-bank reservation for its true global cell. -/
def Row.InBank (r : Row) (banks : CellBanks.Layout) : Prop :=
  r.number < banks.cells ∧ r.base=banks.bank r.number ∧ r.canonical+r.bits.length ≤ banks.stride

variable {pre : BeforeTasks} {banks : CellBanks.Layout} {frame control scalars digits : ℕ}
local notation "alloc" => allocatedLayout pre frame control scalars digits

private theorem prefixBounds (pre : BeforeTasks) :
    pre.tailWidths=pre.start ∧ pre.tailWidths+pre.bound.cells ≤ pre.counters ∧
    pre.counters+2*pre.bound.cells ≤ pre.four ∧ pre.four+4*pre.bound.cells=pre.six ∧
    pre.six+6*pre.bound.cells ≤ pre.limit := by
  simp only [BeforeTasks.tailWidths,BeforeTasks.counters,BeforeTasks.supplement,BeforeTasks.four,
    BeforeTasks.merged,BeforeTasks.six,BeforeTasks.limit,BeforeTasks.bundleTable,BeforeTasks.ranges]
  exact ⟨trivial,by omega,by omega,trivial,by omega⟩

private theorem bankEnd {r : Row} (hr : r.InBank banks) :
    r.start+r.bits.length ≤ banks.bankStart+banks.cells*banks.stride := by
  obtain ⟨num,base,len⟩ := hr
  have endBank := Nat.mul_le_mul_right banks.stride (show r.number+1 ≤ banks.cells by omega)
  simp only [Nat.add_mul,Nat.one_mul] at endBank
  simp only [Row.start,base,CellBanks.Layout.bank]
  omega

/-- The counter pair, width, and guessed bits of an actual row are separated
using the single receive-bank and pre-task partition endpoints. -/
theorem row_separated_le {r : Row} (hr : r.InBank banks) (cells : banks.cells ≤ pre.bound.cells)
    (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start) : r.Separated alloc := by
  have hb := bankEnd hr
  have num := hr.1
  have ⟨ts,tc,cf,_,_⟩ := prefixBounds pre
  unfold Row.Separated
  simp only [allocatedLayout]
  refine ⟨⟨by omega,by omega⟩,?_⟩
  intro a h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h|h <;> right <;> omega

private theorem bankApart {r z : Row} (hr : r.InBank banks) (hz : z.InBank banks)
    (distinct : r.number ≠ z.number) : r.start+r.bits.length ≤ z.base ∨ z.start+z.bits.length ≤ r.base := by
  obtain ⟨_,rb,rf⟩ := hr
  obtain ⟨_,zb,zf⟩ := hz
  simp only [Row.start,rb,zb,CellBanks.Layout.bank]
  rcases lt_or_gt_of_ne distinct with h|h
  · have bound := Nat.mul_le_mul_right banks.stride (show r.number+1 ≤ z.number by omega)
    simp only [Nat.add_mul,Nat.one_mul] at bound
    left; omega
  · have bound := Nat.mul_le_mul_right banks.stride (show z.number+1 ≤ r.number by omega)
    simp only [Nat.add_mul,Nat.one_mul] at bound
    right; omega

/-- Specialization to an allocation of exactly the physical cell count. -/
theorem row_separated {r : Row} (hr : r.InBank banks) (cells : banks.cells=pre.bound.cells)
    (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start) : r.Separated alloc :=
  row_separated_le hr cells.le bankBefore

/-- Distinct genuine global row numbers ensure that every write of one row
lies outside every write of the other, even for adjacent counter pairs. -/
theorem row_apart_le {r z : Row} (hr : r.InBank banks) (hz : z.InBank banks)
    (cells : banks.cells ≤ pre.bound.cells) (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start)
    (distinct : r.number ≠ z.number) (a : ℕ) (ha : ¬ r.Outside alloc a) : z.Outside alloc a := by
  have rEnd := bankEnd hr
  have zEnd := bankEnd hz
  have rn := hr.1
  have zn := hz.1
  have ⟨ts,tc,cf,_,_⟩ := prefixBounds pre
  have adj := bankApart hr hz distinct
  unfold Row.Outside at ha ⊢
  simp only [allocatedLayout] at ha ⊢
  have rstart : r.base ≤ r.start := Nat.le_add_right ..
  have zstart : z.base ≤ z.start := Nat.le_add_right ..
  omega

/-- Specialization to an allocation of exactly the physical cell count. -/
theorem row_apart {r z : Row} (hr : r.InBank banks) (hz : z.InBank banks)
    (cells : banks.cells=pre.bound.cells) (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start)
    (distinct : r.number ≠ z.number) (a : ℕ) (ha : ¬ r.Outside alloc a) : z.Outside alloc a :=
  row_apart_le hr hz cells.le bankBefore distinct a ha

/-- Previously delivered input bits survive all row stores, including the
new report bits for the same cell. -/
theorem supplied_outside_of_banks {r z : Row} (hr : r.InBank banks) (hz : z.InBank banks)
    (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start)
    (same : r.number=z.number → r=z) {i : ℕ} (hi : i < r.canonical) : z.Outside alloc (r.base+i) := by
  have rend := bankEnd hr
  have zn := hz.1
  have ⟨ts,tc,_,_,_⟩ := prefixBounds pre
  by_cases eq : r.number=z.number
  · obtain rfl := same eq
    simp only [Row.Outside,allocatedLayout,Row.start] at *
    omega
  · have adj := bankApart hr hz eq
    simp only [Row.Outside,allocatedLayout,Row.start] at *
    omega

/-- Specialization to an allocation of exactly the physical cell count. -/
theorem supplied_outside {r z : Row} (hr : r.InBank banks) (hz : z.InBank banks)
    (cells : banks.cells=pre.bound.cells) (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start)
    (same : r.number=z.number → r=z) {i : ℕ} (hi : i < r.canonical) : z.Outside alloc (r.base+i) := by
  have rend := bankEnd hr
  have zn := hz.1
  have ⟨ts,tc,_,_,_⟩ := prefixBounds pre
  by_cases eq : r.number=z.number
  · obtain rfl := same eq
    simp only [Row.Outside,allocatedLayout,Row.start] at *
    omega
  · have adj := bankApart hr hz eq
    simp only [Row.Outside,allocatedLayout,Row.start] at *
    omega

/-- The entire report and counter region precedes every word in the public
four- and six-word tables and all subsequent memory. -/
theorem beyond_four_outside_le {r : Row} (hr : r.InBank banks) (cells : banks.cells ≤ pre.bound.cells)
    (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start) {a : ℕ} (after : pre.four ≤ a) :
    r.Outside alloc a := by
  have bound := bankEnd hr
  have num := hr.1
  have ⟨ts,tc,cf,_,_⟩ := prefixBounds pre
  simp only [Row.Outside,allocatedLayout]
  omega

/-- Specialization to an allocation of exactly the physical cell count. -/
theorem beyond_four_outside {r : Row} (hr : r.InBank banks) (cells : banks.cells=pre.bound.cells)
    (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start) {a : ℕ} (after : pre.four ≤ a) :
    r.Outside alloc a :=
  beyond_four_outside_le hr cells.le bankBefore after

/-- Each occupied header and its counter and receive-bank addresses fit even
when the physical cells are a strict subset of the reserved public capacity. -/
theorem row_fits_of_allocation {w : ℕ} {r : Row} {i : ℕ} (hr : r.InBank banks)
    (cells : banks.cells ≤ pre.bound.cells) (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start)
    (fit : pre.limit < 2^w) (rank : i < pre.bound.cells) (width : r.bits.length=scalars*digits) :
    r.Fits alloc w (pre.six+6*i) := by
  have rend := bankEnd hr
  have num := hr.1
  obtain ⟨ts,tc,cf,fs,stop⟩ := prefixBounds pre
  simp only [Row.Fits,allocatedLayout]
  exact ⟨by omega,by omega,by omega,by omega,width⟩

/-- Numeric row room and immutable actual headers suffice for the chronological
native inputs also when additional unused cells are reserved. -/
theorem inputs_allocated_le {w : ℕ} (rows : List Row) (m : ℕ → ℕ)
    (cells : banks.cells ≤ pre.bound.cells) (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start)
    (fit : pre.limit < 2^w) (count : rows.length ≤ pre.bound.cells)
    (incoming : ∀ i : Fin rows.length, rows[i].InBank banks)
    (width : ∀ i : Fin rows.length, rows[i].bits.length=scalars*digits)
    (stored : ∀ i : Fin rows.length, rows[i].Stored (pre.six+6*i.val) m) :
    Inputs alloc w rows pre.six m := by
  apply inputs_from_stored _ _ _ _ _ stored
  · intro i
    exact row_fits_of_allocation (incoming i) cells bankBefore fit (i.isLt.trans_le count) (width i)
  · intro i j _ k
    apply beyond_four_outside_le (incoming i) cells bankBefore
    have h := (prefixBounds pre).2.2.2.1
    omega

/-- Numeric row room and immutable actual headers suffice for the entire
chronological native report input predicate. No pairwise read/write
separation condition on headers is needed. -/
theorem inputs_allocated {w : ℕ} (rows : List Row) (m : ℕ → ℕ)
    (cells : banks.cells=pre.bound.cells) (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start)
    (fit : pre.limit < 2^w) (count : rows.length ≤ pre.bound.cells)
    (incoming : ∀ i : Fin rows.length, rows[i].InBank banks)
    (width : ∀ i : Fin rows.length, rows[i].bits.length=scalars*digits)
    (stored : ∀ i : Fin rows.length, rows[i].Stored (pre.six+6*i.val) m) :
    Inputs alloc w rows pre.six m :=
  inputs_allocated_le rows m cells.le bankBefore fit count incoming width stored

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI
