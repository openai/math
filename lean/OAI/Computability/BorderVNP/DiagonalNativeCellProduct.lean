import OAI.Computability.BorderVNP.DiagonalNativeCellValue
import OAI.Computability.BorderVNP.CubePhysicalMergedCellRead

/-! # Reindexing the native owned-cell products over all private assignments

On each team the actual address test decides which directory rows are called.
With a faithful ordinal for the cells and the common ownership data, multiplying
these row products visits each cell once. Expanding its checked signed private
sum then enumerates one complete assignment of all the cell-local wires.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellDispatch

open VPVNP.BurstRAM CompactMachine CellMacro CellSparse
open scoped BigOperators Classical

variable {w : ℕ} {Cell : Type*} [Fintype Cell]

private theorem prod_filter {A R : Type*} [CommMonoid R] (p : A → Bool) (f : A → R) (xs : List A) :
    ((xs.filter p).map f).prod = (xs.map fun i => if p i then f i else 1).prod := by
  induction xs with
  | nil => rfl
  | cons i xs ih => cases h : p i <;> simp [h,ih]

/-- The true native owned-row product can be read in any finite naming of the same cells.
The unowned rows are inspected but contribute the multiplicative unit. -/
theorem Frame.ownedRows_product (f : Frame) (m : Memory w) (order : Fin f.count ≃ Cell)
    (value : ℕ → ℤ) (owner : Cell → ℕ) (amount : Cell → ℤ)
    (ownerAt : ∀ i : Fin f.count, (m (f.address i.val)).val = owner (order i))
    (valueAt : ∀ i : Fin f.count, owner (order i) = f.team → value i.val = amount (order i)) :
    ((f.ownedRows m 0 f.count).map value).prod = ∏ c, if owner c = f.team then amount c else 1 := by
  rw [ownedRows,prod_filter]
  have rangeEq : List.range' 0 f.count = List.ofFn (fun i : Fin f.count => i.val) := by
    apply List.ext_getElem <;> simp
  rw [rangeEq,List.map_ofFn,List.prod_ofFn,←order.prod_comp (fun c => if owner c = f.team then amount c else 1)]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Function.comp_def,decide_eq_true_eq,ownerAt]
  split <;> first | rfl | exact valueAt _ ‹_›

/-- Multiplying the true row products on all teams gives precisely one factor for
each global cell. An unowned row can have arbitrary contents on that team. -/
theorem all_ownedRows_product {T : ℕ} (frames : Fin T → Frame) (mem : Fin T → Memory w)
    (order : ∀ t, Fin (frames t).count ≃ Cell) (owner : Cell → Fin T)
    (rows : Fin T → ℕ → CellInput) (cells : Cell → CellInput)
    (teamAt : ∀ t, (frames t).team = t.val)
    (ownerAt : ∀ t (i : Fin (frames t).count), ((mem t) ((frames t).address i.val)).val = (owner (order t i)).val)
    (cellAt : ∀ t (i : Fin (frames t).count), owner (order t i) = t → rows t i.val = cells (order t i)) :
    (∏ t : Fin T, (((frames t).ownedRows (mem t) 0 (frames t).count).map fun i => (rows t i).weight).prod) =
      ∏ c, (cells c).weight := by
  have row (t : Fin T) := (frames t).ownedRows_product (mem t) (order t) (fun i => (rows t i).weight)
    (fun c => (owner c).val) (fun c => (cells c).weight) (ownerAt t)
    (fun i eq => congrArg CellInput.weight (cellAt t i (Fin.ext (eq.trans (teamAt t)))))
  simp_rw [row,teamAt,←Fin.ext_iff]
  rw [Finset.prod_comm]
  simp

/-- The product of native cell call weights expands into one sum over all independent
private bit assignments. Each directory reads exactly those bits followed by its fixed
external data. -/
theorem all_ownedRows_private_sum {T : ℕ} (frames : Fin T → Frame) (mem : Fin T → Memory w)
    (order : ∀ t, Fin (frames t).count ≃ Cell) (owner : Cell → Fin T)
    (rows : Fin T → ℕ → CellInput) (cells : Cell → CellInput)
    (teamAt : ∀ t, (frames t).team = t.val)
    (ownerAt : ∀ t (i : Fin (frames t).count), ((mem t) ((frames t).address i.val)).val = (owner (order t i)).val)
    (cellAt : ∀ t (i : Fin (frames t).count), owner (order t i) = t → rows t i.val = cells (order t i)) :
    (∏ t : Fin T, (((frames t).ownedRows (mem t) 0 (frames t).count).map fun i => (rows t i).weight).prod) =
      ∑ z : (c : Cell) → Fin (cells c).privateWires → Bool,
        ∏ c, (cells c).directory.weight (lookup (List.ofFn (z c) ++ (cells c).external)) := by
  rw [all_ownedRows_product frames mem order owner rows cells teamAt ownerAt cellAt]
  simp only [CellInput.weight,Finset.prod_univ_sum,Fintype.piFinset_univ]

end RoutingISA.CellDispatch

end BorderVNP
end Computability
end OAI
