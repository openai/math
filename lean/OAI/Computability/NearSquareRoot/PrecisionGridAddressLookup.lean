import OAI.Computability.NearSquareRoot.PrecisionPhaseAddress
import OAI.Computability.NearSquareRoot.BoxRank

/-! # Address order of the generated phase table

The first supplied local table is the most significant (outermost) coordinate
of the generated coefficient stream. Reversing the natural list of axis
tables puts the least significant axis first in the physical address.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseStream
variable {α : Type*}

@[simp] theorem length_addresses (rows : List (List α)) :
    (addresses rows).length = (rows.map List.length).prod := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp [addresses, List.length_flatMap, ih]

private theorem getElem?_flatMap_row {β : Type*} (row : List α) (f : α → List β)
    (w : ℕ) (hw : ∀ a ∈ row, (f a).length = w) (j t : ℕ) (a : α)
    (hj : row[j]? = some a) (ht : t < w) :
    (row.flatMap f)[j*w+t]? = (f a)[t]? := by
  induction row generalizing j with
  | nil => simp at hj
  | cons b row ih =>
    have hb := hw b (by simp)
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst a
      simp only [Nat.zero_mul, Nat.zero_add, List.flatMap_cons]
      exact List.getElem?_append_left (hb ▸ ht)
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      rw [Nat.succ_mul, List.flatMap_cons, List.getElem?_append_right (by omega)]
      rw [hb, show j*w+w+t-w = j*w+t by omega]
      exact ih (fun a ha => hw a (by simp [ha])) j hj

/-- Looking up one tuple in the generated stream needs its mixed-radix rank
in row order. The row data need no distinctness or decidable equality. -/
theorem addresses_lookup (xs : List (List α × ℕ × α))
    (h : ∀ x ∈ xs, x.1[x.2.1]? = some x.2.2) :
    (addresses (xs.map Prod.fst))[BoxRank.position (xs.map fun x => x.1.length)
      (xs.map fun x => x.2.1)]? = some (xs.map fun x => x.2.2) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have tail := ih (fun y hy => h y (by simp [hy]))
    let rr := xs.map Prod.fst
    let j := BoxRank.position (xs.map fun y => y.1.length) (xs.map fun y => y.2.1)
    have hj : j < (addresses rr).length := by
      by_contra! hn
      have z := List.getElem?_eq_none (l := addresses rr) (i := j) hn
      rw [show (addresses rr)[j]? = some (xs.map fun y => y.2.2) from tail] at z
      contradiction
    simp only [List.map_cons, addresses, BoxRank.position]
    have size_rows : (xs.map fun y => y.1.length).prod = (addresses rr).length := by
      simp [rr, List.map_map, Function.comp_def]
    rw [size_rows, getElem?_flatMap_row _ _ _ (fun a _ => List.length_map ..) _ _ x.2.2
      (h x (by simp)) hj]
    simp only [List.getElem?_map]
    rw [tail]
    rfl

/-- The `CRT.rank` of independent local indices retrieves the tuple formed
from all of their local entries. The rows and output tuple are both supplied
slowest coordinate first. -/
theorem addresses_ofFn_rev {d : ℕ} (r : Fin d → ℕ) (v : ∀ i, Fin (r i) → α)
    (x : ∀ i, Fin (r i)) :
    (addresses ((List.ofFn fun i => List.ofFn (v i)).reverse))[CRT.rank r (fun i => (x i).val)]? =
        some ((List.ofFn (fun i => v i (x i))).reverse) := by
  let row (i : Fin d) : List α × ℕ × α := ⟨List.ofFn (v i), (x i).val, v i (x i)⟩
  have H := addresses_lookup ((List.ofFn row).reverse) (fun y hy => by
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp (List.mem_reverse.mp hy)
    subst y
    simp [row, (x i).isLt])
  simpa [row, List.map_reverse, List.map_ofFn, Function.comp_def, BoxRank.position_ofFn_rev] using H

/-- The online prefix program consumes rows from the highest to the lowest
place value. Each individual row lists its own entries in increasing order. -/
def radixRows {d : ℕ} {r : Fin d → ℕ} (v : ∀ j, Fin (r j) → α) : List (List α) :=
  (List.ofFn fun j => List.ofFn (v j)).reverse

/-- Row lookup for the varying-count table forest read by the tape program. -/
def radixTable {d : ℕ} {r : Fin d → ℕ} (v : ∀ j, Fin (r j) → α) (j : ℕ) : List α :=
  ((radixRows v)[j]?).getD []

theorem radixTable_range {d : ℕ} {r : Fin d → ℕ} (v : ∀ j, Fin (r j) → α) :
    (List.range d).map (radixTable v) = radixRows v := by
  apply List.ext_getElem <;> simp [radixTable,radixRows]
  intro i hi
  have hlen : i < ((List.ofFn fun a => List.ofFn (v a)).reverse).length := by simpa using hi
  rw [List.getElem?_eq_getElem hlen]
  simp

theorem radixTable_row {d : ℕ} {r : Fin d → ℕ} (v : ∀ j, Fin (r j) → α) {t : ℕ}
    (ht : t < d) : ∃ j, radixTable v t = List.ofFn (v j) := by
  have h : radixTable v t ∈ (List.range d).map (radixTable v) := List.mem_map_of_mem (List.mem_range.mpr ht)
  rw [radixTable_range] at h
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp (List.mem_reverse.mp h)
  exact ⟨j,hj.symm⟩

theorem radixTable_count {d : ℕ} {r : Fin d → ℕ} (v : ∀ j, Fin (r j) → α) :
    ((List.range d).map (fun t => (radixTable v t).length)).prod = ∏ i, r i := by
  rw [show (fun t => (radixTable v t).length) = List.length ∘ radixTable v from rfl,
    ← List.map_map, radixTable_range]
  simp [radixRows, List.map_reverse, List.map_ofFn, Fin.prod_ofFn, Function.comp_def]

/-- The product of the local phase-table entries at the mixed-radix address
equals the single diagonal coefficient at the corresponding physical index. -/
theorem radixTable_coefficient {β : Type*} [CommMonoid β] {d : ℕ} {r : Fin d → ℕ}
    (v : ∀ j, Fin (r j) → α) (ideal : α → β) (x : ∀ j, Fin (r j)) :
    (((addresses ((List.range d).map (radixTable v))).map (fun xs => (xs.map ideal).prod))[CRT.rank r (fun i => (x i).val)]?) = some (∏ i, ideal (v i (x i))) := by
  rw [radixTable_range, radixRows, List.getElem?_map, addresses_ofFn_rev r v x]
  simp [List.map_reverse, List.map_ofFn, Function.comp_def, Fin.prod_ofFn]

end PhaseStream

end NearSquareRoot
end Computability
end OAI
