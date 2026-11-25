import OAI.Hierarchy.ProtocolRAMMarkPaths
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic

namespace OAI
/-! # Public gate addresses in the purchase-path tape

Each candidate emits `4*H+3` gates. Its ordinal selects both the candidate
and a row-independent gate shape. A field contains either a public literal
address or the stock address associated with one raw tile ID in the row.
-/

namespace Hierarchy.ProtocolRAMPurchaseGateShape

open ProtocolRAM.MarkTape

inductive Field (H : ℕ) where
  | literal (address : ℕ)
  | stock (pos : Fin H)
deriving DecidableEq

def Field.eval {H tiles : ℕ} (f : Field H) (work : ℕ) (row : Fin H → Fin tiles) : ℕ :=
  match f with
  | .literal address => address
  | .stock pos => work + 4 + (row pos).val

def Field.stockPos? {H : ℕ} : Field H → Option (Fin H)
  | .literal _ => none
  | .stock pos => some pos

/-- The public bank stores a literal address or the index of a raw tile ID. -/
def Field.payload {H : ℕ} : Field H → ℕ
  | .literal address => address
  | .stock pos => pos.val

structure Shape (H : ℕ) where
  lhs : Field H
  rhs : Field H
  dst : Field H
deriving DecidableEq

def Shape.eval {H tiles : ℕ} (s : Shape H) (work : ℕ) (row : Fin H → Fin tiles) : Gate :=
  ⟨s.lhs.eval work row, s.rhs.eval work row, s.dst.eval work row⟩

def Shape.field {H : ℕ} (s : Shape H) : Fin 3 → Field H := ![s.lhs, s.rhs, s.dst]

/-- Public shape of the init, test, pivot, clear and output portions of a row. -/
def pathList (tiles work i H : ℕ) : List (Shape H) :=
  let flag := Field.literal (work + 1)
  let tmp := Field.literal (work + 2)
  let keep := Field.literal (work + 3)
  [⟨.literal work, .literal work, flag⟩] ++
    (List.finRange H).flatMap (fun j => [⟨flag, .stock j, tmp⟩, ⟨tmp, tmp, flag⟩]) ++
    [⟨flag, flag, keep⟩] ++
    (List.finRange H).flatMap (fun j => [⟨keep, .stock j, tmp⟩, ⟨tmp, tmp, .stock j⟩]) ++
    [⟨keep, keep, .literal (work + 4 + tiles + i)⟩]

private theorem length_pairs {α β : Type*} (l : List α) (u v : α → β) :
    (l.flatMap (fun x => [u x, v x])).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, Nat.mul_add]

@[simp] theorem pathList_length (tiles work i H : ℕ) :
    (pathList tiles work i H).length = 4 * H + 3 := by
  simp only [pathList, List.length_append, List.length_singleton, length_pairs, List.length_finRange]
  omega

def pathShape (tiles work i H : ℕ) (j : Fin (4 * H + 3)) : Shape H :=
  (pathList tiles work i H)[j.val]'(by rw [pathList_length]; exact j.isLt)

/-- Reading one raw tile ID suffices for all three addresses of a gate. -/
theorem pathShape_single_stock (tiles work i H : ℕ) (j : Fin (4 * H + 3)) :
    let s := pathShape tiles work i H j
    s.lhs.stockPos? = none ∧ (s.rhs.stockPos? = none ∨ s.dst.stockPos? = none) := by
  have every : ∀ s ∈ pathList tiles work i H,
      s.lhs.stockPos? = none ∧ (s.rhs.stockPos? = none ∨ s.dst.stockPos? = none) := by
    simp [pathList, Field.stockPos?]
    rintro s (⟨u,rfl | rfl⟩ | rfl | ⟨u,rfl | rfl⟩ | rfl) <;> simp
  exact every (pathShape tiles work i H j) (List.getElem_mem ..)

private theorem pathShape_ofFn (tiles work i H : ℕ) :
    List.ofFn (pathShape tiles work i H) = pathList tiles work i H := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.getElem_ofFn, pathShape]

theorem pathList_eval {H tiles : ℕ} (work i : ℕ) (row : Fin H → Fin tiles) :
    (pathList tiles work i H).map (fun s => s.eval work row) =
      compilePath tiles work i (List.ofFn row) := by
  have hrow : (List.finRange H).map row = List.ofFn row := by
    simp [List.finRange, List.map_ofFn, Function.comp_def]
  rw [← hrow]
  simp [pathList, compilePath, test, clear, both, List.map_flatMap, List.flatMap_map, Shape.eval,
    Field.eval]

theorem compilePath_eq_ofFn {H tiles : ℕ} (work i : ℕ) (row : Fin H → Fin tiles) :
    compilePath tiles work i (List.ofFn row) =
      List.ofFn (fun j => (pathShape tiles work i H j).eval work row) := by
  calc
    _ = (List.ofFn (pathShape tiles work i H)).map (fun s => s.eval work row) := by
      rw [pathShape_ofFn, pathList_eval]
    _ = _ := List.map_ofFn

def candidate {R H : ℕ} (g : Fin (R * (4 * H + 3))) : Fin R := g.divNat

def offset {R H : ℕ} (g : Fin (R * (4 * H + 3))) : Fin (4 * H + 3) := g.modNat

@[simp] theorem candidate_val {R H : ℕ} (g : Fin (R * (4 * H + 3))) :
    (candidate g).val = g.val / (4 * H + 3) := rfl

@[simp] theorem offset_val {R H : ℕ} (g : Fin (R * (4 * H + 3))) :
    (offset g).val = g.val % (4 * H + 3) := rfl

/-- Address-field selectors depend only on the public sizes, base and gate ordinal. -/
def shapeAt {R H : ℕ} (tiles work first : ℕ) (g : Fin (R * (4 * H + 3))) : Shape H :=
  pathShape tiles work (first + (candidate g).val) H (offset g)

private theorem compilePaths_rows {R tiles : ℕ} (work first : ℕ) (rows : Fin R → List (Fin tiles)) :
    compilePaths tiles work first (List.ofFn rows) =
      (List.ofFn (fun i => compilePath tiles work (first + i.val) (rows i))).flatten := by
  induction R generalizing first with
  | zero => simp [compilePaths]
  | succ R ih =>
    rw [List.ofFn_succ, compilePaths, List.ofFn_succ, List.flatten_cons, ih]
    simp [Fin.val_succ, Nat.add_comm, Nat.add_left_comm]

private theorem pair_parts {R N : ℕ} (i : Fin R) (j : Fin N) (h : i.val * N + j.val < R * N) :
    ((⟨i.val * N + j.val, h⟩ : Fin (R * N)).divNat,
      (⟨i.val * N + j.val, h⟩ : Fin (R * N)).modNat) = (i, j) := by
  have he : (⟨i.val * N + j.val, h⟩ : Fin (R * N)) = finProdFinEquiv (i, j) := by
    apply Fin.ext
    change i.val * N + j.val = j.val + N * i.val
    ac_rfl
  rw [he]
  exact finProdFinEquiv.symm_apply_apply (i, j)

private theorem candidate_mk {R H : ℕ} (i : Fin R) (j : Fin (4 * H + 3))
    (h : i.val * (4 * H + 3) + j.val < R * (4 * H + 3)) :
    candidate (R := R) (H := H) ⟨i.val * (4 * H + 3) + j.val, h⟩ = i :=
  congrArg Prod.fst (pair_parts i j h)

private theorem offset_mk {R H : ℕ} (i : Fin R) (j : Fin (4 * H + 3))
    (h : i.val * (4 * H + 3) + j.val < R * (4 * H + 3)) :
    offset (R := R) (H := H) ⟨i.val * (4 * H + 3) + j.val, h⟩ = j :=
  congrArg Prod.snd (pair_parts i j h)

/-- Evaluating the static fields against each candidate's raw tile IDs gives
every gate of the actual compiled purchase program, in the emitted order. -/
theorem compilePaths_eq_ofFn {R H tiles : ℕ} (work first : ℕ) (rows : Fin R → Fin H → Fin tiles) :
    compilePaths tiles work first (List.ofFn (fun i => List.ofFn (rows i))) =
      List.ofFn (fun g => (shapeAt tiles work first g).eval work (rows (candidate g))) := by
  rw [compilePaths_rows, List.ofFn_mul (fun g => (shapeAt tiles work first g).eval work (rows (candidate g)))]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [compilePath_eq_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [shapeAt, candidate_mk, offset_mk]

/-- The same compiler equation for the candidate and row lists in `finRange.map` order. -/
theorem compilePaths_finRange_map {R H tiles : ℕ} (work first : ℕ)
    (rows : Fin R → Fin H → Fin tiles) :
    compilePaths tiles work first ((List.finRange R).map (fun i => (List.finRange H).map (rows i))) =
      List.ofFn (fun g => (shapeAt tiles work first g).eval work (rows (candidate g))) := by
  simpa only [List.finRange, List.map_ofFn, Function.comp_def] using
    compilePaths_eq_ofFn work first rows

end Hierarchy.ProtocolRAMPurchaseGateShape

end OAI
