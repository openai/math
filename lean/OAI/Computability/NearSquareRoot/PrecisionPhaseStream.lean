import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Forall2

/-!
# Prefix streams for tensor-product phase tables

At each pass the outer loop reads prefixes and the inner loop scans a local
coefficient table. These definitions keep the emitted records in tape order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseStream

variable {α β : Type*}

/-- One left-to-right scan of the table for each previous prefix. -/
def extend (step : β → α → β) (prefixes : List β) (table : List α) : List β :=
  prefixes.flatMap fun p => table.map (step p)

/-- All successive prefix tapes, including the seed tape. -/
def streams (step : β → α → β) (prefixes : List β) : List (List α) → List (List β)
  | [] => [prefixes]
  | table :: rest => prefixes :: streams step (extend step prefixes table) rest

/-- Independent address enumeration with the most significant block first. -/
def addresses : List (List α) → List (List α)
  | [] => [[]]
  | table :: rest => table.flatMap fun x => (addresses rest).map (x :: ·)

/-- Address membership is the independent choice of one entry from each block. -/
theorem mem_addresses {tables : List (List α)} {xs : List α} :
    xs ∈ addresses tables ↔ List.Forall₂ (· ∈ ·) xs tables := by
  induction tables generalizing xs with
  | nil => cases xs <;> simp [addresses]
  | cons tab rest ih =>
    simp only [addresses, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨x, hx, ys, hys, rfl⟩
      exact .cons hx (ih.mp hys)
    · intro h
      cases h with
      | cons hx hxs => exact ⟨_, hx, _, ih.mpr hxs, rfl⟩

theorem length_of_mem_addresses {tables : List (List α)} {xs : List α}
    (h : xs ∈ addresses tables) : xs.length = tables.length :=
  (mem_addresses.mp h).length_eq

theorem forall_of_mem_addresses {tables : List (List α)} {xs : List α} {P : α → Prop}
    (h : xs ∈ addresses tables) (hP : ∀ tab ∈ tables, ∀ x ∈ tab, P x) : ∀ x ∈ xs, P x := by
  have hs := mem_addresses.mp h
  clear h
  induction hs with
  | nil => simp
  | @cons x tab xs tabs hmem _ ih =>
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hP tab (by simp) _ hmem
    · exact ih (fun t ht => hP t (by simp [ht])) y hy

/-- Folding the prefix-expansion passes gives one left-associated product per
lexicographically enumerated address. The operation may include rounding. -/
theorem foldl_extend (step : β → α → β) (prefixes : List β) (tables : List (List α)) :
    tables.foldl (extend step) prefixes =
      prefixes.flatMap fun p => (addresses tables).map (fun xs => xs.foldl step p) := by
  induction tables generalizing prefixes with
  | nil => simp [addresses]
  | cons tab rest ih =>
    simp only [List.foldl_cons, ih, extend, addresses, List.flatMap_assoc,
      List.flatMap_map, List.map_flatMap, List.map_map, Function.comp_def, List.foldl_cons]

/-- In exact arithmetic the record at an address is its ordered phase product. -/
theorem phaseProducts [Monoid α] (tables : List (List α)) :
    tables.foldl (extend (· * ·)) [1] = (addresses tables).map List.prod := by
  rw [foldl_extend]
  simp [List.prod_eq_foldl]

@[simp] theorem length_extend (step : β → α → β) (prefixes : List β) (table : List α) :
    (extend step prefixes table).length = prefixes.length * table.length := by
  induction prefixes with
  | nil => simp [extend]
  | cons p ps ih =>
    simp [extend, Nat.succ_mul, Nat.add_comm] at ih ⊢

theorem final_length (step : β → α → β) (prefixes : List β) (tables : List (List α)) :
    (tables.foldl (extend step) prefixes).length = prefixes.length * (tables.map List.length).prod := by
  induction tables generalizing prefixes with
  | nil => simp
  | cons tab tables ih => simp [ih, Nat.mul_assoc]

/-- The initial tape and every pass together use at most `2N - 1` emitted
records from a singleton seed, where `N` is the final record count. -/
theorem total_records (step : β → α → β) (prefixes : List β) (tables : List (List α))
    (h : ∀ tab ∈ tables, 2 ≤ tab.length) :
    ((streams step prefixes tables).map List.length).sum + prefixes.length ≤
      2 * (tables.foldl (extend step) prefixes).length := by
  induction tables generalizing prefixes with
  | nil => simp [streams, Nat.two_mul]
  | cons tab rest ih =>
    have htab := h tab (by simp)
    have hrest := ih (extend step prefixes tab) (fun t ht => h t (by simp [ht]))
    have hdouble : prefixes.length * 2 ≤ prefixes.length * tab.length :=
      Nat.mul_le_mul_left _ htab
    simp only [length_extend] at hrest
    simp only [streams, List.map_cons, List.sum_cons, List.foldl_cons]
    omega

end PhaseStream

end NearSquareRoot
end Computability
end OAI
