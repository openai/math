import OAI.Computability.BorderVNP.ParseBatchSort

/-!
# Simultaneous addressed reads in Lemma 2.3

Each read proposes its answer before sorting. The table row comes first on
ties of the address. Comparing adjacent records therefore forces every proposed
answer, even if many requests read the same address. A request for an absent
address fails. The answers are already attached to the original request ports.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchLookup

open BorderVNP.ParseBatchSort

/-- A table row or a request, carrying an address and its value. -/
structure Row (α : Type*) where
  /-- The table address used by the row. -/
  address : ℕ
  /-- Table rows have the zero tag and requests have the one tag. -/
  request : Bool
  /-- Supplied table data or a proposed read result. -/
  payload : α

/-- Address-major sorting puts a table row before all reads of its address. -/
def Row.key {α : Type*} (r : Row α) : ℕ := 2 * r.address + r.request.toNat

/-- All table entries are present, and the provided table rows have their true values. -/
def TableSpec {k : ℕ} {α : Type*} (table : ℕ → Option α) (rows : Fin k → Row α) : Prop :=
  (∀ i, (rows i).request = false → table (rows i).address = some (rows i).payload) ∧
  (∀ a v, table a = some v → ∃ i, (rows i).request = false ∧ (rows i).address = a)

/-- A read must immediately follow a row of the same address and value. This local check
also excludes a first-position request, since that position has no predecessor. -/
def Adjacent {k : ℕ} {α : Type*} (rows : Fin k → Row α) : Prop :=
  ∀ i, (rows i).request = true → ∃ j : Fin k, j.val + 1 = i.val ∧
    (rows j).address = (rows i).address ∧ (rows j).payload = (rows i).payload

private theorem address_mono {k : ℕ} {α : Type*} {rows : Fin k → Row α}
    (hs : Monotone (fun i => (rows i).key)) : Monotone (fun i => (rows i).address) := by
  intro i j hij
  change (rows i).address ≤ (rows j).address
  have h := hs hij
  cases ha : (rows i).request <;> cases hb : (rows j).request <;>
    simp only [Row.key, ha, hb, Bool.toNat_true, Bool.toNat_false] at h <;> omega

/-- The adjacent checks accept exactly the true values of all simultaneous reads.
No injectivity of the requested addresses is required. -/
theorem adjacent_iff {k : ℕ} {α : Type*} (table : ℕ → Option α) (rows : Fin k → Row α)
    (ht : TableSpec table rows) (hs : Monotone (fun i => (rows i).key)) :
    Adjacent rows ↔ ∀ i, table (rows i).address = some (rows i).payload := by
  constructor
  · intro h i
    generalize he : i.val = n
    induction n using Nat.strong_induction_on generalizing i with
    | h n ih =>
      cases hr : (rows i).request with
      | false => exact ht.1 i hr
      | true =>
        obtain ⟨j, hj, ha, hv⟩ := h i hr
        rw [← ha, ← hv]
        exact ih j.val (by omega) j rfl
  · intro h i hi
    obtain ⟨j, hj, ha⟩ := ht.2 _ _ (h i)
    have hji : j < i := by
      by_contra! hn
      have hh := hs hn
      simp only [Row.key, hi, hj, ha, Bool.toNat_true, Bool.toNat_false] at hh
      omega
    let prev : Fin k := ⟨i.val - 1, by have := i.isLt; omega⟩
    have hjprev : j ≤ prev := by change j.val ≤ i.val - 1; change j.val < i.val at hji; omega
    have hprevi : prev ≤ i := by change i.val - 1 ≤ i.val; omega
    have hp : (rows prev).address = (rows i).address := le_antisymm (address_mono hs hprevi)
      (ha ▸ address_mono hs hjprev)
    refine ⟨prev, ?_, hp, Option.some.inj ?_⟩
    · change i.val - 1 + 1 = i.val
      change j.val < i.val at hji
      omega
    · rw [← h prev, ← h i, hp]

/-- Concatenate high bits with a lower field. The width is written with the lower field
first in the addition so that recursion exposes the high bits in order. -/
def prepend {α : Type*} {w : ℕ} : {a : ℕ} → (Fin a → α) → (Fin w → α) → Fin (w + a) → α
  | 0, _, tail => tail
  | _ + 1, head, tail => Fin.cons (head 0) (prepend (fun i => head i.succ) tail)

/-- The numeric sort key of concatenated fields has the high field in the high bits. -/
theorem value_prepend {a w : ℕ} (head : Fin a → Bool) (tail : Fin w → Bool) :
    value (prepend head tail) = value head * 2 ^ w + value tail := by
  induction a with
  | zero => simp [prepend, value]
  | succ a ih =>
    simp only [prepend, value, Fin.cons_zero, Fin.cons_succ]
    change (head 0).toNat * 2 ^ (w + a) + value (prepend (fun i => head i.succ) tail) = _
    rw [ih, pow_add]
    ring

/-- An address, followed by its table/read tag and then an arbitrary payload, forms a
binary sort key. Low fields can also include a request number or fixed padding. -/
def bits {α : Type*} {a w : ℕ} (address : Fin a → α) (request : α) (tail : Fin w → α) :
    Fin ((w + 1) + a) → α := prepend address (Fin.cons request tail)

/-- The numeric address/tag key is recovered by discarding exactly the low field. -/
theorem bits_key {a w : ℕ} (address : Fin a → Bool) (request : Bool) (tail : Fin w → Bool) :
    value (bits address request tail) / 2 ^ w = 2 * value address + request.toNat := by
  have hval : value (bits address request tail) =
      value tail + (2 * value address + request.toNat) * 2 ^ w := by
    rw [bits, value_prepend]
    simp only [value, Fin.cons_zero, Fin.cons_succ, pow_succ]
    ring
  rw [hval, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt (value_lt _), zero_add]

/-- Sorting the complete binary keys orders the address and tag even when lower
fields break ties. -/
theorem keys_mono_of_bits {k a w : ℕ} (address : Fin k → Fin a → Bool)
    (request : Fin k → Bool) (tail : Fin k → Fin w → Bool)
    (h : Monotone (fun i => value (bits (address i) (request i) (tail i)))) :
    Monotone (fun i => 2 * value (address i) + (request i).toNat) := by
  intro i j hij
  dsimp only
  rw [← bits_key (address i) (request i) (tail i), ← bits_key (address j) (request j) (tail j)]
  exact Nat.div_le_div_right (h hij)

end ParseBatchLookup

end BorderVNP
end Computability
end OAI
