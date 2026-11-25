import OAI.Computability.BorderVNP.ParseBatchLookup
import OAI.Computability.BorderVNP.ParseBatchSortBounds

/-!
# Joining the Boolean sort to the simultaneous table-read checks

The tag and address are obtained from the sorted binary word itself. The
arbitrary low-order suffix can store a request identifier and proposed data.
All table rows and all requests, with their multiplicities, are carried by the sort.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchLookup

open VPVNP.VerifierNetwork BorderVNP.ParseBatchSort

/-- Decode the sort key of an actual row. The payload is any selected group of
bits, so a caller may also reserve an identifier in the low field. -/
def fromWord {α : Type*} {w : ℕ} (low : ℕ) (get : (Fin w → Bool) → α)
    (x : Fin w → Bool) : Row α where
  address := value x / 2^low / 2
  request := decide (value x / 2^low % 2 = 1)
  payload := get x

/-- Extracting the combined address/tag key drops the low bits. -/
theorem key_fromWord {α : Type*} {w : ℕ} (low : ℕ) (get : (Fin w → Bool) → α)
    (x : Fin w → Bool) : (fromWord low get x).key = value x / 2 ^ low := by
  unfold fromWord Row.key
  let k := value x / 2 ^ low
  change 2*(k/2) + (decide (k % 2 = 1)).toNat = k
  by_cases hk : k%2 = 1 <;> simp [hk] <;> omega

/-- The address and request flag of a packed record decode without consulting its suffix. -/
theorem fromWord_bits {α : Type*} {a w : ℕ} (get : (Fin ((w + 1) + a) → Bool) → α)
    (address : Fin a → Bool) (request : Bool) (tail : Fin w → Bool) :
    fromWord w get (bits address request tail) =
      ⟨value address, request, get (bits address request tail)⟩ := by
  unfold fromWord
  rw [bits_key]
  cases request <;> simp
  omega

/-- Local comparisons on the outputs of the actual Boolean DAG accept precisely
the true answers on its original table and request ports. A failed read is rejected
on every internal assignment. -/
theorem checks_after_sort_iff {α σ : Type*} [Fintype σ] {b w : ℕ} (f : Frame σ (Pins b w))
    (x : σ → Bool) (low : ℕ) (get : (Fin w → Bool) → α) (table : ℕ → Option α)
    (ht : TableSpec table (fun i => fromWord low get (fun k => f.eval x (i,k)))) :
    Adjacent (fun i => fromWord low get (fun k => (phases b le_rfl f).eval x (i,k))) ↔
      ∀ i, table (fromWord low get (fun k => f.eval x (i,k))).address =
        some (get (fun k => f.eval x (i,k))) := by
  let before := fun i : Fin (2^b) => fun k => f.eval x (i,k)
  let after := fun i : Fin (2^b) => fun k => (phases b le_rfl f).eval x (i,k)
  have perm : (List.ofFn after).Perm (List.ofFn before) := phases_perm f x
  have forward (i) : ∃ j, after i = before j := by
    have hi : after i ∈ List.ofFn after := List.mem_ofFn.mpr ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp (perm.mem_iff.mp hi)
    exact ⟨j,hj.symm⟩
  have backward (i) : ∃ j, before i = after j := by
    have hi : before i ∈ List.ofFn before := List.mem_ofFn.mpr ⟨i,rfl⟩
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp (perm.mem_iff.mpr hi)
    exact ⟨j,hj.symm⟩
  have htable : TableSpec table (fun i => fromWord low get (after i)) := by
    constructor
    · intro i
      obtain ⟨j,hj⟩ := forward i
      dsimp only
      rw [hj]
      exact ht.1 j
    · intro a v hv
      obtain ⟨i,hi,ha⟩ := ht.2 a v hv
      obtain ⟨j,hj⟩ := backward i
      refine ⟨j, ?_⟩
      dsimp only
      rw [← hj]
      exact ⟨hi,ha⟩
  have hs : Monotone (fun i => (fromWord low get (after i)).key) := by
    intro i j hij
    change (fromWord low get (after i)).key ≤ (fromWord low get (after j)).key
    rw [key_fromWord, key_fromWord]
    exact Nat.div_le_div_right (phases_monotone f x hij)
  rw [adjacent_iff table _ htable hs]
  constructor
  · intro h i
    obtain ⟨j,hj⟩ := backward i
    change table (fromWord low get (before i)).address = some (get (before i))
    rw [hj]
    exact h j
  · intro h i
    obtain ⟨j,hj⟩ := forward i
    change table (fromWord low get (after i)).address = some (get (after i))
    rw [hj]
    exact h j

end ParseBatchLookup

end BorderVNP
end Computability
end OAI
