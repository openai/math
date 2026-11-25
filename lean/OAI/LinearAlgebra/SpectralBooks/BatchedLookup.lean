import Mathlib.Data.List.Sort

namespace OAI
/-! # Simultaneous lookup by merging sorted table and request records

Table rows precede requests at an equal address. A left-to-right scan retains the last table
row and returns a tagged answer for each request, including a missing-address marker.
-/

namespace LinearAlgebra.SpectralBooks

inductive LookupRecord (V T : Type*) where
  | row (address : ℕ) (value : V)
  | request (address : ℕ) (tag : T)

namespace LookupRecord

variable {V T : Type*}

def address : LookupRecord V T → ℕ
  | .row k _ | .request k _ => k

/-- Doubling the address leaves one low-order bit for the table-before-request tie break. -/
def key : LookupRecord V T → ℕ
  | .row k _ => 2*k
  | .request k _ => 2*k+1

private def read (buffer : Option (ℕ × V)) (k : ℕ) : Option V :=
  buffer.bind fun p ↦ if p.1 = k then some p.2 else none

/-- One equality test and one tagged read per request; one buffer update per table row. -/
def scan (buffer : Option (ℕ × V)) : List (LookupRecord V T) → List (T × Option V)
  | [] => []
  | .row k v :: tail => scan (some (k,v)) tail
  | .request k t :: tail => (t, read buffer k) :: scan buffer tail

/-- Request results given direct access to the table. -/
def answers (table : ℕ → Option V) : List (LookupRecord V T) → List (T × Option V)
  | [] => []
  | .row _ _ :: tail => answers table tail
  | .request k t :: tail => (t,table k) :: answers table tail

private theorem le_address_of_key_le {a b : LookupRecord V T} (h : key a ≤ key b) :
    address a ≤ address b := by cases a <;> cases b <;> simp_all [key, address] <;> omega

private theorem scan_eq_answers (table : ℕ → Option V) (records : List (LookupRecord V T))
    (sorted : records.Pairwise (fun a b ↦ key a ≤ key b)) (buffer : Option (ℕ × V))
    (buf_ok : ∀ k v, buffer = some (k,v) → table k = some v)
    (buf_le : ∀ k v, buffer = some (k,v) → ∀ a ∈ records, k ≤ a.address)
    (rows : ∀ k v, row k v ∈ records → table k = some v)
    (covers : ∀ k t v, request k t ∈ records → table k = some v →
      row k v ∈ records ∨ buffer = some (k,v)) :
    scan buffer records = answers table records := by
  induction records generalizing buffer with
  | nil => rfl
  | cons a tail ih =>
    obtain ⟨hle, hs⟩ := List.pairwise_cons.mp sorted
    have hrows k v (h : row k v ∈ tail) := rows k v (List.mem_cons_of_mem a h)
    cases a with
    | row k v =>
      refine ih hs (some (k,v)) ?_ ?_ hrows ?_
      · rintro k' v' h
        cases h
        exact rows k v (by simp)
      · rintro k' v' h a ha
        cases h
        exact le_address_of_key_le (hle a ha)
      · intro k' t v' hr hv'
        rcases covers k' t v' (List.mem_cons_of_mem _ hr) hv' with source | old
        · rcases List.mem_cons.mp source with head | ht
          · cases head; exact Or.inr rfl
          · exact Or.inl ht
        · have hk₁ := buf_le _ _ old (.row k v) (by simp)
          have hk₂ := le_address_of_key_le (hle _ hr)
          change k' ≤ k at hk₁
          change k ≤ k' at hk₂
          obtain rfl : k' = k := le_antisymm hk₁ hk₂
          have hv := rows k' v (by simp)
          obtain rfl : v' = v := Option.some.inj (hv'.symm.trans hv)
          exact Or.inr rfl
    | request k t =>
      have hread : read buffer k = table k := by
        cases hval : table k with
        | none =>
          cases hbuf : buffer with
          | none => rfl
          | some p =>
            rcases p with ⟨i,v⟩
            have hne : i ≠ k := by
              rintro rfl
              simpa [hval] using buf_ok _ _ hbuf
            simp [read, hne]
        | some w =>
          rcases covers k t w (by simp) hval with source | old
          · have hin : row k w ∈ tail := List.mem_cons.mp source |>.resolve_left (by simp)
            have := hle _ hin
            simp only [key] at this
            omega
          · simp [read, old]
      simp only [scan, answers, hread, List.cons.injEq, true_and]
      refine ih hs buffer buf_ok ?_ hrows ?_
      · intro k' v' h a ha
        exact buf_le _ _ h a (List.mem_cons_of_mem _ ha)
      · intro k' t' w hr hw
        rcases covers k' t' w (List.mem_cons_of_mem _ hr) hw with h | h
        · exact Or.inl ((List.mem_cons.mp h).resolve_left (by simp))
        · exact Or.inr h

/-- A sorted batch with one correct row for each requested defined address resolves all
queries. Absent addresses give `none`, and arbitrary tags are retained for the final sort. -/
theorem scan_sorted (table : ℕ → Option V) (records : List (LookupRecord V T))
    (sorted : records.Pairwise (fun a b ↦ key a ≤ key b))
    (rows : ∀ k v, row k v ∈ records → table k = some v)
    (covers : ∀ k t v, request k t ∈ records → table k = some v → row k v ∈ records) :
    scan none records = answers table records :=
  scan_eq_answers table records sorted none (by simp) (by simp) rows
    (fun k t v hr hv ↦ Or.inl (covers k t v hr hv))

private theorem answers_perm (table : ℕ → Option V) {a b : List (LookupRecord V T)}
    (h : a.Perm b) : (answers table a).Perm (answers table b) := by
  induction h with
  | nil => exact .nil
  | cons x _ ih =>
    cases x with
    | row => exact ih
    | request k t => exact ih.cons (t, table k)
  | swap x y l => cases x <;> cases y <;> simp [answers, List.Perm.swap]
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

/-- A sorter may use arbitrary tie-breaking inside a run. After scanning its output, the
tagged answers form exactly the multiset of original request results. -/
theorem scan_sorted_perm (table : ℕ → Option V) {input sorted : List (LookupRecord V T)}
    (permutation : sorted.Perm input) (ordered : sorted.Pairwise (fun a b ↦ key a ≤ key b))
    (rows : ∀ k v, row k v ∈ input → table k = some v)
    (covers : ∀ k t v, request k t ∈ input → table k = some v → row k v ∈ input) :
    (scan none sorted).Perm (answers table input) := by
  rw [scan_sorted table sorted ordered (fun k v hr ↦ rows _ _ (permutation.mem_iff.mp hr))
    (fun k t v hr hv ↦ permutation.mem_iff.mpr (covers k t v (permutation.mem_iff.mp hr) hv))]
  exact answers_perm table permutation

end LookupRecord
end LinearAlgebra.SpectralBooks

end OAI
