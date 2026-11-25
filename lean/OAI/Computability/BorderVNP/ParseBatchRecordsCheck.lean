import OAI.Computability.BorderVNP.ParseBatchRecordsPacked

/-!
# The child requests and local tests of a preorder block

A verifier checks one interval per row. Its one root read and two reads per production can
all be issued simultaneously: no returned value is used to choose the address of another
read. The payload of a read consists only of the layer and grammar state.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseRecords

open VPVNP

variable {V H : Type*} {n : ℕ}

/-- One addressed layer/state check. A missing table row causes rejection. -/
structure ChildRequest (H : Type*) where
  /-- Row index inside this tree's block. -/
  address : ℕ
  /-- Required layer (number of leaves minus one). -/
  layer : ℕ
  /-- Required grammar state. -/
  parent : H

/-- A production at `u` emits its two child reads. A terminal emits none. -/
def childRequests (u : ℕ) : GrammarLabel V H n → List (ChildRequest H)
  | .inl _ => []
  | .inr ⟨d, _, b, i, j⟩ => [⟨u + 1, b.val, i⟩, ⟨u + 2*(b.val+1), d.val-1-b.val, j⟩]

/-- Reads for a consecutive block of records, beginning at the specified address. -/
def requestsFrom (u : ℕ) : List (GrammarLabel V H n) → List (ChildRequest H)
  | [] => []
  | r :: rs => childRequests u r ++ requestsFrom (u+1) rs

/-- The full batch contains the root read followed by the reads for each production. -/
def allRequests (d : Fin n) (h : H) (rs : List (GrammarLabel V H n)) : List (ChildRequest H) :=
  ⟨0, d.val, h⟩ :: requestsFrom 0 rs

/-- Check the returned layer and state, rejecting an out-of-range address. -/
def readOK [DecidableEq H] (table : List (GrammarLabel V H n)) (q : ChildRequest H) : Bool :=
  match table[q.address]? with
  | none => false
  | some r => decide (depth r = q.layer ∧ state r = q.parent)

/-- Read acceptance is precisely the root-at-address predicate. -/
theorem readOK_iff [DecidableEq H] (table : List (GrammarLabel V H n)) (q : ChildRequest H) :
    readOK table q = true ↔ RootAt table q.address q.layer q.parent := by
  unfold readOK RootAt
  cases table[q.address]? <;> simp

/-- An internal-node interval must stay inside the block. The same inequality checks
that a terminal's own address is present. -/
def boundsFrom (size u : ℕ) : List (GrammarLabel V H n) → Bool
  | [] => true
  | r :: rs => decide (u + 2*depth r < size) && boundsFrom size (u+1) rs

/-- The range and padding tests on the raw fields occur in `unpack`; on typed labels
only the length, interval checks and returned child labels remain. -/
def check [DecidableEq H] (d : Fin n) (h : H) (rs : List (GrammarLabel V H n)) : Bool :=
  decide (rs.length = 2*d.val+1) && boundsFrom rs.length 0 rs &&
    (allRequests d h rs).all (readOK rs)

private theorem rowCheck_iff [DecidableEq H] (table : List (GrammarLabel V H n))
    (u : ℕ) (r : GrammarLabel V H n) :
    (u + 2*depth r < table.length ∧ (childRequests u r).all (readOK table) = true) ↔
      Local table u r := by
  rcases r with v | ⟨d, h, b, i, j⟩ <;>
    simp [childRequests, Local, readOK_iff]

private theorem scan_iff [DecidableEq H] (table xs : List (GrammarLabel V H n)) (u : ℕ) :
    (boundsFrom table.length u xs = true ∧ (requestsFrom u xs).all (readOK table) = true) ↔
      ∀ k r, xs[k]? = some r → Local table (u+k) r := by
  induction xs generalizing u with
  | nil => simp [boundsFrom, requestsFrom]
  | cons a xs ih =>
    simp only [boundsFrom, requestsFrom, List.all_append, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨hsize, hrest⟩, hread, htail⟩ k r hr
      cases k with
      | zero =>
        have : a = r := Option.some.inj hr
        subst r
        simpa only [Nat.add_zero] using (rowCheck_iff table u a).mp ⟨hsize, hread⟩
      | succ k =>
        have hl := (ih (u+1)).mp ⟨hrest, htail⟩ k r hr
        simpa only [Nat.add_right_comm u 1 k, Nat.add_assoc] using hl
    · intro hall
      have root := (rowCheck_iff table u a).mpr (by simpa using hall 0 a rfl)
      have tail := (ih (u+1)).mpr fun k r hr => by
        simpa only [Nat.add_right_comm u 1 k, Nat.add_assoc] using hall (k+1) r hr
      exact ⟨⟨root.1, tail.1⟩, root.2, tail.2⟩

/-- The executable simultaneous verifier recognizes exactly the valid preorder blocks. -/
theorem check_iff_valid [DecidableEq H] (d : Fin n) (h : H) (rs : List (GrammarLabel V H n)) :
    check d h rs = true ↔ Valid d h rs := by
  simp only [check, allRequests, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, readOK_iff,
    Valid]
  have hi := scan_iff rs rs 0
  simp only [Nat.zero_add] at hi
  exact ⟨fun ⟨⟨hlen, hbounds⟩, hroot, hreads⟩ =>
    ⟨hlen, hroot, hi.mp ⟨hbounds, hreads⟩⟩, fun ⟨hlen, hroot, hvalid⟩ =>
    ⟨⟨hlen, (hi.mpr hvalid).1⟩, hroot, (hi.mpr hvalid).2⟩⟩

/-- Every production emits exactly two child addresses, and hence the whole batch has
at most two reads per input record. -/
theorem requestsFrom_length_le (u : ℕ) (rs : List (GrammarLabel V H n)) :
    (requestsFrom u rs).length ≤ 2*rs.length := by
  induction rs generalizing u with
  | nil => simp [requestsFrom]
  | cons r rs ih =>
    have h := ih (u+1)
    rcases r with t | ⟨d, h, b, i, j⟩ <;> simp [requestsFrom, childRequests] <;> omega

/-- The root and all child reads together use at most `1+2r` requests on an `r`-row block. -/
theorem allRequests_length_le (d : Fin n) (h : H) (rs : List (GrammarLabel V H n)) :
    (allRequests d h rs).length ≤ 1 + 2*rs.length := by
  have := requestsFrom_length_le 0 rs
  simp only [allRequests, List.length_cons]
  omega

/-- All computed child addresses fit below `4n` when the current row is within a
`2n-1`-row block. This also bounds addresses from malformed guesses prior to lookup. -/
theorem child_address_lt (r : GrammarLabel V H n) {u : ℕ} (hu : u < 2*n-1)
    {q : ChildRequest H} (hq : q ∈ childRequests u r) : q.address < 4*n := by
  rcases r with t | ⟨d, h, b, i, j⟩
  · simp [childRequests] at hq
  · simp only [childRequests, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> dsimp <;> have := d.isLt <;> have := b.isLt <;> omega

end ParseRecords

end BorderVNP
end Computability
end OAI
