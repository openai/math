import OAI.Computability.VPVNP.RAMBoundary
import OAI.Computability.VPVNP.RAMValidatorBoundaryWord

/-!
# A single pass over the local sorted RAM block

The predecessor register starts at the received last record. At each physical
slot the validator checks a possible read, latches the status, and replaces
the predecessor even if the current slot is padding. At the end it compares
this register with the outgoing field on sites that have a successor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMBoundary

open RAMMemory BurstRAM

variable {B S w : ℕ} {α β V : Type*}

private def finish (equal : α → α → Bool × ℕ) (expected : Option α) (previous : α)
    (ok : Bool) (work : ℕ) : Bool × ℕ :=
  match expected with
  | none => (ok, work + 3)
  | some sent =>
    let checked := equal sent previous
    (ok && checked.1, work + checked.2 + 4)

/-- The address argument counts the slots *after* the next slot, decreasing
from `B - 1` to zero. The physical offset is its reversal in `Fin B`. This
passes a constant-size index into a fixed buffer on each iteration. -/
private def loop (read equal : α → α → Bool × ℕ) (expected : Option α) (get : Fin B → α) :
    (k : ℕ) → k ≤ B → α → Bool → ℕ → Bool × ℕ
  | 0, _, previous, ok, work => finish equal expected previous ok work
  | k + 1, hk, previous, ok, work =>
    let current := get ⟨k, hk⟩
    let checked := read previous current
    -- Offset subtraction, record loads and register copies, status and loop control.
    loop read equal expected get k (by omega) current (ok && checked.1) (work + checked.2 + 16)

private def remaining (get : Fin B → α) (k : ℕ) (hk : k ≤ B) : List α :=
  List.ofFn fun i : Fin k ↦ get (i.rev.castLE hk)

private theorem remaining_succ (get : Fin B → α) (k : ℕ) (hk : k+1 ≤ B) :
    remaining get (k+1) hk = get ⟨k, hk⟩ :: remaining get k (by omega) := by
  rw [remaining, List.ofFn_succ, Fin.rev_zero]
  simp only [remaining, Fin.rev_succ]
  rfl

private theorem remaining_full (block : Fin B → α) :
    remaining (fun i ↦ block i.rev) B le_rfl = List.ofFn block := by
  simp [remaining]

private theorem loop_spec [Zero V]
    (read equal : Option (Record V) → Option (Record V) → Bool × ℕ)
    (hr : ∀ p c, (read p c).1 = true ↔ ∀ r ∈ c, r.kind = .read → r.value = previousValue p r.address)
    (he : ∀ a b, (equal a b).1 = true ↔ a = b)
    (expected : Option (Option (Record V))) (get : Fin B → Option (Record V))
    (k : ℕ) (hk : k ≤ B) (previous : Option (Record V)) (ok : Bool) (work : ℕ) :
    (loop read equal expected get k hk previous ok work).1 = true ↔
      ok = true ∧ PaddedCheck previous (remaining get k hk) ∧
        ∀ x ∈ expected, x = (remaining get k hk).getLast?.getD previous := by
  induction k generalizing previous ok work with
  | zero =>
    cases expected <;> simp [loop, finish, remaining, PaddedCheck, he]
  | succ k ih =>
    rw [loop, ih, remaining_succ, List.getLast?_cons, Option.getD_some, Bool.and_eq_true, hr]
    cases hc : get ⟨k, hk⟩ <;> simp [PaddedCheck, and_assoc]

private theorem loop_cost (read equal : α → α → Bool × ℕ)
    (hr : ∀ p c, (read p c).2 ≤ 48) (he : ∀ a b, (equal a b).2 ≤ 60)
    (expected : Option α) (get : Fin B → α) (k : ℕ) (hk : k ≤ B)
    (previous : α) (ok : Bool) (work : ℕ) :
    (loop read equal expected get k hk previous ok work).2 ≤ work + 64 * k + 64 := by
  induction k generalizing previous ok work with
  | zero =>
    cases expected with
    | none => simp [loop, finish]
    | some s =>
      simp only [loop, finish, Nat.mul_zero, Nat.add_zero]
      have := he s previous
      omega
  | succ k ih =>
    rw [loop]
    have := hr previous (get ⟨k, hk⟩)
    exact (ih (by omega) _ _ _).trans (by omega)

private theorem loop_map (f : α → β) (read equal : α → α → Bool × ℕ)
    (read' equal' : β → β → Bool × ℕ) (hr : ∀ p c, read p c = read' (f p) (f c))
    (he : ∀ a b, equal a b = equal' (f a) (f b))
    (expected : Option α) (get : Fin B → α) (k : ℕ) (hk : k ≤ B)
    (previous : α) (ok : Bool) (work : ℕ) :
    loop read equal expected get k hk previous ok work =
      loop read' equal' (expected.map f) (fun i ↦ f (get i)) k hk (f previous) ok work := by
  induction k generalizing previous ok work with
  | zero => cases expected <;> simp [loop, finish, he]
  | succ k ih => simp only [loop, hr, ih]

/-- The loop counter is decremented by one in the machine word type. -/
private def decrement (hw : 2 ≤ w) (counter : Word w) : Word w :=
  let one : Word w := ⟨1, by have := Nat.pow_le_pow_right (by decide : 0 < 2) hw; omega⟩
  counter - one

private theorem decrement_val (hw : 2 ≤ w) (counter : Word w) (hn : counter.val ≠ 0) :
    (decrement hw counter).val = counter.val - 1 :=
  Fin.sub_val_of_le (by change 1 ≤ counter.val; omega)

/-- Machine-word offset of the next record in the allocated local array. -/
private def wordOffset (width counter : Word w) (hc : counter ≤ width) (hn : counter.val ≠ 0) :
    Fin width.val :=
  ⟨(width - counter).val, by rw [Fin.sub_val_of_le hc]; change counter.val ≤ width.val at hc; omega⟩

private theorem wordOffset_val (width counter : Word w) (hc : counter ≤ width) (hn : counter.val ≠ 0) :
    (wordOffset width counter hc hn).val = width.val - counter.val := Fin.sub_val_of_le hc

/-- An executable loop over a materialized array. The counter, the decrement,
and the subtraction that produces the next array offset use the machine word
type. Loop termination follows from the counter value. -/
private def wordLoop (hw : 2 ≤ w) (read equal : α → α → Bool × ℕ) (expected : Option α)
    (buffer : Array α) (width : Word w) (hwidth : width.val = buffer.size)
    (counter : Word w) (hc : counter ≤ width) (previous : α) (ok : Bool) (work : ℕ) : Bool × ℕ :=
  if hz : counter.val = 0 then finish equal expected previous ok work else
    let offset := wordOffset width counter hc hz
    let current := buffer[offset.val]'(hwidth ▸ offset.isLt)
    let checked := read previous current
    wordLoop hw read equal expected buffer width hwidth (decrement hw counter)
      (by change (decrement hw counter).val ≤ width.val; rw [decrement_val _ _ hz]
          exact (Nat.sub_le ..).trans hc) current (ok && checked.1) (work + checked.2 + 16)
termination_by counter.val
decreasing_by rw [decrement_val _ _ hz]; omega

private theorem wordLoop_eq (hw : 2 ≤ w) (read equal : α → α → Bool × ℕ) (expected : Option α)
    (buffer : Array α) (width : Word w) (hwidth : width.val = buffer.size)
    (k : ℕ) (hk : k ≤ buffer.size) (counter : Word w) (hc : counter ≤ width) (hcount : counter.val = k)
    (previous : α) (ok : Bool) (work : ℕ) :
    wordLoop hw read equal expected buffer width hwidth counter hc previous ok work =
      loop read equal expected (fun i : Fin buffer.size ↦ buffer[i.rev.val]) k hk previous ok work := by
  induction k generalizing counter previous ok work with
  | zero => rw [wordLoop, dite_eq_left hcount, loop]
  | succ k ih =>
    have hn : counter.val ≠ 0 := by omega
    rw [wordLoop, dite_eq_right hn, loop]
    have hn' : (decrement hw counter).val = k := by rw [decrement_val _ _ hn]; omega
    have hoff : (wordOffset width counter hc hn).val = (⟨k, hk⟩ : Fin buffer.size).rev.val := by
      rw [wordOffset_val, Fin.val_rev, hwidth, hcount]
    simp only [hoff]
    exact ih _ _ _ hn' _ _ _

/-- Scan the site's sorted slots in increasing order. The second argument is
absent at the final site. A present field can itself contain padding. -/
def scan (previous : Slot w) (expected : Option (Slot w)) (block : Fin B → Slot w) : Bool × ℕ :=
  loop readOK equalSlot expected (fun i ↦ block i.rev) B le_rfl previous true 0

/-- The status for independently supplied incoming and outgoing fields. -/
theorem scan_ok_iff (hB : 0 < B) (previous : Slot w) (expected : Option (Slot w))
    (block : Fin B → Slot w) :
    (scan previous expected block).1 = true ↔
      PaddedCheck previous (List.ofFn block) ∧ ∀ x ∈ expected, x = lastSlot hB block := by
  have hlast : (List.ofFn block).getLast? = some (lastSlot hB block) := by
    rw [List.getLast?_eq_some_getLast (mt List.ofFn_eq_nil_iff.mp (Nat.ne_of_gt hB)), List.getLast_ofFn]
    rfl
  simpa only [scan, remaining_full, hlast, Option.getD_some, true_and] using
    loop_spec readOK equalSlot readOK_spec equalSlot_spec expected (fun i ↦ block i.rev) B
      le_rfl previous true 0

/-- The counted local scan implements the boundary predicate of Lemma 10.1
on all message and record assignments. -/
theorem scan_spec (hB : 0 < B) (sent : Sends S (Word w)) (v : Fin S) (block : Fin B → Slot w) :
    (scan (receive sent v) (if v.val + 1 < S then some (outgoing sent v) else none) block).1 = true ↔
      checkAt hB sent v block := by
  rw [scan_ok_iff hB]
  by_cases hv : v.val + 1 < S <;> simp [checkAt, hv]

/-- Every slot is visited once, including slots after a failing read check. -/
theorem scan_cost (previous : Slot w) (expected : Option (Slot w)) (block : Fin B → Slot w) :
    (scan previous expected block).2 ≤ 64 * B + 64 := by
  simpa only [scan, Nat.zero_add] using
    loop_cost readOK equalSlot (fun p c ↦ (readOK_cost p c).trans (by decide))
      (fun a b ↦ (equalSlot_cost a b).trans (by decide)) expected (fun i ↦ block i.rev) B
      le_rfl previous true 0

/-- The five fields of a physical slot occupy a fixed-size array. -/
abbrev WordTuple (w : ℕ) := Vector (Word w) 5

/-- Execute the same pass directly on a finite array of five-word tuples.
The bound on the buffer length is the representability of the initial word
counter. Every subsequent counter and offset fits by construction. -/
def scanWords (hw : 2 ≤ w) (previous : WordTuple w) (expected : Option (WordTuple w))
    (buffer : Array (WordTuple w)) (hfit : buffer.size < 2 ^ w) : Bool × ℕ :=
  let width : Word w := ⟨buffer.size, hfit⟩
  wordLoop hw (fun p c ↦ readRaw hw p.get c.get) (fun a b ↦ equalRaw hw a.get b.get)
    expected buffer width rfl width le_rfl previous true 0

/-- Both decision and work agree with the parsed-slot scan. Unknown tags and
noncanonical payloads are included, with the parser's interpretation of each
tuple. Canonicality is enforced when loading shared messages. -/
theorem scanWords_eq (hw : 2 ≤ w) (previous : WordTuple w) (expected : Option (WordTuple w))
    (buffer : Array (WordTuple w)) (hfit : buffer.size < 2 ^ w) :
    let parse := fun r : WordTuple w ↦ (RAMSort.parsedSlot hw r.get).record
    scanWords hw previous expected buffer hfit =
      scan (parse previous) (expected.map parse) (fun i : Fin buffer.size ↦ parse buffer[i.val]) := by
  let width : Word w := ⟨buffer.size, hfit⟩
  let read := fun p c : WordTuple w ↦ readRaw hw p.get c.get
  let equal := fun a b : WordTuple w ↦ equalRaw hw a.get b.get
  exact (wordLoop_eq hw read equal expected buffer width rfl buffer.size
    le_rfl width le_rfl rfl previous true 0).trans
    (loop_map (fun r : WordTuple w ↦ (RAMSort.parsedSlot hw r.get).record) read equal readOK
      equalSlot (fun p c ↦ readRaw_eq hw p.get c.get) (fun a b ↦ equalRaw_eq hw a.get b.get)
      expected (fun i : Fin buffer.size ↦ buffer[i.rev.val]) buffer.size le_rfl previous true 0)

theorem scanWords_cost (hw : 2 ≤ w) (previous : WordTuple w) (expected : Option (WordTuple w))
    (buffer : Array (WordTuple w)) (hfit : buffer.size < 2 ^ w) :
    (scanWords hw previous expected buffer hfit).2 ≤ 64 * buffer.size + 64 := by
  rw [scanWords_eq]
  exact scan_cost ..

end RAMBoundary

end VPVNP
end Computability
end OAI
