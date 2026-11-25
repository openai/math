import OAI.Computability.IntegerMultiplication.Code.Decompose
import OAI.Computability.NearSquareRoot.ShortWordCall
import Mathlib.Tactic.Ring

/-!
# Aligning the address slots of a binary template

The arity is fixed before compiling the P192 stack program. Each slot is a
delimited stream, and all slots have the same variable length. Successive
zippers turn these streams into a single stream of columns. The programs
also run in reverse and leave parked stack data untouched.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelSelectorAlign

open IntegerMultiplication.Code

/-- A column with `n + 1` bit positions, stored in slot order. -/
abbrev Column : ℕ → Type
  | 0 => Bool
  | n+1 => Bool × Column n

instance columnCodec : (n : ℕ) → Codec (Column n)
  | 0 => inferInstanceAs (Codec Bool)
  | n+1 =>
    letI := columnCodec n
    inferInstanceAs (Codec (Bool × Column n))

instance columnFinite : (n : ℕ) → FiniteState (Column n)
  | 0 => inferInstanceAs (FiniteState Bool)
  | n+1 =>
    letI := columnFinite n
    inferInstanceAs (FiniteState (Bool × Column n))

/-- Convert an indexed address column to its physical nested-pair encoding. -/
def ofFn : (n : ℕ) → (Fin (n+1) → Bool) → Column n
  | 0, f => f 0
  | n+1, f => (f 0, ofFn n (fun i => f i.succ))

/-- Read a slot using its position in the fixed column. -/
def get : (n : ℕ) → Column n → Fin (n+1) → Bool
  | 0, c, _ => c
  | n+1, c, i => Fin.cases c.1 (get n c.2) i

@[simp] theorem get_ofFn : ∀ (n : ℕ) (f : Fin (n+1) → Bool),
    get n (ofFn n f) = f
  | 0, f => by funext i; exact congrArg f (Fin.ext (by omega))
  | n+1, f => by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simpa only [get, ofFn, Fin.cases_succ] using
      congrFun (get_ofFn n (fun j => f j.succ)) j

@[simp] theorem ofFn_get : ∀ (n : ℕ) (c : Column n),
    ofFn n (get n c) = c
  | 0, c => rfl
  | n+1, ⟨b,c⟩ => by simp [ofFn, get, ofFn_get n c]

/-- The slot-major input. Its first component holds all bits of the first
slot, and each remaining component holds the next complete slot. -/
def slots : (n : ℕ) → List (Column n) → Tree
  | 0, xs => send xs
  | n+1, xs => .fork (send (xs.map Prod.fst)) (slots n (xs.map Prod.snd))

theorem column_size : ∀ (n : ℕ) (c : Column n), size c = 2*n+1
  | 0, _ => rfl
  | n+1, c => by
    change 1 + size c.2 + 1 = _
    rw [column_size]
    omega

theorem columns_size (n : ℕ) (xs : List (Column n)) :
    size xs = (2*n+2)*xs.length + 1 := by
  induction xs with
  | nil => simp
  | cons c xs ih => simp only [size_cons, column_size, ih, List.length_cons, Nat.mul_add,
      Nat.mul_one]; omega

private theorem bits_size (xs : List Bool) : size xs = 2 * xs.length + 1 :=
  columns_size 0 xs

/-- All delimiter, bit, and tuple constructors in the slot-major layout. -/
theorem slots_count : ∀ (n : ℕ) (xs : List (Column n)),
    (slots n xs).count + 1 = (2*n+2)*(xs.length+1)
  | 0, xs => by
    change size xs + 1 = _
    rw [bits_size]
    omega
  | n+1, xs => by
    have ih := slots_count n (xs.map Prod.snd)
    have hb := bits_size (xs.map Prod.fst)
    simp only [List.length_map] at ih hb
    change size (xs.map Prod.fst) + (slots n (xs.map Prod.snd)).count + 1 + 1 = _
    rw [hb]
    ring_nf at ih ⊢
    omega

private def firstSlot (n : ℕ) (xs : List (Column (n+1))) := send (xs.map Prod.fst)

private def tailColumns (n : ℕ) (xs : List (Column (n+1))) := send (xs.map Prod.snd)

private def headBit (n : ℕ) (c : Column (n+1)) := send c.1

private def tailBits (n : ℕ) (c : Column (n+1)) := send c.2

private theorem forest_head (n : ℕ) (xs : List (Column (n+1))) :
    Task.forest (headBit n) xs = firstSlot n xs :=
  (Task.forest_map send Prod.fst xs).symm.trans (Task.forest_send _)

private theorem forest_tail (n : ℕ) (xs : List (Column (n+1))) :
    Task.forest (tailBits n) xs = tailColumns n xs :=
  (Task.forest_map send Prod.snd xs).symm.trans (Task.forest_send _)

private theorem pair_bits (n : ℕ) (c : Column (n+1)) :
    Tree.fork (headBit n c) (tailBits n c) = send c := rfl

/-- One merging pass zip-pairs the initial bit slot with the aligned tail. -/
private theorem merge (n : ℕ) : Task List.length
    (fun xs => .fork (firstSlot n xs) (tailColumns n xs))
    (fun xs : List (Column (n+1)) => send xs) := by
  have h := Task.zipTrees (headBit n) (tailBits n)
  simp only [forest_head n, forest_tail n, pair_bits n, Task.forest_send] at h
  apply h.bound (2*n+6)
  intro xs
  change size (xs.map Prod.fst) + size (xs.map Prod.snd) + 1 ≤ _
  rw [bits_size, columns_size n, List.length_map, List.length_map]
  ring_nf; omega

/-- Slot-major to column-major conversion by a fixed composable P192 program.
Its step bound is linear in the number of columns for each fixed arity. -/
theorem align : ∀ n, Task List.length (slots n) (fun xs : List (Column n) => send xs)
  | 0 => Task.self
  | n+1 => by
    have ih := ((align n).on (fun xs : List (Column (n+1)) => xs.map Prod.snd)).right
      (firstSlot n)
    apply (ih.compose (merge n)).bound 5
    intro xs
    change size (xs.map Prod.fst) + (xs.map Prod.snd).length + xs.length + 1 ≤ _
    rw [bits_size, List.length_map, List.length_map]
    omega

private theorem splitColumns (n : ℕ) : Task List.length
    (fun xs : List (Column (n+1)) => send xs)
    (fun xs => .fork (firstSlot n xs) (tailColumns n xs)) := by
  have h := Task.unzipTrees (headBit n) (tailBits n)
  simp only [forest_head n, forest_tail n, pair_bits n, Task.forest_send] at h
  apply h.bound (2*n+6)
  intro xs
  change size xs + 1 ≤ _
  rw [columns_size]
  ring_nf; omega

/-- Inverse conversion restores the delimited streams in their original order. -/
theorem unalign : ∀ n, Task List.length (fun xs : List (Column n) => send xs) (slots n)
  | 0 => Task.self
  | n+1 => by
    have ih := ((unalign n).on (fun xs : List (Column (n+1)) => xs.map Prod.snd)).right
      (firstSlot n)
    apply ((splitColumns n).compose ih).bound 5
    intro xs
    change xs.length + (size (xs.map Prod.fst) + (xs.map Prod.snd).length) + 1 ≤ _
    rw [bits_size, List.length_map, List.length_map]
    omega

/-- Apply a fixed column transition while traversing the slot-major input.
A state can hold all query parities and a final finite lookup can select
the numerical coefficient. The transition cost includes aligning the slots. -/
theorem foldSlots (n : ℕ) {S : Type} [Codec S] [FiniteState S]
    (step : S → Column n → S) (initial : S) :
    Task List.length (slots n) (fun xs => send (xs.foldl step initial)) := by
  let transducer (x : Column n) (s : S) : S × List Unit := (step s x, [])
  have em : Easy (fun xs : List (Column n) => machine transducer (xs,initial)) :=
    Easy.machine (Easy.identity.pair (Easy.const initial))
  have h := em.sndCompose
  have final (xs : List (Column n)) (s : S) :
      (machine transducer (xs,s)).2 = xs.foldl step s := by
    induction xs generalizing s with
    | nil => rfl
    | cons x xs ih => simpa only [machine_cons, transducer, List.foldl_cons] using ih (step s x)
  simp only [final] at h
  apply ((align n).compose h).bound (2*n+4)
  intro xs
  rw [columns_size]
  ring_nf; omega

/-- Retaining the slot-major input supplies the caller with its intact
address after looking up a coefficient. The scan and copy are both charged. -/
theorem foldSlotsKeep (n : ℕ) {S : Type} [Codec S] [FiniteState S]
    (step : S → Column n → S) (initial : S) :
    Task List.length (slots n)
      (fun xs => .fork (send (xs.foldl step initial)) (slots n xs)) := by
  have scan := (foldSlots n step initial).left (slots n)
  apply ((Task.copy (slots n)).compose scan).bound (2*n+3)
  intro xs
  have h := slots_count n xs
  ring_nf at h ⊢
  omega

/-- Run a fixed family of binary query functions and look up the coefficient
indexed by their parities. For an input column family of length `f`, each
parity counts the selected columns modulo two. -/
theorem selectByParity (n m : ℕ) {Y : Type} [Codec Y]
    (query : Fin (m+1) → Column n → Bool) (table : (Fin (m+1) → Bool) → Y) :
    Task List.length (slots n)
      (fun xs => .fork (send (table fun j => decide (xs.countP (query j) % 2 = 1)))
        (slots n xs)) := by
  let add (s : Column m) (x : Column n) :=
    ofFn m fun j => (get m s j).xor (query j x)
  let initial := ofFn m fun _ => false
  have parity (xs : List (Column n)) (s : Column m) (j : Fin (m+1)) :
      get m (xs.foldl add s) j = (get m s j).xor (decide (xs.countP (query j) % 2 = 1)) := by
    induction xs generalizing s with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldl_cons, ih, add, get_ofFn, List.countP_cons]
      by_cases hx : query j x
      · rcases (show xs.countP (query j) % 2 = 0 ∨ xs.countP (query j) % 2 = 1 by omega) with h | h <;>
          cases get m s j <;> simp [hx, Nat.add_mod, h]
      · simp [hx]
  have assign : Easy (fun s : Column m => table (get m s)) := Easy.finite _
  have act := ((assign.on (fun xs : List (Column n) => xs.foldl add initial)).left (slots n))
  have doneScan := (foldSlotsKeep n add initial).compose act
  have eval (xs : List (Column n)) :
      get m (xs.foldl add initial) = fun j => decide (xs.countP (query j) % 2 = 1) := by
    funext j
    simp [parity, initial]
  simp only [eval] at doneScan
  apply doneScan.bound (2*m+3)
  intro xs
  rw [column_size]
  ring_nf
  omega

/-- The slot extraction, temporary stacks, coefficient lookup and restoration
all participate in the actual fixed-tape execution. -/
theorem physicalSelectByParity (n m : ℕ) {Y : Type} [Codec Y]
    (query : Fin (m+1) → Column n → Bool) (table : (Fin (m+1) → Bool) → Y) :
    NearSquareRoot.ShortWord.PhysicalTask List.length (slots n)
      (fun xs => .fork (send (table fun j => decide (xs.countP (query j) % 2 = 1)))
        (slots n xs)) :=
  NearSquareRoot.ShortWord.physicalTask (selectByParity n m query table)

/-- The same slots as lists of bare bits, before adding any delimiters. -/
def bitStreams : (n : ℕ) → List (Column n) → List (List Bool)
  | 0, xs => [xs]
  | n+1, xs => xs.map Prod.fst :: bitStreams n (xs.map Prod.snd)

/-- The flat address in slot order. -/
def flatBits (n : ℕ) (xs : List (Column n)) : List Bool :=
  (bitStreams n xs).flatten

@[simp] theorem flat_length : ∀ (n : ℕ) (xs : List (Column n)),
    (flatBits n xs).length = (n+1)*xs.length
  | 0, xs => by simp [flatBits, bitStreams]
  | n+1, xs => by
    change ((xs.map Prod.fst) ++ flatBits n (xs.map Prod.snd)).length = _
    rw [List.length_append, flat_length, List.length_map, List.length_map, Nat.succ_mul]
    ring

private theorem slotRulers : ∀ (n : ℕ) (xs : List (Column n)),
    (bitStreams n xs).map (tally ∘ List.length) = List.replicate (n+1) (tally xs.length)
  | 0, xs => rfl
  | n+1, xs => by simp [bitStreams, slotRulers, List.replicate_succ]

private theorem frame : ∀ n, Task List.length (fun xs => send (bitStreams n xs)) (slots n)
  | 0 => by
    apply (Task.dropRight (fun xs : List (Column 0) => send xs)
      (fun _ => send ([] : List (List Bool)))).bound 4
    intro xs
    change size xs + 1 + 1 ≤ _
    rw [columns_size]
    omega
  | n+1 => by
    have h := ((frame n).on (fun xs : List (Column (n+1)) => xs.map Prod.snd)).right
      (firstSlot n)
    apply h.bound 4
    intro xs
    change size (xs.map Prod.fst) + (xs.map Prod.snd).length + 1 ≤ _
    rw [bits_size, List.length_map, List.length_map]
    omega

/-- Parse a flat unmarked address. The first scan divides its length by the
fixed number of slots and produces a unary width. Subsequent scans copy the
width and cut the bit stream at the resulting boundaries. -/
theorem flatToSlots (n : ℕ) : Task List.length (fun xs => send (flatBits n xs)) (slots n) := by
  cases n with
  | zero =>
    have e (xs : List (Column 0)) : flatBits 0 xs = xs := by simp [flatBits, bitStreams]
    simpa only [e, slots] using (Task.self (b := List.length) (p := send (X := List Bool)))
  | succ n =>
    let a := n+2
    have ha : 2 ≤ a := by omega
    let width (l : List Bool) := (catalog a ha (ruler l)).1
    have getWidth : Easy width := (Easy.ruler Easy.identity).compose (easy_catalog a ha).fstCompose
    have ew (xs : List (Column (n+1))) : width (flatBits (n+1) xs) = tally xs.length := by
      let l := ruler (flatBits (n+1) xs)
      have len := len_catalog a ha l
      have hr := (catalog a ha l).2.isLt
      have e : l.length = a*xs.length := by simp [l, a]
      rw [e] at len
      have h := congrArg (· / a) len
      rw [Nat.mul_add_div (by omega : 0 < a), Nat.div_eq_of_lt hr, Nat.mul_div_cancel_left _ (by omega : 0 < a)] at h
      change (catalog a ha l).1 = _
      rw [← recover_tally (catalog a ha l).1, ← (by simpa using h : xs.length = (catalog a ha l).1.length)]
    have repeatWidth (r : ℕ) : Easy (fun l => List.replicate r (width l)) := by
      induction r with
      | zero => exact Easy.const []
      | succ r ih =>
        simp only [List.replicate_succ]
        exact (getWidth.pair ih).compose Easy.cons
    have seg := (Piecework.easySegment (repeatWidth a) (easy_id (X := List Bool))).fstCompose
    have hseg := seg.on (flatBits (n+1))
    have eseg (xs : List (Column (n+1))) :
        (Piecework.segment (List.replicate a (width (flatBits (n+1) xs))) (flatBits (n+1) xs)).1 =
          bitStreams (n+1) xs := by
      rw [ew, ← slotRulers, flatBits, Piecework.prescribed]
    simp only [eseg] at hseg
    apply (hseg.compose (frame (n+1))).bound (2*a+3)
    intro xs
    rw [bits_size, flat_length]
    dsimp only [a]
    ring_nf
    omega

/-- Concrete P192 machine from the unmarked slot-major address to the
lookup result and the same address with its slot boundaries marked. -/
theorem physicalFlatSelectByParity (n m : ℕ) {Y : Type} [Codec Y]
    (query : Fin (m+1) → Column n → Bool) (table : (Fin (m+1) → Bool) → Y) :
    NearSquareRoot.ShortWord.PhysicalTask List.length (fun xs => send (flatBits n xs))
      (fun xs => .fork (send (table fun j => decide (xs.countP (query j) % 2 = 1)))
        (slots n xs)) := by
  apply NearSquareRoot.ShortWord.physicalTask
  apply ((flatToSlots n).compose (selectByParity n m query table)).bound 2
  intro xs
  omega

end KernelSelectorAlign

end NearSquareRoot
end Computability
end OAI
