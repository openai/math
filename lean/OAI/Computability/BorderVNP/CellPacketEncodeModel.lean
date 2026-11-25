import OAI.Computability.BorderVNP.CellDirectoryWire
import OAI.Computability.BorderVNP.RoutingISACompactWrite

/-! # Native encoding of the natural-word sparse directory

The source is a consecutive interval of machine words. Register 14 addresses the next
source word, 15 is its exclusive end, and 20 addresses the next output digit. The
generator reads a one record marker, zero-tagged little-endian digits, and a one
terminator per word. The optional enclosing word adds a zero tag to every emitted
packet bit. All loops and memory operations are physical team instructions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacketEncode

open RationalHitting.StackLanguage

/-- Sparse bitstream consumed by the generator's record scanner. -/
def packet (words : List ℕ) : List Bool := CellMacro.Generator.records (words.map Nat.bits)

/-- An enclosing self-delimiting field inserts a zero before every payload bit. -/
def tags (enclosed : Bool) (bs : List Bool) : List Bool :=
  if enclosed then pairWord bs else bs

@[simp] theorem tags_nil (enclosed : Bool) : tags enclosed [] = [] := by cases enclosed <;> rfl

@[simp] theorem tags_append (enclosed : Bool) (xs ys : List Bool) :
    tags enclosed (xs ++ ys) = tags enclosed xs ++ tags enclosed ys := by cases enclosed <;> simp [tags]

/-- The optional outer framing multiplies the number of scratch cells by at most two. -/
theorem tags_length (enclosed : Bool) (bs : List Bool) :
    (tags enclosed bs).length = (if enclosed then 2 else 1)*bs.length := by
  cases enclosed
  · simp [tags]
  · have h := codeWord_length bs
    rw [codeWord_pair, List.length_append] at h
    simp only [tags, ite_true]
    simpa using (by simp at h; omega : (pairWord bs).length = 2*bs.length)

/-- One complete sparse record consists of its iteration marker and framed scalar. -/
theorem packet_cons (a : ℕ) (rest : List ℕ) :
    packet (a::rest) = [true] ++ pairWord a.bits ++ [true] ++ packet rest := by
  simp [packet, CellMacro.Generator.records, codeWord_pair]

/-- Each scalar in a physical source occupies at most twice the machine width plus two bits. -/
theorem packet_length_le {w : ℕ} (xs : List ℕ) (h : ∀ a ∈ xs, a < 2^w) :
    (packet xs).length ≤ xs.length*(2*w+2) := by
  induction xs with
  | nil => simp [packet, CellMacro.Generator.records]
  | cons a xs ih =>
    have ha := Nat.size_le.mpr (h a List.mem_cons_self)
    rw [← Nat.size_eq_bits_len] at ha
    have ht := ih fun x hx => h x (List.mem_cons_of_mem _ hx)
    change (true :: (codeWord a.bits ++ packet xs)).length ≤ _
    simp only [List.length_cons, List.length_append, codeWord_length]
    rw [Nat.add_mul, one_mul]
    omega

/-- Chronological stores of Boolean-valued machine words in shared memory. -/
def putDigits (m : ℕ → ℕ) (dst : ℕ) : List Bool → ℕ → ℕ
  | [] => m
  | b :: bs => putDigits (Function.update m dst b.toNat) (dst+1) bs

/-- Consecutive runs of the writer concatenate their bitstreams. -/
theorem putDigits_append (m : ℕ → ℕ) (dst : ℕ) (xs ys : List Bool) :
    putDigits m dst (xs++ys) = putDigits (putDigits m dst xs) (dst+xs.length) ys := by
  induction xs generalizing m dst with
  | nil => simp [putDigits]
  | cons b xs ih => simp only [List.cons_append, putDigits, List.length_cons, ih]; congr 1; omega

/-- The encoder preserves every address outside its output interval. -/
theorem putDigits_outside (m : ℕ → ℕ) (dst j : ℕ) (bs : List Bool)
    (outside : j < dst ∨ dst+bs.length ≤ j) : putDigits m dst bs j = m j := by
  induction bs generalizing m dst with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons] at outside
    rw [putDigits, ih _ _ (by omega), Function.update_of_ne (by omega : j ≠ dst)]

/-- The output interval reads back the original Boolean digits in order. -/
theorem putDigits_read (m : ℕ → ℕ) (dst : ℕ) (bs : List Bool) (i : Fin bs.length) :
    putDigits m dst bs (dst+i) = bs[i].toNat := by
  induction bs generalizing m dst with
  | nil => exact i.elim0
  | cons b bs ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [Fin.val_zero, Nat.add_zero, putDigits]
      rw [putDigits_outside _ _ _ _ (Or.inl (by omega)), Function.update_self]
      rfl
    · simp only [Fin.val_succ, putDigits]
      simpa [Nat.add_assoc, Nat.add_comm 1] using ih (Function.update m dst b.toNat) (dst+1) k

/-- The source, temporary quotient and remainder, and destination cursors are the only
registers changed after the constants have been initialized. -/
def Fixed (start finish : Reg → ℕ) : Prop :=
  ∀ j, j ≠ 14 → j ≠ 16 → j ≠ 17 → j ≠ 20 → finish j = start j

/-- Values of the three arithmetic constants used in the loop. -/
def Constants (r : Reg → ℕ) : Prop := r 0 = 0 ∧ r 1 = 1 ∧ r 18 = 2

/-- Protected constants survive one or more writer steps. -/
theorem Fixed.constants {r t : Reg → ℕ} (h : Fixed r t) (c : Constants r) : Constants t :=
  ⟨(h 0 (by decide) (by decide) (by decide) (by decide)).trans c.1,
    (h 1 (by decide) (by decide) (by decide) (by decide)).trans c.2.1,
    (h 18 (by decide) (by decide) (by decide) (by decide)).trans c.2.2⟩

/-- Register preservation across successive native code fragments. -/
theorem Fixed.trans {r t u : Reg → ℕ} (h : Fixed r t) (g : Fixed t u) : Fixed r u :=
  fun j a b c d => (g j a b c d).trans (h j a b c d)

/-- Emit one bit into the unpacked scratch interval, optionally prefixing a zero tag. -/
def emit (enclosed : Bool) (r : Reg) : Code :=
  let write (v : Reg) : Code := .seq (.store 20 v) (.binary .add 20 20 1)
  if enclosed then .seq (write 0) (write r) else write r

/-- One native binary division and two writes of a tagged little-endian digit. -/
def digit (enclosed : Bool) : Code := .seq (.block [.binary .mod 17 16 18, .binary .div 16 16 18])
  (.seq (emit enclosed 0) (emit enclosed 17))

/-- Consume one source word and surround its tagged digits with the generator's two markers. -/
def record (enclosed : Bool) : Code :=
  .seq (.block [.load 16 14, .binary .add 14 14 1]) (.seq (emit enclosed 1)
    (.seq (.whileLt 0 16 (digit enclosed)) (emit enclosed 1)))

/-- Stream the entire source interval using a fixed finite instruction sequence. -/
def encoder (enclosed : Bool) : Code := .whileLt 14 15 (record enclosed)

end RoutingISA.CellPacketEncode

end BorderVNP
end Computability
end OAI
