import OAI.Computability.BorderVNP.CellPacketEncodeModel
import OAI.Computability.BorderVNP.CellDirectoryWire

/-!
# Public address descriptors for sparse private-cell packets

A public descriptor carries a source address and a length field. For public natural
words this is a word count. For a private site the length field is the fixed width of
the binary length header in the delivered opaque slice. Only the physical payload tells
the team how many private bits to copy. Copy multiplicities stay inside the private
packet's strided records.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket

open CellPacketEncode

/-- One compact packet source and its mathematical interpretation. The public directory
contains `descriptor`, which omits the private body and its length. -/
inductive Chunk
  | words (base : ℕ) (xs : List ℕ)
  | box (base headerWidth : ℕ) (payload : List Bool)

/-- The sparse packet bits contributed by a single input range. -/
def Chunk.bits : Chunk → List Bool
  | .words _ xs => packet xs
  | .box _ _ bs => bs

/-- A fixed three-word public descriptor. Private payload size is read from the opaque
header at runtime. -/
def Chunk.descriptor : Chunk → List ℕ
  | .words a xs => [0,a,xs.length]
  | .box a h _ => [1,a,h]

/-- Actual source representation in shared memory, independently of any destination
or other packet fields. An opaque box begins with its little-endian length header. -/
def Chunk.Stored (mem : ℕ → ℕ) : Chunk → Prop
  | .words a xs => ∀ i : Fin xs.length, mem (a+i.val) = xs[i.val]
  | .box a h bs => bs.length < 2^h ∧
      (∀ i : Fin h, mem (a+i.val) = (bs.length.testBit i.val).toNat) ∧
      ∀ i : Fin bs.length, mem (a+h+i.val) = bs[i].toNat

/-- Exclusive end of all physically consumed input data for a chunk. -/
def Chunk.endSource : Chunk → ℕ
  | .words a xs => a+xs.length
  | .box a h bs => a+h+bs.length

/-- Charge in the sparse loop, depending on actual public word count and private bytes
but independent of every represented repetition count. -/
def Chunk.work (w : ℕ) : Chunk → ℕ
  | .words _ xs => 60*(xs.length+1)*(w+1)
  | .box _ h bs => 60*(h+bs.length+1)

/-- Words for the array scanned by the outer fixed program. -/
def descriptors (cs : List Chunk) : List ℕ := cs.flatMap Chunk.descriptor

/-- An array of descriptors has three words for each sparse chunk. -/
theorem descriptors_length (cs : List Chunk) : (descriptors cs).length = 3*cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [descriptors, Chunk.descriptor] at ih ⊢ <;> omega

/-- A contiguous list of natural words at its actual shared-memory addresses. -/
def WordsAt (mem : ℕ → ℕ) (base : ℕ) (xs : List ℕ) : Prop :=
  ∀ i : Fin xs.length, mem (base+i.val) = xs[i.val]

/-- Reading the leading portion of a contiguous array of actual words. -/
theorem WordsAt.left {mem : ℕ → ℕ} {a : ℕ} {xs ys : List ℕ} (h : WordsAt mem a (xs++ys)) :
    WordsAt mem a xs := by
  intro i
  simpa only [List.getElem_append_left i.isLt] using h ⟨i.val,by simp; omega⟩

/-- The remaining words begin immediately after the leading portion. -/
theorem WordsAt.right {mem : ℕ → ℕ} {a : ℕ} {xs ys : List ℕ} (h : WordsAt mem a (xs++ys)) :
    WordsAt mem (a+xs.length) ys := by
  intro i
  simpa only [Nat.add_assoc, List.getElem_append_right (by omega : xs.length ≤ xs.length+i.val),
    Nat.add_sub_cancel_left] using h ⟨xs.length+i.val, by simp⟩

/-- Writing scratch bits after a reserved source range leaves the entire chunk readable. -/
theorem Chunk.Stored.putDigits {m : ℕ → ℕ} {c : Chunk} (h : c.Stored m)
    {a : ℕ} (apart : c.endSource ≤ a) (bs : List Bool) : c.Stored (putDigits m a bs) := by
  cases c with
  | words x xs =>
    intro i
    rw [putDigits_outside _ _ _ _ (Or.inl (by change x+xs.length ≤ a at apart; have := i.isLt; omega))]
    exact h i
  | box x hd ys =>
    change x+hd+ys.length ≤ a at apart
    refine ⟨h.1, fun i => ?_, fun i => ?_⟩
    · rw [putDigits_outside _ _ _ _ (Or.inl (by have := i.isLt; omega))]
      exact h.2.1 i
    · rw [putDigits_outside _ _ _ _ (Or.inl (by have := i.isLt; omega))]
      exact h.2.2 i

end RoutingISA.CellPacket

end BorderVNP
end Computability
end OAI
