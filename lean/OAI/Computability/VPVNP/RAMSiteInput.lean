import OAI.Computability.VPVNP.RAMBitLocality
import OAI.Computability.VPVNP.UniversalMachine

/-!
# Input string of a live or primed site

Section 9.2 uses a literal self-delimiting program prefix, the site's address,
four header bits, its incident communication bits, and zeros. The full string
is an input to the coefficient machine. The prescribed header word and address
are recovered from exactly the fields that appear on its input tape.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM.ProcessorInput

open RAMLayout RAMSerialization

variable {d H w n : ℕ}

/-- Four header bits for a site, in the order group index, advice, incoming cut, and outgoing
cut. -/
abbrev Header := Fin 4 → Bool

/-- The four header bits are group index, advice, incoming cut, outgoing cut. -/
def header (index advice incoming outgoing : Bool) : Header := ![index, advice, incoming, outgoing]

/-- The low four bits of the site's initialized word hold its header. -/
def headerWord (_hw : 4 ≤ w) (hdr : Header) : Word w :=
  (wordBits w).symm fun i => if h : i.val < 4 then hdr ⟨i.val, h⟩ else false

theorem headerWord_bit (hw : 4 ≤ w) (hdr : Header) (j : Fin 4) :
    wordBits w (headerWord hw hdr) (j.castLE hw) = hdr j := by
  simp [headerWord]

theorem headerWord_padding (hw : 4 ≤ w) (hdr : Header) (j : Fin w) (hj : 4 ≤ j.val) :
    wordBits w (headerWord hw hdr) j = false := by simp [headerWord, Nat.not_lt.mpr hj]

/-- Address, literal index/advice and cut bits, and incident communication fields. -/
def payload (v : Fin (2^d)) (hdr : Header) (inc : Fin (width d H w) → Bool) : List Bool :=
  List.ofFn (wordBits d v) ++ List.ofFn hdr ++ List.ofFn inc

@[simp] theorem length_payload (v : Fin (2^d)) (hdr : Header) (inc : Fin (width d H w) → Bool) :
    (payload v hdr inc).length = d + 4 + width d H w := by simp only [payload, List.length_append, List.length_ofFn]

/-- The self-delimiting program prefix, site address, four header bits, and all incident
communication bits fit within the input length. -/
abbrev Fits (program : UniversalMachine.Program) (n d H w : ℕ) :=
  (UniversalMachine.programPrefix program).length + (d + 4 + width d H w) ≤ n

/-- Construct the site’s literal input by concatenating the program prefix, address, header,
and incident bits, then filling the available suffix with zeros. -/
def tape (program : UniversalMachine.Program) (n : ℕ) (v : Fin (2^d)) (hdr : Header)
    (inc : Fin (width d H w) → Bool) : List Bool :=
  let used := (UniversalMachine.programPrefix program).length + (d + 4 + width d H w)
  UniversalMachine.programPrefix program ++ (payload v hdr inc ++ List.replicate (n-used) false)

theorem length_tape (p : UniversalMachine.Program) (v : Fin (2^d)) (hdr : Header)
    (inc : Fin (width d H w) → Bool) (hf : Fits p n d H w) :
    (tape p n v hdr inc).length = n := by
  simp only [tape, List.length_append, length_payload, List.length_replicate]
  unfold Fits at hf
  omega

/-- Index the fitted site input tape by its n positions to obtain a Boolean coefficient input. -/
def encode (program : UniversalMachine.Program) (n : ℕ) (v : Fin (2^d)) (hdr : Header)
    (inc : Fin (width d H w) → Bool) (hf : Fits program n d H w) : Fin n → Bool :=
  fun j => (tape program n v hdr inc)[j.val]'(by rw [length_tape _ _ _ _ hf]; exact j.isLt)

@[simp] theorem ofFn_encode (p : UniversalMachine.Program) (n : ℕ) (v : Fin (2^d)) (hdr : Header)
    (inc : Fin (width d H w) → Bool) (hf : Fits p n d H w) :
    List.ofFn (encode p n v hdr inc hf) = tape p n v hdr inc := by
  apply List.ext_getElem
  · rw [List.length_ofFn, length_tape _ _ _ _ hf]
  · intro i _ _
    simp [encode]

/-- The first field really is the self-delimiting prefix accepted by the
universal coefficient machine, independently of all other sites' choices. -/
theorem decode (p : UniversalMachine.Program) (n : ℕ) (v : Fin (2^d)) (hdr : Header)
    (inc : Fin (width d H w) → Bool) (hf : Fits p n d H w) :
    UniversalMachine.decode (List.ofFn (encode p n v hdr inc hf)) = some p := by
  rw [ofFn_encode, tape, UniversalMachine.decode_programPrefix]

theorem coefficient (p : UniversalMachine.Program) (n : ℕ) (v : Fin (2^d)) (hdr : Header)
    (inc : Fin (width d H w) → Bool) (hf : Fits p n d H w) :
    acceptingCount (encode p n v hdr inc hf) =
      UniversalMachine.paths p (n^clockExponent) (UniversalMachine.initial p (tape p n v hdr inc)) := by
  dsimp only [acceptingCount]
  rw [decode, ofFn_encode]

/-- The exact suffix after the literal prefix, including zero padding. -/
theorem drop_prefix (p : UniversalMachine.Program) (n : ℕ) (v : Fin (2^d)) (hdr : Header)
    (inc : Fin (width d H w) → Bool) :
    (tape p n v hdr inc).drop (UniversalMachine.programPrefix p).length =
      payload v hdr inc ++ List.replicate (n - ((UniversalMachine.programPrefix p).length +
        (d + 4 + width d H w))) false := by simp [tape]

/-- Every designated address, header, and communication bit can be read
directly at its own offset. -/
theorem payload_address (v : Fin (2^d)) (hdr : Header) (inc : Fin (width d H w) → Bool)
    (i : Fin d) : (payload v hdr inc)[i.val]? = some (wordBits d v i) := by
  simp only [payload, List.append_assoc]
  rw [List.getElem?_append_left (by simpa only [List.length_ofFn] using i.isLt)]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.getElem_ofFn]

theorem payload_header (v : Fin (2^d)) (hdr : Header) (inc : Fin (width d H w) → Bool)
    (i : Fin 4) : (payload v hdr inc)[d+i.val]? = some (hdr i) := by
  simp only [payload, List.append_assoc]
  rw [List.getElem?_append_right (by simp), List.length_ofFn, Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa only [List.length_ofFn] using i.isLt)]
  rw [List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.getElem_ofFn]

theorem payload_incident (v : Fin (2^d)) (hdr : Header) (inc : Fin (width d H w) → Bool)
    (i : Fin (width d H w)) : (payload v hdr inc)[d+4+i.val]? = some (inc i) := by
  simp only [payload, List.append_assoc]
  rw [List.getElem?_append_right (by simp only [List.length_ofFn]; omega), List.length_ofFn,
    show d+4+i.val-d = 4+i.val by omega]
  rw [List.getElem?_append_right (by simp only [List.length_ofFn]; omega), List.length_ofFn,
    Nat.add_sub_cancel_left, List.getElem?_eq_getElem (by simpa only [List.length_ofFn] using i.isLt)]
  simp only [List.getElem_ofFn]

end BurstRAM.ProcessorInput

end VPVNP
end Computability
end OAI
