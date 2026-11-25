import OAI.ThreeFlat.RAM.TraceAddressReader
import OAI.ThreeFlat.RAM.TraceTemplateReaders
import OAI.ThreeFlat.RAM.WordSegment

namespace OAI
/-! # Packed public data for the fixed trace enumerator -/

namespace ThreeFlat.RAM.FixedTraceImage

open Computability.VPVNP.BurstRAM BitLayout Diagonal.TraceAddressRecord
open scoped Fin.CommRing
variable {F : Type*} [CommSemiring F] {w q : ℕ}

/-- Each local gate and each source-address formula occupies eleven words. -/
def word (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record) (i : ℕ) : Word w :=
  if i<11*N.cells then TraceTemplate.localWord N code i else
    let z := i-11*N.cells
    (TraceAddressReader.fields (TraceTemplate.getRecord R (z/11)) ⟨z%11,Nat.mod_lt _ (by decide)⟩ : Word w)

omit [CommSemiring F] in
theorem gate (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record)
    (i : Fin N.cells) (j : Fin 11) :
    word N code R (11*i.val+j.val) = record N code i j := by
  have h : 11*i.val+j.val<11*N.cells := by have := i.isLt; have := j.isLt; omega
  simpa [word,h] using TraceTemplate.localWord_at N code i j

omit [CommSemiring F] in
theorem port (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record)
    (i : Fin q) (j : Fin 11) :
    word N code R (11*N.cells+(11*i.val+j.val)) = (TraceAddressReader.fields (R i) j : Word w) := by
  have eq : (11*i.val+j.val)/11=i.val := by
    simp [Nat.mul_add_div (by decide : 0<11),Nat.div_eq_of_lt j.isLt]
  have rem : (11*i.val+j.val)%11=j.val := by simp [Nat.mod_eq_of_lt j.isLt]
  simp [word,TraceTemplate.getRecord,eq,rem,i.isLt]

def count (N : BitNetwork F q) := 11*(N.cells+q)

def packed (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record)
    (base : ℕ) (m : Memory w) : Memory w :=
  fillSegment base (count N) (fun a => word N code R (a-base)) m

omit [CommSemiring F] in
theorem packed_gate (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record)
    (base : ℕ) (m : Memory w) (i : Fin N.cells) (j : Fin 11) :
    packed N code R base m (base+11*i.val+j.val) = record N code i j := by
  have h : 11*i.val+j.val<count N := by
    unfold count; have := i.isLt; have := j.isLt; omega
  simpa [packed,fillSegment,Nat.add_assoc,h] using gate N code R i j

omit [CommSemiring F] in
theorem packed_port (N : BitNetwork F q) (code : FieldCode F w) (R : Fin q → Record)
    (base : ℕ) (m : Memory w) (i : Fin q) (j : Fin 11) :
    packed N code R base m (TraceAddressReader.address (base+11*N.cells) i.val j) =
      (TraceAddressReader.fields (R i) j : Word w) := by
  have h : 11*N.cells+(11*i.val+j.val)<count N := by
    unfold count; have := i.isLt; have := j.isLt; omega
  simpa [packed,fillSegment,TraceAddressReader.address,Nat.add_assoc,h] using port N code R i j

/-- Public parameters use one bit per input word, most significant bit first. -/
def bits (words : ℕ → Word w) (a : ℕ) : Bool :=
  (words (a/w)).val.testBit (w-1-a%w)

theorem bits_at (words : ℕ → Word w) (i : ℕ) (j : Fin w) :
    bits words (w*i+j.val) = (words i).val.testBit (w-1-j.val) := by
  have hw : 0<w := Nat.zero_lt_of_lt j.isLt
  simp [bits,Nat.mul_add_div hw,Nat.div_eq_of_lt j.isLt,Nat.mod_eq_of_lt j.isLt]

end ThreeFlat.RAM.FixedTraceImage

end OAI
