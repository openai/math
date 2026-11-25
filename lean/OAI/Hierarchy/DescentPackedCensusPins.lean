import OAI.Hierarchy.DescentSIMDEncodedPin
import OAI.Hierarchy.DescentPackedCensusRows

namespace OAI
/-! # Literal local occupancy, outgoing, history and hub pins of the packed census -/

namespace Hierarchy.DescentSixParty.PackedCensus
open DescentSIMDLookup DescentColonies
open scoped Classical Fin.CommRing
noncomputable section

private theorem low (upper field b j : ℕ) (fit : field<2^b) (inside : j<b) :
    (upper*2^b+field).testBit j=field.testBit j := by
  have h : (upper*2^b+field)%2^b=field := by simp [Nat.add_mod,Nat.mod_eq_of_lt fit]
  have bit:=congrArg (fun n : ℕ=>n.testBit j) h
  simpa only [Nat.testBit_mod_two_pow,inside,decide_true,Bool.true_and] using bit

private theorem high (upper field b j : ℕ) (fit : field<2^b) :
    (upper*2^b+field).testBit (j+b)=upper.testBit j := by
  have h : (upper*2^b+field)/2^b=upper := by
    rw [Nat.mul_comm upper (2^b),Nat.mul_add_div (Nat.two_pow_pos b),Nat.div_eq_of_lt fit,Nat.add_zero]
  have bit:=congrArg (fun n : ℕ=>n.testBit j) h
  simpa only [Nat.testBit_div_two_pow] using bit

theorem occupancy_pin {b cap : ℕ} (hub : Cell 1) (atoms : Cell b) (live paid : Finset (Fin cap))
    (sub : paid⊆live) (i : Fin cap) :
    (header b cap ((hub,atoms),tags live paid)).val.testBit (2*i.val)=decide (i∈live) := by
  rw [header_value,low _ _ _ _ (encode 2 cap (tags live paid)).isLt (by omega)]
  have p := encode_pin (tags live paid) i (0:Fin 2)
  simp only [Fin.val_zero,Nat.zero_add] at p
  rw [p]
  by_cases yes : i∈paid
  · simp [tags,yes,sub yes]
  · by_cases isLive : i∈live <;> simp [tags,yes,isLive]

theorem outgoing_pin {b cap : ℕ} (hub : Cell 1) (atoms : Cell b) (live paid : Finset (Fin cap))
    (i : Fin cap) :
    (header b cap ((hub,atoms),tags live paid)).val.testBit (1+2*i.val)=decide (i∈paid) := by
  rw [header_value,low _ _ _ _ (encode 2 cap (tags live paid)).isLt (by omega)]
  have p := encode_pin (tags live paid) i (1:Fin 2)
  change (encode 2 cap (tags live paid)).val.testBit (1+2*i.val)=(tags live paid i).val.testBit 1 at p
  rw [p]
  by_cases yes : i∈paid <;> by_cases isLive : i∈live <;> simp [tags,yes,isLive] <;> decide

theorem history_pin {b cap : ℕ} (hub : Cell 1) (atoms : Cell b) (slots : Fin cap→Cell 2)
    (j : Fin b) :
    (header b cap ((hub,atoms),slots)).val.testBit (j.val+2*cap)=atoms.val.testBit j.val := by
  rw [header_value,high _ _ _ _ (encode 2 cap slots).isLt,low _ _ _ _ atoms.isLt j.isLt]

theorem hub_pin {b cap : ℕ} (hub : Cell 1) (atoms : Cell b) (slots : Fin cap→Cell 2) :
    (header b cap ((hub,atoms),slots)).val.testBit (b+2*cap)=hub.val.testBit 0 := by
  rw [header_value,high _ _ _ _ (encode 2 cap slots).isLt]
  simpa using high hub.val atoms.val b 0 atoms.isLt

end
end Hierarchy.DescentSixParty.PackedCensus

end OAI
