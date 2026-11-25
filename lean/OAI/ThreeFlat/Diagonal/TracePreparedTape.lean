import OAI.ThreeFlat.Diagonal.TraceBitInput
import OAI.ThreeFlat.RAM.PhysicalRawTape

namespace OAI
/-! # The native H evaluator starts on the physical trace's initialized header -/

namespace ThreeFlat.Diagonal.TraceBitHeader

open Computability.VPVNP BurstRAM RAMMemory
variable {F : Type*} [Fintype F] [Field F] {w S q : ℕ}
variable (I : RAM.PhysicalPrelude.Image F w)

/-- Every H datum, including the local tensor/port table bits, is exposed
at its prescribed raw address, with the separate executable after the
complete native image. -/
theorem prepare_raw {base : ℕ} (fit : I.sizes.rawCount ≤ S) (sep : I.sizes.rawCount ≤ base)
    (fixed : Fin q → Bool) (D : Fin I.advice → Bool) (x y : Fin I.endpointBits → Bool)
    (par : Fin I.parameters → Bool) :
    I.Raw D x y par (RAM.memoryWithAdvice base fixed (initialMemory S (fun i =>
      binaryWord w (I.tapeBit D x y par i)))) := by
  apply I.raw_of_agree D x y par
  intro i hi
  rw [RAM.memoryWithAdvice_outside base fixed _ (.inl (by omega))]
  simp only [initialMemory,ite_eq_left (hi.trans_le fit)]
  cases I.tapeBit D x y par i <;> rfl

/-- In the prepared H image, the actual row/column open slots are the
even/odd physical pins used by the XOR row layout. -/
theorem prepare_paired_pins {base : ℕ} (fit : I.sizes.rawCount ≤ S) (sep : I.sizes.rawCount ≤ base)
    (fixed : Fin q → Bool) (D : Fin I.advice → Bool) (x y : Fin I.endpointBits → Bool)
    (par : Fin I.parameters → Bool) (j : Fin I.endpointBits) :
    let bound : 2*j.val+1 < I.sizes.rawCount := by
      have ha : I.sizes.rawParams=2*I.endpointBits+I.advice := rfl
      have hb : I.sizes.rawTable=I.sizes.rawParams+I.parameters := rfl
      have hc : I.sizes.rawCount=I.sizes.rawTable+w*RAM.FixedTraceImage.count I.G := rfl
      have := j.isLt
      omega
    let pin := advicePins (S:=S) base fixed (I.tapeBit D x y par)
    pin ⟨2*j.val,by omega⟩=x j ∧ pin ⟨2*j.val+1,by omega⟩=y j := by
  intro bound pin
  have even : ¬base ≤ 2*j.val := by omega
  have odd : ¬base ≤ 2*j.val+1 := by omega
  simpa only [pin,advicePins,even,odd,false_and,dite_eq_right,not_false_eq_true] using I.tape_pair D x y par j

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
