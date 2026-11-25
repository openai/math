import OAI.ThreeFlat.Diagonal.TracePreparedTape
import OAI.ThreeFlat.Diagonal.TraceEndpointSlice

namespace OAI
/-! # The actual H header separates into alternating true pins and a public suffix -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP BurstRAM RAMMemory TraceSuffix
variable {F : Type*} [Fintype F] [Field F] {w S q : ℕ} (I : RAM.PhysicalPrelude.Image F w)

def endpointPin {T : ℕ} (x y : Fin T→Bool) (i : Fin (2*T)) : Bool :=
  let j : Fin T := ⟨i.val/2,by have := i.isLt; omega⟩
  if i.val%2=0 then x j else y j

noncomputable def publicAt (base : ℕ) (fixed : Fin q→Bool) (D : Fin I.advice→Bool)
    (params : Fin I.parameters→Bool) (i : ℕ) :=
  if h : base≤ i ∧ i-base<q then fixed ⟨_,h.2⟩ else I.tapeBit D (fun _ => false) (fun _ => false) params i

theorem actual_publicAt (base : ℕ) (fixed : Fin q→Bool) (D : Fin I.advice→Bool) (params : Fin I.parameters→Bool)
    (x y : Fin I.endpointBits→Bool) (i : Fin S) (past : 2*I.endpointBits≤ i.val) :
    publicAt I base fixed D params i.val=advicePins base fixed (I.tapeBit D x y params) i := by
  simp [publicAt,advicePins,RAM.PhysicalPrelude.Image.tapeBit,RAM.PhysicalPinsInput.rawBit,Nat.not_lt.mpr past]

theorem trueHeader_eq {base : ℕ} (span : 2*I.endpointBits≤S) (sep : 2*I.endpointBits≤base)
    (fixed : Fin q→Bool) (D : Fin I.advice→Bool) (params : Fin I.parameters→Bool) (x y : Fin I.endpointBits→Bool) :
    fullHeader span (endpointPin x y) (publicAt I base fixed D params)=advicePins base fixed (I.tapeBit D x y params) := by
  funext i
  by_cases free : i.val<2*I.endpointBits
  · have before : ¬base≤ i.val := by omega
    have count : I.sizes.rawParams=2*I.endpointBits+I.advice := rfl
    have entry : i.val<I.sizes.rawParams := by omega
    simp [fullHeader,free,endpointPin,advicePins,before,RAM.PhysicalPrelude.Image.tapeBit,entry,RAM.PhysicalPinsInput.rawBit]
  · simpa only [fullHeader,dite_eq_right free] using actual_publicAt I base fixed D params x y i (by omega)

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
