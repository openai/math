import OAI.ThreeFlat.Diagonal.TracePreparedSuffix
import OAI.ThreeFlat.Diagonal.TracePairLeaf

namespace OAI
/-! # All public H advice is fixed before exposing the genuine matrix endpoints -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP BurstRAM RAMMemory
variable {F : Type*} [Fintype F] [Field F] {w p S f q low bits : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3≤w+1) (hp : p≤2^(w+1))
    (base : ℕ) (st : Word w) (hs : S≤2^w) (hf : f≤2^(w+1)) (r k : ℕ)
    (I : RAM.PhysicalPrelude.Image F w) (D : Fin I.advice→Bool) (par : Fin I.parameters→Bool) (fixed : Fin bits→Bool)

theorem trueEndpoint_eval (span : 2*I.endpointBits≤S) (sep : 2*I.endpointBits≤base)
    (x y : Fin I.endpointBits→Bool) :
    (trueNetwork (q:=q) (low:=low) hF hw hp base st hs hf r k span (publicAt I base fixed D par)).eval (endpointPin x y) =
    (network hF hw hp base st hs hf r k ((q+1)+low)).eval (advicePins base fixed (I.tapeBit D x y par)) := by
  rw [trueNetwork_eval,trueHeader_eq I span sep fixed D par x y]


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
