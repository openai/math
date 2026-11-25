import OAI.ThreeFlat.Diagonal.TraceBitInput
import OAI.ThreeFlat.Diagonal.TraceBitNetwork
import OAI.ThreeFlat.Diagonal.TraceStaticNetwork

namespace OAI
/-! # Weighted semantics on the compressed public bit header -/

namespace ThreeFlat.Diagonal.TraceBitHeader

open Computability.VPVNP BurstRAM RAMSerialization RAMMemory LaneCursor
variable {F : Type*} {S w : ℕ}

variable [Fintype F] [CommRing F] {p r k' d f : ℕ}

theorem eval_advice (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (hp0 : 0 < p)
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (grid : S+f ≤ 2^(1+d))
    {q : ℕ} (text : (1+6*p+k')*w ≤ q) (inMemory : base+q ≤ S) (D : Fin q → Bool) (x : ℕ → Bool) :
    (network hF hw hp base st hs hf r k' d).eval (advicePins base D x) =
      RAM.adviceValue (RAM.FieldCode.ofCardLe hF) p r k' text D f st base
        (initialMemory S (fun a => binaryWord w (x a))) := by
  rw [network,eval (by omega)]
  have h := TraceStaticRow.network_advice (r:=r) hF hw hp hp0 base st hs hf grid text inMemory D
    (fun a => binaryWord w (x a))
  simpa only [TracePhysical.headerPins,adviceWords_inside] using h

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
