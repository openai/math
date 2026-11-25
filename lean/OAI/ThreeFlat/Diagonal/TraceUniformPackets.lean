import OAI.ThreeFlat.Diagonal.TraceUniformRow

namespace OAI
/-! # Scalar and Boolean packets in the dynamically fetched trace -/

namespace ThreeFlat.Diagonal.TraceUniformRow

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM TraceRows TraceRowPackets TraceCompose TraceProgram

variable {F : Type*} [CommRing F] [Fintype F] {w p r k f S d : ℕ}

abbrev Check (F : Type*) (w p k : ℕ) := Factor F ⊕ (Unit ⊕ (Text w p k × Bool))

noncomputable def check (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hp0 : 0 < p) (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (v : Fin (2^d)) : Check F w p k → Packet (Port w p r k d)
  | .inl a => dynamic hF hw hp hp0 st hs hf v a
  | .inr (.inl _) => programHeader v
  | .inr (.inr (j,b)) => relay (by omega) base v j b

def coefficient : Check F w p k → Bool → F
  | .inl a => scalar a
  | .inr _ => fun b => if b then 1 else 0

end ThreeFlat.Diagonal.TraceUniformRow

end OAI
