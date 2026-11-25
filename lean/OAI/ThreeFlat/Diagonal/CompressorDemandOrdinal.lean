import OAI.ThreeFlat.Diagonal.CompressorRadixKey
import OAI.ThreeFlat.Diagonal.CompressorWordEncoding

namespace OAI
/-! # The physical width-array address as a common old-arc ordering -/

namespace ThreeFlat.Diagonal.CompressorPacking
open Computability.VPVNP.Compression
variable {V H Tag L : Type*} {c d a l : ℕ}
variable (P : PackingData V H Tag L d c)

def demandOrdinal (v : V ↪ ℕ) (tag : Tag ↪ Fin a) (lane : L ↪ Fin l) :
    Arc V H Tag L d c ↪ ℕ where
  toFun e := appendKey (appendKey (appendKey (appendKey (appendKey
    (v e.1.1.1) e.1.2) (lane e.1.1.2.2)) (tag e.1.1.2.1)) (P.slotLabel e.2.2))
      (Native.tagOrdinal c e.2.1)
  inj' := by
    intro x y h
    obtain ⟨h,bits⟩ := appendKey_inj h
    obtain ⟨h,labels⟩ := appendKey_inj h
    obtain ⟨h,tags⟩ := appendKey_inj h
    obtain ⟨h,lanes⟩ := appendKey_inj h
    obtain ⟨bases,ports⟩ := appendKey_inj h
    exact Prod.ext (Prod.ext (Prod.ext (v.injective bases)
      (Prod.ext (tag.injective tags) (lane.injective lanes))) ports)
      (Prod.ext ((Native.tagOrdinal c).injective bits) (P.slotLabel.injective labels))

theorem demandOrdinal_formula (v : V ↪ ℕ) (tag : Tag ↪ Fin a) (lane : L ↪ Fin l)
    (e : Arc V H Tag L d c) :
    demandOrdinal P v tag lane e =
      (v e.1.1.1*d+e.1.2.val)*(l*a*d*2^c) + ((Native.tagOrdinal c e.2.1).val +
        2^c*((P.slotLabel e.2.2).val+d*((tag e.1.1.2.1).val+a*(lane e.1.1.2.2).val))) := by
  simp only [demandOrdinal,Function.Embedding.coeFn_mk,appendKey]
  ring

end ThreeFlat.Diagonal.CompressorPacking

end OAI
