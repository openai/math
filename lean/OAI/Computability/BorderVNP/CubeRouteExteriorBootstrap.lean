import OAI.Computability.BorderVNP.CubeScatterTransmissionHeader

/-! # Starting the public schedule before its payload widths have been computed -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader

open Diagonal.Layout Routing

variable {R r link : ℕ}

/-- Physical exterior containing the supplied bits on the prefix of each block and zeros on the suffix. -/
def bootstrap (bits : List Bool) (x : Exterior R r link) : Bool :=
  bits[(finProdFinEquiv x.2).val]?.getD false

/-- The preliminary layout fits from the header bound alone. Its messages have no routed bits. -/
def headerOnly (bits : List Bool) (three : 2 < R+1) (room : bits.length ≤ r*link) : WireLayout (R+1) r link :=
  ⟨three,fun _ _ => 0,bits.length,fun b => by
    have empty (u v : Fin (R+1)) : legLoad three (fun _ _ => 0) u v = 0 := by
      unfold legLoad
      apply Finset.sum_eq_zero
      intro z _
      by_cases h : u=z <;> simp [demand,pairLoad,pairBits,h]
    simpa only [empty,Nat.add_zero] using room⟩

/-- Encoding an empty payload in any later computed layout recovers exactly the initial physical bits. -/
theorem exterior_zero (L : WireLayout (R+1) r link) (bits : List Bool) (len : bits.length=L.header) :
    exterior L bits len (fun _ _ _ => false) = bootstrap bits := by
  funext ⟨block,addr⟩
  obtain ⟨slot,rfl⟩ := (L.coordinates block).surjective addr
  change L.regionValues _ block ((L.coordinates block).symm (L.coordinates block slot)) =
    bits[(finProdFinEquiv (L.coordinates block slot)).val]?.getD false
  rw [Equiv.symm_apply_apply]
  have ordinal : finProdFinEquiv (L.coordinates block slot) = L.position block slot :=
    finProdFinEquiv.apply_symm_apply _
  simp only [ordinal]
  rcases slot with j | p | p | j
  · simp only [L.position_header]
    rw [List.getElem?_eq_getElem (by have := j.isLt; omega)]
    rfl
  · simp only [L.position_low]
    rw [List.getElem?_eq_none (by omega)]
    rfl
  · simp only [L.position_high]
    rw [List.getElem?_eq_none (by omega)]
    rfl
  · simp only [L.position_padding]
    rw [List.getElem?_eq_none (by omega)]
    rfl

/-- The bootstrap and the intended exterior present the same bit list to the native header copy. -/
theorem observed_exterior (L : WireLayout (R+1) r link) (bits : List Bool) (len : bits.length=L.header)
    (payload : Fin (R+1) → Fin (R+1) → ℕ → Bool) (block : Block (R+1)) :
    observed L (exterior L bits len payload) block = bits := by
  unfold observed
  rw [exterior_header]
  have list {H : ℕ} (h : bits.length=H) : List.ofFn (headerBits bits h)=bits := by
    subst H
    exact List.ofFn_getElem
  exact list len

/-- This startup uses only the shared header length and physical block capacity. -/
theorem bootstrap_observed (bits : List Bool) (three : 2 < R+1) (room : bits.length ≤ r*link) (block : Block (R+1)) :
    observed (headerOnly bits three room) (bootstrap bits) block = bits := by
  rw [← exterior_zero (headerOnly bits three room) bits rfl]
  exact observed_exterior _ _ _ _ _

end TeamContraction.JointHeader

end BorderVNP
end Computability
end OAI
