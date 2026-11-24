import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod

/-!
# Independence of the color bits in Appendix C

A position in Lemma C.1 of *VP and VNP differ over every field* has one bit
per base color and a separate outgoing-slot coordinate. Fixing the endpoint
types of a translated arc fixes precisely two distinct color bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SlotPacking

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Restricting a function away from its prescribed coordinates forgets exactly
the values that are forced. -/
private def freeBits (s : Finset I) (v : I → ZMod 2) :
    {u : I → ZMod 2 // ∀ i ∈ s, u i = v i} ≃ (↥sᶜ → ZMod 2) where
  toFun u i := u.1 i
  invFun f := ⟨fun i ↦ if hi : i ∈ s then v i else f ⟨i, Finset.mem_compl.mpr hi⟩,
    fun i hi ↦ by simp [hi]⟩
  left_inv u := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · simp [hi, u.property i hi]
    · simp [hi]
  right_inv f := by
    funext i
    simp [Finset.mem_compl.mp i.property]

/-- Exact number of bit vectors with prescribed values on any subset of colors. -/
theorem card_prescribedBits (s : Finset I) (v : I → ZMod 2) :
    Fintype.card {u : I → ZMod 2 // ∀ i ∈ s, u i = v i} = 2 ^ (Fintype.card I - s.card) := by
  rw [Fintype.card_congr (freeBits s v), Fintype.card_fun, Fintype.card_coe, Finset.card_compl,
    ZMod.card]

/-- One endpoint test cuts the color vectors in half. -/
theorem card_oneBit (i : I) (a : ZMod 2) :
    Fintype.card {u : I → ZMod 2 // u i = a} = 2 ^ (Fintype.card I - 1) := by
  simpa using card_prescribedBits ({i} : Finset I) (fun _ ↦ a)

/-- Prescribing the two endpoint types fixes two independent color bits. -/
theorem card_twoBits {i j : I} (hne : i ≠ j) (a b : ZMod 2) :
    Fintype.card {u : I → ZMod 2 // u i = a ∧ u j = b} = 2 ^ (Fintype.card I - 2) := by
  simpa [hne, Ne.symm hne] using
    card_prescribedBits ({i, j} : Finset I) (fun k ↦ if k = i then a else b)

/-- An arc translation may displace either endpoint test. -/
theorem card_translatedBits {i j : I} (hne : i ≠ j) (δ₁ δ₂ a b : ZMod 2) :
    Fintype.card {u : I → ZMod 2 // u i + δ₁ = a ∧ u j + δ₂ = b} =
      2 ^ (Fintype.card I - 2) := by
  simpa only [eq_sub_iff_add_eq] using card_twoBits hne (a - δ₁) (b - δ₂)

/-- Free choice of the independent outgoing slot multiplies the endpoint count
by the degree. -/
theorem card_translatedBits_slots {i j : I} (hne : i ≠ j) (δ₁ δ₂ a b : ZMod 2) (d : ℕ) :
    Fintype.card {p : (I → ZMod 2) × Fin d // p.1 i + δ₁ = a ∧ p.1 j + δ₂ = b} =
      2 ^ (Fintype.card I - 2) * d := by
  rw [Fintype.card_congr (Equiv.prodSubtypeFstEquivSubtypeProd (β := Fin d)
    (p := fun u : I → ZMod 2 ↦ u i + δ₁ = a ∧ u j + δ₂ = b)), Fintype.card_prod]
  simp [card_translatedBits hne]

end SlotPacking

end VPVNP
end Computability
end OAI
