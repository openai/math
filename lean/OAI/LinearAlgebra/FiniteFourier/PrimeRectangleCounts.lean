import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleCharged
import Mathlib.Data.Fintype.Powerset

/-! # Cardinality and incidence bounds for charged rectangles -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped Classical

variable {L b : ℕ}

private theorem card_chargedSupports_le (L t : ℕ) :
    Fintype.card ((j : Fin (t+1)) × ChargedSupport L j.val) ≤ 2 ^ L := by
  let f : ((j : Fin (t+1)) × ChargedSupport L j.val) → Finset (Fin L) := fun R => R.2.val
  have hf : Function.Injective f := by
    rintro ⟨j,S⟩ ⟨k,T⟩ he
    change S.val = T.val at he
    have hj : S.val.card = j.val := (Finset.mem_powersetCard.mp S.property).2
    have hk : T.val.card = k.val := (Finset.mem_powersetCard.mp T.property).2
    have hjk : j = k := Fin.ext (hj.symm.trans ((congrArg Finset.card he).trans hk))
    subst k
    exact congrArg (Sigma.mk j) (Subtype.ext he)
  simpa using Fintype.card_le_of_injective f hf

/-- A support of size at most `t` admits at most `(2^b)^t` common restrictions. -/
theorem card_chargedRectangle_le (L b t : ℕ) :
    Fintype.card (ChargedRectangle L b t) ≤ 2^L * (2^b)^t := by
  classical
  calc
    _ = ∑ j : Fin (t+1), ∑ S : ChargedSupport L j.val,
        Fintype.card (S.val → BitLetter b) := by simp only [ChargedRectangle, Fintype.card_sigma]
    _ ≤ ∑ j : Fin (t+1), ∑ _S : ChargedSupport L j.val, (2^b)^t := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro S _
      have hS := (Finset.mem_powersetCard.mp S.property).2
      simpa [BitLetter, hS] using Nat.pow_le_pow_right (by positivity : 0 < 2^b) (Nat.le_of_lt_succ j.isLt)
    _ = Fintype.card ((j : Fin (t+1)) × ChargedSupport L j.val) * (2^b)^t := by
      simp [Fintype.card_sigma, Finset.sum_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ (card_chargedSupports_le L t)

/-- A fixed label determines the letters for each choice of common positions. -/
theorem card_chargedEndpoint_incidence_le (v : BitLabel L b) (t : ℕ) :
    Fintype.card {R : ChargedRectangle L b t // v ∈ chargedEndpoint R} ≤ 2^L := by
  let f : {R : ChargedRectangle L b t // v ∈ chargedEndpoint R} →
      ((j : Fin (t+1)) × ChargedSupport L j.val) := fun R => ⟨R.val.1, R.val.2.1⟩
  apply (Fintype.card_le_of_injective f ?_).trans (card_chargedSupports_le L t)
  rintro ⟨⟨j,S,w⟩,hw⟩ ⟨⟨k,T,z⟩,hz⟩ he
  change (⟨j,S⟩ : (n : Fin (t+1)) × ChargedSupport L n.val) = ⟨k,T⟩ at he
  cases he
  apply Subtype.ext
  have hwz : w = z := funext fun i => (hw i).trans (hz i).symm
  cases hwz
  rfl

end FiniteFourier
end LinearAlgebra
end OAI
