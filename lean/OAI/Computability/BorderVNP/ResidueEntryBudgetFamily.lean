import OAI.Computability.BorderVNP.ResidueEntryBudgetJoint

/-! # Singly exponential coefficient and exponent bounds suffice for short matrix entries

The available hypotheses are on binary sizes of the field cardinality, extraction power,
chart radius and interval. They yield polynomial query and guess lengths, gate count and
serialized advice length simultaneously in the manuscript's size parameter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueEntryBudget

open VPVNP ResidueEntryField

/-- If the coefficient field embeds in the interpolation field, both basis dimensions
and the modulus fit the one interpolation-field bit bound. -/
theorem field_dimensions {p D d : ℕ} [Fact p.Prime] {E K : Type*} [Field E] [Field K]
    [Fintype E] [Fintype K] [Algebra (ZMod p) E] [Algebra (ZMod p) K] (φ : E →+* K)
    (B₀ : Module.Basis (Fin D) (ZMod p) E) (B : Module.Basis (Fin d) (ZMod p) K) :
    D ≤ Nat.clog 2 (Fintype.card K) ∧ d ≤ Nat.clog 2 (Fintype.card K) ∧ p ≤ Fintype.card K := by
  have hk := Nat.le_pow_clog Nat.one_lt_two (Fintype.card K)
  have he := (Fintype.card_le_of_injective φ φ.injective).trans hk
  exact ⟨(dimensions_le B₀ he).1,(dimensions_le B hk).1,by
    simpa only [ZMod.card] using Fintype.card_le_of_injective _ (algebraMap (ZMod p) K).injective⟩

private theorem size_pred_le_clog (n : ℕ) : (n-1).size ≤ Nat.clog 2 n := by
  apply Nat.size_le.mpr
  have := Nat.le_pow_clog Nat.one_lt_two n
  have : 0 < 2^Nat.clog 2 n := by positivity
  omega

/-- Under the paper's dimension and logarithmic cardinality/radius bounds all four
entry resources are polynomially bounded in the original index. Here `card` is the
interpolation field's cardinality, so `(card-1-1).size` is the width of the Fermat
exponent used by the circuit for the inverse of a nonzero grid element. -/
theorem polynomiallyBounded_paperResources {h charts s q H width card D d p labels m : ℕ → ℕ}
    (hh : PolynomiallyBounded h) (hc : PolynomiallyBounded charts) (hs : PolynomiallyBounded s)
    (hq : PolynomiallyBounded fun n => Nat.clog 2 (q n))
    (hH : PolynomiallyBounded fun n => Nat.clog 2 (H n))
    (hwidth : PolynomiallyBounded fun n => Nat.clog 2 (width n))
    (hf : PolynomiallyBounded fun n => Nat.clog 2 (card n))
    (hL : PolynomiallyBounded labels) (hm : PolynomiallyBounded m)
    (hfield : ∀ n, D n ≤ Nat.clog 2 (card n) ∧ d n ≤ Nat.clog 2 (card n) ∧ p n ≤ card n) :
    let idx := fun n => ResidueIndex.workWidth (q n) (H n) (width n)
    let b := fun n => Nat.clog 2 (p n)
    let w := fun n => b n + 1
    let dag := fun n => gadgetBudget (charts n) (h n) (s n) (q n - 1).size (card n - 1 - 1).size
      (idx n) (labels n) (m n)
    let gates := fun n => jointBudget (h n) (idx n) (D n) (d n) (w n) (labels n) (m n) (dag n)
    let u := fun n => queryWidth (h n) (idx n) (D n) (labels n) (m n)
    let v := fun n => guessWidth (h n) (d n) (w n) (b n)
    PolynomiallyBounded u ∧ PolynomiallyBounded v ∧ PolynomiallyBounded gates ∧
      PolynomiallyBounded fun n => adviceBits (u n) (v n) (gates n) := by
  have hi := ResidueIndex.polynomiallyBounded_workWidth hq hH hwidth
  have hb := hf.of_le (fun n => Nat.clog_mono_right 2 (hfield n).2.2)
  have hw := hb.add (.const 1)
  have hD := hf.of_le fun n => (hfield n).1
  have hd := hf.of_le fun n => (hfield n).2.1
  have hqbits := hq.of_le fun n => size_pred_le_clog (q n)
  have hfbits := hf.of_le fun n => (Nat.size_le_size (show card n-1-1 ≤ card n-1 by omega)).trans
    (size_pred_le_clog (card n))
  have hdag := polynomiallyBounded_gadgetBudget hc hh hs hqbits hfbits hi hL hm
  have hgate := polynomiallyBounded_jointBudget hh hi hD hd hw hL hm hdag
  have hu := polynomiallyBounded_queryWidth hh hi hD hL hm
  have hv := polynomiallyBounded_guessWidth hh hd hw hb
  exact ⟨hu,hv,hgate,polynomiallyBounded_adviceBits hu hv hgate⟩

end ResidueEntryBudget

end BorderVNP
end Computability
end OAI
