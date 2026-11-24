import OAI.Computability.VPVNP.JointScalarLeaf
import OAI.Computability.VPVNP.JointScalarResources

/-! # Uniform space and time budgets of the returning signed scalar callback -/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointScalar.Leaf

open RAMTape UniversalCountStack JointLabelSystem

/-- Unary width templates, copies, cleanup, and reduction modulo the field
prime have quadratic cost in the size of the caller's bank. -/
theorem localCost_le (L : Layout) (wr pay : ℕ) :
    let b := bankSize L wr pay
    localCost L b ≤ 6000*(b+1)^2 := by
  intro b
  have h1 : L.witnessBits+1+ (L.witnessBits+1) + L.degree + L.limbWidth + 1 ≤ 3*(b+1) := by
    dsimp [b,bankSize]; omega
  have h2 := SliceArithmeticSignedCount.callCap_le (L.witnessBits+1) (L.witnessBits+1) L.degree L.limbWidth
  have h3 := h2.trans (Nat.mul_le_mul_left 600 (Nat.pow_le_pow_left h1 2))
  have h4 : L.rowBits ≤ b := by dsimp [b,bankSize]; omega
  have h5 : 2*(L.witnessBits+1) + L.degree + L.limbWidth ≤ 3*(b+1) := by omega
  unfold localCost
  ring_nf at h3 ⊢
  omega

private theorem time_le {time T k work : ℕ} (h : time ≤ 2^T) (hk : k ≤ work) :
    2*time+k ≤ 2^(T+work+2) := by
  have hpos := Nat.one_le_two_pow (n := T)
  have hwpos := Nat.one_le_two_pow (n := work)
  have hsmall : work ≤ 2^work := Nat.lt_two_pow_self.le
  rw [pow_add,pow_add]
  norm_num
  nlinarith [Nat.mul_le_mul_left (2^T) hwpos, Nat.mul_le_mul_right (2^work) hpos]

set_option maxHeartbeats 400000 in
/-- The row/exponent/field widths may depend on the length. The polynomial
caps apply also when the selected prime and its field presentation depend
on the original circuit. -/
theorem budgets (V I : Type*) [Fintype V] [Fintype I] (F : I → MvPolynomial V ℤ) (c : ℕ)
    {width row degree limb : ℕ → ℕ} (hW : PolynomiallyBounded width) (hr : PolynomiallyBounded row)
    (he : PolynomiallyBounded degree) (hv : PolynomiallyBounded limb) :
    ∃ space exp : ℕ → ℕ, PolynomiallyBounded space ∧ PolynomiallyBounded exp ∧
      ∀ n (hn : 2 ≤ n) (p e v wr : ℕ), e ≤ degree n → v ≤ limb n → wr ≤ row n →
      let L := layout V I F c hn (width n) p e v
      let C := checker V I F c hn (width n)
      let b := bankSize L wr (FixedRows.labelTotal V n c * width n)
      let k := localCost L b
      max (stackLimit C) b + k ≤ space n ∧ 2*(2^L.witnessBits * perChoice C) + k ≤ 2^(exp n) := by
  obtain ⟨A,B,S,T,hA,_,hS,hT,bounds⟩ := Resources.checker_polynomial_resources V I F c hW
  let k (n : ℕ) := witnessWidth (ParseOracle.flagCount c n) (n^clockExponent) (motifWidth V I F)
  let b (n : ℕ) := row n + FixedRows.labelTotal V n c * width n + (n+highWidth I) + k n + limb n +
    degree n + degree n*limb n + A n + 2
  let work (n : ℕ) := 6000*(b n+1)^2
  have hk : PolynomiallyBounded k := (ParseOracle.flagCount_polynomial c).add
    ((PolynomiallyBounded.id.pow clockExponent).add (.const _))
  have hpay := (FixedRows.labelTotal_polynomiallyBounded V c).mul hW
  have hb : PolynomiallyBounded b := (((((((hr.add hpay).add (PolynomiallyBounded.id.add (.const _))).add hk).add hv).add he).add (he.mul hv)).add hA).add (.const 2)
  have hwork : PolynomiallyBounded work := (PolynomiallyBounded.const 6000).mul ((hb.add (.const 1)).pow 2)
  refine ⟨fun n => S n+b n+work n, fun n => T n+work n+2, (hS.add hb).add hwork,
    (hT.add hwork).add (.const 2), ?_⟩
  intro n hn p e v wr hed hvl hwr L C live cost
  obtain ⟨ha,_,hs,ht⟩ := bounds n hn
  have hwitness : L.witnessBits = k n := congrArg
    (fun f => witnessWidth f (n^clockExponent) (motifWidth V I F)) (ParseOracle.flags_eq_flagCount c n)
  have hbank : live ≤ b n := by
    change wr + _ + (n+highWidth I) + L.witnessBits + v + e + e*v + L.circuitAdvice.length + 2 ≤ _
    dsimp only [b]
    rw [hwitness]
    have hadvice : L.circuitAdvice.length ≤ A n := by
      dsimp only [L,layout,Layout.circuitAdvice]
      exact ha
    exact Nat.add_le_add_right (Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
        (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hwr _) _) _) hvl) hed)
        (Nat.mul_le_mul hed hvl)) hadvice) 2
  have hlocal : cost ≤ work n := (localCost_le L wr _).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hbank 1) 2))
  have htime : 2^L.witnessBits*perChoice C ≤ 2^(T n) := by
    dsimp only [L,layout,Layout.witnessBits,C]
    exact ht
  have hspace : stackLimit C ≤ S n := hs
  constructor
  · exact Nat.add_le_add (max_le (hspace.trans (Nat.le_add_right ..)) (hbank.trans (Nat.le_add_left ..))) hlocal
  · exact time_le htime hlocal

end JointScalar.Leaf

end VPVNP
end Computability
end OAI
