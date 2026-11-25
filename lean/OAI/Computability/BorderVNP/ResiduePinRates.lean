import OAI.Computability.BorderVNP.BranchCurveBoxOrder
import OAI.Computability.BorderVNP.ResidueEntryFieldBudget

/-!
# Binary widths on the actual selected residue box

One bound on the coordinate count and on the binary lengths of the scalar
field, input degree and total chart degree suffices for the box addresses,
the Cartier power and the finite interpolation field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueRates

open Branch ResidueBox ResiduePins VPVNP

/-- Bit bound for the chosen extraction power on inputs with common size ceiling M. -/
def powerBits (M : ℕ) :=
  let b := 2*M+7
  let c := ((b+2)*(4*(M+3))+2)*(M+1)
  M+(c+b)+c*M

/-- Bit and dimension ceiling for the interpolation field, the power and the box. -/
def gridBits (M : ℕ) := powerBits M + 2*M + 8

theorem polynomiallyBounded_gridBits : PolynomiallyBounded gridBits := by
  let n := PolynomiallyBounded.id
  let k := PolynomiallyBounded.const
  have b := ((k 2).mul n).add (k 7)
  have c := (((b.add (k 2)).mul ((k 4).mul (n.add (k 3)))).add (k 2)).mul (n.add (k 1))
  exact (((n.add (c.add b)).add (c.mul n)).add ((k 2).mul n)).add (k 8)

/-- The padded pin has `h+2` fields of `M+6` bits. The same numerical ceiling
also bounds the binary lengths of the interpolation interval and its field. -/
theorem chart_bit_bounds {h L S card q D N M : ℕ} (hh : h ≤ M) (hL : L ≤ 2^M)
    (hS : S ≤ 2^M) (hE : card ≤ 2^M) (hD : D ≤ M)
    (hq : q ≤ card * max (chartBoxPoleBudget h (radius L S) S) 1)
    (hN : N ≤ card * ((q-1)*S+1)) :
    let H := radius L S
    let width := (q-1)*S
    D ≤ 2^(M+6) ∧ 2*H < 2^(M+6) ∧
      Nat.clog 2 q ≤ powerBits M ∧ Nat.clog 2 H ≤ gridBits M ∧
      Nat.clog 2 width ≤ gridBits M ∧ Nat.clog 2 N ≤ gridBits M ∧
      (h+2)*(M+6) ≤ (M+2)*(M+6) := by
  intro H width
  have hm : M ≤ 2^M := (Nat.lt_two_pow_self : M < 2^M).le
  have hp : 0 < 2^M := pow_pos (by decide) _
  have hH : H ≤ 2^(M+4) := by
    dsimp only [H, radius]
    rw [pow_add]
    omega
  have hdeg : boxEliminantInputDegree h H S ≤ 2^(2*M+7) := by
    dsimp only [boxEliminantInputDegree]
    have ha : h*H ≤ 2^M * 2^(M+4) := Nat.mul_le_mul (hh.trans hm) hH
    have hs : 2^M ≤ 2^M * 2^M := Nat.le_mul_of_pos_right _ hp
    rw [two_mul, pow_add, pow_add]
    rw [pow_add] at ha hH
    norm_num only [Nat.reducePow] at ha hH ⊢
    rw [← Nat.mul_assoc] at ha
    omega
  have hb := chart_box_pin_power_bits hE hdeg hq
  have hq' : Nat.clog 2 q ≤ powerBits M := by
    dsimp only [powerBits]
    apply hb.trans
    gcongr
  have hQ : q ≤ 2^powerBits M := (Nat.le_pow_clog (by decide) q).trans (Nat.pow_le_pow_right (by decide) hq')
  have hw : width ≤ 2^(powerBits M + M) := by
    rw [pow_add]
    exact Nat.mul_le_mul ((Nat.sub_le ..).trans hQ) hS
  have hN' : N ≤ 2^(powerBits M+2*M+1) := by
    have hw1 : width+1 ≤ 2^(powerBits M+M+1) := by
      rw [pow_succ]
      have : 0 < 2^(powerBits M+M) := pow_pos (by decide) _
      omega
    have hn := hN.trans (Nat.mul_le_mul hE hw1)
    rw [← pow_add] at hn
    convert hn using 1
    congr 1
    omega
  have h6 : M+6 ≤ gridBits M := by unfold gridBits; omega
  have hd6 := hD.trans (hm.trans (Nat.pow_le_pow_right (by decide : 0 < 2) (show M ≤ M+6 by omega)))
  have ht6 : 2*H < 2^(M+6) := by
    rw [pow_add] at hH ⊢
    omega
  refine ⟨hd6,ht6,hq', (Nat.clog_le_of_le_pow hH).trans (by omega),?_,?_, Nat.mul_le_mul_right _ (by omega)⟩
  · exact (Nat.clog_le_of_le_pow hw).trans (by unfold gridBits; omega)
  · exact (Nat.clog_le_of_le_pow hN').trans (by unfold gridBits; omega)

end ResidueRates

end BorderVNP
end Computability
end OAI
