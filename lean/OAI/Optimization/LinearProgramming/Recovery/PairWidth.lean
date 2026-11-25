import Mathlib.Algebra.Polynomial.Eval.Defs
import OAI.Optimization.LinearProgramming.Geometry.ResidualBitsCommon
import OAI.Optimization.LinearProgramming.Recovery.PairBuilderBounds
import OAI.Optimization.LinearProgramming.Recovery.PairWidthAlgebra

/-! A closed register-width polynomial for both row-basis calls and the
intervening residual projector in the recovery pair builder. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder

open RAM Compression Elimination
open _root_.OAI.Optimization.LinearProgramming.Geometry

private theorem rowWidth_at {a n e z E : ℕ} (ha : a≤z) (hn : n≤z) (hz : 0<z)
    (h₃ : 3≤E) (he : e≤E) : rowWidth a n e ≤ 128*E*z^4 := by
  have hB : max 3 e≤E := max_le h₃ he
  have hd : dotBitBound n (max 3 e) (max 3 e) ≤ dotBitBound z E E := by
    unfold dotBitBound; gcongr
  have hb : detRegisterBits a (dotBitBound n (max 3 e) (max 3 e)) ≤ detRegisterBits z (dotBitBound z E E) := by
    unfold detRegisterBits; gcongr
  apply le_trans _ (rowWidth_majorant z E hz (by omega))
  unfold rowWidth rowBasisBits
  exact max_le (hB.trans (by omega)) (max_le (hd.trans (by omega)) (hb.trans (by omega)))

private theorem residualWidth_at {a n e z E : ℕ} (ha : a≤z) (hn : n≤z) (hz : 0<z)
    (hE : 0<E) (he : e≤E) : residualWidth a n e ≤ 1300*E*z^6 := by
  have hm : gramWorkspaceBits a n e ≤ gramWorkspaceBits z z E := by
    dsimp only [gramWorkspaceBits,gramDetBits,dotBitBound]; gcongr
  have hw := hm.trans (gramWorkspaceBits_majorant z E hz hE)
  have hpr : gramProjectorBits a n e ≤ gramWorkspaceBits a n e := by
    dsimp only [gramProjectorBits,gramWorkspaceBits]; omega
  have he' : e≤E*z^6 := he.trans (Nat.le_mul_of_pos_right E (pow_pos hz _))
  have hp : 0<E*z^6 := Nat.mul_pos hE (pow_pos hz _)
  rw [Nat.mul_assoc] at hw ⊢
  unfold residualWidth ResidualBitsCommon.residualEntryBits
  exact max_le (max_le (by omega) (by omega)) (max_le (by omega) (by omega))

private theorem composedWidth_at (row residual : ℕ → ℕ → ℕ → ℕ)
    (row_bound : ∀ {a n e z E : ℕ}, a ≤ z → n ≤ z → 0 < z → 3 ≤ E → e ≤ E →
      row a n e ≤ 128*E*z^4)
    (residual_bound : ∀ {a n e z E : ℕ}, a ≤ z → n ≤ z → 0 < z → 0 < E → e ≤ E →
      residual a n e ≤ 1300*E*z^6)
    (h n e z : ℕ) (hh : h ≤ z) (hn : n ≤ z) (he : e ≤ z) (hz : 0 < z) :
    max (max 3 (row h n e)) (max (residual n n (row h n e))
      (row n n (residual n n (row h n e)))) ≤ 64000000*z^15 := by
  have first : row h n e ≤ 384*z^5 := by
    calc
      _ ≤ 128*(3*z)*z^4 := row_bound hh hn hz (Nat.le_mul_of_pos_right 3 hz)
        (he.trans (Nat.le_mul_of_pos_left z (by decide : 0 < 3)))
      _ = _ := by ring
  have middle : residual n n (row h n e) ≤ 499200*z^11 := by
    calc
      _ ≤ 1300*(384*z^5)*z^6 := residual_bound hn hn hz
        (Nat.mul_pos (by decide : 0 < 384) (pow_pos hz 5)) first
      _ = _ := by ring
  have last : row n n (residual n n (row h n e)) ≤ 63897600*z^15 := by
    calc
      _ ≤ 128*(499200*z^11)*z^4 := row_bound hn hn hz
        ((by decide : 3 ≤ 499200).trans (Nat.le_mul_of_pos_right 499200 (pow_pos hz 11))) middle
      _ = _ := by ring
  have three : 3 ≤ 64000000*z^15 :=
    (by decide : 3 ≤ 64000000).trans (Nat.le_mul_of_pos_right 64000000 (pow_pos hz 15))
  exact max_le (max_le three (first.trans (Nat.mul_le_mul (by decide : 384 ≤ 64000000)
    (Nat.pow_le_pow_right hz (by decide : 5 ≤ 15)))))
    (max_le (middle.trans (Nat.mul_le_mul (by decide : 499200 ≤ 64000000)
      (Nat.pow_le_pow_right hz (by decide : 11 ≤ 15))))
      (last.trans (Nat.mul_le_mul_right _ (by decide : 63897600 ≤ 64000000))))

/-- Two storage-preserving basis extractions and the exact residual Gram projection
have scalar width of degree fifteen in the dimensions and the original entry width. -/
theorem pairWidth_polynomial (h n e : ℕ) :
    pairWidth h n e ≤ polyBound 64000000 15 (h+n+e) := by
  dsimp only [pairWidth, polyBound]
  exact composedWidth_at rowWidth residualWidth (@rowWidth_at) (@residualWidth_at)
    h n e (h+n+e+1) (by omega) (by omega) (by omega) (by omega)

/-- The polynomial witness for the recovery builder's register encodings. -/
noncomputable def pairWidthPolynomial : Polynomial ℕ :=
  Polynomial.C 64000000 * (Polynomial.X+1)^15

private theorem eval_width_polynomial (c degree x : ℕ) :
    (Polynomial.C c * (Polynomial.X+1)^degree : Polynomial ℕ).eval x = polyBound c degree x := by
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, polyBound]

theorem pairWidth_le_eval (h n e : ℕ) :
    pairWidth h n e ≤ pairWidthPolynomial.eval (h+n+e) :=
  (pairWidth_polynomial h n e).trans_eq (eval_width_polynomial 64000000 15 (h+n+e)).symm

end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI
