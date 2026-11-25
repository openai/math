import OAI.Optimization.LinearProgramming.Lattice.BitRadix
import OAI.Optimization.LinearProgramming.Lattice.BitDriverWire
import OAI.Optimization.LinearProgramming.Lattice.ProjectionGram
import OAI.Optimization.LinearProgramming.Lattice.QuerySize

/-! Polynomial packet widths at the outer boundary of the adaptive rounding machine. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace RoundWidth
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open WithLp

def parameter (p M : ℕ) : ℕ := p+M.size+12
def digitCap (p M : ℕ) : ℕ := searchDenominator p M^(p+1)+1

noncomputable def widthBound : Polynomial ℕ := Polynomial.X+5*Polynomial.X^2+3
noncomputable def rowBound : Polynomial ℕ := Polynomial.X*(2*(widthBound+3)+2)+1
noncomputable def rowsBound : Polynomial ℕ := Polynomial.X*(2*rowBound+2)+1
noncomputable def envBound : Polynomial ℕ := 14*Polynomial.X+7+rowsBound
noncomputable def coefficientBound : Polynomial ℕ :=
  ((2*Polynomial.X+2*widthBound)*Polynomial.X+1)*(Polynomial.X*Polynomial.X+1)
noncomputable def answerBound : Polynomial ℕ := Polynomial.X*(2*(widthBound*Polynomial.X)+2)

def DirectionBounds {p : ℕ} (M : ℕ) (old : List (Fin p → ℤ)) : Prop :=
  ∀ z∈old, ∀ i, (z i).natAbs ≤ digitCap p M

theorem directionBounds_of_abs {p M : ℕ} {old : List (Fin p → ℤ)}
    (h : ∀ z∈old, ∀ i, |z i| ≤ (digitCap p M : ℤ)) : DirectionBounds M old := by
  intro z hz i
  have h' := h z hz i
  rw [Int.abs_eq_natAbs] at h'
  exact_mod_cast h'

theorem dim_le (p M : ℕ) : p ≤ parameter p M := by unfold parameter; omega

theorem width_le (p M : ℕ) : radixWidth p M ≤ widthBound.eval (parameter p M) := by
  let N := parameter p M
  have he : precisionExponent p M ≤ 5*N := by dsimp [N,parameter,precisionExponent]; omega
  have hp : p+1 ≤ N := by dsimp [N,parameter]; omega
  have hM : M.size ≤ N := by dsimp [N,parameter]; omega
  have hmul := Nat.mul_le_mul he hp
  change _ ≤ widthBound.eval N
  simp only [widthBound,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_pow,radixWidth]
  nlinarith

theorem digitCap_size (p M : ℕ) : (digitCap p M).size ≤ radixWidth p M :=
  Nat.size_le.mpr (digit_bounds p M).1

private theorem signedSize (z : ℤ) : (intCode z).length = z.natAbs.size+3 := by
  simp [intCode,intData,prodCode,pairBits_length,boolCode,Nat.size_eq_bits_len]
  omega

theorem row_length {p M : ℕ} (z : Fin p → ℤ) (hz : ∀ i, (z i).natAbs ≤ digitCap p M) :
    (intRowCode (List.ofFn z)).length ≤ rowBound.eval (parameter p M) := by
  let N := parameter p M
  have he (i : Fin p) (_ : i∈List.finRange p) : (intCode (z i)).length ≤ widthBound.eval N+3 := by
    rw [signedSize]
    exact Nat.add_le_add_right (((Nat.size_le_size (hz i)).trans (digitCap_size p M)).trans (width_le p M)) _
  have hl := listCode_length_map_bound intCode z (List.finRange p) (widthBound.eval N+3) he
  rw [← List.ofFn_eq_map] at hl
  simp only [List.length_finRange] at hl
  change _ ≤ rowBound.eval N
  simp only [rowBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  exact hl.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (dim_le p M)) _)

theorem table_length {p M : ℕ} (old : List (Fin p → ℤ)) (hlen : old.length ≤ p)
    (hd : DirectionBounds M old) : (intMatrixCode (old.map List.ofFn)).length ≤ rowsBound.eval (parameter p M) := by
  let N := parameter p M
  have he (z : Fin p → ℤ) (hz : z∈old) := row_length z (hd z hz)
  have hl := listCode_length_map_bound intRowCode List.ofFn old (rowBound.eval N) he
  change _ ≤ rowsBound.eval N
  simp only [rowsBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  exact hl.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ (hlen.trans (dim_le p M))) _)

theorem residual_width {p M : ℕ} (old : List (Fin p → ℤ)) (hlen : old.length ≤ p)
    (hd : DirectionBounds M old)
    (hli : LinearIndependent ℝ (fun i : Fin old.length => toLp 2 (realCoordinates (old.get i))))
    (i j : Fin p) : (integralRows (rationalResidualMatrix old) i j).natAbs.size ≤
      coefficientBound.eval (parameter p M) := by
  let N := parameter p M
  have hp : p ≤ N := dim_le p M
  have hc : (digitCap p M).size ≤ widthBound.eval N := (digitCap_size p M).trans (width_le p M)
  have hr := integralRows_natAbs_size (fun i j => rationalResidualMatrix old i j)
    (rationalResidualMatrix_entry_size old hlen hd hli) i j
  apply hr.trans
  simp only [coefficientBound,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  gcongr

theorem answer_length {p M : ℕ} (old : List (Fin p → ℤ)) (hlen : old.length ≤ p)
    (hd : DirectionBounds M old) :
    (Driver.signPacket (Horner.assembleWord ((p,radixWidth p M),old.map List.ofFn))).length ≤
      answerBound.eval (parameter p M) := by
  let N := parameter p M
  let w := radixWidth p M
  have hw : w ≤ widthBound.eval N := width_le p M
  have hlen' : old.length ≤ N := hlen.trans (dim_le p M)
  have hrow (z : Fin p → ℤ) (hz : z∈old.reverse) (i : Fin p) : |z i| < (2:ℤ)^w :=
    int_abs_lt_two_pow_iff.mpr ((Nat.size_le_size (hd z (by simpa using hz) i)).trans (digitCap_size p M))
  have hval (i : Fin p) :
      (radixVector ((2:ℤ)^w) old.reverse i).natAbs.size ≤ widthBound.eval N*N := by
    have h := abs_radixVector_lt (by positivity : 0 < (2:ℤ)^w) old.reverse hrow i
    rw [← pow_mul,List.length_reverse] at h
    exact (int_abs_lt_two_pow_iff.mp h).trans (Nat.mul_le_mul hw hlen')
  rw [Horner.assembleWordPack,Driver.signPacket_pack,signRowWord_length]
  calc
    _ ≤ ∑ _ : Fin p, (2*(widthBound.eval N*N)+2) :=
      Finset.sum_le_sum (fun i _ => Nat.add_le_add_right (Nat.mul_le_mul_left _ (hval i)) _)
    _ = p*(2*(widthBound.eval N*N)+2) := by simp
    _ ≤ N*(2*(widthBound.eval N*N)+2) := Nat.mul_le_mul_right _ (dim_le p M)
    _ = answerBound.eval N := by simp [answerBound]

end RoundWidth
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
