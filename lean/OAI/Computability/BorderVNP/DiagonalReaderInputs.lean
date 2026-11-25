import OAI.Computability.BorderVNP.DiagonalBranchScale

/-! # A common numerical bound for the inputs to the residue reader

The count of terms in a batch may be stretched-exponential. The reader
works with its binary length and with the polynomial-size table parameters.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial VPVNP
open scoped Classical

universe u v

variable {K : Type v} [Field K] {D m : ℕ} {ι : Type} {G : PaidIdentity K D m}
variable {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
variable {R : CommonField G aux q k s ord}

/-- Sum of the degrees of the actual chosen deformation equations. -/
noncomputable def AdvisedBranch.degreeSum (chart : AdvisedBranch R) : ℕ :=
  ∑ i, (signedEquations chart.E k s ord chart.advice i).totalDegree

theorem AdvisedBranch.degreeSum_le (chart : AdvisedBranch R) :
    chart.degreeSum ≤ pairedTableParameters (k+1) s * (2*k+3) := by
  apply (Finset.sum_le_sum (fun i _ => chart.degree i)).trans_eq
  simp

private theorem clog_two_le (n : ℕ) : Nat.clog 2 n ≤ n :=
  Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

/-- A ceiling for each input of the uniform finite-field matrix reader. -/
structure ReaderInputs [Fintype ι] (chart : AdvisedBranch R) (teams r multBits T : ℕ) : Prop where
  parameters : pairedTableParameters (k+1) s ≤ T
  degrees : Nat.clog 2 (chart.degreeSum + 1) ≤ T
  monomials : Nat.clog 2 (batchDegree teams (pairedTableParameters (k+1) s) r k + 1) ≤ T
  fieldBits : Nat.clog 2 (Nat.card chart.E) ≤ T
  gates : adviceGateBudget (2*(k+1)) k s ≤ T
  labels : Fintype.card (G.Entry ⊕ ι) ≤ T
  multiplicities : multBits ≤ T

/-- All seven reader inputs are bounded by one polynomial. The ceiling on the
batch count is logarithmic. The number of teams and the binary width of each
expanded multiplicity are separate parameters of the physical construction. -/
theorem common_reader_inputs [Fintype ι] (q : ℕ) [CharP K q] (G : PaidIdentity K D m)
    (aux : ι → K) :
    ∃ A C : ℕ, ∀ (k s teams r multBits M : ℕ), 2*(k+1)+s+1 ≤ M → teams ≤ M →
      Nat.clog 2 (r+1) ≤ M → multBits ≤ M →
      ∀ (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (F : Type u) [Field F] [CharP F q],
      BorderApprox (k+1) s (map (Int.castRingHom F) (Pstar (k+1))) →
        ∃ (R : CommonField G aux q k s ord) (chart : AdvisedBranch R),
          ReaderInputs chart teams r multBits (A*(M+1)^C) := by
  obtain ⟨A,C,chooseChart⟩ := joint_advice_of_borderApprox.{u,v} q G aux
  let u := Fintype.card (G.Entry ⊕ ι)
  let h (M : ℕ) := M*M + M^2*M^3
  let budget (M : ℕ) := h M + (h M*(M+3)+1) + (3*M+h M+4) + A*(M+1)^C + 64*(M+1)^5 + u + M
  have hi := PolynomiallyBounded.id
  have hh : PolynomiallyBounded h := (hi.mul hi).add ((hi.pow 2).mul (hi.pow 3))
  have degreeCost := (hh.mul (hi.add (.const 3))).add (.const 1)
  have bitCost := (((PolynomiallyBounded.const 3).mul hi).add hh).add (.const 4)
  have adviceCost := (PolynomiallyBounded.const A).mul ((hi.add (.const 1)).pow C)
  have gateCost := (PolynomiallyBounded.const 64).mul ((hi.add (.const 1)).pow 5)
  have hbudget : PolynomiallyBounded budget :=
    ((((((hh.add degreeCost).add bitCost).add adviceCost).add gateCost).add (.const u)).add hi)
  obtain ⟨A',C',uniform⟩ := hbudget.exists_global_bound
  refine ⟨A',C',?_⟩
  intro k s teams r mb M hM hteams hr hmb ord F _ _ hp
  obtain ⟨R,chart,hdata⟩ := chooseChart k s ord F hp
  have hn : k+1 ≤ M := by omega
  have hv : 2*(k+1) ≤ M := by omega
  let count := pairedTableParameters (k+1) s
  have hcount : count ≤ h M := by
    refine (pairedTableParameters_le ..).trans ?_
    change (2*(k+1)+s+1)*(2*(k+1)) + (k+1)^2*(2*(k+1)+s+1)^3 ≤ M*M+M^2*M^3
    gcongr
  have hsum := (clog_two_le (chart.degreeSum+1)).trans
    (Nat.succ_le_succ (chart.degreeSum_le.trans (Nat.mul_le_mul hcount (show 2*k+3 ≤ M+3 by omega))))
  have hdeg := batchDegree_bits teams count r k
  have hmono : Nat.clog 2 (batchDegree teams count r k + 1) ≤ 3*M+h M+4 := by
    have ht := clog_two_le (teams+1)
    have hh := clog_two_le (count+1)
    have hk := clog_two_le (2*k+2)
    omega
  let f := Nat.clog 2 (Nat.card chart.E)
  have hfield : f ≤ A*(M+1)^C := by
    have hf : f ≤ chartBitBudget u count f (Nat.clog 2 R.p) := by
      unfold chartBitBudget
      nlinarith [Nat.zero_le ((u+count*(count+3))*f)]
    exact (hf.trans hdata).trans (Nat.mul_le_mul_left A (Nat.pow_le_pow_left (by omega) _))
  have hg := adviceGateBudget_le hv (show k ≤ M by omega) (show s ≤ M by omega)
  have hu := uniform M
  dsimp only [budget] at hu
  refine ⟨R,chart,⟨hcount.trans ?_,hsum.trans ?_,hmono.trans ?_,hfield.trans ?_,hg.trans ?_,?_,?_⟩⟩
  all_goals omega

end Diagonal

end BorderVNP
end Computability
end OAI
