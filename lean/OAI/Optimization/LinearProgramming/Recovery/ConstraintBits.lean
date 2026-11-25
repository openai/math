import OAI.Optimization.LinearProgramming.Recovery.ConstraintBases
import OAI.Optimization.LinearProgramming.Recovery.Layout
import OAI.Optimization.LinearProgramming.PrimalDual.InputSize

/-! Entry heights for the physical row-packing/Gram route. Both rounds use inputs
from the original stored pair and freshly installed zero/one flags. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery

open Matrix RAM Polynomial
open _root_.OAI.Optimization.LinearProgramming.Geometry
open scoped Matrix

private def dotExpr {R : Type*} [CommSemiring R] (s b c : R) := 3+2*s*(b+c+1)
private def detExpr {R : Type*} [CommSemiring R] (s b : R) := 3+s^2+b*s+2*b*s^3

/-- Coefficient envelope for an identity-minus-projector entry from a matrix bounded by B. -/
def residualBitFormula {R : Type*} [CommSemiring R] (N B : R) :=
  let inv := 2*detExpr N (dotExpr N B B)
  3+2*(3+dotExpr N (dotExpr N B inv) B)

def packedBitFormula {R : Type*} [CommSemiring R] (N B : R) :=
  let first := B+residualBitFormula N B
  first+residualBitFormula N first

noncomputable def packedLPBitPolynomial : Polynomial ℕ := packedBitFormula (2*X+2) (X+3)

theorem packedLPBitPolynomial_eval (L : ℕ) :
    packedLPBitPolynomial.eval L=packedBitFormula (2*L+2) (L+3) := by
  simp only [packedLPBitPolynomial,packedBitFormula,residualBitFormula,dotExpr,detExpr,eval_add,eval_mul,
    eval_pow,eval_ofNat,eval_X,eval_one]

private theorem dotExpr_mono {r s a b c d : ℕ} (hr : r ≤ s) (ha : a ≤ b) (hc : c ≤ d) :
    dotExpr r a c ≤ dotExpr s b d :=
  Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hr)
    (Nat.add_le_add_right (Nat.add_le_add ha hc) 1)) 3

private theorem detExpr_mono {r s a b : ℕ} (hr : r ≤ s) (ha : a ≤ b) :
    detExpr r a ≤ detExpr s b :=
  Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_left (Nat.pow_le_pow_left hr 2) 3)
    (Nat.mul_le_mul ha hr)) (Nat.mul_le_mul (Nat.mul_le_mul_left 2 ha) (Nat.pow_le_pow_left hr 3))

theorem kernelRows_bits {r n B N : ℕ} (D : Matrix (Fin r) (Fin n) ℚ)
    (hr : r ≤ N) (hn : n ≤ N) (hD : ∀ i j,ratBits (D i j) ≤ B) (i j : Fin n) :
    ratBits (kernelRows D i j) ≤ residualBitFormula N B := by
  have a := computeGramProjector_bits D hD i j
  have b : ratBits ((1 : Matrix (Fin n) (Fin n) ℚ) i j) ≤ 3 := by
    rw [Matrix.one_apply]; split <;> decide
  have c := PrimalDual.ratBits_sub_le ((1 : Matrix (Fin n) (Fin n) ℚ) i j) (computeGramProjector D i j)
  rw [kernelRows,tabulateRect_eq,Matrix.sub_apply]
  have gram : dotExpr n B B ≤ dotExpr N B B := dotExpr_mono hn le_rfl le_rfl
  have inv : 2*detExpr r (dotExpr n B B) ≤ 2*detExpr N (dotExpr N B B) :=
    Nat.mul_le_mul_left 2 (detExpr_mono hr gram)
  have proj : gramProjectorBits r n B ≤ dotExpr N (dotExpr N B (2*detExpr N (dotExpr N B B))) B :=
    dotExpr_mono hr (dotExpr_mono hr le_rfl inv) le_rfl
  exact c.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (Nat.add_le_add b (a.trans proj))) 3)

theorem maskedEquations_bits {r n B : ℕ} (E : Matrix (Fin r) (Fin n) ℚ) (S : Finset (Fin n))
    (h : ∀ i j,ratBits (E i j) ≤ B) (b : 3 ≤ B) :
    ∀ i j,ratBits (maskedEquations E S i j) ≤ B := by
  have h0 : ratBits 0 ≤ B := (by decide : ratBits 0 ≤ 3).trans b
  have hid (i j : Fin n) : ratBits ((1 : Matrix (Fin n) (Fin n) ℚ) i j) ≤ B := by
    rw [Matrix.one_apply]; split
    · exact (by decide : ratBits 1 ≤ 3).trans b
    · exact h0
  have hP : (Presentation.fromKernel E).entriesSatisfy (fun x=>ratBits x ≤ B) := ⟨h,hid⟩
  exact (Presentation.restrict_entries hP h0 S).1

/-- During all LP decisions the opposite unreduced row matrix is either an original
input row or one residual row. Repeated support tests never iterate the width recurrence. -/
theorem packed_query_entries {r s n B N : ℕ} (D : Matrix (Fin r) (Fin n) ℚ) (opposite : Matrix (Fin s) (Fin n) ℚ)
    (S : Finset (Fin n)) (hB : 3 ≤ B) (hr : r ≤ N) (_hs : s ≤ N) (hn : n ≤ N)
    (hD : ∀ i j,ratBits (D i j) ≤ B) (picked : ∀ i j,ratBits (opposite i j) ≤ B ∨
      ∃ a b, opposite i j=kernelRows D a b) :
    (∀ i j,ratBits (maskedEquations opposite S i j) ≤ B+residualBitFormula N B) ∧
    ∀ {t : ℕ} (Q : Matrix (Fin t) (Fin n) ℚ), t ≤ N →
      (∀ i,∃ k,Q.row i=(maskedEquations opposite S).row k) →
      ∀ i j, ratBits (kernelRows Q i j) ≤ packedBitFormula N B := by
  have opp i j : ratBits (opposite i j) ≤ B+residualBitFormula N B := by
    rcases picked i j with h | ⟨a,b,h⟩
    · omega
    · rw [h]; exact (kernelRows_bits D hr hn hD a b).trans (Nat.le_add_left _ _)
  have cut := maskedEquations_bits opposite S opp (by omega)
  refine ⟨cut,?_⟩
  intro t Q hQ sub i j
  have qbits (a : Fin t) (b : Fin n) : ratBits (Q a b) ≤ B+residualBitFormula N B := by
    obtain ⟨c,h⟩ := sub a
    exact (congrArg ratBits (congrFun h b)) ▸ cut c b
  exact (kernelRows_bits Q hQ hn qbits i j).trans (Nat.le_add_left _ _)

end Recovery
end LinearProgramming
end Optimization
end OAI
