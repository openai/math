import OAI.LinearAlgebra.SpectralBooks.UniformDecorations.UniformDecorations
import OAI.LinearAlgebra.SpectralBooks.GridRecurrence

/-! # Universal map polynomials and the last compression round -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace UniformDecorations

open MvPolynomial PortGraph PlanarPatch Arithmetic Arithmetic.RecursiveBlock
open scoped BigOperators Classical

variable {F : Type*} [Field F]

/-- One independent scalar input for each address in the shared tables. -/
def Zpoly (N w : ℕ) : MvPolynomial (Address w) F := Z N w (fun θ x => X ⟨θ,x⟩)

/-- Substitution of the table entries commutes with the sum over map classes,
over all edge assignments and with every local product. -/
@[simp] theorem bind₁_Zpoly {I : Type*} {w : ℕ} (U : Address w → MvPolynomial I F) (N : ℕ) :
    bind₁ U (Zpoly N w) = Z N w (fun θ x => U ⟨θ,x⟩) := by
  simp only [Zpoly, Z, map_sum, classEval_out, eval, contraction, map_prod,
    View.localize, bind₁_X_right]

private theorem sum_formula {I L : Type*} [Fintype L] {W : ℕ} (hW : 1 ≤ W)
    (p : L → MvPolynomial I F) (hp : ∀ j, HasFormula W (p j)) :
    HasFormula ((Fintype.card L+1)*W) (∑ j, p j) := by
  let e := (Fintype.equivFin L).symm
  rw [← Equiv.sum_comp e p]
  exact HasFormula.finSum hW (fun j => hp (e j))

private theorem prod_formula {I : Type*} {n W : ℕ} (hW : 1 ≤ W)
    (p : Fin n → MvPolynomial I F) (hp : ∀ j, HasFormula W (p j)) :
    HasFormula ((n+1)*W) (∏ j, p j) := by
  induction n with
  | zero => simpa using (HasFormula.const (I := I) (1 : F)).mono hW
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    exact ((hp 0).mul (ih _ (fun i => hp i.succ))).mono (by nlinarith)

private theorem classEval_one_formula (w : ℕ) (M : MapClass 1) :
    HasFormula (2 * (2^(2*w) + 1))
      (classEval M (fun θ (x : Fin θ.degree.val → Bits w) => X (R := F) (⟨θ,x⟩ : Address w))) := by
  let r := M.out
  have hv : r.vertexCount.val ≤ 1 := Nat.le_of_lt_succ r.vertexCount.isLt
  have he : r.edgeCount.val ≤ 2 := Nat.le_of_lt_succ r.edgeCount.isLt
  let : DecidableEq (Fin r.edgeCount.val) := Classical.decEq _
  rw [classEval_out]
  unfold eval contraction
  apply (sum_formula (W := 2) (by decide) _ (fun x => ?_)).mono
  · change (Fintype.card (Fin r.edgeCount.val → Bits w) + 1) * 2 ≤ _
    simp only [Bits, Fintype.card_fun, Fintype.card_fin, ← pow_mul]
    have hle : 2 ^ (w * r.edgeCount.val) ≤ 2 ^ (2 * w) :=
      Nat.pow_le_pow_right (by decide) (by nlinarith only [Nat.mul_le_mul_left w he])
    omega
  · exact (prod_formula (W := 1) (by decide) _ (fun _ => HasFormula.input _)).mono (by omega)

/-- There are only constantly many one-vertex maps. A map with `N=1` has
at most two edges, including loops, so direct contraction has exponential
cost in the final table width. -/
theorem Zpoly_one_cost (w : ℕ) :
    polynomialProgramCost (Zpoly (F := F) 1 w) ≤
      2 ^ ((Fintype.card (MapClass 1) + 4) * (w+1)) := by
  obtain ⟨e, he, hc⟩ := sum_formula (F := F) (W := 2*(2^(2*w)+1)) (by exact Nat.mul_pos (by decide) (Nat.succ_pos _)) _ (classEval_one_formula w)
  let q := Family.expressions (fun _ : Unit => e)
  have hh := familyPolynomial_expressions (fun _ : Unit => e) ()
  change registerPolynomial q.program (q.output ()) = _ at hh
  have bound : polynomialProgramCost (Zpoly (F := F) 1 w) ≤ e.cost := by
    have h : registerPolynomial q.program (q.output ()) = Zpoly 1 w := hh.trans he
    have hh := polynomialProgramCost_le q.program (q.output ())
    rw [h] at hh
    change polynomialProgramCost _ ≤ q.cost at hh
    simpa [q, Family.cost_expressions] using hh
  apply (bound.trans ((Nat.le_succ _).trans hc)).trans
  let H := Fintype.card (MapClass 1)
  have h₁ : H+1 ≤ 2^H := Nat.lt_two_pow_self
  have h₂ : 2^(2*w)+1 ≤ 2^(2*w+1) := by rw [pow_succ]; have := Nat.two_pow_pos (2*w); omega
  calc
    (H+1)*(2*(2^(2*w)+1)) ≤ 2^H*(2*2^(2*w+1)) := by gcongr
    _ = 2^(H + (1 + (2*w+1))) := by simp only [pow_add, pow_one]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by dsimp [H]; nlinarith)

end UniformDecorations

end

end SpectralBooks
end LinearAlgebra
end OAI
