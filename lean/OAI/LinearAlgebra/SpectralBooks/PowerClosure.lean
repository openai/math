import OAI.LinearAlgebra.SpectralBooks.BorderRank
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Closure of the tensor-power span

Every linear equation on a tensor power pulls back to a polynomial equation
on the original tensor. Thus membership in a fixed linear span extends to the
Zariski closure of a rank locus.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open Foundation

variable {K X Y Z : Type*} [Field K] [Fintype X] [Fintype Y] [Fintype Z]

private theorem power_dual_is_polynomial (n : ℕ)
    (f : Module.Dual K (Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z))) :
    ∃ p : MvPolynomial (X × Y × Z) K, ∀ S : Tensor K X Y Z,
      tensorEval S p = f (Tensor.power S n) := by
  classical
  let e (x : Fin n → X) (y : Fin n → Y) (z : Fin n → Z) :
      Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z) :=
    fun x' y' z' => if x = x' ∧ y = y' ∧ z = z' then 1 else 0
  refine ⟨∑ x, ∑ y, ∑ z, MvPolynomial.C (f (e x y z)) *
    ∏ i : Fin n, MvPolynomial.X (x i, y i, z i), ?_⟩
  intro S
  have he : Tensor.power S n =
      ∑ x, ∑ y, ∑ z, (Tensor.power S n x y z) • e x y z := by
    funext x' y' z'
    simp [e, Finset.sum_apply, Pi.smul_apply, ite_and]
  rw [he]
  simp [tensorEval, Tensor.power, mul_comm]

/-- A linear span containing all powers of tensors of rank at most `r`
contains the powers of tensors in the Zariski closure of that rank locus. -/
theorem power_mem_span_of_closure {ι : Type*} {r n : ℕ} {T : Tensor K X Y Z}
    (hT : ∀ p : MvPolynomial (X × Y × Z) K,
      (∀ S : Tensor K X Y Z, S.RankAtMost r → tensorEval S p = 0) → tensorEval T p = 0)
    (W : ι → Tensor K (Fin n → X) (Fin n → Y) (Fin n → Z))
    (hW : ∀ S : Tensor K X Y Z, S.RankAtMost r →
      Tensor.power S n ∈ Submodule.span K (Set.range W)) :
    Tensor.power T n ∈ Submodule.span K (Set.range W) := by
  by_contra hn
  obtain ⟨f, hf, hker⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  obtain ⟨p, hp⟩ := power_dual_is_polynomial n f
  apply hf
  rw [← hp]
  apply hT
  intro S hS
  rw [hp, ← Submodule.mem_bot K, ← hker]
  exact ⟨_, hW S hS, rfl⟩

end SpectralBooks
end LinearAlgebra
end OAI
