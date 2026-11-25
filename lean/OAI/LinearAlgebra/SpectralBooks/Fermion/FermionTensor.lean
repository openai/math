import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionFactor
import OAI.LinearAlgebra.SpectralBooks.ShiftedCrossing.ShortenTensor

/-! # The two integral fermionic channels over every coefficient field -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
namespace Fermion

open scoped BigOperators Classical

/-- Reindex the ordered states and both channels by finite ordinals, then
reduce the integral identity over the chosen field. -/
def Factors.toFactorization {I A P M : Type} [Fintype I] [Fintype A] [DecidableEq I] [DecidableEq A] [Fintype P] [Fintype M]
    (F : Factors I A P M) (hF : ∀ i j α β, F.entry i j α β = if i=j ∧ α=β then 1 else 0)
    (K : Type*) [Field K] : ShiftedCrossing.Factorization K
      (Fintype.card I) (Fintype.card A) (Fintype.card P) (Fintype.card M) := by
  let c (T : Type) [Fintype T] := (Fintype.equivFin T).symm
  apply ShiftedCrossing.Factorization.ofInt
    (fun i α k ↦ F.plusLeft (c I i) (c A α) (c P k))
    (fun j β k ↦ F.plusRight (c I j) (c A β) (c P k))
    (fun i β k ↦ F.minusLeft (c I i) (c A β) (c M k))
    (fun j α k ↦ F.minusRight (c I j) (c A α) (c M k))
  intro i j α β
  have h := hF (c I i) (c I j) (c A α) (c A β)
  simp only [Equiv.apply_eq_iff_eq, Factors.entry] at h
  by_cases he : i = j ∧ α = β <;> simp only [he, ↓reduceIte] at h ⊢ <;> rw [← h] <;> congr 1
  all_goals
    apply Fintype.sum_equiv (Fintype.equivFin _) _ _
    simp [c]

/-- Integer channel sizes for input doubled energies `H,E` and integer shift `s`. -/
theorem finite_factorization {C : State → State → ℤ} {Y : ModeMatrix}
    (h : CoefficientIdentity C Y) (hzero : ∀ i j : State, i.card ≠ j.card → C i j = 0)
    (H E : ℕ) (s : ℤ) (B : Matrix (Label H) (Label H) ℤ)
    (hB : B * (Matrix.of fun i j : Label H ↦ C i.val j.val) = 1) (K : Type*) [Field K] :
    Nonempty (ShiftedCrossing.Factorization K ((states H).card-1) (states E).card
      ((H+1)^3 * (states (E+H+2*s)).card) ((H+1)^3 * (states (E+H-2*s)).card)) := by
  obtain ⟨F, hF⟩ := exists_integral_factors h hzero H E s B hB
  simpa only [Finset.card_erase_of_mem (empty_mem_states_nat H), card_channel, PlusStates, MinusStates, Fintype.card_coe] using
    (⟨F.toFactorization hF K⟩ : Nonempty _)

end Fermion

end

end SpectralBooks
end LinearAlgebra
end OAI
