import OAI.LinearAlgebra.FiniteFourier.CompanionCNF.CompanionSignedWitnessCNF
import OAI.Computability.BorderVNP.SignedCNF

/-! # Polynomial choice tables for the companion's signed family

The integer signed-CNF theorem supplies one presentation of the original
machine's polynomial in all characteristics. Its first-satisfied-literal
choice table therefore feeds the planar independent-set reduction directly.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
namespace CompanionCNF

open OAI.LinearAlgebra.SpectralBooks.IndependentSetGraph MvPolynomial Filter
open OAI.Computability.VPVNP OAI.Computability.VPVNP.HardnessCNF OAI.Computability.BorderVNP
open scoped Classical BigOperators

/-- The integral coefficients, signs and variable positions are those of the
companion polynomial `Pstar` at the given input length. -/
theorem choicePresentation_Pstar (R : Type*) [CommRing R] :
    HasPolynomialChoicePresentation R (fun n => map (Int.castRingHom R) (Pstar n)) := by
  obtain ⟨k, cs, pw, hk, hl, hc, atom, value⟩ := SignedCNF.exists_Pstar_encoding
  have mapped (n : ℕ) (i : Fin (k n)) : ∃ a : ProjectionAtom R (Fin n × Bool),
      atomPolynomial a = map (Int.castRingHom R) (pw n i) := by
    rcases atom n i with h | h | ⟨v,h⟩
    · exact ⟨.inr 1, by simp [atomPolynomial,h]⟩
    · exact ⟨.inr (-1), by simp [atomPolynomial,h]⟩
    · exact ⟨.inl v, by simp [atomPolynomial,h]⟩
  choose w spec using mapped
  have bound := ((PolynomiallyBounded.const 3).mul hk).add (hc.mul (hl.add (.const 1)))
  obtain ⟨A,b,N,late⟩ := bound
  refine ⟨A+1,b+1,Nat.succ_pos _,Nat.succ_pos _,?_⟩
  filter_upwards [eventually_ge_atTop (max 1 N)] with n hn
  refine ⟨table (cs n).get (w n), ?_, ?_⟩
  · rw [← value n]
    rw [table_integer (cs n) (w n) (pw n) (spec n),weightedCNF]
    apply congrArg (MvPolynomial.map (σ := Fin n × Bool) (Int.castRingHom R))
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : Satisfies (cs n) x
    · exact (ite_eq_left (show ∀ c ∈ cs n, ∃ lit ∈ c, x lit.1 = lit.2 from h)).trans (ite_eq_left h).symm
    · exact (ite_eq_right (show ¬∀ c ∈ cs n, ∃ lit ∈ c, x lit.1 = lit.2 from h)).trans (ite_eq_right h).symm
  · exact (table_list_size_le _ _).trans ((late n ((le_max_right ..).trans hn)).trans
      (Nat.mul_le_mul (Nat.le_succ A) (Nat.pow_le_pow_right ((le_max_left ..).trans hn) (Nat.le_succ b))))

end CompanionCNF

end

end FiniteFourier
end LinearAlgebra
end OAI
