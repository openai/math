import OAI.LinearAlgebra.SpectralBooks.Fermion.FermionLaurent
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickClearTerm
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickCommutator
import OAI.LinearAlgebra.SpectralBooks.Fermion.WickSum

/-! # The integral shifted coefficient identity

At a fixed Laurent coefficient, all non-full matchings have their poles
cleared. The surviving full matchings contribute the signed Pascal determinant
times the identity in the input and output states.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace Fermion

open Filter LaurentPolynomial

theorem laurentCrossingIdentity : LaurentCrossingIdentity := by
  intro i j a b hi hij _ s
  have hl {x : State} (c : Bool) : (fieldWord c x).length = x.card := by simp [fieldWord]
  have htag (x : State) (c : Bool) : ∀ f ∈ fieldWord c x, f.1 = c := by
    intro f hf
    obtain ⟨t, _, rfl⟩ := List.mem_map.mp hf
    rfl
  have hne : fieldWord false i ≠ [] := by
    intro h
    have h' := hl (x := i) false
    rw [h, List.length_nil] at h'
    exact hi.card_pos.ne h'
  have het := eventually_cleared_wick_sum i j a b hij s (order (weight i) (weight j)) fun p ↦ by
    have h := p.eventually_clear_term (by simpa only [hl] using hij) hne (htag i false)
      (htag j true) a b s
    by_cases hp : p.residual = [] <;> simpa [hp, wordWeight_fieldWord] using h
  filter_upwards [het] with N hN
  intro α β ha hb
  rw [fieldMatrix_commutator_apply N i j α β]
  simpa only [ha, hb] using hN

end Fermion

end SpectralBooks
end LinearAlgebra
end OAI
