import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic

namespace OAI
/-! # Unique occurrences in a short aperture containing holes and repeated neighbors -/
namespace Hierarchy.DescentFallbackLeafScan
open scoped Classical
noncomputable section
variable {V : Type} [DecidableEq V] {Δ : ℕ} (peer : V→Fin Δ→Option V)
def first (v : V) (j : Fin Δ) : Option V :=
  if ∃i : Fin Δ,i<j ∧ peer v i=peer v j then none else peer v j

theorem first_one (v x : V) (live : ∃j,peer v j=some x) : ∃j,first peer v j=some x := by
  let xs:=(Finset.univ.filter (fun j : Fin Δ=>peer v j=some x))
  have exists' : xs.Nonempty := by
    obtain ⟨j,hit⟩ := live
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩⟩
  let j:=xs.min' exists'
  have good := (Finset.mem_filter.mp (xs.min'_mem exists')).2
  have before : ¬∃i : Fin Δ,i<j ∧ peer v i=peer v j := by
    rintro ⟨i,lt,same⟩
    exact (not_lt_of_ge (xs.min'_le i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,same.trans good⟩))) lt
  refine ⟨j,?_⟩
  rw [first,ite_eq_right before]
  exact good

theorem first_real {v x : V} {i : Fin Δ} (hit : first peer v i=some x) : peer v i=some x := by
  unfold first at hit
  split at hit <;> simp_all

theorem first_unique {v x : V} {i j : Fin Δ} (a : first peer v i=some x) (b : first peer v j=some x) : i=j := by
  have same:=(first_real peer a).trans (first_real peer b).symm
  rcases lt_trichotomy i j with lt|eqn|gt
  · simp [first,show ∃t : Fin Δ,t<j ∧ peer v t=peer v j from ⟨i,lt,same⟩] at b
  · exact eqn
  · simp [first,show ∃t : Fin Δ,t < i ∧ peer v t=peer v i from ⟨j,gt,same.symm⟩] at a

end
end Hierarchy.DescentFallbackLeafScan

end OAI
