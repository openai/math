import OAI.Hierarchy.DescentCoarseCoordinates

namespace OAI
/-! # Summing exactly the donor coordinates of a single measured block -/
namespace Hierarchy.DescentPlainTerminal
open DescentColonies DescentIssuedFallbackPanel
open scoped Classical BigOperators
noncomputable section
variable {m c : ℕ} (small : c≤m)

/-- Conditional sums over the input ordering keep their original strict-order
tests. Only the points in the measured common cell are visited. -/
theorem sum_cell (L : Equiv.Perm (Block m)) (a : Block c) (chosen : Block m→Prop)
    (w : Block m→ℕ) (all : ∀x,chosen x→high small (L x)=a) :
    (∑x∈Finset.univ.filter chosen,w x)=
      ∑j : Block (m-c), if chosen (L.symm (join small a j)) then w (L.symm (join small a j)) else 0 := by
  rw [←Finset.sum_filter]
  apply Finset.sum_bij' (fun x _=> low (L x)) (fun j _=>L.symm (join small a j))
  · intro x hx
    have c₀:=(Finset.mem_filter.mp hx).2
    have orig : L.symm (join small a (low (L x)))=x := by
      rw [←all x c₀,join_high_low,Equiv.symm_apply_apply]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [orig]
    exact c₀
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
  · intro x hx
    rw [←all x (Finset.mem_filter.mp hx).2,join_high_low,Equiv.symm_apply_apply]
  · intro j hj
    rw [Equiv.apply_symm_apply,low_join]
  · intro x hx
    rw [←all x (Finset.mem_filter.mp hx).2,join_high_low,Equiv.symm_apply_apply]

end
end Hierarchy.DescentPlainTerminal

end OAI
