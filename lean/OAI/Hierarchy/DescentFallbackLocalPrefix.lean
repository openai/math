import OAI.Hierarchy.DescentPlainTerminal
import OAI.Hierarchy.DescentCoarseCellSum

namespace OAI
/-! # Both actual balanced row prefixes within the chosen coarse cell -/

namespace Hierarchy.DescentPlainTerminal
open DescentColonies DescentGL DescentIssuedFallbackPanel DescentFineTerminals
open scoped Classical BigOperators
noncomputable section
variable {m c : ℕ} (small : c≤m)

variable {V : Type} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V] in
theorem baseSum_local (b : V→ℕ) (L : Layout m) (wt : V→Block m→ℕ) (v : V) (x : Block m) (lo : c≤b v) :
    baseSum b L wt v x=
      ∑j : Block (m-c),let y:=(rearrange L).symm (join small (high small (rearrange L x)) j)
        if y<x ∧ group (b v) (rearrange L y)=group (b v) (rearrange L x) then wt v y else 0 := by
  let chosen (y : Block m) := y<x ∧ group (b v) (rearrange L y)=group (b v) (rearrange L x)
  have stays (y : Block m) (hy : chosen y) :
      high small (rearrange L y)=high small (rearrange L x) :=
    Fin.ext (group_ancestor lo hy.2)
  have cell := sum_cell small (rearrange L) (high small (rearrange L x)) chosen (wt v) stays
  refine Eq.trans ?_ (cell.trans ?_)
  · unfold baseSum
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext y
    simp only [Finset.mem_filter,chosen]
  · refine Finset.sum_congr rfl ?_
    intro j _
    by_cases hy : chosen ((rearrange L).symm (join small (high small (rearrange L x)) j))
    · dsimp only [chosen] at hy ⊢; simp only [ite_eq_left hy]
    · dsimp only [chosen] at hy ⊢; simp only [ite_eq_right hy]

omit [Fintype V] [DecidableEq V] in
theorem leafSum_local (near : V→Finset V) (b : V→ℕ) (wt : V→Block m→ℕ)
    (f D B : ℕ) (room : ∀v x,wt v x≤B) (v : V) (x : Block m) (lo : c≤b v) :
    let groupAt:=leafKey (D:=D) (f:=f) near wt room b v
    leafSum b near wt f D B room v x=
      ∑j : Block (m-c),let y:=join small (high small x) j
        if y<x ∧ groupAt y=groupAt x then wt v y else 0 := by
  intro groupAt
  let chosen (y : Block m) := y<x ∧ groupAt y=groupAt x
  have stays (y : Block m) (hy : chosen y) : high small y=high small x := by
    have d_eq:=congrArg Prod.fst hy.2
    have grp:=congrArg Prod.snd hy.2
    change leaf (D:=D) (f:=f) near wt room b v y=leaf (D:=D) (f:=f) near wt room b v x at d_eq
    change group (leaf (D:=D) (f:=f) near wt room b v y) y=
      group (leaf (D:=D) (f:=f) near wt room b v x) x at grp
    rw [d_eq] at grp
    have depth : b v≤leaf (D:=D) (f:=f) near wt room b v x := le_max_left _ _
    exact Fin.ext (group_ancestor (lo.trans depth) grp)
  have cell := sum_cell small (Equiv.refl (Block m)) (high small x) chosen (wt v) stays
  refine Eq.trans ?_ (cell.trans ?_)
  · unfold leafSum
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext y
    simp only [Finset.mem_filter, chosen, groupAt]
  · refine Finset.sum_congr rfl ?_
    intro j _
    dsimp only [chosen, groupAt, Equiv.refl_symm, Equiv.refl_apply]
    split
    · exact ite_eq_left ‹_›
    · exact ite_eq_right ‹_›

end
end Hierarchy.DescentPlainTerminal

end OAI
