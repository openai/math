import OAI.ThreeFlat.Diagonal.DoublePorts
import OAI.ThreeFlat.ExpanderCloudConnected
import OAI.Computability.VPVNP.MotifSelector

namespace OAI
/-! # Connected selector ports from a real Poincaré bound -/

namespace ThreeFlat.Diagonal.DoublePorts
open Expander Computability.VPVNP
open scoped BigOperators Classical

/-- A symmetric regular matrix passing the scalar Poincaré bound yields the
incident anchors and the path connectivity needed by the selector check. -/
noncomputable def connectedSupply {m d : ℕ} (c : Fin m → Fin m → ℕ) (hd : 0 < d)
    (deg : ∀ i, ∑ j, c i j = d) (sym : ∀ i j, c i j = c j i) {γ : ℝ}
    (hb : Bound (transition c d) ℝ γ) : MotifSelector.Supply (Fin m) (Arc c) := by
  have out (i : Fin m) : ∃ j, 0 < c i j := by
    by_contra! h
    have zero (j : Fin m) : c i j = 0 := Nat.eq_zero_of_le_zero (h j)
    have bad := deg i
    simp only [zero, Finset.sum_const_zero] at bad
    omega
  choose next live using out
  refine ⟨arcStart, arcEnd, (fun i => ⟨(i,next i),⟨0,live i⟩⟩), (fun _ => Or.inl rfl), ?_⟩
  intro i j
  have path := connected_of_real_bound c sym hb i j
  induction path with
  | refl => exact .refl
  | @tail j k _ edge ih =>
    exact ih.tail ⟨⟨(j,k),⟨0,edge⟩⟩, Or.inl ⟨rfl,rfl⟩⟩

end ThreeFlat.Diagonal.DoublePorts

end OAI
