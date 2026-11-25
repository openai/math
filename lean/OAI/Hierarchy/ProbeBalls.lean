import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace OAI
/-! # Finite bounded-radius balls in the physical column graph -/

namespace Hierarchy.AdaptiveProbe
open scoped Classical
noncomputable section

variable {V : Type*} [DecidableEq V]

/-- Each step permits waiting at the current column or traversing a genuine
horizontal tile or join. It is independent of the number of columns. -/
def neighborhood (next : V → Finset V) (x : V) : ℕ → Finset V
  | 0 => {x}
  | r+1 => (neighborhood next x r).biUnion fun y => insert y (next y)

theorem mem_neighborhood_step (next : V → Finset V) (x y : V) (r : ℕ) :
    y ∈ neighborhood next x (r+1) ↔ ∃ z ∈ neighborhood next x r, y=z ∨ y ∈ next z := by
  simp [neighborhood]

theorem neighborhood_card (next : V → Finset V) (degree : ℕ) (h : ∀ y, (next y).card ≤ degree)
    (x : V) (r : ℕ) : (neighborhood next x r).card ≤ (degree+1)^r := by
  induction r with
  | zero => simp [neighborhood]
  | succ r ih =>
    rw [neighborhood,pow_succ]
    exact (Finset.card_biUnion_le_card_mul _ _ _ fun z _ =>
      (Finset.card_insert_le ..).trans (Nat.add_le_add_right (h z) 1)).trans
      (Nat.mul_le_mul_right _ ih)

/-- The ball can be followed from either end when physical links are undirected. -/
theorem neighborhood_concat (next : V → Finset V) {x y z : V} {r s : ℕ}
    (xy : y ∈ neighborhood next x r) (yz : z ∈ neighborhood next y s) :
    z ∈ neighborhood next x (r+s) := by
  induction s generalizing z with
  | zero =>
    have eq : z=y := Finset.mem_singleton.mp yz
    subst z
    simpa using xy
  | succ s ih =>
    obtain ⟨u,hu,step⟩ := (mem_neighborhood_step next y z s).mp yz
    exact (mem_neighborhood_step next x z (r+s)).mpr ⟨u,ih hu,step⟩

theorem neighborhood_symm (next : V → Finset V) (symm : ∀ x y, x ∈ next y → y ∈ next x)
    {x y : V} {r : ℕ} (inside : y ∈ neighborhood next x r) : x ∈ neighborhood next y r := by
  induction r generalizing y with
  | zero => simpa [neighborhood,eq_comm] using inside
  | succ r ih =>
    obtain ⟨z,hz,stay|edge⟩ := (mem_neighborhood_step next x y r).mp inside
    · subst y
      exact (mem_neighborhood_step next z x r).mpr ⟨x,ih hz,Or.inl rfl⟩
    · have step : z ∈ neighborhood next y 1 := by
        apply (mem_neighborhood_step next y z 0).mpr
        exact ⟨y,Finset.mem_singleton_self _,Or.inr (symm _ _ edge)⟩
      simpa only [Nat.add_comm 1 r] using neighborhood_concat next step (ih hz)

/-- The symmetric conflict list for radius-r tests is bounded by (D+1)^(2r).
It covers every pair of tests sharing any physical column or site. -/
theorem overlap_implies_neighbor (next : V → Finset V) (symm : ∀ x y, x ∈ next y → y ∈ next x)
    (r : ℕ) {x y z : V} (a : z ∈ neighborhood next x r) (b : z ∈ neighborhood next y r) :
    y ∈ neighborhood next x (2*r) := by
  simpa [two_mul] using neighborhood_concat next a (neighborhood_symm next symm b)

/-- A path-price witness on every true horizontal link transfers to all pairs
of columns in the ball, simultaneously on every signed layer. -/
theorem ball_path_bound {P : V → V → ℕ → Prop} (next : V → Finset V)
    (self : ∀ x, P x x 0) (link : ∀ x y, y ∈ next x → P x y 1)
    (append : ∀ x y z r s, P x y r → P y z s → P x z (r+s))
    (pad : ∀ x y r, P x y r → P x y (r+1)) {x y : V} {r : ℕ}
    (inside : y ∈ neighborhood next x r) : P x y r := by
  induction r generalizing y with
  | zero =>
    have eq : y=x := Finset.mem_singleton.mp inside
    subst y
    exact self x
  | succ r ih =>
    obtain ⟨z,hz,stay|edge⟩ := (mem_neighborhood_step next x y r).mp inside
    · subst y
      exact pad x z _ (ih hz)
    · exact append x z y r 1 (ih hz) (link z y edge)

end
end Hierarchy.AdaptiveProbe

end OAI
