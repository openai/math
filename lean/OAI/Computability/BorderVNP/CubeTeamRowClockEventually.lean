import OAI.Computability.BorderVNP.CubeTeamCheckedRowClock
import OAI.Computability.BorderVNP.CubeGroupNativeEventually

/-! # Eventual exterior-width clock of the actual owned-row traversal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRowClock

open Physical GroupWeights TeamScales Filter

/-- At the rounded group scales, even one processor's exterior width covers
all ordered endpoint-label candidates once the processor length is large. -/
theorem eventually_labelSquare_le_exterior {α ξ : ℝ} (hα : 0 < α) (a : ℕ)
    (gap : 8*α*a < 1-ξ) :
    ∀ᶠ k : ℕ in atTop, ∀ r : ℕ, 1 ≤ r → ((alphabet α k)^a)^2 ≤ exterior ξ r k := by
  have pos : 0 < 1-ξ := lt_of_le_of_lt (by positivity) gap
  filter_upwards [eventually_labelCount_power hα a 2, eventually_rpow_gap gap 2,
    eventually_exterior_volume_lower pos] with k labels room exteriorRoom
  have eq : 4*α*a*(2 : ℕ) = 8*α*a := by push_cast; ring
  rw [eq] at labels
  intro r hr
  have h := exteriorRoom r 1 hr le_rfl
  rw [Nat.mul_one] at h
  have le : (labelCount α a k : ℝ)^2 ≤ exterior ξ r k := by linarith only [labels,room,h]
  simp only [labelCount,Nat.cast_pow] at le
  exact_mod_cast le

universe u v

/-- For a fixed packet identity, every sufficiently large processor length
gives a clock at most a fixed multiple of `X₀` on every physical team. The
capacity guard follows from the balanced labels and the actual passing lengths. -/
theorem eventually_physicalTeamTicks {F : Type u} [Field F] {n : ℕ} {η α ξ : ℝ}
    (p : PacketFormat F n η) (hη : 0 < η) (fixed : 100*(2/Real.sqrt (n+1)+η) < 1/10^6)
    (hα : 0 < α) (hξ : ξ < α/3) (gap : 8*α*(n+1) < 1-ξ) :
    ∀ᶠ k : ℕ in atTop, ∀ (r : ℕ) (l : GroupWeights.Layout) (teams : TeamNative.Layout) (blocks : ℕ)
      (orig mem : ℕ → ℕ) (A : Type v) [Fintype A] (D : LengthDeclaration n l.groups)
      (select : Packet n l.groups blocks → Selector n p.K p.h)
      (label : Fin l.cells → Label (n+1) l.groups) (recv : A → Fin l.cells) (w : A → ℕ),
      1 ≤ r → (teams.r+1 : ℝ) ≤ (k : ℝ)^(2*α) → l.groups = alphabet α k →
      blocks = blocksFor (exterior ξ r k*(teams.r+1) : ℕ) (p.h*p.b) (l.groups^(n+1)) →
      ScheduleResult l teams orig mem → PhysicalImage l orig blocks p.b p.K p.h D label recv w →
      passesLengths p.b p.s select D →
      (∀ u, Balancing.load (Balancing.datum (fun j : Balancing.Bits w => recv j.1) u) label ≤
        4*((exterior ξ r k*(teams.r+1) : ℕ) : ℝ)/((l.groups^(n+1) : ℕ) : ℝ)) →
      (∑ a, w a) ≤ 3*(teams.r+1)*r*literal α k →
      ∀ (team : Fin (teams.r+1)) (dispatch : TeamRowPrepare.Layout),
      dispatch.d = l.groups → dispatch.teamID = team.val →
      TeamRows.ticks dispatch (fun u => mem (teams.owners+u))
        (roleAt (physicalRoleTicks blocks p.b p.h p.K p.s D.1 : Fin l.groups → Fin l.groups → ℕ)) ≤
        2*physicalCoefficient n p.b p.h p.K p.s*exterior ξ r k := by
  have gap' : 8*α*((n+1 : ℕ) : ℝ) < 1-ξ := by simpa only [Nat.cast_add,Nat.cast_one] using gap
  filter_upwards [p.eventually_budget_passes hη fixed hα hξ gap,
    eventually_labelSquare_le_exterior hα (n+1) gap', eventually_ge_atTop 1] with k budget labels hk
  intro r l teams blocks orig mem A _ D select label recv w hr hR groups blockCount result image pass balanced data
    team dispatch hd ht
  have ok := budget r l teams blocks orig mem A D select label recv w hr hR groups blockCount result image pass balanced data
  have pos : 0 < l.groups := groups ▸ Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hk : (0:ℝ) < k) _)
  have volume : (l.groups^(n+1))^2 ≤ exterior ξ r k := groups ▸ labels r hr
  apply (checkedTeamTicks_le_sq result image team dispatch hd ht (exterior ξ r k) p.s p.blockPositive pos ok).trans
  calc
    _ ≤ physicalCoefficient n p.b p.h p.K p.s*(exterior ξ r k+exterior ξ r k) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_right volume _)
    _ = _ := by ring

end Cube.TeamRowClock

end BorderVNP
end Computability
end OAI
