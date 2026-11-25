import OAI.Computability.BorderVNP.CubeGroupPacketFormat
import OAI.Computability.BorderVNP.CubeGroupNativeRoom
import OAI.Computability.BorderVNP.CubeGroupChargeRoom
import OAI.Computability.BorderVNP.CubeGroupWeightCheckedSchedule

/-! # Eventual acceptance of the physical team-weight guard

Fix the packet format over the field before taking the processor length large.
The same threshold works for every team multiplicity, passing selector
declaration, balanced labeling, and admissible delivery inventory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Physical TeamScales Filter

universe u v

/-- At the paper's rounded dimensions, a verified group schedule satisfies both
native capacity tests on its actual output memory. -/
theorem PacketFormat.eventually_budget_passes {F : Type u} [Field F] {n : ℕ} {η α ξ : ℝ}
    (p : PacketFormat F n η) (hη : 0 < η) (fixed : 100*(2/Real.sqrt (n+1)+η) < 1/10^6)
    (hα : 0 < α) (hξ : ξ < α/3) (hgap : 8*α*(n+1) < 1-ξ) :
    ∀ᶠ k : ℕ in atTop, ∀ (r : ℕ) (l : Layout) (teams : TeamNative.Layout) (blocks : ℕ)
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
      (⟨teams.r+1,exterior ξ r k,teams.totals⟩ : TeamBudget.Layout).Passes mem := by
  have gap : 8*α*((n+1 : ℕ) : ℝ) < 1-ξ := by simpa only [Nat.cast_add,Nat.cast_one] using hgap
  filter_upwards [eventually_group_charge_room hα hξ (n+1) (p.h*p.b) p.expansion p.blockPositive gap,
    eventually_ge_atTop 1] with k room hk
  intro r l teams blocks orig mem A _ D select label recv w hr hR groups blockCount result image pass balanced data
  obtain ⟨small,localCap,pad,dataCap⟩ := room r (teams.r+1) hr (by omega) (by exact_mod_cast hR)
  rw [← groups] at small localCap pad
  rw [← blockCount] at pad
  have hd : 0 < l.groups := by
    rw [groups]
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hk : (0:ℝ) < k) _)
  have cap := result.team_le_exterior image p.s select pass (exterior ξ r k) p.expansion
    (by dsimp [PacketFormat.expansion]; omega) hd η hη.le fixed p.expansion_le p.width p.selector balanced
    (by simpa only [Nat.cast_add,Nat.cast_one] using small) localCap pad (dataCap _ data)
  exact result.passes_of_physical image (exterior ξ r k) cap

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
