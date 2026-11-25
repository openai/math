import OAI.ThreeFlat.Diagonal.PhysicalLocalTariff

namespace OAI
/-! # Cofinal word bounds for the two finite physical tile menus -/

noncomputable section
namespace Hierarchy.TraceDistribution.Physical

open ThreeFlat Diagonal Diagonal.PhysicalStage
open Filter
open scoped Classical BigOperators Topology

variable {F : Type} [Field F] [Fintype F] (B : PhysicalStage.Block F)

omit [Fintype F] in
theorem fresh_price_scale (w : ℕ) : 2 ≤ B.localCoefficient*(16*w^10+1)^3 := by
  have floor : 2 ≤ B.localCoefficient := by unfold Block.localCoefficient; omega
  exact floor.trans (Nat.le_mul_of_pos_right _ (by positivity))

omit [Fintype F] in
theorem fixed_tile_word_caps :
    ∀ᶠ w : ℕ in atTop,
      (∀ i : Fin (B.shrink.more.length+1), (B.shrink.block (B.shrink.row i)).bitCap ≤ 2^w) ∧
      (∀ i : Fin (B.refresh.last+1), (B.refresh.block i).bitCap ≤ 2^w) := by
  let small := ∑ i : Fin (B.shrink.more.length+1), (B.shrink.block (B.shrink.row i)).bitCap
  let large := ∑ i : Fin (B.refresh.last+1), (B.refresh.block i).bitCap
  filter_upwards [eventually_ge_atTop (small+large)] with w hw
  have bound : w ≤ 2^w := Nat.lt_two_pow_self.le
  constructor
  · intro i
    have one : (B.shrink.block (B.shrink.row i)).bitCap ≤ small :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (B.shrink.block (B.shrink.row j)).bitCap) (Finset.mem_univ i)
    exact one.trans ((Nat.le_add_right small large).trans (hw.trans bound))
  · intro i
    have one : (B.refresh.block i).bitCap ≤ large :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (B.refresh.block j).bitCap) (Finset.mem_univ i)
    exact one.trans ((Nat.le_add_left large small).trans (hw.trans bound))

omit [Fintype F] in
theorem fixed_tile_caps :
    ∀ᶠ w : ℕ in atTop,
      (∀ i : Fin (B.shrink.more.length+1), (B.shrink.block (B.shrink.row i)).bitCap ≤ 2^(w^10)) ∧
      (∀ i : Fin (B.refresh.last+1), (B.refresh.block i).bitCap ≤ 2^(w^10)) := by
  filter_upwards [fixed_tile_word_caps B] with w caps
  have room : 2^w ≤ 2^(w^10) := Nat.pow_le_pow_right (by decide : 0 < 2)
    (Nat.le_self_pow (by decide : (10:ℕ)≠0) w)
  exact ⟨fun i => (caps.1 i).trans room, fun i => (caps.2 i).trans room⟩


end Hierarchy.TraceDistribution.Physical

end
end OAI
