import OAI.Hierarchy.DescentOrdinaryReturnBill
import OAI.Hierarchy.DescentOrdinaryArgumentWidths
import Mathlib.Algebra.Order.Floor.Div

namespace OAI
/-! # The bought post-packing supplies all four final metadata lookup apertures -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentPacking.PackedMatch.Local.Stage.DateBill
noncomputable section
set_option quotPrecheck false

theorem filled_rows {H G h u m : ℕ} (pos : 0<u) (wide : 2*u≤h) (filled : h≤ m*u) :
    H*chunks G m≤words H G h u :=by
  let M:=lanes h u
  have positive : 0<M:=(occupancy h u pos wide).1
  have lePitch : M≤ m:=by
    apply Nat.div_le_of_le_mul
    simpa only [Nat.mul_comm m (2*u)] using filled.trans (Nat.mul_le_mul_left m (by omega : u≤2*u))
  have mpos:=positive.trans_le lePitch
  have cover : G≤M*chunks G M:=ThreeFlat.Routing.CallPool.count_le_batches_mul G M positive
  have cap : G≤ m*chunks G M:=cover.trans (Nat.mul_le_mul_right _ lePitch)
  have fewer : chunks G m≤chunks G M :=(ceilDiv_le_iff_le_mul mpos).2 cap
  exact (Nat.mul_le_mul_left H fewer).trans (Nat.le_add_left ..)

variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)
variable (A : ArgumentEntry v) (other : ℕ)
local notation "ext" => max (v.fullArgumentUnit A) other
local notation "W" => v.withFundedArguments ext A
local notation "M" => (v.fundedClip ext).postPitch

theorem funded_shelf_rows (u : ℕ) (pos : 0<u) (wide : 2*u≤v.payload)
    (physical : (W).resolver.lanes=M) (filled : v.payload≤M*u) : (W).ShelfRows u 1 :=by
  have «meta»:=v.funded_metadata_widths A other
  have final:=(v.funded_final_widths A other).1
  have old : (W).nodeChart.lanes=M:=physical
  refine ⟨pos,wide,?_,?_,?_,?_,?_⟩
  · rw [old]
    have bitRoom := «meta».1
    simp only [Nat.mul_add,Nat.mul_one] at bitRoom
    exact bitRoom
  · rw [old]
    exact «meta».2.1
  · rw [old]
    exact «meta».2.2
  · rw [physical]
    exact final
  · change (W).resolver.hosts*chunks (W).resolver.groups (W).resolver.lanes ≤ 1*words _ _ _ _
    rw [physical,Nat.one_mul]
    exact filled_rows pos wide filled

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
