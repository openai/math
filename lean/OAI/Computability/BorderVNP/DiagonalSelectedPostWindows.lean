import OAI.Computability.BorderVNP.RoutingISAScheduleClockSourceWindows
import OAI.Computability.BorderVNP.RoutingISASignedTaskArena

/-! # The three capacities of a returning signed subtotal in the common clock -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open TeamScales CellPacketGeometry
open private nat_le_ceiling nat_le_multiple_ceiling from OAI.Computability.BorderVNP.RoutingISAScheduleClockSourceWindows

/-- The published source bits fit the public window, and the original powers
and actual square group scan fit the local window of this same length. -/
theorem post_window_capacities {n r R a D p d gates inputs outputs field w powers packetBits : ℕ} {α ξ : ℝ}
    (hn : 1≤n) (hr : 1≤r) (hR : 1≤R) (hξ : ξ≤1) (hw : 1≤w) (hb : 1≤field)
    (emitted : Total p d ≤ outputs)
    (geometry : GeometryAdviceRate.ticks gates inputs outputs field w+packetBits ≤ r*width n (95/100:ℝ))
    (slots : powers ≤ r) :
    let P := ⌈publicWork a α r n R⌉₊
    let L := ⌈localWork a D α ξ r n R⌉₊
    2^p+2^d ≤ P ∧ powers ≤ L ∧ (Routing.labelCount a α n)^2+exterior ξ r n+1 ≤ 2*L := by
  intro P L
  have sorted := (geometrySubarrays_le (k:=gates) (u:=inputs) hw hb emitted).1
  have words := (Nat.le_mul_of_pos_left (2^p+2^d) (Nat.succ_pos w)).trans sorted
  have positive : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have rx : r≤exterior ξ r n := Nat.le_mul_of_pos_right _
    (Nat.le_floor (by simpa using Real.one_le_rpow positive (sub_nonneg.mpr hξ)))
  have fit : (exterior ξ r n : ℝ) ≤ localWork a D α ξ r n R := by
    have factor : (1 : ℝ) ≤ (logWidth r n : ℝ)^D := one_le_pow₀ (by exact_mod_cast (GeometryAdviceRate.indexWidths hr hn).1)
    unfold localWork
    exact (le_add_of_nonneg_right (by positivity)).trans (le_mul_of_one_le_right (by positivity) factor)
  have paid := ((Nat.le_add_right _ packetBits).trans geometry)
  have pubBase : (r:ℝ)*(n:ℝ)^(19/20:ℝ) ≤ publicWork a α r n R := by
    unfold publicWork
    exact le_add_of_nonneg_right (by positivity)
  have column : (width n (95/100:ℝ):ℝ) ≤ (n:ℝ)^(19/20:ℝ) := by
    rw [show (95/100:ℝ)=19/20 by norm_num]
    exact Nat.floor_le (by positivity)
  have ticks : (GeometryAdviceRate.ticks gates inputs outputs field w:ℝ) ≤ publicWork a α r n R :=
    (Nat.cast_le.mpr paid).trans (by
      rw [Nat.cast_mul]
      exact (mul_le_mul_of_nonneg_left column (Nat.cast_nonneg _)).trans pubBase)
  refine ⟨nat_le_ceiling ((Nat.cast_le.mpr words).trans ticks),slots.trans (rx.trans (nat_le_ceiling fit)),?_⟩
  apply nat_le_multiple_ceiling
  push_cast
  exact cubeUnits_le_localWork (a:=a) (D:=D) (α:=α) (ξ:=ξ) hn hr hR

end RoutingISA.Evaluator.ScheduleClock

namespace RoutingISA.SignedTaskArena

/-- Uniform bounds for the actual local accumulator, native power slots, two
projected output sorts and square scan in this frozen evaluator. -/
structure Layout.FinishWindows (task : Layout) (r w p d expBits exterior P L reader : ℕ) : Prop where
  slots : task.cube.teams*(task.p.parameters*expBits) ≤ r
  rectangle : 512*(task.cube.teams+1)*(task.dim+1)*(w+1)+(7+reader) ≤ r
  sorts : 2^p+2^d ≤ P
  powers : task.cube.teams*(task.p.parameters*expBits) ≤ L
  units : (task.cube.header.d^(task.cube.n+1))^2+exterior+1 ≤ 2*L

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
