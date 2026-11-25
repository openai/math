import OAI.Hierarchy.DescentStageMeasures
import OAI.Hierarchy.DescentMarkedLoad
import OAI.Hierarchy.DescentOutgoingLoad

namespace OAI
/-! # Integer input columns for the colony multiplier on a marked network -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open DescentBaseVariance
open scoped BigOperators Classical
noncomputable section

variable {F : Type*} [Field F] {D : ℕ} {P : Type*} {bits : P → ℕ} {Aty : Type*}
variable (W : MarkedWorld F D P bits) (hub : W.graph.Site → Bool)
variable (atoms : W.graph.Site → List Aty) (wire β hist : ℕ)

omit [Field F] in
theorem siteUnits_scaled (q : ℝ) (v : W.graph.Site) :
    q*(siteUnits W hub atoms wire β hist v:ℝ) =
      W.siteLoad hub atoms (q*wire) β (q*hist) v := by
  unfold siteUnits siteLoad load
  push_cast
  simp only [mul_add,Finset.mul_sum]
  congr 1
  · congr 1 <;> apply Finset.sum_congr rfl <;> intro e _
    · by_cases he : v=W.graph.src e <;> cases h : hub (W.graph.src e) <;> simp [he] <;> ring
    · by_cases he : v=W.graph.dst e <;> cases h : hub (W.graph.dst e) <;> simp [he] <;> ring
  · ring

omit [Field F] in
/-- Each individually charged incident wire is present in at least one of
the two physical endpoint columns, including for loop cables. -/
theorem siteUnits_cover (hβ : 1≤β) (v : W.graph.Site) :
    wire*GadgetNetwork.siteLoad W.graph v ≤ siteUnits W hub atoms wire β hist v := by
  unfold GadgetNetwork.siteLoad siteUnits
  rw [Finset.mul_sum]
  apply le_trans _ (Nat.le_add_right _ _)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  have src : 1≤(if hub (W.graph.src e) then β else 1) := by split <;> omega
  have dst : 1≤(if hub (W.graph.dst e) then β else 1) := by split <;> omega
  have sc := Nat.mul_le_mul_left (wire*W.graph.width e) src
  have dc := Nat.mul_le_mul_left (wire*W.graph.width e) dst
  simp only [Nat.mul_one] at sc dc
  by_cases incident : W.graph.src e=v ∨ W.graph.dst e=v
  · rw [ite_eq_left incident]
    rcases incident with atSource|atTarget
    · rw [ite_eq_left atSource.symm]
      exact sc.trans (Nat.le_add_right _ _)
    · rw [ite_eq_left atTarget.symm]
      exact dc.trans (Nat.le_add_left _ _)
  · rw [ite_eq_right incident,Nat.mul_zero]
    exact Nat.zero_le _

omit [Field F] in
theorem siteUnits_outgoing {C : Type} [Fintype C] [DecidableEq C] (home : W.graph.Site→C)
    (unit : ℕ) (paid : ∀e∈W.core,unit≤wire*W.graph.width e) (hβ : 1≤β) (v : W.graph.Site) :
    unit*DescentPacking.live (DescentPacking.nativeTraffic W.graph W.core home) v ≤
      siteUnits W hub atoms wire β hist v :=
  (StarKeys.scaled_outgoing_le W.graph W.core home unit wire paid v).trans
    (siteUnits_cover W hub atoms wire β hist hβ v)

omit [Field F] in
/-- Clearing the common denominator has no effect on the relative charge
in the minimizing multiplier's leaf-count term. -/
theorem siteUnits_density (q : ℝ) (positive : 0<q) (a cap : ℕ) :
    240*(∑v,(siteUnits W hub atoms wire β hist v:ℝ))/(2^a*cap:ℕ) =
      240*(∑v,W.siteLoad hub atoms (q*wire) β (q*hist) v)/((2:ℝ)^a*(q*cap)) := by
  simp_rw [←siteUnits_scaled W hub atoms wire β hist q]
  rw [←Finset.mul_sum]
  push_cast
  by_cases hc : cap=0
  · simp [hc]
  · field_simp [hc,positive.ne']


end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
