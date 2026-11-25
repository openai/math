import OAI.Hierarchy.DescentPhysicalResetAmounts
import OAI.Hierarchy.DescentWholeGrain

namespace OAI
/-! # Read the same old physical measurement in raw and bundled coordinates -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open DescentColonies DescentBaseVariance DescentChosenRouter.Dyadic
open Hierarchy.DescentSixParty.StarKeys
open scoped BigOperators Classical
noncomputable section
variable {F H P V : Type} [Field F] [Fintype V] [DecidableEq V] {k d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (count : W.graph.Edge→ℕ) (grain : ℕ)
variable (fit : ∀e,W.graph.width e=count e*grain)
local notation "A" => W.countWorld count
local notation "N" => W.granular count grain fit

include fit in
theorem units_of_counts (hub : W.graph.Site→Bool) (atoms : W.graph.Site→List H) (wire β hist : ℕ) (v) :
    (A).siteUnits hub atoms (wire*grain) β hist v=W.siteUnits hub atoms wire β hist v := by
  simp only [siteUnits,countWorld,fit,mul_assoc,mul_left_comm,mul_comm]
  congr 1

include fit in
omit [Fintype V] in
theorem mass_of_counts (pos : W.graph.Site→V) (ix : W.graph.Site→Block k)
    (hub : W.graph.Site→Bool) (atoms : W.graph.Site→List H) (wire β hist : ℕ) (v i) :
    blockMass (A).graph pos ix ((A).siteUnits hub atoms (wire*grain) β hist) v i =
      blockMass W.graph pos ix (W.siteUnits hub atoms wire β hist) v i := by
  unfold blockMass
  apply Finset.sum_congr (Finset.ext fun u => ⟨fun _ => Finset.mem_univ u, fun _ => Finset.mem_univ u⟩)
  intro u _
  by_cases hu : pos u = v ∧ ix u = i
  · simpa only [ite_eq_left hu] using units_of_counts W count grain fit hub atoms wire β hist u
  · simp only [ite_eq_right hu]

theorem count_core_amount : (A).fine.liveWidth*grain=(N).liveWidth := by
  rw [fine_core,granular_core]
  unfold liveWidth
  simp only [countWorld,Finset.sum_mul,fit]

theorem count_tether_amount : (A).fine.tetherWidth*grain=(N).tetherWidth := by
  rw [fine_tether,granular_tether]
  unfold tetherWidth
  simp only [countWorld,Finset.sum_mul,fit]
  exact Finset.sum_congr (Finset.ext fun _ => Finset.mem_compl.trans Finset.mem_compl.symm) (fun _ _ => rfl)

omit [Field F] in
theorem granular_units (hub : W.graph.Site→Bool) (atoms : W.graph.Site→List H)
    (wire β hist : ℕ) (v : W.graph.Site) :
    (N).siteUnits hub atoms wire β hist v=W.siteUnits hub atoms wire β hist v := by
  have side (endAt : W.graph.Edge → W.graph.Site) :
      (∑ p : Σ e : W.graph.Edge, Fin (count e),
        if v = endAt p.1 then wire * grain * (if hub (endAt p.1) then β else 1) else 0) =
      ∑ e : W.graph.Edge,
        if v = endAt e then wire * W.graph.width e * (if hub (endAt e) then β else 1) else 0 := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hit : v = endAt e <;> simp [hit, fit, mul_left_comm, mul_comm]
  exact congrArg (fun n => n + hist * (atoms v).length)
    (congrArg₂ Nat.add (side W.graph.src) (side W.graph.dst))

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
