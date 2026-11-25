import OAI.Hierarchy.TaggedShorterSupergroups
import OAI.Hierarchy.ProbeActualGroups
import OAI.Hierarchy.ProbeStageWidthRatio

namespace OAI
/-! # Next-fit directory for every group of the installed nine-digit template -/

noncomputable section
namespace Hierarchy.TaggedShorterSupergroups
open ProbeStage TaggedShorterPacking
open scoped Classical BigOperators

def reserved (h W copies : ℕ) (g : AllGroups h (2^W)) : ℕ :=
  (stageAt h (2^W) g.1).span*copies

/-- Copies accounts for the two path alphabets, fixed roles and any subslot
multiplicity. Choosing a dyadic constant above twice their product works for
the actual outer stages and central stage at every height. -/
theorem stage_fits (h W copies pad : ℕ) (padding : 2*copies≤2^pad)
    (g : AllGroups h (2^W)) :
    2*reserved h W copies g ≤ 2^superAddress W pad h := by
  have positive : 1≤2^W := Nat.two_pow_pos W
  have geom := (template_dyadic positive (stageAt h (2^W) g.1) (List.get_mem ..)).1
  have scaled := Nat.mul_le_mul_left (stageAt h (2^W) g.1).span padding
  have sizes : (stageAt h (2^W) g.1).span*2^pad ≤ 2^superAddress W pad h := by
    rcases geom with outer|inner
    · rw [outer,←pow_add]
      exact Nat.pow_le_pow_right (by decide) (outer_address_fits ..)
    · rw [inner,←pow_add]
      exact Nat.pow_le_pow_right (by decide) (center_address_fits ..)
  simpa [reserved,Nat.mul_left_comm,Nat.mul_assoc,Nat.mul_comm] using scaled.trans sizes

theorem total_reserved (h W copies : ℕ) :
    (∑ g : AllGroups h (2^W),reserved h W copies g) ≤
      ((2*rounds (2^W)+1)*4^(rounds (2^W)+1)*2^h)*copies := by
  have positive : 1≤2^W := Nat.two_pow_pos W
  have bound := all_ports (h:=h) positive
  have integral : (∑ g : AllGroups h (2^W),(stageAt h (2^W) g.1).span) ≤
      (permutationFabric h (2^W)).shapes.length*(4^(rounds (2^W)+1)*2^h) := by
    exact_mod_cast bound
  have count : (permutationFabric h (2^W)).shapes.length=2*rounds (2^W)+1 := template_length ..
  rw [count] at integral
  simpa only [reserved,←Finset.sum_mul,Nat.mul_assoc] using
    Nat.mul_le_mul_right copies integral

/-- The directory uses a fixed finite number of words per original stage
group. Both its reservation addresses and its supergroup count are derived
from the complete concrete template before seeing the tagged permutation. -/
theorem purchase_stages (h W copies pad : ℕ) (padding : 2*copies≤2^pad) :
    ∃ d : Directory (reserved h W copies) (2^superAddress W pad h),
      d.groups*(2^superAddress W pad h) ≤
        2*(((2*rounds (2^W)+1)*4^(rounds (2^W)+1)*2^h)*copies)+2^superAddress W pad h := by
  classical
  let xs := (Finset.univ : Finset (AllGroups h (2^W))).toList
  obtain ⟨dir,_,count⟩ := purchase (reserved h W copies) (2^superAddress W pad h) xs
    (by intro g; simp [xs]) (stage_fits h W copies pad padding)
  refine ⟨dir,count.trans ?_⟩
  have volume : load (reserved h W copies) xs = ∑ g,reserved h W copies g := by
    simp [load,xs,Finset.sum_map_toList]
  rw [volume]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (total_reserved ..)) _

end Hierarchy.TaggedShorterSupergroups

end
end OAI
