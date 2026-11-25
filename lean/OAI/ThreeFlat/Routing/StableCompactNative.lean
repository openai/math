import OAI.ThreeFlat.Routing.StableCompactLocal
import OAI.ThreeFlat.Routing.StableCompactSite
import OAI.ThreeFlat.Routing.StableCompactSources
import OAI.Computability.VPVNP.RAMSortCostLayout

namespace OAI
/-! # Native stable compaction with one polynomial-size template shared by all sites

A stage boundary stores one record at every site. Its index is the stage-bit
ordinal followed by the site bits. Each stage reads from its own site and
from the site displaced by its public xor stride. The stage and bit ordinals
range over the local template only.
-/

noncomputable section
open scoped Classical BigOperators
namespace ThreeFlat.Routing.StableCompactNative

open StableCompactRows StableCompactSite StableCompactStages
open StableCompaction (record masked compact)

/-- Every site has the same number of register slots, indexed by stage and bit first. -/
def registerCount (F : Type*) [Zero F] [One F] (m : ℕ) :=
  shared m + (StableCompactSite.network F m (stages m)).internal

def template (F : Type*) [Zero F] [One F] (m : ℕ) : Template F m (registerCount F m) :=
  ofLocal (StableCompactSite.network F m (stages m)) (wires m)

def network (F : Type*) [Zero F] [One F] (m : ℕ) : BitNetwork F (2^m+(2^m+2^m)) :=
  (template F m).network

theorem network_cells_eq (F : Type*) [Zero F] [One F] (m : ℕ) :
    (network F m).cells = (template F m).cells*2^m := rfl

theorem network_internal_eq (F : Type*) [Zero F] [One F] (m : ℕ) :
    (network F m).internal = registerCount F m*2^m := rfl

theorem network_eval {F : Type*} [CommSemiring F] (m : ℕ) (M X Y : Bits m) :
    (network F m).eval (Fin.append M (Fin.append X Y)) = if Y = compact M X then 1 else 0 := by
  change (ofLocal (StableCompactSite.network F m (stages m)) (wires m)).network.eval (pins M X Y) = _
  rw [ofLocal_eval]
  have site (h : Regs m) (v : Sites m) :
      (StableCompactSite.network F m (stages m)).eval (fun p => (wires m p).read M X Y h v) =
        if ∀ g : Gate m (stages m), pass (m:=m) (k:=stages m) g
          (fun j => labelBits M X Y h v ⟨g,j⟩) then 1 else 0 :=
    StableCompactSite.network_value (labelBits M X Y h v)
  simp_rw [site]
  simp only [Fintype.prod_boole, accepted]
  by_cases yes : Y = compact M X
  · obtain ⟨T, hT, unique⟩ := (existsUnique_history M X Y).mpr yes
    let h₀ := (history m).symm T
    rw [ite_eq_left yes, Finset.sum_eq_single_of_mem h₀ (Finset.mem_univ _)]
    · simp only [h₀,Equiv.apply_symm_apply,ite_eq_left hT]
    · intro h _ hn
      exact ite_eq_right (fun hp => hn ((history m).eq_symm_apply.mpr (unique _ hp)))
  · rw [ite_eq_right yes]
    exact Finset.sum_eq_zero (fun h _ => ite_eq_right (fun hp => yes (sound_history hp)))

private theorem stage_width (m : ℕ) : (stages m+1)*(width m+1) ≤ 6*(m+1)^3 := by
  have hs : stages m ≤ (m+1)^2 := by
    simp only [stages,steps,Computability.VPVNP.RAMSort.length_phases,Nat.choose_two_right]
    rw [pow_two]
    exact (Nat.div_le_self ..).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
  have hp : 0 < (m+1)^2 := by positivity
  have left : stages m+1 ≤ 2*(m+1)^2 := by omega
  have right : width m+1 ≤ 3*(m+1) := by unfold width; omega
  exact (Nat.mul_le_mul left right).trans_eq (by ring)

theorem template_cells (F : Type*) [Zero F] [One F] (m : ℕ) :
    (template F m).cells ≤ 32000*(m+1)^3 := by
  have hs := Nat.mul_le_mul_left 5000 (stage_width m)
  have hc := StableCompactSite.network_cells F m (stages m)
  change (StableCompactSite.network F m (stages m)).cells ≤ _
  rw [Nat.mul_assoc] at hc
  omega

theorem registerCount_le (F : Type*) [Zero F] [One F] (m : ℕ) :
    registerCount F m ≤ 32000*(m+1)^3 := by
  have hw := stage_width m
  have hs := Nat.mul_le_mul_left 5000 hw
  have hc := StableCompactSite.network_internal F m (stages m)
  have hreg : shared m ≤ (stages m+1)*(width m+1) := Nat.mul_le_mul_left _ (Nat.le_succ _)
  rw [Nat.mul_assoc] at hc
  unfold registerCount
  omega

theorem network_cells (F : Type*) [Zero F] [One F] (m : ℕ) :
    (network F m).cells ≤ 2^m*(32000*(m+1)^3) := by
  rw [network,Template.network_cells,Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (template_cells F m)

theorem network_internal (F : Type*) [Zero F] [One F] (m : ℕ) :
    (network F m).internal ≤ 2^m*(32000*(m+1)^3) := by
  rw [network,Template.network_internal,Nat.mul_comm]
  exact Nat.mul_le_mul_left _ (registerCount_le F m)

end ThreeFlat.Routing.StableCompactNative

end
end OAI
