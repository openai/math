import OAI.Hierarchy.DescentPackMass
import OAI.Hierarchy.DescentMergedSiteLoad

namespace OAI
/-! # Exact marked outgoing bundles and their full old-site load -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking GadgetNetwork
open scoped Classical BigOperators
noncomputable section

variable {n : ℕ} {P : Type*} {bits : P→ℕ} (N : Network n P bits)
    (core : Finset N.Edge) {C : Type} [Fintype C] [DecidableEq C] (home : N.Site→C)

theorem outgoing_count (u : N.Site) :
    live (nativeTraffic N core home) u=(core.filter fun e=>N.src e=u).card := by
  let out := core.filter fun e=>N.src e=u
  let regroup : (Σ c : C,{e : core // N.src e.val=u ∧ home (N.dst e.val)=c}) ≃ out :=
    { toFun := fun ix=>⟨ix.2.val.val,Finset.mem_filter.mpr ⟨ix.2.val.property,ix.2.property.1⟩⟩
      invFun := fun ⟨e,he⟩=>⟨home (N.dst e),⟨⟨e,(Finset.mem_filter.mp he).1⟩,(Finset.mem_filter.mp he).2,rfl⟩⟩
      left_inv := by rintro ⟨c,⟨e,es,ec⟩⟩;subst c;rfl
      right_inv := fun _=>rfl }
  change (∑c,Fintype.card {e : core // N.src e.val=u ∧ home (N.dst e.val)=c})=_
  rw [←Fintype.card_sigma,Fintype.card_congr regroup,Fintype.card_coe]

/-- A marked cable consumes at least one unit at its actual source, even
when several marked cables share a destination and when a cable is a loop. -/
theorem outgoing_le_siteLoad (unit : ∀e∈core,1≤N.width e) (u : N.Site) :
    live (nativeTraffic N core home) u≤siteLoad N u := by
  let out := core.filter fun e=>N.src e=u
  let cost := fun e=>if N.src e=u ∨ N.dst e=u then N.width e else 0
  rw [outgoing_count]
  change out.card≤∑e,cost e
  calc
    out.card = ∑_∈out,1 := by simp
    _ ≤ ∑e∈out,cost e := Finset.sum_le_sum fun e he=>by
      have h := Finset.mem_filter.mp he
      simpa [cost,h.2] using unit e h.1
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- A colored thin list spends only the full incoming mass of its own colony. -/
theorem thin_le_fiber (color : N.Site→Bool) (full : N.Site→ℕ)
    (unit : ∀e∈core,1≤N.width e) (enough : ∀u,siteLoad N u≤full u) (c : C) :
    amount (live (nativeTraffic N core home)) (thinList home color c)≤
      ∑u∈Finset.univ.filter (fun u=>home u=c),full u := by
  let xs := thinList home color c
  have nd : xs.Nodup := colorSites_nodup home color false c
  let load : N.Site → ℕ := fun u => live (nativeTraffic N core home) u
  calc
    _ = ∑ u ∈ xs.toFinset, load u := (List.sum_toFinset load nd).symm
    _ ≤ ∑ u ∈ xs.toFinset, full u := Finset.sum_le_sum fun u _ =>
      (outgoing_le_siteLoad N core home unit u).trans (enough u)
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((mem_colorSites home color false c u).mp (List.mem_toFinset.mp hu)).1⟩

/-- A marked item can consume several units of normalized width. This
sum compares the native unscaled count to the scaled physical site width. -/
theorem scaled_outgoing_le (marked wireScale : ℕ)
    (paid : ∀ e∈core,marked≤wireScale*N.width e) (u : N.Site) :
    marked*live (nativeTraffic N core home) u≤wireScale*siteLoad N u := by
  let out := core.filter fun e=>N.src e=u
  let wt := fun e=>if N.src e=u ∨ N.dst e=u then N.width e else 0
  rw [outgoing_count]
  change marked*out.card≤wireScale*∑e,wt e
  rw [Finset.mul_sum]
  calc
    marked*out.card = ∑_∈out,marked := by simp [Nat.mul_comm]
    _ ≤ ∑e∈out,wireScale*wt e := Finset.sum_le_sum fun e he=>by
      have hz := Finset.mem_filter.mp he
      simpa [wt,hz.2] using paid e hz.1
    _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _)

theorem scaled_thin_le_fiber (color : N.Site→Bool) (full : N.Site→ℕ) (unit : ℕ)
    (enough : ∀u,unit*live (nativeTraffic N core home) u≤full u) (c : C) :
    unit*amount (live (nativeTraffic N core home)) (thinList home color c)≤
      ∑u∈Finset.univ.filter (fun u=>home u=c),full u := by
  let xs := thinList home color c
  have nd : xs.Nodup := colorSites_nodup home color false c
  let loads : N.Site → ℕ := fun u => live (nativeTraffic N core home) u
  calc
    _ = unit*(∑ u ∈ xs.toFinset, loads u) := congrArg (unit * ·) (List.sum_toFinset loads nd).symm
    _ = ∑ u ∈ xs.toFinset,unit*loads u := Finset.mul_sum ..
    _ ≤ ∑ u ∈ xs.toFinset,full u := Finset.sum_le_sum fun u _=>enough u
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        ((mem_colorSites home color false c u).mp (List.mem_toFinset.mp hu)).1⟩

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
