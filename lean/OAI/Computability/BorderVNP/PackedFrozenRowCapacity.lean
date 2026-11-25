import OAI.Computability.BorderVNP.PackedFrozenBirthFields
import OAI.Computability.BorderVNP.PackedInheritedHookQuery
import OAI.Computability.BorderVNP.PackedSubdivisionGateRows
import OAI.Computability.BorderVNP.ShortenPublicPaddedCapacity

/-! # Physical row counts of the immutable public tape

The retained endpoint fragments, terminal hooks, paid birth tables and
subdivision records have fixed finite schemas. Even on inactive slots their
combined row and scalar arities are linear in the actual sewn rectangle.
The one-copy private descriptor is stored through its fixed reference fields.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Shortening Shortening.StaticRows Shortening.PublicCapacity Crossing BankJoint
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- The two sparse geometry dimensions whose occupied/empty bands both persist. -/
def physicalRows (s : Shape) := s.sites+s.edges

/-- The old site and cable rectangles survive every physical replacement. -/
theorem retained_le_sewn (s : Shape) (seeds : ℕ) : physicalRows s ≤ physicalRows (s.sew e seeds) := by
  change s.sites+s.edges ≤ siteCapacity e s.sites seeds+edgeCapacity e s.edges seeds
  rw [edgeCapacity_eq]
  unfold siteCapacity
  have cap : s.edges ≤ 3*(2*D+1)*s.edges := Nat.le_mul_of_pos_left _ (by positivity)
  omega

/-- Physical site/cable rows never disappear at the initial geodesic subdivision. -/
theorem retained_le_subdivided (s : Shape) (extra : ℕ) : physicalRows s ≤ physicalRows (s.subdivide extra) := by
  simp only [physicalRows,Shape.subdivide]
  nlinarith

/-- The parallel presentation has exactly one complete physical rectangle per child. -/
theorem parallel_physicalRows (s : Shape) (k : ℕ) : physicalRows (s.parallel k) = k*physicalRows s := by
  simp [physicalRows,Shape.parallel,Nat.mul_add]

/-- Actual fixed main birth rows at one seed, including paid sites and terminals. -/
noncomputable def mainRows (first : Fin D × Bool) :=
  ∑ v : TemplateSite e, (rows e first v).length

/-- Exact number of frozen paid/main rows in a whole geometric seed directory. -/
theorem main_card (first : Fin D × Bool) (A : Type*) [Fintype A] :
    Fintype.card (Birth.Row e first A) = Fintype.card A*mainRows e first := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin,Fintype.sum_prod_type,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mainRows,Nat.cast_id]

/-- The complete fresh combining record rectangle attached at this node. -/
noncomputable abbrev RoundRows (first : Fin D × Bool) (A : Type*) (old np : ℕ) :=
  Layer.Row old D np ⊕ (Birth.Row e first A ⊕ InheritedHook.Row old D)

/-- The actual payload pin rectangle, with immutable bit widths at the producing node. -/
noncomputable abbrev RoundData (first : Fin D × Bool) (A : Type*) (old np w : ℕ) :=
  (Layer.Row old D np × Fin 9 × Fin w) ⊕ ((A × Output e first × Fin w) ⊕ (InheritedHook.Row old D × Fin 9 × Fin w))

/-- Fixed multiplier for the physical row and scalar counts of a combining node. -/
noncomputable def roundSlots (first : Fin D × Bool) := 9*(6*D+3)+mainRows e first+Fintype.card (Output e first)+1

private theorem stage_capacity (old : Shape) (seeds : ℕ) :
    old.sites ≤ physicalRows (old.sew e seeds) ∧ old.edges ≤ physicalRows (old.sew e seeds) ∧
      seeds ≤ physicalRows (old.sew e seeds) := by
  have retains := retained_le_sewn e old seeds
  have templates : 1 ≤ Fintype.card (TemplateSite e) := Fintype.card_pos
  have bound := Nat.le_mul_of_pos_right seeds templates
  change _ ≤ siteCapacity e old.sites seeds+edgeCapacity e old.edges seeds ∧
    _ ≤ siteCapacity e old.sites seeds+edgeCapacity e old.edges seeds ∧
    _ ≤ siteCapacity e old.sites seeds+edgeCapacity e old.edges seeds
  change old.sites+old.edges ≤ siteCapacity e old.sites seeds+edgeCapacity e old.edges seeds at retains
  unfold siteCapacity at *
  omega

/-- Bound both reserved row slots and payload-bit pins for the actual retained
commands, main template packets and hook commands on this physical step. -/
theorem round_cards (first : Fin D × Bool) (old : Shape) (np w seeds : ℕ) (A : Type*) [Fintype A]
    (ports : np ≤ old.sites) (arity : Fintype.card A = seeds) :
    Fintype.card (RoundRows e first A old.edges np) ≤ roundSlots e first*physicalRows (old.sew e seeds) ∧
    Fintype.card (RoundData e first A old.edges np w) ≤ roundSlots e first*physicalRows (old.sew e seeds)*w := by
  let R := physicalRows (old.sew e seeds)
  obtain ⟨site,edge,seed⟩ := stage_capacity e old seeds
  have ports' : np ≤ R := ports.trans site
  have inherit : Fintype.card (Layer.Row old.edges D np) ≤ (4*D+3)*R := by
    simp only [Layer.Row,Shortening.SeedIntervals.Band,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
      Fintype.card_option,Fintype.card_bool]
    nlinarith only [ports',Nat.mul_le_mul_right (D*2+1) edge]
  have hook : Fintype.card (InheritedHook.Row old.edges D) ≤ 2*D*R := by
    simp only [InheritedHook.Row,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    nlinarith only [Nat.mul_le_mul_right D edge]
  have main := Nat.mul_le_mul_right (mainRows e first) seed
  have data := Nat.mul_le_mul_right (Fintype.card (Output e first)) seed
  change seeds * mainRows e first ≤ R * mainRows e first at main
  change seeds * Fintype.card (Output e first) ≤ R * Fintype.card (Output e first) at data
  constructor
  · simp only [Layer.Row,InheritedHook.Row,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at inherit hook
    simp only [RoundRows,main_card,arity,Layer.Row,InheritedHook.Row,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    unfold roundSlots
    change _ ≤ _*R
    nlinarith only [inherit,hook,main]
  · simp only [RoundData,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,arity]
    have count : Fintype.card (Layer.Row old.edges D np)*9 + seeds*Fintype.card (Output e first) +
        Fintype.card (InheritedHook.Row old.edges D)*9 ≤ roundSlots e first*R := by
      unfold roundSlots
      nlinarith only [inherit,hook,data]
    apply (le_of_eq (by simp only [Layer.Row,InheritedHook.Row,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]; ring) : _ ≤ (Fintype.card (Layer.Row old.edges D np)*9 + seeds*Fintype.card (Output e first) +
      Fintype.card (InheritedHook.Row old.edges D)*9)*w).trans (Nat.mul_le_mul_right _ count)

/-- Number of endpoint, port and relay rows inserted by the actual subdivision. -/
theorem subdivision_card (s : Shape) (np extra : ℕ) (ports : np ≤ s.sites) :
    Fintype.card (Subdivision.Gates.Row s.edges np extra) ≤ 2*physicalRows (s.subdivide extra) := by
  simp only [Subdivision.Gates.Row,Subdivision.Gates.Old,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
    Fintype.card_bool,physicalRows,Shape.subdivide]
  nlinarith only [ports]

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
