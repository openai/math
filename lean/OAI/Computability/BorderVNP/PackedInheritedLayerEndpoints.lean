import OAI.Computability.BorderVNP.PackedInheritedEndpointViews
import OAI.Computability.BorderVNP.PackedInheritedLayerInputs

/-! # Physical endpoint chosen for each inherited interval -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Layer

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork
open private cut from OAI.Computability.BorderVNP.PackedBankInheritedRead
open scoped Classical

variable {D m old np seeds : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {P : Type*} {bits : P → ℕ} (p : Pack D P bits K)
variable {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
variable (oldID : p.layout.Edge ↪ Fin old) (seed : A ↪ Fin seeds)
local notation3 "G" => (output e p bin perm positive first q).layout
local notation3 "nextID" => outputRows e p bin perm positive first q oldID seed

/-- Occupancy of the source hook candidate distinguishes selected and retained old bands. -/
theorem candidate_zero (z : p.layout.Edge) (b : Band D) :
    bandCandidate e seeds 0 (oldID z) b ∈ Set.range nextID ↔
      (z,b) ∈ (partition p.layout bin perm m).selected := by
  change bandCandidate e seeds 0 (oldID z) b ∈ Set.range (edgeRows e p bin perm oldID seed) ↔ _
  rw [bandCandidate_mem_iff e p bin perm oldID seed]
  constructor
  · rintro ⟨u,hu,ht⟩
    obtain rfl := oldID.injective hu
    exact ht.mpr (by decide)
  · intro h
    exact ⟨z,rfl,iff_of_true h (by decide)⟩

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The dynamic hook mux selects the canonical endpoint of the actual sewn cable,
also at source-first self-loops and retained destination ends. -/
theorem chosen_end (v : p.layout.Site) (z : Incident p.layout v) (b : Band D) :
    let side := decide (p.layout.src z.val = v)
    let new := oldBandWire e p bin perm positive first q v z b
    (if (z.val,b) ∈ (partition p.layout bin perm m).selected then
      edgeEnd (n := np) (bandCandidate e seeds (if side then 0 else 1) (oldID z.val) b) true
    else edgeEnd (bandCandidate e seeds 2 (oldID z.val) b) side) =
      edgeEnd (nextID new.val) (decide ((G).src new.val = .inl v)) := by
  intro side new
  by_cases h : (z.val,b) ∈ (partition p.layout bin perm m).selected
  · let c : ↥((partition p.layout bin perm m).selected) := ⟨(z.val,b),h⟩
    by_cases hs : p.layout.src z.val = v
    · have hz : new.val = .inl (.inl c) := by simp only [new,oldBandWire,cut,h,hs,dite_true]; rfl
      have ends : (G).src new.val = .inl v := by rw [hz]; exact congrArg Sum.inl hs
      rw [ite_eq_left h,decide_eq_true ends,hz]
      rw [show side = true from decide_eq_true hs]
      change edgeEnd (n := np) (bandCandidate e seeds 0 (oldID c.val.1) c.val.2) true =
        edgeEnd ((edgeRows e p bin perm oldID seed) (.inl (.inl c))) true
      exact congrArg (fun n => edgeEnd (n := np) n true)
        (hook_candidate e p bin perm oldID seed c).1.symm
    · have hz : new.val = .inl (.inr c) := by simp only [new,oldBandWire,cut,h,hs,dite_true,dite_false]; rfl
      have ends : (G).src new.val = .inl v := by rw [hz]; exact congrArg Sum.inl (z.property.resolve_left hs)
      rw [ite_eq_left h,decide_eq_true ends,hz]
      rw [show side = false from decide_eq_false hs]
      change edgeEnd (n := np) (bandCandidate e seeds 1 (oldID c.val.1) c.val.2) true =
        edgeEnd ((edgeRows e p bin perm oldID seed) (.inl (.inr c))) true
      exact congrArg (fun n => edgeEnd (n := np) n true)
        (hook_candidate e p bin perm oldID seed c).2.symm
  · let c : {u : (SeedIntervals.layout p.layout bin perm m).Edge // u ∉ (partition p.layout bin perm m).selected} :=
      ⟨(z.val,b),h⟩
    have hz : new.val = .inr (.inl c) := by simp only [new,oldBandWire,cut,h,dite_false]; rfl
    have ends : (G).src new.val = .inl (p.layout.src z.val) := by rw [hz]; rfl
    have sideEq : decide ((G).src new.val = .inl v) = side := by
      rw [ends]
      simp [side]
      exact ⟨Sum.inl.inj,congrArg Sum.inl⟩
    rw [ite_eq_right h,sideEq,hz]
    change edgeEnd (n := np) (bandCandidate e seeds 2 (oldID c.val.1) c.val.2) side =
      edgeEnd ((edgeRows e p bin perm oldID seed) (.inr (.inl c))) side
    exact congrArg (fun n => edgeEnd (n := np) n side) (retained_candidate e p bin perm oldID seed c).symm

end Packing.Inherited.Layer

end BorderVNP
end Computability
end OAI
