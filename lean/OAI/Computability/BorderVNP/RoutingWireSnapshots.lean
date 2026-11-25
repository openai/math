import OAI.Computability.BorderVNP.RoutingWireChecks

/-! # Exterior multiplicity during a sequence of native checks

Scratch memory can change between the source, relay, and padding instructions.
Each snapshot records the currently initialized input and scheduling table. The
same exterior assignment is therefore read throughout all of these checks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA
open scoped Classical

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
  {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {L : WireLayout (R+1) r link}

/-- In a finite sum over the actual processor-by-partner exterior variables, the
unique passing histories contribute the selected term once, in any additive monoid. -/
theorem sum_physical_snapshots {M : Type*} [AddCommMonoid M] (hw : 0 < w)
    (S : ∀ ext : Exterior R r link → Bool, WireSnapshots G pin ext L w)
    (b : Block (R+1)) (header : Fin L.header → Bool) (high payload : Fin (R+1) → Fin (R+1) → ℕ → Bool)
    (value : M) :
    (∑ ext : Exterior R r link → Bool, if (S ext).Passes b header high payload then value else 0) = value := by
  obtain ⟨chosen,pass,unique⟩ := L.existsUnique_exterior b header high payload
  have h (ext : Exterior R r link → Bool) : (S ext).Passes b header high payload ↔ ext = chosen :=
    ((S ext).passes_iff hw ..).trans ⟨unique ext, fun he => he ▸ pass⟩
  simp only [h]
  simp

/-- Summing over all original exterior assignments and over the fully assigned
expansion terms returns exactly the original sum. Each term may have its own
leg widths, broadcast payload, and scratch snapshots throughout the checks. -/
theorem sum_expansion_snapshots {M ι : Type*} [AddCommMonoid M] [Fintype ι] (hw : 0 < w)
    (layout : ι → WireLayout (R+1) r link)
    (S : ∀ i ext, WireSnapshots G pin ext (layout i) w)
    (b : ι → Block (R+1)) (header : ∀ i, Fin (layout i).header → Bool)
    (high payload : ι → Fin (R+1) → Fin (R+1) → ℕ → Bool) (value : ι → M) :
    (∑ ext : Exterior R r link → Bool, ∑ i : ι,
      if (S i ext).Passes (b i) (header i) (high i) (payload i) then value i else 0) = ∑ i, value i := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => sum_physical_snapshots hw (S i) (b i) (header i) (high i) (payload i) (value i)

end TeamContraction

end BorderVNP
end Computability
end OAI
