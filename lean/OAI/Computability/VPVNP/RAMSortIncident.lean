import OAI.Computability.VPVNP.RAMSharedFields
import OAI.Computability.VPVNP.RAMSortCostLayout
import OAI.Computability.VPVNP.RAMBitTranscript

/-!
# Linear addressing of a site's incident fields

The word validator sees a contiguous bit array. Restricting the sender
arrays to a site uses the physical port offsets, including clamped ports.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

/-- Extend the finite local bit array by zero at unused addresses. -/
def readIncident {n : ℕ} (inc : Fin n → Bool) (a : ℕ) : Bool :=
  if h : a < n then inc ⟨a, h⟩ else false

@[simp] theorem readIncident_at {n : ℕ} (inc : Fin n → Bool) (i : Fin n) :
    readIncident inc i.val = inc i := by simp [readIncident, i.isLt]

end RAMSort

namespace BurstRAM

open RAMLayout RAMSort

variable {d e w : ℕ}

/-- Read the bit at a site’s linear incident address from its shared sender arrays, returning
false beyond the incident layout. -/
def sortIncident (b : SendArrays d (2^e) w) (v : Fin (2^d)) (a : ℕ) : Bool :=
  readIncident (fun j ↦ (incidentEquiv d (2^e) w b).val (v, (offset d (2^e) w).symm j)) a

@[simp] theorem sortIncident_offset (b : SendArrays d (2^e) w) (v : Fin (2^d))
    (slot : RAMLayout.Slot d (2^e) w) :
    sortIncident b v (offset d (2^e) w slot).val = (incidentEquiv d (2^e) w b).val (v, slot) := by
  simp [sortIncident]

theorem record_width (e : ℕ) : 2^(2+e) = 4*2^e := by rw [Nat.pow_add]

end BurstRAM

end VPVNP
end Computability
end OAI
