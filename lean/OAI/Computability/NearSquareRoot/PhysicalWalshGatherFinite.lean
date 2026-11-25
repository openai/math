import OAI.Computability.NearSquareRoot.PhysicalWalshGatherMask
import OAI.Computability.NearSquareRoot.PhysicalWalshGatherAccuracy

/-! # Physical gather controls for finite sets of address bits -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherProgram

variable {k : ℕ}

/-- One tape flag per bit position, in increasing least-significant-bit order. -/
def flags (bits : Finset (Fin k)) : List Bool := List.ofFn (fun i => decide (i ∈ bits))

@[simp] theorem flags_length (bits : Finset (Fin k)) : (flags bits).length = k := List.length_ofFn

@[simp] theorem flags_count (bits : Finset (Fin k)) : (flags bits).count true = bits.card := by
  have en : ((List.finRange k).toFinset.filter (· ∈ bits)) = bits := by ext; simp
  rw [flags,List.ofFn_eq_map,List.count_eq_countP,List.countP_map,← en]
  simpa [en,Function.comp_def] using
    ((List.nodup_finRange k).card_eq_countP (P := fun i => i ∈ bits)).symm

/-- The routing permutation from the physical mask readout, indexed by the
original bit width. -/
def gatherPerm (bits : Finset (Fin k)) : Equiv.Perm (Fin k) :=
  (finCongr (flags_length bits)).permCongr (GatherMask.perm (flags bits))

/-- Exactly the selected positions are placed in the low field. -/
theorem gatherPerm_low (bits : Finset (Fin k)) (i : Fin k) : (gatherPerm bits i).val < bits.card ↔ i ∈ bits := by
  let j := (finCongr (flags_length bits)).symm i
  have h := GatherMask.low_iff (flags bits) j
  rw [flags_count] at h
  change (GatherMask.perm (flags bits) j).val < bits.card ↔ i ∈ bits
  rw [h]
  simp [flags,j,List.get_eq_getElem]
  rfl

private theorem control_cast {n m : ℕ} (h : n = m) (c : ℕ) (p : Equiv.Perm (Fin n)) :
    control c ((finCongr h).permCongr p) = control c p := by
  subst m
  rfl

/-- The encoded control packet is the literal output of the mask scanner. -/
theorem control_eq (bits : Finset (Fin k)) : control bits.card (gatherPerm bits) =
    control ((flags bits).count true) (GatherMask.perm (flags bits)) := by
  rw [flags_count, gatherPerm,control_cast]

end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI
