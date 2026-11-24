import OAI.Computability.VPVNP.CompressorSlotOwnerAgreement
import OAI.Computability.VPVNP.CompressorSlotOwnerRuns

/-!
# Physical input bounds for the shrinking slot directory

The mixed-radix scan reads only the three descriptor arrays and the cyclic
successor array. Their lengths follow from the packed graph parameters. Placing
them below a common scratch base gives the source bounds for both owner passes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotOwners

open Compression Compression.PackingData Compression.SurvivingSlots Slots BurstRAM

variable {V H Tag L : Type*} {d c N J nL pad w : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (subdiv : Fin 4 → ℕ)
variable (vertices : V ≃ Fin N) (tags : Tag ≃ Fin J) (lanes : L ≃ Fin nL)

/-- The role, old arc and subdivision arrays end below the scratch base.
Every decoded read is therefore stable throughout the two owner scans. -/
theorem genuineInputs_before {layout : Bool} {g : Fin 8 → Word w} {mem : Memory w}
    (tables : GenuineTables P subdiv vertices tags lanes layout g mem) (base : Word w)
    (oldEnd : (g 3).val + 4*(oldBaseArcCount N J d c*nL) ≤ base.val)
    (roleEnd : (g 4).val+8 ≤ base.val) (subdivEnd : (g 5).val+4 ≤ base.val) :
    ∀ i < (keyCount N J d c subdiv*nL)*2, ∀ a ∈ genuineInputs g mem (Fin.ofNat _ i),
      a.val < base.val := by
  intro i hi
  have roles (j : ℕ) (hj : j < 8) : (mem ((g 4).val+j)).val < 3 := by
    let t : Fin 4 := ⟨j/2, by omega⟩
    let s : Fin 2 := ⟨j%2, by omega⟩
    have idx : 2*t.val+s.val = j := by dsimp only [t,s]; omega
    have h := tables.role t s
    rw [idx] at h
    rw [h]
    cases endRole layout (decide (s=1)) t <;> decide
  apply genuine_inputs_before g mem (Fin.ofNat _ i) base _ roleEnd subdivEnd roles
  · rw [tables.baseCount, tables.subdivCount, tables.laneCount]
    apply (Nat.mod_le i (2^w)).trans_lt
    simpa only [keyCount, oldBaseArcCount, Nat.mul_assoc] using hi
  · simpa only [tables.baseCount, tables.laneCount] using oldEnd

omit [AddCommGroup Tag] [AddCommGroup L] in
/-- Both sides of every dummy field read below the scratch base when the
packed-site successor array ends there. -/
theorem dummyInput_before {p : Fin 3 → Word w} {mem : Memory w}
    (tables : DummyTables vertices tags lanes pad p mem) (base : Word w)
    (nextEnd : (p 1).val + N*(J*nL) ≤ base.val) :
    ∀ i < ((N*(J*nL))*pad)*2, (p 1+dummySource p (Fin.ofNat _ i)).val < base.val := by
  intro i hi
  apply dummy_input_before p (Fin.ofNat _ i) base (N*(J*nL)) nextEnd tables.twoFits
  rw [tables.padCount]
  exact (Nat.mod_le i (2^w)).trans_lt hi

end CompressorRecords.SlotOwners

end VPVNP
end Computability
end OAI
