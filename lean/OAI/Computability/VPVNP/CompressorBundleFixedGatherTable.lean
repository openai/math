import OAI.Computability.VPVNP.CompressorBundleGatherCoordinates
import OAI.Computability.VPVNP.CompressorBundleFixedGatherScan

/-!
# The complete key rectangle built by a single fixed native scan

The dense traversal visits the live prefixes of both row classes exactly
once and preserves all padding. The resulting key table has the same
readback and external frame as the bounded row-wise construction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleGather.Fixed

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM BundleKeys

variable {w : ℕ} (t : KeyTable w) (reg : t.Layout)

private theorem slot_at (b : Fin t.bundles) (i : Fin t.thickCount ⊕ Fin t.motifCount) :
    (slot t reg (entryIndex t (b,i))).val = i.elim
      (fun z ↦ b.val*t.stride+z.val) (fun z ↦ (t.bundles+b.val)*t.stride+z.val) := by
  cases i <;> simp [slot,physical,finProdFinEquiv, Nat.mul_comm,Nat.add_comm]

private theorem live (j : Fin (entryCount t)) :
    ∃ b i, b < 2*t.bundles ∧ i < t.rowSize b ∧ (slot t reg j).val = b*t.stride+i := by
  obtain ⟨⟨b,i | i⟩,rfl⟩ := (entryIndex t).surjective j
  · exact ⟨b.val,i.val,by have := b.isLt; omega,by simp [KeyTable.rowSize,b.isLt],slot_at t reg b (.inl i)⟩
  · exact ⟨t.bundles+b.val,i.val,by have := b.isLt; omega,by simp [KeyTable.rowSize],slot_at t reg b (.inr i)⟩

private theorem cover (b : ℕ) (hb : b < 2*t.bundles) (i : ℕ) (hi : i < t.rowSize b) :
    ∃ j, (slot t reg j).val = b*t.stride+i := by
  by_cases h : b < t.bundles
  · let z : Fin t.thickCount := ⟨i, by simpa [KeyTable.rowSize,h] using hi⟩
    exact ⟨entryIndex t (⟨b,h⟩,.inl z),slot_at t reg _ _⟩
  · let z : Fin t.motifCount := ⟨i, by simpa [KeyTable.rowSize,h] using hi⟩
    let r : Fin t.bundles := ⟨b-t.bundles,by omega⟩
    refine ⟨entryIndex t (r,.inr z), ?_⟩
    rw [slot_at]
    change (t.bundles + (b-t.bundles))*t.stride+i = _
    rw [Nat.add_sub_of_le (by omega)]

/-- Single native table and one public parameter bank for all old IDs.
The total call count is the sum of the exact two fiber sizes over all ports. -/
theorem table_run (hsize : entryCount t < 2^w) (m : Memory w)
    (legal : ∀ b < 2*t.bundles, ∀ i < t.rowSize b, (m (t.idStart b+i)).val < t.arcCount) :
    ∃ rs, FullRun (parameters t) m (slot t reg) rs ∧
      t.Completed m (after m (eventLog rs)) (2*t.bundles) := by
  have eqn : slots t = 2*t.bundles*t.stride := by rw [slots,two_mul]
  have regions : ScanLayout (parameters t) (slots t) t.arcCount := by
    rw [eqn]; exact ⟨reg.idsFit,reg.keysFit,reg.outputFits,reg.idsApart,reg.keysApart⟩
  obtain ⟨rs,run⟩ := full_run (parameters t) m (slot t reg) regions (offset_eq t reg hsize) (fun j ↦ by
    obtain ⟨b,i,hb,hi,he⟩ := live t reg j
    change (m (t.idsBase.val+(slot t reg j).val)).val < _
    rw [he,← Nat.add_assoc]; exact legal b hb i hi)
  refine ⟨rs,run,⟨fun b hb i hi ↦ ?_,fun addr outside ↦ ?_⟩⟩
  · obtain ⟨j,he⟩ := cover t reg b hb i hi
    simpa only [KeyTable.lookup,KeyTable.idStart,KeyTable.outStart,he,Nat.add_assoc,show parameters t 4 = t.idsBase from rfl,show parameters t 5 = t.keyBase from rfl,show parameters t 6 = t.outputBase from rfl] using run.readback j
  · apply run.frame
    intro j
    obtain ⟨b,i,hb,hi,he⟩ := live t reg j
    change addr ≠ t.outputBase.val+(slot t reg j).val
    have bound := outside b hb
    dsimp [KeyTable.outStart] at bound
    rw [he]; omega

end CompressorRecords.BundleGather.Fixed

end VPVNP
end Computability
end OAI
