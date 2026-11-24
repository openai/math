import OAI.Computability.VPVNP.PairTraversalScanDirectory
import OAI.Computability.VPVNP.CompressorSourceTransport

/-!
# Retaining a completed placement directory through later stages

The traversal only reads the owner column, count column and bounded child
rows of each elementary placement. Preserving those three regions carries
the typed directory from the producing memory to the final descriptor
memory, even as later workers update the scheduler and other levels.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows.Directory

open BurstRAM CompressorRecords LocalHistory NetworkKernel Compression
open private countAt_val rowAt_val from OAI.Computability.VPVNP.CompressorRecordPreimageScan
open scoped Classical

variable {w : ℕ} {A : Type*} [CommRing A] {N : Network} {t : Term A N}
variable {old : Order N.Site} {next : Order t.output.Site} {m m' : Memory w} {limit : ℕ}

/-- The bounded physical data cells of the raw placement, including
the unused capacity in every child row. -/
def cells (pub : Fin 6 → Word w) (x : ℕ) : Prop :=
  ((pub 1).val ≤ x ∧ x < (pub 1).val+(pub 0).val) ∨
  ((pub 3).val ≤ x ∧ x < (pub 3).val+(pub 2).val) ∨
  ((pub 5).val ≤ x ∧ x < (pub 5).val+(pub 2).val*(pub 4).val)

omit [CommRing A] in
theorem cells_interval (d : Directory t old next m limit) {x : ℕ} (h : cells d.pub x) :
    (d.pub 1).val ≤ x ∧ x < limit := by
  obtain ⟨hc,hr,_⟩ := d.regions
  have hlim := d.inputEnd
  rcases h with h|h|h <;> omega

/-- A later worker can change any address outside the actual placement
arrays. The same table, bounds and ordered preimage witnesses then apply
in the later memory. -/
def transport (d : Directory t old next m limit) (agree : SourceTransport.Agree (cells d.pub) m m') :
    Directory t old next m' limit := by
  refine ⟨d.pub,d.oldCount,d.newCount,d.regions,d.inputEnd,⟨?_,?_⟩,d.capacity⟩
  · intro i hi
    change m' (d.pub 1+i).val = _
    have hlo := d.regions.ownersBeforeCounts
    have hv : i.val < (d.pub 0).val := hi
    have haddr : (d.pub 1+i).val = (d.pub 1).val+i.val :=
      (Fin.val_add ..).trans (Nat.mod_eq_of_lt (by have h' := (d.pub 3).isLt; omega))
    have region : cells d.pub (d.pub 1+i).val := Or.inl (by rw [haddr]; omega)
    exact (agree _ region).symm.trans (d.collected.owners i hi)
  · intro v hv
    obtain ⟨hc,hr⟩ := d.collected.rows v hv
    have count := countAt_val d.regions hv
    have row := rowAt_val d.regions hv
    have vmax : v.val < (d.pub 2).val := hv
    have cap := d.capacity v hv
    refine ⟨(congrArg Fin.val (agree _ (Or.inr (Or.inl (by rw [count]; omega))))).symm.trans hc,?_⟩
    intro i
    have hi := i.isLt.trans_le cap
    have hg := Nat.mul_le_mul_right (d.pub 4).val (Nat.succ_le_of_lt vmax)
    rw [Nat.succ_mul] at hg
    have region : cells d.pub ((rowAt d.pub v).val+i.val) := Or.inr (Or.inr (by rw [row]; omega))
    exact (agree _ region).symm.trans (hr i)

end PairSimulation.TraversalRows.Directory

end VPVNP
end Computability
end OAI
