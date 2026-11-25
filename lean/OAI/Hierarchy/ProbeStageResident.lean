import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Resident natural-valued word columns -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

/-- Contents of a bank are specified on the actual logical domain. Every
function appearing in the public tables below is independent of the matching. -/
def Resident {k w : ℕ} (b : Bank) (mem : Memory w) (f : Fin k → ℕ) : Prop :=
  ∀ i, b.read mem (i.val : Word w) = (f i : Word w)

theorem Resident.of_cells {k w : ℕ} (b : Bank) (m : Memory w) (f : Fin k → ℕ)
    (size : k ≤ b.size) (word : k ≤ 2^w) (stored : ∀ i, m (b.base+i.val) = (f i : Word w)) :
    Resident b m f := by
  intro i
  change m (b.base+(i.val : Word w).val%b.size) = _
  rw [Fin.val_cast_of_lt (i.isLt.trans_le word), Nat.mod_eq_of_lt (i.isLt.trans_le size)]
  exact stored i

end Hierarchy.ProbeStage.Native

end OAI
