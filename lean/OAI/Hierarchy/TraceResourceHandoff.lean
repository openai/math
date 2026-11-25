import OAI.Hierarchy.TraceResourceRoom
import OAI.ThreeFlat.RAM.PhysicalInputCopy

namespace OAI
/-! # Publish the true per-factor resource rows to the grid register

The counting passes use increasing scratch addresses inside the archive workspace. A
contiguous ten-label native copy sends the completed matrix to the separate public grid
resource bank while retaining the parent, list and charge records in their original banks.
-/
namespace Hierarchy.TraceAdmission.Resources
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical

def transfer (W src count dst : ℕ) : Procedure W :=
  ⟨10,5,3,PhysicalInputCopy.block W,PhysicalInputCopy.parameters src count dst⟩

theorem transfer_spec {W : ℕ} (src count dst : ℕ) (source : src+count<2^W)
    (target : dst+count<2^W) (prior : dst ≤ src) :
    (transfer W src count dst).Spec (fun _=>True)
      (fun m o=>o=PhysicalInputCopy.copied src count dst m) (6+5*count) := by
  intro P R K M pc reg pub exit installed data c m start _
  exact ⟨_,le_rfl,_,_,PhysicalInputCopy.advance_copy M pc reg pub exit src count dst installed data
    source target (.inl prior) c m start,PhysicalInputCopy.finalConfig_pc ..,rfl⟩

def handoff (W ctrl dst : ℕ) (p : Parameters ℕ) : Procedure W :=
  ((scratchPass W ctrl).seq (resourcePass W ctrl)).seq (transfer W p.resources (resourceLength p) dst)

def publicRows {W : ℕ} (dst : ℕ) (p : Parameters ℕ) (m : Memory W) :=
  PhysicalInputCopy.copied p.resources (resourceLength p) dst (completed p m)

theorem handoff_spec {W ctrl header dst : ℕ} (p : Parameters ℕ) (r : Room W ctrl header p)
    (m old : Memory W) (H : Header ctrl header p m) (dest : Fin p.lanes→Fin p.roots)
    (lists : TraceIntervalScanner.Output p.heads p.links dest old m) (prior : dst≤p.resources) :
    (handoff W ctrl dst p).Spec (·=m) (fun _ o=>o=publicRows dst p m)
      (ticks ctrl p+(6+5*resourceLength p)) := by
  have src : p.resources+resourceLength p<2^W := r.space
  intro P R K machine
  exact PhysicalProcedure.Procedure.Spec.mono (A := handoff W ctrl dst p)
    (PhysicalProcedure.Procedure.Spec.seq
      (A := (scratchPass W ctrl).seq (resourcePass W ctrl))
      (B := transfer W p.resources (resourceLength p) dst)
      (publish p r m old H dest lists)
      (transfer_spec p.resources (resourceLength p) dst src
        ((Nat.add_le_add_right prior _).trans_lt src) prior)
      (fun _ _ _=>trivial))
    (fun _ h=>h) (by rintro _ out ⟨mid,rfl,rfl⟩;rfl) le_rfl machine

/-- Read any column directly at the public resource base chosen by the grid. -/
theorem public_row {W : ℕ} (dst : ℕ) (p : Parameters ℕ) (m : Memory W)
    (v : Fin p.roots) (j : Fin (p.directions+2)) :
    publicRows dst p m (dst+v.val*(p.directions+2)+j.val)=
      completed p m (p.resources+v.val*(p.directions+2)+j.val) := by
  rw [Nat.add_assoc,Nat.add_assoc]
  apply PhysicalInputCopy.copied_at
  have bound := Nat.mul_le_mul_right (p.directions+2) (Nat.succ_le_of_lt v.isLt)
  rw [Nat.succ_mul] at bound
  have := j.isLt
  dsimp [resourceLength]
  omega

/-- The column handoff preserves every cell outside the row matrix. -/
theorem public_frame {W : ℕ} (dst : ℕ) (p : Parameters ℕ) (m : Memory W) (z : ℕ)
    (free : z<dst ∨ dst+resourceLength p≤z) :
    publicRows dst p m z=completed p m z :=
  PhysicalInputCopy.copied_outside _ _ _ _ _ free

end Hierarchy.TraceAdmission.Resources

end OAI
