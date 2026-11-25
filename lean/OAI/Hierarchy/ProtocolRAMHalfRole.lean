import OAI.Hierarchy.ProtocolRAMSupergroupDirectory

namespace OAI
/-! # Static local-role decoder for permanent turn seats -/

namespace Hierarchy.ProtocolRAMHalfRole
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAMSupergroupDirectory
open scoped Fin.CommRing

def mount {W : ℕ} (start roles : ℕ) (mem : Memory W) :=
  store start (fun i : Fin (2*roles)=>i.val/2) mem

theorem read {W : ℕ} (start roles : ℕ) (mem : Memory W) (r : ℕ)
    (hr : r < 2*roles) (room : 2*roles ≤ 2^W) :
    (groupBank start (2*roles)).read (mount start roles mem) (r:Word W)=((r/2:ℕ):Word W) := by
  change mount start roles mem (start+(r:Word W).val%span (2*roles))=_
  rw [Fin.val_cast_of_lt (hr.trans_le room),Nat.mod_eq_of_lt (hr.trans (slotFits _))]
  exact store_read start (fun i : Fin (2*roles)=>i.val/2) mem ⟨r,hr⟩

theorem read_encoded {W : ℕ} (start roles : ℕ) (mem : Memory W) (r : Fin roles)
    (time : Bool) (room : 2*roles ≤ 2^W) :
    (groupBank start (2*roles)).read (mount start roles mem) ((2*r.val+time.toNat:ℕ):Word W)=(r.val:Word W) := by
  cases time <;> rw [read start roles mem _ (by have := r.isLt;simp <;> omega) room] <;> congr 1 <;> simp; omega

theorem space_le (roles : ℕ) : span (2*roles) ≤ 4*roles+2 := by
  have h := space (2*roles)
  omega

end Hierarchy.ProtocolRAMHalfRole

end OAI
