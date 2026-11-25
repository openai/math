import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! A complete group vector has exactly one packed row at each host. -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentSIMDLookup ThreeFlat.Routing
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
noncomputable section
variable {groups shops : ℕ}
theorem whole_groups (pos : 0<groups) : chunks groups groups=1 := by
  unfold chunks poolBatchCount
  apply (Nat.div_eq_iff pos).mpr
  constructor <;> omega

def onlyBatch (pos : 0<groups) : Fin (chunks groups groups) := ⟨0,by rw [whole_groups pos];decide⟩

theorem whole_row (pos : 0<groups) (i : Fin shops) : (DescentSIMDLookup.row shops groups groups (i,onlyBatch pos)).val=i.val := by
  change (onlyBatch pos).val+chunks groups groups*i.val=_
  simp [onlyBatch,whole_groups pos]
end
end Hierarchy.DescentTerminalVertexFields

namespace Hierarchy.DescentTerminalPointerDigits.Gather
open DescentSIMDLookup
variable {H : ℕ}
theorem at_whole (groups : ℕ) (positive : 0<groups) (h : Fin H) (g : Fin groups) :
    (row H groups groups (position h g positive)).val=h.val ∧ (lane g positive).val=g.val := by
  have atZero : position h g positive=(h,DescentTerminalVertexFields.onlyBatch positive):=by
    apply Prod.ext
    · rfl
    · exact Fin.ext (Nat.div_eq_of_lt g.isLt)
  rw [atZero]
  exact ⟨DescentTerminalVertexFields.whole_row positive h,Nat.mod_eq_of_lt g.isLt⟩
end Hierarchy.DescentTerminalPointerDigits.Gather

end OAI
