import OAI.Hierarchy.TaggedWideDatedResources
import OAI.Hierarchy.ProbeFixedWideDatedSockets

namespace OAI
/-! # Actual resources of the fixed dated part of both native programs -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage Native WideCPU
open ThreeFlat.RAM
open scoped Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

theorem wide_dated_resources (ell : ℕ) :
    ∃ K : ℕ,∀ h width unitCost rom work W,
      let g:=v.wideDated h width ell unitCost
      let T:=(events v.mesh).length
      (∑i,(g.sheets rom work i).ticks)≤K*2^h ∧
        text (ProcedureBank.program (Dated.last T) (fun i=>(g.sheets rom work i).code W))≤K ∧
        CheapCode (ProcedureBank.program (Dated.last T) (fun i=>(g.sheets rom work i).code W)) ∧
        g.romEnd rom≤rom+K*2^h ∧ g.workEnd work≤work+K*2^h := by
  obtain ⟨U,actual⟩:=v.wide_dated_role_inputs
  exact v.wide_dated_resources_of_roles ell U (fun h width unitCost=>actual h width ell unitCost)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
