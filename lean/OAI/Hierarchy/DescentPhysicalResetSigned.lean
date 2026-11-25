import OAI.Hierarchy.DescentDatedPhysicalReset
import OAI.Hierarchy.DescentResetWindowTail

namespace OAI
/-! # The dated candidate and rank operands of the signed-window issuer -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open ProtocolRAM DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (v : ResetOutput)
local notation "A" => v.receiver

/-- Numerical expression templates shared by all inputs at one program date. -/
structure RenderInputs where
  «meta» : Fin (A).blocks→Fin (A).candidates→Expr
  offsets : Fin (A).blocks→Fin 3→Fin (A).candidates→Expr

variable (input : v.RenderInputs) (base degree : ℕ)
def renderProgram (w : ℕ) :=
  DescentResetWindowTail.program (v.rankEnd base) (A).blocks degree (A).capacity v.assemblerBits
    (A).lanes (A).hosts (A).groups w input.meta input.offsets
def renderTicks :=
  DescentResetWindowTail.time (v.rankEnd base) (A).blocks degree (A).capacity v.assemblerBits
    (A).lanes (A).hosts (A).groups input.meta input.offsets
def renderMemory {w : ℕ} (m : Memory w) :=
  DescentResetWindowTail.memory (v.rankEnd base) (A).blocks degree (A).capacity v.assemblerBits
    (A).lanes (A).hosts (A).groups input.meta input.offsets m

theorem render_end (width : (A).signedBits=v.assemblerBits) :
    DescentResetWindowTail.endAddress (v.rankEnd base) (A).blocks (A).capacity v.assemblerBits
      (A).lanes (A).hosts (A).groups=(A).rendered (v.fieldsEnd base) := by
  unfold PublicOutput.rendered
  rw [width]; rfl

/-- The same output also retains the private counter and all earlier receipts below the rank tape. -/
theorem render_any {w : ℕ} (m : Memory w) (width : (A).signedBits=v.assemblerBits)
    («meta» : ∀x j,(input.meta x j).Fits w (v.rankEnd base))
    (offsets : ∀x q j,(input.offsets x q j).Fits w (v.rankEnd base))
    (last : (A).rendered (v.fieldsEnd base)<2^w) :
    (v.renderProgram input base degree w).Exec m (v.renderMemory input base degree m) (v.renderTicks input base degree) ∧
    (∀i,i<v.rankEnd base ∨ (A).rendered (v.fieldsEnd base)≤ i → (v.renderMemory input base degree m) i=m i) ∧
    CheapCode (v.renderProgram input base degree w) := by
  have span:=v.render_end base width
  have seen:=DescentResetWindowTail.any (v.rankEnd base) (A).blocks degree (A).capacity v.assemblerBits
    (A).lanes (A).hosts (A).groups input.meta input.offsets m «meta» offsets (by simpa only [span] using last)
  exact ⟨seen.1,fun i cut=>seen.2.1 i (by rwa [span]),seen.2.2⟩

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
