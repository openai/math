import OAI.Hierarchy.DescentTerminalSliceWordRead
import OAI.Hierarchy.DescentTerminalSliceMachine
import OAI.Hierarchy.DescentTerminalDatedSliceWidth
import OAI.Hierarchy.DescentTerminalResetRoleArity
import OAI.Hierarchy.DescentTerminalPointerArchive

namespace OAI
/-! # The actual final date's primitive token, operand arity and repeated affine fields -/
namespace Hierarchy.DescentTerminalSliceRuns
open DescentTerminalSliceShelf DescentTerminalPointerDigits DescentSIMDLookup DescentPackedColony
open DescentCompiler DescentSixParty DescentDatedAddressBook ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable (v:ResetOutput) (base:ℕ)
local notation "A" => v.argumentSlots
local notation "B" => v.receiver.blocks
local notation "H" => v.receiver.hosts
local notation "N" => v.nodes
local notation "Gs" => v.receiver.groups
variable (tok:v.receiver.blocks=v.primitive.chart.blocks) (argc:v.receiver.blocks=v.metadata.chart.blocks)
local notation "field_" f:arg j:arg b:arg => v.terminalField base (Fin.natAdd 4 (f:Fin 3)) j b

def datedChart (c:Fin (Columns A)) (b:Fin B) : Gather.Address :=
  .hosts (Sum.elim (fun (j:Fin 2)=>if j.val=0 then v.terminalRole base (b.cast tok)
    else v.terminalArity base (b.cast argc))
    (fun (w:Fin (3*A))=>let z:Fin 3×Fin A:=finProdFinEquiv.symm w
      field_ z.1 z.2 b) (finSumFinEquiv.symm c))

def datedWidths : RawWidths := ⟨v.primitive.chart.bits,v.nodeBits,fun _=>v.nodeBits⟩

local notation "chart" => datedChart v base tok argc

theorem token_bank (b:Fin B) : chart (leading 0) b=.hosts (v.terminalRole base (b.cast tok)) := by
  simp [datedChart,leading]

theorem count_bank (b:Fin B) : chart (leading 1) b=.hosts (v.terminalArity base (b.cast argc)) := by
  simp [datedChart,leading]

theorem span_bank (f:Fin 3) (j:Fin A) (b:Fin B) : chart (triple f j) b=.hosts (field_ f j b) := by
  simp only [datedChart, triple, Equiv.symm_apply_apply, Sum.elim_inr]

variable {w d:ℕ} (start:ℕ) (ended:v.metadataEnd base≤ start) (room:start<2^w)
    (one:DescentSIMDLookup.chunks v.receiver.groups v.receiver.lanes=1)
    (tokenRows:v.receiver.hosts≤v.primitive.chart.rows) (countRows:v.receiver.hosts≤v.metadata.chart.rows)

include ended room one tokenRows countRows in
theorem dated_room (c:Fin (Columns A)) (b:Fin B) : (chart c b).Fits start H w := by
  let indeces:Fin 2 ⊕ Fin (3*A):=finSumFinEquiv.symm c
  have lim:=ended.trans_lt room
  rcases eqn:indeces with j|e
  · have hc:c=leading j:=by
      change finSumFinEquiv.symm c=Sum.inl j at eqn
      exact (finSumFinEquiv.symm_apply_eq.mp eqn)
    subst c
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · rw [token_bank]
      obtain ⟨fits,capacity⟩:=v.terminal_role_room base lim (b.cast tok)
      exact ⟨⟨fits.1,fits.2.1,fits.2.2.trans ((v.terminal_order base).2.2.trans ended)⟩,tokenRows.trans capacity⟩
    · rw [count_bank]
      obtain ⟨fits,capacity⟩:=v.terminal_arity_room base lim (b.cast argc)
      exact ⟨⟨fits.1,fits.2.1,fits.2.2.trans ended⟩,countRows.trans capacity⟩
  · obtain ⟨⟨f,j⟩,ef⟩:=finProdFinEquiv.surjective e
    have hc:c=triple f j:=by
      change finSumFinEquiv.symm c=Sum.inr e at eqn
      exact finSumFinEquiv.symm_apply_eq.mp (by simpa [ef] using eqn)
    subst c
    rw [span_bank]
    obtain ⟨fits,capacity⟩:=v.terminal_field_room base lim (Fin.natAdd 4 f) j b
    have order:=v.terminal_order base
    exact ⟨⟨fits.1,fits.2.1,fits.2.2.trans (order.1.trans (order.2.1.trans (order.2.2.trans ended)))⟩,
      by simpa only [one,Nat.mul_one] using capacity⟩

end
end Hierarchy.DescentTerminalSliceRuns

end OAI
