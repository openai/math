import OAI.Hierarchy.DescentHistoryPrivateLedger
import OAI.Hierarchy.DescentClosedReset

namespace OAI
/-! # Reblocking the closed reset does not hide any additional cables -/

namespace Hierarchy.DescentHistoryOrder
open DescentSixParty
noncomputable section
variable {P : Type} {D : ℕ} {bits : P→ℕ}
variable {F : Type} [Field F] {A : MarkedWorld F D P bits}

theorem mergeFee_appendNames (n : Normalize A) (site : Equiv.Perm n.result.graph.Site)
    (edge : Equiv.Perm n.result.graph.Edge) : mergeFee (n.appendNames site edge)=mergeFee n := by
  induction n with
  | done=>rfl
  | split _ _ _ _ rest ih=>exact ih site edge
  | named _ _ _ rest ih=>exact ih site edge
  | merge W V key hub k g rest ih=>exact congrArg (absorbed W.graph (MarkedWorld.address W key hub k g)+·) (ih site edge)

variable {q ε : ℝ} {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule} {k i z D' w hist n h C f g cut tail : ℕ}
variable {a : Reached A G q ε S k i z D' w hist} {ctl : ResetRates G S k D' n h C f g cut tail}

/-- Named reset reblocking only splits wires and permutes their public names. -/
@[simp] theorem reset_reblock_fee (b : ClosedReset a ctl) : mergeFee b.reblock=0 := by
  unfold ClosedReset.reblock ResetInput.namedReset
  rw [mergeFee_appendNames]
  rfl

end
end Hierarchy.DescentHistoryOrder

end OAI
