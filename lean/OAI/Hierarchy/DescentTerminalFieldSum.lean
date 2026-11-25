import OAI.Hierarchy.DescentTerminalPhysicalFieldCount
import OAI.Hierarchy.DescentTerminalCohortRate

namespace OAI
/-! # The nine physical terminal channel widths on the calibrated calendar -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentPrimitivePalette
open DescentTerminalVertexFields Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec)

/-- The actual shape fed to the terminal host readers. -/
def earnedFormat (S : AtomSchedule) (q p drift : ℕ) : Home.Format :=
  let K:=NativeBranch.privateSlotCapacity G S drift
  let tags:=DescentBundleTagKeys.capacity (colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op)
    (max 8 (2^S.capGain)) K p drift
  ⟨q,tags,K,S.epochPower^S.localTokenExponent,K,p,S.groupCount S.length⟩

theorem earned_field_sum (S : AtomSchedule) (q p drift : ℕ) :
    fieldSum (earnedFormat G op S q p drift) S.radix=
      S.groupCount S.length*S.radix*actualSpan G S op q p drift :=by
  apply (Nat.pow_right_inj (by decide : 1<(2:ℕ))).mp
  rw [←terminalCohortCapacity_eq G S op q p drift]
  unfold terminalCohortCapacity cohortSize
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

theorem earned_field_rate (drift t f g reset τ B : ℕ) (branch : G.b≤2^(capRate G t g)) (pos : 0<B)
    (scaleBuy : 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀M p q : ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
        p≤h → q≤h → 32*fieldSum (earnedFormat G op S q p drift) S.radix≤h :=by
  filter_upwards [terminal_cohort_room G op drift t f g reset τ B branch pos scaleBuy] with h paid
  dsimp only
  intro M p q small short
  rw [earned_field_sum]
  exact (paid M p q small short).1

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
