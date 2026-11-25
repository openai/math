import OAI.Hierarchy.DescentTerminalIssuedScale

namespace OAI
/-! # Size of all possible raw role cells at the actual joint terminal age -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentResetGates DescentPrimitivePalette
open Filter
open scoped Classical BigOperators
noncomputable section
variable {F:Type} [Field F] (G:PoweredGadget F)

theorem terminal_raw_room (op:RotorSpec) (drift t f g reset τ B:ℕ)
    (branch:G.b≤2^(capRate G t g)) (pos:0<B)
    (ageFit:2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))≤B) :
    ∀ᶠ h:ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
      ∀M p q:ℕ, let S:=stageNumbers G t J f g reset M (tail τ J)
        p≤h→q≤h→32*((S.groupCount S.length*2^k)*actualRawSpan G S op p drift)≤h := by
  filter_upwards [issued_terminal_spans G op drift t f g reset τ B branch pos,
    eventually_home τ (groupRate G t f g reset) (6*(terminalDegree G t f g reset+1)+19) B pos ageFit]
    with h prices homes
  dsimp only
  intro M p q hp hq
  apply homes.2 _ _ _ _ (groupBits_linear ..) ((prices M p q hp hq).2)
  simp only [AtomSchedule.groupCount,Nat.sub_self,pow_zero,Nat.mul_one,stageNumbers,Nat.le_refl]

end
end Hierarchy.DescentSixParty

end OAI
