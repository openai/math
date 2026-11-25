import OAI.Hierarchy.DescentOperandWidth
import OAI.Hierarchy.DescentSeedEpochRoom
import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Positive physical operand pitch on the selected initial venue -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

def SeedOperandLanesAt (t f g reset drift limit τ β h : ℕ) : Prop :=
  let J := Nat.log 2 h/(2*β)
  let k := groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
  ∀ M degree p, p≤h → degree≤limit →
    let S := stageNumbers G t J f g reset M (tail τ J)
    let bits := DescentOperandWidth.recordBits G S k (tail τ J) drift degree p
    4*bits≤h ∧ 0 < DescentSIMDLookup.lanes h (2*bits)

theorem seed_operand_lane_positive (t f g reset drift limit τ β : ℕ) (budget : 5≤β) :
    ∀ᶠ h : ℕ in atTop, SeedOperandLanesAt G t f g reset drift limit τ β h :=by
  have positive : 0<β:=by omega
  filter_upwards [DescentOperandWidth.issued G drift limit t f g reset τ β positive,
    age_room β positive,eventually_ge_atTop 1] with h width epoch payload
  dsimp only [SeedOperandLanesAt]
  intro M degree p pRoom degreeRoom
  let J:=Nat.log 2 h/(2*β)
  let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let bits:=DescentOperandWidth.recordBits G S k (tail τ J) drift degree p
  have fit : bits ≤ scale J 3:=width M p degree pRoom degreeRoom
  have four : 4*bits≤h:=(Nat.mul_le_mul_left 4 fit).trans (epoch_room h β 3 payload budget epoch.1)
  have offset : Nat.log 2 p+1≤bits:=le_max_right ..
  refine ⟨four,?_⟩
  change 0<h/(2*(2*bits))
  exact Nat.div_pos (by omega) (by omega)

end Hierarchy.DescentDatedSeedStartup

end OAI
