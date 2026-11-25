import OAI.Hierarchy.DescentTerminalCohortSize
import OAI.Hierarchy.DescentTerminalIssuedScale
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # The literal capacity of all nine terminal fields at the calendar width -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentResetGates DescentPrimitivePalette
open DescentTerminalVertexFields Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) (op : RotorSpec)
variable (q p drift : ℕ)
local notation "K" => NativeBranch.privateSlotCapacity G S drift
local notation "palette" => colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
local notation "tags" => DescentBundleTagKeys.capacity palette (max 8 (2^S.capGain)) K p drift
local notation "nodes" => S.epochPower^S.localTokenExponent
local notation "table" => cohortSize (q:=q) (t:=tags) (H:=K) (N:=nodes) (A:=K) (w:=p)
  (groups:=S.groupCount S.length) (blocks:=S.radix)

/-- All nine fields of every candidate group/block slot, including unoccupied slots. -/
def terminalCohortCapacity := table

theorem terminalCohortCapacity_eq :
    terminalCohortCapacity G S op q p drift=2^(S.groupCount S.length*S.radix*actualSpan G S op q p drift) :=
  cohort_size

theorem terminal_cohort_room (t f g reset τ B : ℕ) (branch : G.b≤2^(capRate G t g)) (positive : 0<B)
    (bought : 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))≤B) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀M p q : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J)
        p≤h → q≤h →
        32*((S.groupCount S.length*S.radix)*actualSpan G S op q p drift)≤h ∧
          terminalCohortCapacity G S op q p drift≤2^(h/2) := by
  let σ:=6*(terminalDegree G t f g reset+1)+19
  filter_upwards [issued_terminal_spans G op drift t f g reset τ B branch positive,
    eventually_home τ (groupRate G t f g reset) σ B positive bought] with h spans layouts
  dsimp only
  intro M p q pw qw
  let J:=Nat.log 2 h/(2*B)
  let S:=stageNumbers G t J f g reset M (tail τ J)
  let k:=groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
  have slots : S.groupCount S.length*S.radix≤2^(tail τ J)*2^k :=by
    simp [S,k,AtomSchedule.groupCount,stageNumbers]
  have room:=layouts.2 k _ _ slots (groupBits_linear ..) (spans M p q pw qw).1
  refine ⟨room,?_⟩
  rw [terminalCohortCapacity_eq]
  apply Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
  change 32*((S.groupCount S.length*S.radix)*actualSpan G S op q p drift) ≤ h at room
  change (S.groupCount S.length*S.radix)*actualSpan G S op q p drift ≤ h/2
  omega

end
end Hierarchy.DescentSixParty

end OAI
