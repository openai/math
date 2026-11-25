import OAI.Hierarchy.DescentTerminalCohortRoom
import OAI.Hierarchy.DescentPrivateMaskResources

namespace OAI
/-! # Word, address and instruction bounds for the physical terminal multiplicity program -/
namespace Hierarchy.DescentSixParty.NativeBranch
open DescentCompiler DescentCompiler.TerminalScale DescentResetGates Filter
variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec)

/-- The actual padded bank, mark tables, counter registers and checked program tariff
all use the same height, word size, calendar and free scalar grain. -/
theorem terminal_mask_setup (drift t f g reset e apertureRate τ B prior c : ℕ)
    (branch : G.b≤2^(capRate G t g)) (reserve : 5+(hostRate t reset*(t+1)+1)+e≤τ)
    (bought : 2*apertureRate+1≤B)
    (chart : 2*(τ+groupRate G t f g reset+(6*(terminalDegree G t f g reset+1)+19))≤B)
    (cpu : max (clockRate G t f g reset τ) (privateMaskArenaRate G t f g reset τ prior)≤c) :
    ∀ᶠ h : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
      ∀M base socket split q₀ : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J)
      M≤2^(2*h) → 2^h≤2*(M*S.copies) → 0<socket → 0<split → socket≤ scale J e →
      socket*split≤ scale J apertureRate → q₀≤h → base≤2^(prior*h) →
      let p:=split*(h/(16*(socket*split)))
      let W:=c*h
      let homes:=S.hostSize S.length
      let cap:=terminalCohortCapacity G S op q₀ p drift
      let cells:=terminalCohortCells G S op q₀ p drift
      32*((S.groupCount S.length*S.radix)*actualSpan G S op q₀ p drift)≤h ∧
      Nat.log 2 (privateMax G S p)+1≤W ∧ base+cells+cap+homes+homes+3<2^W ∧
      (privateMaskedClock cells cap homes S.radix p+privateMaskedNames cells cap S.radix p)*W*S.epochPower≤
        3213*c*((M*S.copies)*p) := by
  filter_upwards [terminal_cohort_room G op drift t f g reset τ B branch (by omega) chart,
    stage_mask_resources G t f g reset e apertureRate τ B prior c reserve bought cpu] with h charts runs
  dsimp only
  intro M base socket split q₀ slots funded used positive socketSize packetSize qword earlier
  let p:=split*(h/(16*(socket*split)))
  let S:=stageNumbers G t (Nat.log 2 h/(2*B)) f g reset M (tail τ (Nat.log 2 h/(2*B)))
  obtain ⟨fits,page⟩:=charts M p q₀ (physical_grain_le h socket split used) qword
  exact ⟨fits,runs M base socket split _ _ slots funded used positive socketSize packetSize page earlier
    (terminalCohortCells_le G S op q₀ p drift)⟩

end Hierarchy.DescentSixParty.NativeBranch

end OAI
