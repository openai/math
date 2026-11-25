import OAI.Hierarchy.DescentPrivateGateScale
import OAI.Hierarchy.DescentPrivateShapeNumbers
import OAI.Hierarchy.DescentCalendarNumbers

namespace OAI
/-! # The cofinal clock bound for the terminal private gate on the chosen physical calendar -/

namespace Hierarchy.DescentSixParty.NativeBranch
open DescentCompiler DescentCompiler.TerminalScale Filter

variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The reset gate stride is fixed by the chosen degree and rotor word count.
The residual population may vary with the epoch height and the input.
One cutoff works for every later refinement of the binary age denominator. -/
theorem stage_private_gate (t f g reset degree rotorBits e : ℕ) :
    ∃cutoff,∀B≥cutoff,∀ᶠ h : ℕ in atTop,
      let J:=Nat.log 2 h/(2*B)
      ∀M tail factor W socket : ℕ, let S:=stageNumbers G t J f g reset M tail
      2^h≤2*(M*S.copies) → W≤factor*h → 0< socket → socket≤ scale J e →
      let R:=max 1 (max rotorBits (degree*rotorBits))
      let bits:=privateSlotBits G S R*privateSlotCapacity G S R
      let p:=h/(16*socket)
      2*bits≤h ∧ terminalGateBill h W factor (Reached.siteLimit S) bits p*S.epochPower≤
        318*factor*((M*S.copies)*p) := by
  let R:=max 1 (max rotorBits (degree*rotorBits))
  let model:=stageNumbers G t 0 f g reset 0 0
  let n:=operandExponent G model+model.localTokenExponent
  let v:=model.hostGain*(model.rounds+1)
  refine ⟨2*e+(v+(2*(n+1)+1)+1),?_⟩
  intro B bought
  filter_upwards [eventually_private_gate R n v e B bought] with h paid
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro M tail factor W socket fund cpu occupied short
  let S:=stageNumbers G t J f g reset M tail
  have sites : Reached.siteLimit S=(M*S.copies)*(2^J)^v := packedSiteLimit S
  exact paid M S.copies (Reached.siteLimit S) factor W socket fund sites cpu occupied short

end Hierarchy.DescentSixParty.NativeBranch

end OAI
