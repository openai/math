import OAI.Hierarchy.DescentTerminalSeedCircuit
import OAI.Hierarchy.DescentTerminalWeightedHost
import OAI.Hierarchy.DescentTerminalEpochEntries

namespace OAI
/-! # The actual seed weight at one unary gate per packed count bit -/
namespace Hierarchy.DescentTerminalSeedChip
open Catalyst CatalystSubstitution Tagged DescentSeedRoot DescentTerminalLocalFactors
open ThreeFlat Routing
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {k data R s : ℕ} (X : Approximation F k data) {B : Type} [Fintype B]
  (input : Select X R s→B)
local notation "D" => digitsNeeded s
local notation "T" => Fintype.card (CountKey X R)

theorem value (z : B→Bool) :
    TypedWiring.value (circuit X input) z=
      ∏i : CountKey X R,(originalScalar X i)^(rawCount X (z∘input) i).val := by
  rw [circuit,RadixStage.pullPins_value]
  let dig:=fun a : Fin T×Fin D=>z (input ((Fintype.equivFin (CountKey X R)).symm a.1,a.2))
  have ok : Sum.elim z id ∘ pin X input=pins (fun t:Empty=>t.elim) (fun t:Empty=>t.elim) dig := by
    funext u;rcases u with ⟨_,e⟩|a
    · exact e.elim
    · rfl
  rw [ok,network_value]
  simp only [IsEmpty.forall_iff,ite_true]
  rw [←(Fintype.equivFin (CountKey X R)).prod_comp]
  apply Finset.prod_congr rfl
  intro i _
  simp only [coeff,Equiv.symm_apply_apply]
  rw [ProtocolStackContraction.power_bits (originalScalar X i) _ D (rawCount X (z∘input) i).isLt]
  apply Finset.prod_congr rfl
  intro b hb
  simp [dig,raw_digits]

theorem epoch {u ε : ℝ} (G : DescentSixParty.PoweredGadget F) (hu : 0≤u) (he : 0≤ε) {J h C Ht t : ℕ}
    (run : DescentSixParty.Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J (DescentInitialHost.initialGroup X R s))
    (c : (DescentSixParty.Epochs.finish G hu he run).Choice) (z : B→Bool)
    (issued : ∀i,(rawCount X (z∘input) i).val=DescentTerminalReadout.seedCount X R s G hu he run c i) :
    TypedWiring.value (circuit X input) z=(DescentSixParty.Epochs.finish G hu he run).weight c := by
  rw [value,DescentTerminalReadout.epoch_weight X R s G hu he run c]
  exact Finset.prod_congr rfl (fun i _=>congrArg ((originalScalar X i)^·) (issued i))

end
end Hierarchy.DescentTerminalSeedChip

end OAI
