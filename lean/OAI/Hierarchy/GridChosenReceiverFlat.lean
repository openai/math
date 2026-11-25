import OAI.Hierarchy.GridChosenReceiverTariff
import OAI.Hierarchy.PhysicalTraceDistribution

namespace OAI
/-! # From selected RAM rows to flats in every characteristic -/

noncomputable section
namespace Hierarchy.GridChosenReceiver

open ThreeFlat Diagonal PhysicalStage RAM
open TraceDistribution GridScale GridInstalledEvaluator Filter

/-- For the compressor issued by the actual finite expander sequence, all
open execution data are restricted to the selected machine words and their
authentic cost. The receiver program and its constructors are specified by
`Compiled`, and its kernel never receives a value to reproduce. -/
def Receives {F : Type} [Field F] [Fintype F] (B : Block F) (m : ℕ) : Prop :=
  ∃ cutoff : ℕ,
    ∀ A>max cutoff (UniversalTick.saving+2+(0+51)), ∀ Q loss, Envelopes Q loss →
      ∀ q : ℕ→ℕ, (∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) →
        ∀ᶠ w : ℕ in atTop, ∀ t : ℕ,5120≤t → 64*w=16*t^10 → Even w →
          ∀ (v : TickSelection F (m+1) A w Q loss),v.copies=q w →
          ∀ (I : Installed B m A w (degree B) (stageRate B) rootRate v)
            (R : GridInstalledFit.Receipt B m A w (degree B) (stageRate B) rootRate v I reserve 0),
            Compiled I R

theorem compiler_of_selected {F : Type} [Field F] [Fintype F] (m : ℕ)
    (family : NonlinearExpanders.SpectralFamily F)
    (selected : Receives (compressionBlock_of_expanders family).some.physical m) :
    GridTraceCompiler F (m+1) := by
  let B:=(compressionBlock_of_expanders family).some.physical
  obtain ⟨cut,build⟩:=selected
  exact of_compiled B m (degree B) (stageRate B) rootRate reserve 0 cut build

/-- Sufficient native constructions with an actual field-independent width
and descent implementation give all target dimensions over every field. -/
theorem all_flats_of_selected
    (width : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2≤k → HasSpectralFlat (ZMod p) k →
      ¬HasSpectralFlat (ZMod p) (k+1) → NonlinearExpanders.SpectralFamily (ZMod p) →
        Tagged.RadixBound (ZMod p) k ∧ Tagged.WidthReductions (ZMod p) k)
    (descent : ∀ (p : ℕ) [Fact p.Prime], CollapseOracle.Descent (ZMod p))
    (selected : ∀ (p : ℕ) [Fact p.Prime] (m : ℕ), 2≤ m+1 →
      ∀ family : NonlinearExpanders.SpectralFamily (ZMod p),
        Receives (compressionBlock_of_expanders family).some.physical m)
    (F : Type*) [Field F] (d : ℕ) : HasSpectralFlat F d := by
  apply all_flats_of_native_constructions width descent _ F d
  intro p _ k large family
  cases k with
  | zero => omega
  | succ m => exact compiler_of_selected m family (selected p m large family)

end Hierarchy.GridChosenReceiver
end

end OAI
