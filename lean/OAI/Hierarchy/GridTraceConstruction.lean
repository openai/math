import OAI.Hierarchy.GridChosenReceiverTerminalRun

namespace OAI
/-! # Distributing the native universal grid trace -/

noncomputable section
namespace Hierarchy
namespace GridChosenReceiver

open ThreeFlat Diagonal.PhysicalStage
open TraceDistribution GridScale Filter
open scoped Classical

/-- Each finite compressor block supplies the chosen grid receiver, with the
same program and word size at every site. -/
theorem receives {F : Type} [Field F] [Fintype F] (B : Block F) (m : ℕ) : Receives B m := by
  apply receives_of_terminal B m
  intro A _ Q loss env q range
  filter_upwards [eventual_installed_terminal B env m A q range] with w stored
  intro age _ aligned even v copies I R geom
  exact stored age aligned even v copies I R geom

/-- A single nonlinear expander family fixes the compressor before the
controller, replaces every selected tick, and yields its native trace
distribution on a cofinal set of word sizes. -/
theorem native_grid {F : Type} [Field F] [Fintype F] (k : ℕ) (positive : 0<k)
    (family : NonlinearExpanders.SpectralFamily F) : GridTraceCompiler F k := by
  obtain ⟨m,rfl⟩:=Nat.exists_eq_succ_of_ne_zero positive.ne'
  exact compiler_of_selected m family (receives _ m)

end GridChosenReceiver

/-- The finite-characteristic compiler and spectral expander constructions
supply the diagonal for every field once the tagged width and oracle descent
constructions are available. -/
theorem all_flats_of_width_and_descent
    (width : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 2≤k → HasSpectralFlat (ZMod p) k →
      ¬HasSpectralFlat (ZMod p) (k+1) → NonlinearExpanders.SpectralFamily (ZMod p) →
        Tagged.RadixBound (ZMod p) k ∧ Tagged.WidthReductions (ZMod p) k)
    (descent : ∀ (p : ℕ) [Fact p.Prime], CollapseOracle.Descent (ZMod p))
    (F : Type*) [Field F] (d : ℕ) : HasSpectralFlat F d := by
  apply all_flats_of_native_constructions width descent _ F d
  intro p _ k hk family
  exact GridChosenReceiver.native_grid k (by omega) family

end Hierarchy
end

end OAI
