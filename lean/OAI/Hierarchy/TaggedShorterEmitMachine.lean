import OAI.Hierarchy.TaggedShorterEmitMachineCore
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Cheap machine instructions for the concrete shorter-board emitter -/

namespace Hierarchy.TaggedShorterEmitMachine
open ThreeFlat.RAM
open ProtocolRAM

theorem replay_cheap (W src count : ℕ) : CheapCode (EffectSeed.scatter W src count) := by
  intro P K K' pc reg pub exit i
  change Fin 9 at i
  fin_cases i <;> trivial

theorem scanReplay_cheap (W src rows count : ℕ) (e : Expr) :
    CheapCode ((scan W src rows e).seq (EffectSeed.scatter W src count)) :=
  @cheap_seq W (scan W src rows e) (EffectSeed.scatter W src count)
    (scan_cheap W src rows e) (replay_cheap W src count)

theorem cheap (A : Tables) (W src R γ sink : ℕ) : CheapCode (procedure W src R γ sink A) :=
  @scanReplay_cheap W src (10*R) (5*R) (term A γ sink)

end Hierarchy.TaggedShorterEmitMachine

end OAI
