import OAI.Computability.BorderVNP.PackedSiteEpochs
import OAI.Computability.BorderVNP.ShortenDenseSiteEpoch

/-! # Public packing factory for the actual sorted cable directories -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PhysicalEpochs.Factory

open Crossing Cover Epoch Epoch.Round Shortening
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m}

namespace Dense



variable (S : PackedHistoryCircuit.Normalized.SiteSchedule e)

/-- The level-specific sorted machine precedes each child tuple. Its run
keeps the actual directory, histograms and attained minimizing terminal move. -/
structure Programs where
  /-- Fixed public schedule with its true sorted rows and finite stage choices. -/
  machine : ∀ d ≥ S.floor, ∀ (P : Type) [Fintype P] (bits : P → ℕ),
    PackedHistoryCircuit.Normalized.SiteMachine S d P bits
  /-- Same public machine evaluated at each legal child tuple. -/
  run : ∀ d (hd : d ≥ S.floor) (P : Type) [Fintype P] (bits : P → ℕ)
    (input : Fin (S.fanIn^S.rounds) → Pack D P bits K)
    (route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget),
    PackedHistoryCircuit.Normalized.SiteExecution S (machine d hd P bits) input route

/-- The public program can use the specified row requests and selections
from the compiler. Subsequent quantitative and tagged proofs work on those
actual machines and their selected executions. -/
theorem exists_programs
    (cert : ∀ d ≥ S.floor, ∀ (P : Type) [Fintype P] (bits : P → ℕ),
      S.HasPrograms d P bits ∧ ∀ M : PackedHistoryCircuit.Normalized.SiteMachine S d P bits, S.RunsInputs M)
    (before : ∀ d ≥ S.floor, ∀ (P : Type) [Fintype P] (bits : P → ℕ), S.InputRows d P bits)
    (after : ∀ d ≥ S.floor, ∀ (P : Type) [Fintype P] (bits : P → ℕ), S.OutputRows d P bits)
    (sel : ∀ d ≥ S.floor, ∀ (P : Type) [Fintype P] (bits : P → ℕ), S.Selections d P bits) :
    ∃ U : Programs S, ∀ d hd P (fp : Fintype P) bits,
      (@U.machine d hd P fp bits).before = @before d hd P fp bits ∧
      (@U.machine d hd P fp bits).after = @after d hd P fp bits ∧
      (@U.machine d hd P fp bits).select = @sel d hd P fp bits := by
  let choose := fun d hd P (fp : Fintype P) bits =>
    (@cert d hd P fp bits).1.2 (@before d hd P fp bits) (@after d hd P fp bits) (@sel d hd P fp bits)
  let U : Programs S := ⟨fun d hd P fp bits => (choose d hd P fp bits).choose,
    fun d hd P fp bits input route =>
      (PackedHistoryCircuit.Normalized.SiteSchedule.RunsInputs.exists_run S
        ((@cert d hd P fp bits).2 _) input route).some⟩
  exact ⟨U,fun d hd P fp bits => (choose d hd P fp bits).choose_spec⟩

end Dense

/-- Physical outer factory using the real normalized histogram expansion.
No change of scalar field or replacement of the sorted cable order occurs. -/
noncomputable def ofDenseSchedule {S : PackedHistoryCircuit.Normalized.SiteSchedule e}
    (program : Dense.Programs S) : Factory D K where
  L := S.budget
  hL := S.budget_pos
  generators := S.generators
  stages := S.rounds
  stages_pos := S.rounds_pos
  k := S.fanIn
  k_two := S.fanIn_two
  drop := S.drop
  floor := S.floor
  weight := S.weight
  weight_pos := S.weight_pos
  E := S.error
  E_pos := S.error_pos
  choose d hd _ _ _ input route := (program.run d hd _ _ input route).expansion

end Packing.PhysicalEpochs.Factory

end BorderVNP
end Computability
end OAI
