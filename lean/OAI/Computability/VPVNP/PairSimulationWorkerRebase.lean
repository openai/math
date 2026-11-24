import OAI.Computability.VPVNP.CompressorSourceTransport
import OAI.Computability.VPVNP.PairSimulationSelectorReindex

/-! # Transport of worker inputs across changes to scheduler memory -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open Compression CompressorRecords CompressorRecords.SelectedTerms NetworkKernel BurstRAM

variable {k : Type*} [Field k] {S : BlockSchedule k} {B : S.Templates}
  {A : Type*} [CommRing A] {f : B.Entry → A} {hf : B.IsSolution f}
  {a g b n w : ℕ} {X : State a g} {p : StatePass A X b n} {o : PassOrigin B f hf p}

/-- Run a worker from a new memory agreeing on the region containing its demand rows. -/
noncomputable def WorkerInput.rebase (I : WorkerInput o w) (m : Memory w) (lo : ℕ)
    (readable : ∀ i, lo ≤ (I.layout.source i).val)
    (agree : SourceTransport.Agree (lo ≤ ·) I.memory m) : WorkerInput o w :=
  { I with
    memory := m
    inputs := by
      intro i
      funext x
      obtain ⟨j, rfl⟩ := (grid o).demandOrder.entries.surjective x
      have h := congrFun (I.inputs i) ((grid o).demandOrder.entries j)
      rw [DemandPreparation.demandAt_address _ _ _ (I.layout.sourceFits i)] at h ⊢
      exact (congrArg Fin.val (agree _ ((readable i).trans (Nat.le_add_right ..)))).symm.trans h }

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
