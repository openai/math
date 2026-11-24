import OAI.Computability.VPVNP.PairSimulationSelectorReindex

/-! # A common pre-selection state for the physical compressor

Each motif admits the zero supply vector. This gives a selected level whose
header can be constructed before the first guessed bit, at every input
state and in either kind of compressor pass.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open Compression CompressorRecords CompressorRecords.SelectedTerms
open scoped Classical

variable {k R : Type*} [Field k] [CommRing R] {S : BlockSchedule k}
variable {B : S.Templates} {f : B.Entry → R} {hf : B.IsSolution f}
variable {a g b n : ℕ} {X : State a g} {p : StatePass R X b n}

/-- The outer term with all supply payload widths zero is admitted independently
of the current demand vector. -/
noncomputable def defaultSelection (o : PassOrigin B f hf p) : p.step.Choice :=
  (termRows o).rows.symm fun j =>
    ⟨fun _ => 0, by
      apply (MotifConversion.mem_outerIndices_iff (grid o).block (grid o).qPos _ _).mpr
      simp [MotifAdmission.admit,MotifAdmission.energy]⟩

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
