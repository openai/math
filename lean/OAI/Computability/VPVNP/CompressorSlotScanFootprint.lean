import OAI.Computability.VPVNP.CompressorRecordsOrdinalFootprint
import OAI.Computability.VPVNP.RAMChoicePrefix

/-!
# External events of a dense native slot scan

Each successful call advances the cursor by one. A memory invariant can
retain initialized input columns while the scan fills its output.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotEventBounds

open BurstRAM SourceTransport

variable {w : ℕ}

/-- Lift the address bounds of one empty-tape call to the entire ordinal scan. -/
theorem scan {Q : Type*} (P : Program w Q) (fuel n : ℕ)
    (events : Memory w → Word w → List (Event w)) (I : Memory w → Prop) (read write : ℕ → Prop)
    (native : ∀ m i, execute P fuel (P.start i) m [] = some ⟨events m i,some (i+1)⟩)
    (step : ∀ j < n, ∀ m, I m → let es := events m (Fin.ofNat (2^w) j)
      Reads read es ∧ Writes write es ∧ I (after m es))
    (m : Memory w) (rs : List (Report w)) (init : I m)
    (run : runSegment P fuel (some 0) m (List.replicate n []) = some rs) :
    Reads read (eventLog rs) ∧ Writes write (eventLog rs) := by
  apply OrdinalRun.footprint P fuel (Fin.ofNat (2^w)) n (fun _ ↦ I) read write _ 0 _ m rs (by simp) init run
  intro j hj m hm bits rep executed
  let i := Fin.ofNat (2^w) j
  have equal := (execute_prefix_unique (native m i)
    (show execute P fuel (P.start i) m ([]++bits) = some rep from executed)).2
  subst rep
  obtain ⟨rd,wr,inv⟩ := step j hj m hm
  refine ⟨congrArg some ?_,inv,rd,wr⟩
  apply Fin.ext; simp [i,Fin.val_add,Nat.mod_add_mod,Nat.add_mod_mod]

end CompressorRecords.SlotEventBounds

end VPVNP
end Computability
end OAI
