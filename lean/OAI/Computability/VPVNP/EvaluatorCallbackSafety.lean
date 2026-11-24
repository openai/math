import OAI.Computability.VPVNP.EvaluatorReadInterface
import OAI.Computability.VPVNP.RoutineSpace
import OAI.Computability.VPVNP.SpaceRunMonotone

/-!
# Storage specification of the coordinate-entry readers

The streamed determinant queries may take exponentially many ticks. Their
workspace bound records the peak height of each stack independently.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Evaluator.MatrixCallbacks

open RAMTape SliceArithmetic

variable {P : Type} [DecidableEq P] {p e w v : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Algebra (ZMod p) K] {c : Vector p e}
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (dim : BurstRAM.Word v) (extra : Stacks P)

/-- Correct coordinate readback, with a peak bound on every stack throughout
the deterministic call. Row and column use the scheduler's path orientation. -/
def ReadsEntryWithin (read : FiniteRoutine (ReadPort P)) (w label time peak : ℕ)
    (matrix : Matrix (Fin dim.val) (Fin dim.val) K) : Prop :=
  ∀ (s : Fin dim.val × K) (j : Fin dim.val), ∃ d ≤ time, read.BoundedRun peak d
    (queryBank (List.replicate label true) (WeightedStep.bank φ w dim s.1
      (BurstRAM.wordBits (Fin.castLE dim.isLt.le j : BurstRAM.Word v)) [] s.2 extra))
    (queryBank (List.replicate label true) (WeightedStep.bank φ w dim s.1
      (BurstRAM.wordBits (Fin.castLE dim.isLt.le j : BurstRAM.Word v))
      (WeightedStep.bits φ w (matrix s.1 j)) s.2 extra))

/-- The same exact run supplies the count computation's readback law. -/
theorem ReadsEntryWithin.readsEntry {read : FiniteRoutine (ReadPort P)} {label time peak : ℕ}
    {matrix : Matrix (Fin dim.val) (Fin dim.val) K}
    (h : ReadsEntryWithin φ dim extra read w label time peak matrix) :
    ReadsEntry φ dim extra read w label time matrix := by
  intro s j
  obtain ⟨d, hd, hr⟩ := h s j
  exact ⟨d, hd, hr.runs⟩

theorem ReadsEntryWithin.mono {read : FiniteRoutine (ReadPort P)} {label time peak time' peak' : ℕ}
    {matrix : Matrix (Fin dim.val) (Fin dim.val) K} (ht : time ≤ time') (hp : peak ≤ peak')
    (h : ReadsEntryWithin φ dim extra read w label time peak matrix) :
    ReadsEntryWithin φ dim extra read w label time' peak' matrix := by
  intro s j
  obtain ⟨d, hd, run⟩ := h s j
  exact ⟨d, hd.trans ht, run.mono_cap hp⟩

end Evaluator.MatrixCallbacks

end VPVNP
end Computability
end OAI
