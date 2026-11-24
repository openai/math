import OAI.Computability.VPVNP.CompressorUniformEvaluator
import OAI.Computability.VPVNP.CompressorSliceReader

/-! # Uniform envelope of the physical compressor-coordinate readers

For fixed characteristic and circuit exponent the same advice length bound
covers every eligible prime, compressor slice and coordinate call. The
Cramer query clock and its peak space enter on different scales.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

open LabelEvaluator RankQuery.Stack.Coordinate

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)

theorem exists_compressor_reader_envelope
    (ps : List (Evaluator.WeightedStep.Port CompressorReader.Ports)) (q c : ℕ) :
    ∃ a : ℕ → ℕ, PolynomiallyBounded a ∧ ∀ n, ∀ (hn : 2≤n) (p : Nat.Primes),
      (q ≠ 0 → p.val=q) → (q=0 → p.val ≤ 2^B.compressorPrimeBits c n) →
      ∀ M : Model p (B.compressorDegree n) (B.compressorEquations hn c),
        ∃ H : B.SliceReaderAdvice M (CompressorReader.read true) (CompressorReader.read false), H.envelope ps ≤ a n := by
  have hw := B.coordinateWidth_polynomial q c
  obtain ⟨sp,ex,_,_,hfit,hcost⟩ := B.coordinateBudgets CompressorReader.Parts CompressorReader.Work
    CompressorReader.K q c hw
  let cost (n : ℕ) := B.coordinateBudget CompressorReader.Parts CompressorReader.Work CompressorReader.K
    q c n (B.coordinateWidth q c n) (sp n) (ex n)
  obtain ⟨_,he,hv⟩ := B.compressorReaderWidths q c
  have hspace : PolynomiallyBounded (fun n => (cost n).space) := hcost.space
  have htime : PolynomiallyBounded (fun n => Nat.clog 2 (cost n).time) := hcost.time
  obtain ⟨a,ha,bound⟩ := B.exists_reader_envelope ps (CompressorReader.read true) (CompressorReader.read false)
    q c (B.coordinateWidth q c) (B.readerDegreeBudget q c) (B.readerLimbBudget q c)
    (fun n => (cost n).space) (fun n => (cost n).space) (fun n => Nat.clog 2 (cost n).time)
    hw he hv hspace hspace htime 0 (fun n _ hn p hp hz M => by
      obtain ⟨H,hi,hd,hv,hs,hm,hx⟩ := B.exists_sliceReaderAdvice q c hfit n hn p hp hz M
      exact ⟨H,hi.le,hd,hv,hs,hm,hx⟩)
  exact ⟨a,ha,fun n => bound n (Nat.zero_le _)⟩

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
