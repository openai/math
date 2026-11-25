import OAI.Optimization.LinearProgramming.Compression.MinorBatchBounds
import OAI.Optimization.LinearProgramming.Compression.MinorDetFrame

/-! Repeated exact minor requests through one fixed scalar/address RAM program. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorLoad

open RAM

theorem fixedMinorCall {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    BatchCallSpec K determinantBlock := by
  intro v m N hi hdst hm hn hk P initialP hz ho hneg hreg
  obtain ⟨t, c, hcost, eval, hanswer, hframe⟩ := determinantBlock_eval m hi hdst P initialP hz ho hneg hreg
  have hbound := determinantBlock_costBound hm hn hk hcost
  exact ⟨t,c,by omega,eval,hanswer,hframe,determinantBlock_index_frame eval⟩

/-- This code is independent of both the matrix dimensions and the number and identities of the requests. -/
def determinantBatchProgram : Program := batchProgram determinantBlock

/-- Every case runs in the same program at the same instruction address. The descriptor tape
and original input remain available after all answers have been placed in consecutive slots. -/
theorem determinantBatch_trace {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {q : ℕ} (v : BatchLayout K q) (m : Memory K) (initial : BatchInput v m)
    (N : ℕ) (hN : ∀a, (v.query a).m≤N ∧ (v.query a).n≤N ∧ (v.query a).k≤N) (P : K → Prop)
    (initialP : ∀ p, P (m.data p)) (hz : P 0) (ho : P 1) (hneg : ∀ x, P x → P (-x))
    (hreg : ∀a, ∀j<(v.query a).k, ∀r : BirdRegister (v.query a).k,
      P (r.read ((v.query a).matrix.submatrix (v.query a).row (v.query a).col)
        (birdLayer ((v.query a).matrix.submatrix (v.query a).row (v.query a).col) j))) :
    ∃ k ≤ q*(2200*(N+1)^7+17)+3, ∃ tr : Fin (k+1) → State K,
      Trace determinantBatchProgram (m.atPC 0) k tr ∧ (tr (Fin.last k)).output = some 0 ∧
      (∀ a : Fin q, (tr (Fin.last k)).data (v.answerBase+a.val)=answerOf (v.query a)) ∧
      (∀ a, 7≤a → a<v.answerBase → (tr (Fin.last k)).data a=m.data a) ∧
      (∀ a, 20≤a → (tr (Fin.last k)).index a=m.index a) ∧ ∀ i p, P ((tr i).data p) := by
  exact batchProgram_trace determinantBlock fixedMinorCall v m initial N hN P initialP hz ho hneg hreg

/-- In the rational case, performing additional determinant calls never compounds the bit bound.
The polynomial depends on the largest matrix dimension and the initial scalar encoding lengths. -/
theorem determinantBatch_bits {q : ℕ} (v : BatchLayout ℚ q) (m : Memory ℚ) (initial : BatchInput v m)
    (N B : ℕ) (hN : ∀a, (v.query a).m≤N ∧ (v.query a).n≤N ∧ (v.query a).k≤N)
    (hb : ∀ p, ratBits (m.data p) ≤ B) :
    ∃ k ≤ q*(2200*(N+1)^7+17)+3, ∃ tr : Fin (k+1) → State ℚ,
      Trace determinantBatchProgram (m.atPC 0) k tr ∧ (tr (Fin.last k)).output = some 0 ∧
      (∀ a : Fin q, (tr (Fin.last k)).data (v.answerBase+a.val)=answerOf (v.query a)) ∧
      (∀ a, 7≤a → a<v.answerBase → (tr (Fin.last k)).data a=m.data a) ∧
      (∀ a, 20≤a → (tr (Fin.last k)).index a=m.index a) ∧ ∀ i, scalarBound (detRegisterBits N B) (tr i) := by
  exact batchProgram_bits determinantBlock fixedMinorCall v m initial N B hN hb

end MinorLoad
end Compression
end LinearProgramming
end Optimization
end OAI
