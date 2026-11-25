import OAI.Optimization.LinearProgramming.Compression.BinaryPublicLayout
import OAI.Optimization.LinearProgramming.Compression.BinaryAddressDigits

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM OracleSpec.MinorLog Finset
open scoped BigOperators

theorem digitSum_le_width (a n : ℕ) : (∑ i ∈ range n, integerDigit a i) ≤ n := by
  calc
    _ ≤ ∑ _i ∈ range n, 1 := sum_le_sum fun i _ => by rcases integerDigit_cases a i with h | h <;> omega
    _ = n := by simp

private def prepareNumerator : Block := .seq (.op (.const 0 9)) <| .seq (.op (.add 0 4 0)) <|
  .seq (.op (.addrConst 1 10)) (.seq (.op (.addrConst 2 3)) (.op (.copy 3 1)))

def publishNumerator : Block := .seq prepareNumerator addressDigitsBlock

structure NumeratorPublished (m : Memory ℚ) (q : ℚ) (k : ℕ) : Prop where
  buffer : PaddedReply m q k
  numeratorWidth : m.data 1 = (width q.num.natAbs : ℚ)
  denominatorWidth : m.data 2 = (width q.den : ℚ)
  nextBase : m.data 0 = ((10+k : ℕ) : ℚ)
  cursor : m.index 2 = 3 + width q.num.natAbs
  digits : ∀ j < width q.num.natAbs, m.index (3+j) = integerDigit q.num.natAbs j

theorem publishNumerator_spec (m : Memory ℚ) (q : ℚ) (k : ℕ) {P : ℚ → Prop}
    (safe : m.AllData P) (sized : SizedReply m q k) (hw : width q.num.natAbs ≤ k)
    (small : ∀ z : ℕ, z ≤ k+10 → P (z:ℚ)) :
    ∃ s t, Block.Eval (Memory.AllData P) publishNumerator m s t ∧ s ≤ 10*k+8 ∧
      NumeratorPublished t q k := by
  let N := width q.num.natAbs
  let m1 := m.putData 0 9
  let m2 := m1.putData 0 (m1.data 4+m1.data 0)
  let m3 := m2.putIndex 1 10
  let m4 := m3.putIndex 2 3
  let z := m4.putData 3 (m4.data 1)
  have span : m1.data 4+m1.data 0 = ((10+k:ℕ):ℚ) := by simp [m1,sized.position]; ring
  have h9 : P (9:ℚ) := by exact_mod_cast small 9 (by omega)
  have e1 := Block.Eval.op_const m 0 9 safe (safe.putData 0 h9)
  have e2 := Block.Eval.op_add m1 0 4 0 e1.safe_end (e1.safe_end.putData _ (span ▸ small (10+k) (by omega)))
  have e3 := Block.Eval.op_addrConst m2 1 10 e2.safe_end (e2.safe_end.putIndex _ _)
  have e4 := Block.Eval.op_addrConst m3 2 3 e3.safe_end (e3.safe_end.putIndex _ _)
  have e5 := Block.Eval.op_copy m4 3 1 e4.safe_end (e4.safe_end.putData 3 (e4.safe_end 1))
  have prep : Block.Eval (Memory.AllData P) prepareNumerator m 5 z := e1.seq (e2.seq (e3.seq (e4.seq e5)))
  have nd : z.data 3 = (N:ℚ) := by simp [z,m4,m3,m2,m1,N,sized.numeratorWidth]
  have io : z.index 2 = 3 := by simp [z,m4]
  have ir : z.index 1 = 10 := by simp [z,m4,m3]
  have clean (i : ℕ) (h0 : i ≠ 0) (h3 : i ≠ 3) : z.data i = m.data i := by simp [z,m4,m3,m2,m1,h0,h3]
  have zb := sized.toPaddedReply.preserve (fun i hi => clean i (by omega) (by omega))
  have input (i : ℕ) (hi : i < N) : z.data (z.index 1+i) = ((integerDigit q.num.natAbs i : ℕ):ℚ) := by
    rw [ir]; exact zb.num i (hi.trans_le hw)
  obtain ⟨t,run,_,_,dst,bits,fd,_⟩ := addressDigitsBlock_spec z N (integerDigit q.num.natAbs)
    prep.safe_end nd (by omega) (fun i _ => by rcases integerDigit_cases q.num.natAbs i with h | h <;> omega)
    input (fun i _ => by rw [ir]; omega) (fun x h => small x (by dsimp [N] at *; omega))
  have saved (i : ℕ) (h3 : i ≠ 3) (h4 : i ≠ 4) (h5 : i ≠ 5) (h8 : i ≠ 8) := fd i h3 h4 h5 h8
  have tb : PaddedReply t q k := by
    refine ⟨(saved 6 (by decide) (by decide) (by decide) (by decide)).trans zb.value,
      (saved 7 (by decide) (by decide) (by decide) (by decide)).trans zb.sign,?_,?_⟩
    · intro i hi; exact (saved _ (by omega) (by omega) (by omega) (by omega)).trans (zb.num i hi)
    · intro i hi; exact (saved _ (by omega) (by omega) (by omega) (by omega)).trans (zb.den i hi)
  have cost := digitSum_le_width q.num.natAbs N
  refine ⟨_,t,prep.seq run,by dsimp [N] at *; omega,tb,?_,?_,?_,?_,?_⟩
  · exact (saved 1 (by decide) (by decide) (by decide) (by decide)).trans ((clean 1 (by decide) (by decide)).trans sized.numeratorWidth)
  · exact (saved 2 (by decide) (by decide) (by decide) (by decide)).trans ((clean 2 (by decide) (by decide)).trans sized.denominatorWidth)
  · rw [saved 0 (by decide) (by decide) (by decide) (by decide)]; simpa [z,m4,m3,m2] using span
  · simpa only [io,N] using dst
  · simpa only [io,N] using bits

end Compression
end LinearProgramming
end Optimization
end OAI
