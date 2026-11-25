import OAI.Optimization.LinearProgramming.Compression.BinaryPublicNumerator
import OAI.Optimization.LinearProgramming.Compression.ServiceReadHeader

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM OracleSpec.MinorLog Finset
open scoped BigOperators

def publishDenominator : Block := .seq (.op (.copy 8 0)) <| .seq (.op (.copy 9 6)) <|
  .seq (headerToAddress 8 1) (.seq (.op (.copy 3 2)) addressDigitsBlock)

structure WordsPublished (m : Memory ℚ) (q : ℚ) : Prop where
  value : m.data 9 = q
  sign : m.data 7 = (if q.num < 0 then 1 else 0)
  numeratorWidth : m.data 1 = (width q.num.natAbs : ℚ)
  denominatorWidth : m.data 2 = (width q.den : ℚ)
  numerator : ∀ i < width q.num.natAbs, m.index (3+i) = integerDigit q.num.natAbs i
  denominator : ∀ i < width q.den, m.index (3+width q.num.natAbs+i) = integerDigit q.den i

theorem publishDenominator_spec (m : Memory ℚ) (q : ℚ) (k : ℕ) {P : ℚ → Prop}
    (safe : m.AllData P) (before : NumeratorPublished m q k) (hw : width q.den ≤ k)
    (small : ∀ z : ℕ, z ≤ k+10 → P (z:ℚ)) :
    ∃ s t, Block.Eval (Memory.AllData P) publishDenominator m s t ∧ s ≤ 14*k+50 ∧ WordsPublished t q := by
  let D := width q.den
  let N := width q.num.natAbs
  let a := m.putData 8 (m.data 0)
  let b := a.putData 9 (a.data 6)
  have e1 := Block.Eval.op_copy (safe := Memory.AllData P) m 8 0 safe (safe.putData _ (safe 0))
  have e2 := Block.Eval.op_copy (safe := Memory.AllData P) a 9 6 e1.safe_end (e1.safe_end.putData _ (e1.safe_end 6))
  have start : b.data 8 = ((10+k:ℕ):ℚ) := by simpa [a,b] using before.nextBase
  have h1 : P (1:ℚ) := by simpa using small 1 (by omega)
  obtain ⟨c,header,ir,ci,cd⟩ := headerToAddress_spec P b 8 1 (10+k) (by decide) (by decide)
    start e2.safe_end h1 (fun j hj => small j (by omega))
  have scalarInvariant : (fun s : Memory ℚ => ∀ i, P (s.data i)) = Memory.AllData P := by
    funext s
    rfl
  rw [scalarInvariant] at header
  let z := c.putData 3 (c.data 2)
  have cs : c.AllData P := header.safe_end
  have count := Block.Eval.op_copy (safe := Memory.AllData P) c 3 2 cs (cs.putData 3 (cs 2))
  have zd (i : ℕ) (hi3 : i ≠ 3) (hi0 : i ≠ 0) (hi6 : i ≠ 6) : z.data i = b.data i := by
    simpa [z,hi3] using cd i hi0 hi6
  have zi (i : ℕ) (h : i ≠ 1) : z.index i = m.index i := ci i h
  have ptr : z.index 1 = 10+k := ir
  have out : z.index 2 = 3+N := (zi 2 (by decide)).trans before.cursor
  have wd : z.data 3 = (D:ℚ) := by
    simp only [z,Memory.putData_same,cd 2 (by decide) (by decide)]; simpa [b,a,D] using before.denominatorWidth
  have input (i : ℕ) (hi : i < D) : z.data (z.index 1+i) = ((integerDigit q.den i : ℕ):ℚ) := by
    rw [ptr,zd _ (by omega) (by omega) (by omega)]
    simpa [a,b,show 10+k+i ≠ 9 by omega,show 10+k+i ≠ 8 by omega] using before.buffer.den i (hi.trans_le hw)
  obtain ⟨t,run,_,_,_,bits,fd,fi⟩ := addressDigitsBlock_spec z D (integerDigit q.den) count.safe_end wd (by omega)
    (fun i _ => by rcases integerDigit_cases q.den i with h | h <;> omega)
    input (fun i _ => by rw [ptr]; omega) (fun i hi => small i (by dsimp [D] at *; omega))
  have saved (i : ℕ) (i0 : i ≠ 0) (i3 : i ≠ 3) (i4 : i ≠ 4) (i5 : i ≠ 5) (i6 : i ≠ 6) (i8 : i ≠ 8) : t.data i = b.data i :=
    (fd i i3 i4 i5 i8).trans (zd i i3 i0 i6)
  have sum := digitSum_le_width q.den D
  refine ⟨_,t,e1.seq (e2.seq (header.seq (count.seq run))),by dsimp [D] at *; omega,?_,?_,?_,?_,?_,?_⟩
  · rw [saved 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simpa [b,a] using before.buffer.value
  · rw [saved 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simpa [b,a] using before.buffer.sign
  · rw [saved 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simpa [b,a] using before.numeratorWidth
  · rw [saved 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; simpa [b,a] using before.denominatorWidth
  · intro i hi
    rw [fi (3+i) (by omega) (Or.inl (by rw [out]; dsimp [N]; omega)),zi (3+i) (by omega)]
    exact before.digits i hi
  · simpa only [out,N,D] using bits

end Compression
end LinearProgramming
end Optimization
end OAI
