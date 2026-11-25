import OAI.Optimization.LinearProgramming.Compression.BinaryUnpackStage
import OAI.Optimization.LinearProgramming.Compression.BinaryUnpackWords

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- The read cursor now points to three saved, unscaled header cells. All public digits
occupy addresses at least three, so every write here leaves them intact. -/
def finishUnpacking : Block := .seq (.op (.addrLoad 0 1)) <| .seq (.op (.incr 1 1)) <|
  .seq (.op (.incr 2 1)) <| .seq (.op (.addrLoad 2 2)) (.op (.addrLoad 1 1))

structure PublishedPacket (m : Memory ℚ) (n d sign : ℕ) (digit : ℕ → ℕ) : Prop where
  numeratorWidth : m.index 0=n
  denominatorWidth : m.index 1=d
  negative : m.index 2=sign
  words : ∀ i < n+d, m.index (3+i)=digit i

theorem finishUnpacking_spec (m : Memory ℚ) (n d sign : ℕ) (digit : ℕ → ℕ) {P : ℚ → Prop}
    (safe : m.AllData P) (pack : CompactPacket m n d sign digit) :
    ∃ t, Block.Eval (Memory.AllData P) finishUnpacking m 5 t ∧ PublishedPacket t n d sign digit ∧ t.data=m.data := by
  let H := endOfDoubledWords n d
  have high : 6 ≤ H := by dsimp [H,endOfDoubledWords]; omega
  let a := m.putIndex 0 n
  let b := a.putIndex 1 (H+1)
  let c := b.putIndex 2 (H+2)
  let v := c.putIndex 2 sign
  let t := v.putIndex 1 d
  have loadN : m.index (m.index 1)=n := by rw [pack.pointer,pack.numeratorWidth]
  have ptr : a.index 1=H := by simpa [a] using pack.pointer
  have ptrB : b.index 1=H+1 := Memory.putIndex_same ..
  have loadSign : c.index (c.index 2)=sign := by
    rw [show c.index 2=H+2 from Memory.putIndex_same ..]
    calc
      _ = b.index (H+2) := Memory.putIndex_ne _ (by omega) _
      _ = a.index (H+2) := Memory.putIndex_ne _ (by omega) _
      _ = m.index (H+2) := Memory.putIndex_ne _ (by omega) _
      _ = sign := pack.negative
  have ptrV : v.index 1=H+1 := by simp [v,c,b]
  have loadD : v.index (v.index 1)=d := by
    rw [ptrV]
    calc
      _ = c.index (H+1) := Memory.putIndex_ne _ (by omega) _
      _ = b.index (H+1) := Memory.putIndex_ne _ (by omega) _
      _ = a.index (H+1) := Memory.putIndex_ne _ (by omega) _
      _ = m.index (H+1) := Memory.putIndex_ne _ (by omega) _
      _ = d := pack.denominatorWidth
  have e1 : Block.Eval (Memory.AllData P) (.op (.addrLoad 0 1)) m 1 a := by
    simpa only [a,loadN] using Block.Eval.op_addrLoad m 0 1 safe (safe.putIndex _ _)
  have e2 : Block.Eval (Memory.AllData P) (.op (.incr 1 1)) a 1 b := by
    simpa only [b,ptr] using Block.Eval.op_incr a 1 1 e1.safe_end (e1.safe_end.putIndex _ _)
  have e3 : Block.Eval (Memory.AllData P) (.op (.incr 2 1)) b 1 c := by
    simpa only [c,ptrB] using Block.Eval.op_incr b 2 1 e2.safe_end (e2.safe_end.putIndex _ _)
  have e4 : Block.Eval (Memory.AllData P) (.op (.addrLoad 2 2)) c 1 v := by
    simpa only [v,loadSign] using Block.Eval.op_addrLoad c 2 2 e3.safe_end (e3.safe_end.putIndex _ _)
  have e5 : Block.Eval (Memory.AllData P) (.op (.addrLoad 1 1)) v 1 t := by
    simpa only [t,loadD] using Block.Eval.op_addrLoad v 1 1 e4.safe_end (e4.safe_end.putIndex _ _)
  refine ⟨t,e1.seq (e2.seq (e3.seq (e4.seq e5))),⟨by simp [t,v,c,b,a],by simp [t],by simp [t,v],?_⟩,rfl⟩
  intro i hi
  simpa [t,v,c,b,a,show 3+i ≠ 0 by omega,show 3+i ≠ 1 by omega,show 3+i ≠ 2 by omega] using pack.words i hi

/-- The only scalar registers touched by the entire physical address compactor are 5 and 6. -/
def unpackAddressPacket : Block :=
  .seq countDoubledHeader (.seq stageDoubledHeader (.seq compactDoubledWords finishUnpacking))

theorem unpackAddressPacket_spec (m : Memory ℚ) (n d sign : ℕ) (digit : ℕ → ℕ) {P : ℚ → Prop}
    (safe : m.AllData P) (pack : DoubledPacket m n d sign digit) (positive : 2 ≤ n+d)
    (hs : sign ≤ 1) (bits : ∀ i < n+d, digit i ≤ 1) (small : ∀ i : ℕ, i ≤ n+d → P (i:ℚ)) :
    ∃ t, Block.Eval (Memory.AllData P) unpackAddressPacket m (19*(n+d)+24) t ∧
      PublishedPacket t n d sign digit ∧ ∀ i, i ≠ 5 → i ≠ 6 → t.data i=m.data i := by
  obtain ⟨a,ea,counts,fa⟩ := countDoubledHeader_spec m n d sign digit safe pack (by omega) small
  obtain ⟨b,eb,staged,fb⟩ := stageDoubledHeader_spec a n d sign digit ea.safe_end counts positive hs
  obtain ⟨c,ec,compact,fc⟩ := compactDoubledWords_spec b n d sign digit eb.safe_end staged bits small
  obtain ⟨t,et,result,ft⟩ := finishUnpacking_spec c n d sign digit ec.safe_end compact
  refine ⟨t,?_,result,?_⟩
  · simpa only [unpackAddressPacket,show 8*(n+d)+9+(6+(11*(n+d)+4+5))=19*(n+d)+24 by omega] using ea.seq (eb.seq (ec.seq et))
  · intro i i5 i6; rw [ft,fc i i5 i6,fb,fa i i5 i6]

end Compression
end LinearProgramming
end Optimization
end OAI
