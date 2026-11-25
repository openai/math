import OAI.Optimization.LinearProgramming.Compression.BinaryUnpackCounter

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- The even-bank output of the isolated call, before publishing the contiguous packet. -/
structure DoubledPacket (m : Memory ℚ) (n d sign : ℕ) (digit : ℕ → ℕ) : Prop where
  numeratorWidth : m.index 0 = 2*n
  denominatorWidth : m.index 2 = 2*d
  negative : m.index 4 = 2*sign
  words : ∀ i < n+d, m.index (6+2*i)=2*digit i

/-- The saved header is beyond the last even-bank digit. The final physical copy advances
its read pointer there, allowing it to recover all three header cells after publication. -/
def endOfDoubledWords (n d : ℕ) : ℕ := 6+2*(n+d)

structure CountedPacket (m : Memory ℚ) (n d sign : ℕ) (digit : ℕ → ℕ) : Prop where
  pointer : m.index 1=endOfDoubledWords n d
  numeratorWidth : m.index 7=n
  denominatorWidth : m.index 9=d
  negative : m.index 4=2*sign
  count : m.data 5=((n+d:ℕ):ℚ)
  words : ∀ i<n+d, m.index (6+2*i)=2*digit i

structure StagedPacket (m : Memory ℚ) (n d sign : ℕ) (digit : ℕ → ℕ) : Prop where
  numeratorWidth : m.index (endOfDoubledWords n d)=n
  denominatorWidth : m.index (endOfDoubledWords n d+1)=d
  negative : m.index (endOfDoubledWords n d+2)=sign
  count : m.data 5=((n+d:ℕ):ℚ)
  words : ∀ i<n+d, m.index (6+2*i)=2*digit i

def countDoubledHeader : Block := .seq (.op (.const 5 0)) <| .seq (.op (.const 6 1)) <|
  .seq (.op (.addrConst 1 6)) (.seq (unpackCount 0 7) (unpackCount 2 9))

theorem countDoubledHeader_spec (m : Memory ℚ) (n d sign : ℕ) (digit : ℕ → ℕ) {P : ℚ → Prop}
    (safe : m.AllData P) (pack : DoubledPacket m n d sign digit) (hp : 0<n+d)
    (small : ∀ i : ℕ, i≤n+d → P (i:ℚ)) :
    ∃ t, Block.Eval (Memory.AllData P) countDoubledHeader m (8*(n+d)+9) t ∧
      CountedPacket t n d sign digit ∧ ∀ i, i≠5 → i≠6 → t.data i=m.data i := by
  let a := m.putData 5 0
  let b := a.putData 6 1
  let c := b.putIndex 1 6
  have hz : P (0:ℚ) := by simpa using small 0 (by omega)
  have h1 : P (1:ℚ) := by simpa using small 1 (by omega)
  have za := Block.Eval.op_const m 5 0 safe (safe.putData 5 hz)
  have zb := Block.Eval.op_const a 6 1 za.safe_end (za.safe_end.putData 6 h1)
  have zc := Block.Eval.op_addrConst b 1 6 zb.safe_end (zb.safe_end.putIndex _ _)
  obtain ⟨u,ur,un,up,us,ui,ud⟩ := unpackCount_spec c 0 7 n 6 0 zc.safe_end (Or.inl rfl) (Or.inl rfl)
    (by simpa [c,a,b] using pack.numeratorWidth) (by simp [c]) (by simp [c,b,a]) (by simp [c,b])
    (fun _ h => small _ (by omega))
  have ue (i : ℕ) : u.index (2*i)=m.index (2*i) := by
    rw [ui (2*i) (by omega) (by omega) (by omega)]; simp [c,b,a,show 2*i≠1 by omega]
  obtain ⟨v,vr,vd,vp,vs,vi,vdata⟩ := unpackCount_spec u 2 9 d (6+2*n) n ur.safe_end (Or.inr rfl) (Or.inr rfl)
    ((ue 1).trans pack.denominatorWidth) up (by simpa using us) ((ud 6 (by decide)).trans (by simp [c,b])) small
  have ve (i : ℕ) : v.index (2*i)=m.index (2*i) :=
    (vi (2*i) (by omega) (by omega) (by omega)).trans (ue i)
  refine ⟨v,?_,⟨?_,(vi 7 (by decide) (by decide) (by decide)).trans un,vd,(ve 2).trans pack.negative,vs,?_⟩,?_⟩
  · simpa only [countDoubledHeader,show 1+(1+(1+(8*n+3+(8*d+3))))=8*(n+d)+9 by omega] using za.seq (zb.seq (zc.seq (ur.seq vr)))
  · simpa only [endOfDoubledWords,Nat.mul_add,Nat.add_assoc] using vp
  · intro i hi
    rw [← show 2*(3+i)=6+2*i by omega,ve,show 2*(3+i)=6+2*i by omega]
    exact pack.words i hi
  · intro i i5 i6
    rw [vdata i i5,ud i i5]; simp [c,b,a,i5,i6]

end Compression
end LinearProgramming
end Optimization
end OAI
