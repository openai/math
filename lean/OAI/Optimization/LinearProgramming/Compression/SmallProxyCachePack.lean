import OAI.Optimization.LinearProgramming.Compression.SmallProxyPackFramed
import OAI.Optimization.LinearProgramming.RAM.CallableRawTapes
import OAI.Optimization.LinearProgramming.RAM.CallableReturn

/-! Pack an affine row from the permanent service headers. The resulting raw
pair tape is valid for both the numerical sign and the mixed product's offset. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM RAM.Callable

theorem smallProxySink_store_safe (sink : TagSink) (tag : ℕ) (source target : Memory ℚ)
    {P : ℚ → Prop} (hs : (sink.store tag source).AllData P) (ht : target.AllData P) :
    (sink.store tag target).AllData P := by
  cases sink with
  | index => exact ht
  | indexMapped => exact ht
  | scalar d v =>
    apply ht.putData
    simpa [TagSink.store] using hs d

/-- Route permanent service pointers to the shared affine packer. -/
def smallCacheSourceBlock : Block :=
  .seq (.op (.addrCopy 0 83)) <| .seq (.op (.addrCopy 1 67)) <| .seq (.op (.addrCopy 2 81)) <|
    .seq (.op (.addrCopy 3 87)) <| .seq (.op (.addrCopy 9 88)) (.op (.load 8 86))

def smallCacheSource (m : Memory ℚ) : Memory ℚ :=
  (((((m.putIndex 0 (m.index 83)).putIndex 1 (m.index 67)).putIndex 2 (m.index 81)).putIndex 3
    (m.index 87)).putIndex 9 (m.index 88)).putData 8 (m.data (m.index 86))

theorem smallCacheSource_eval (m : Memory ℚ) {P : ℚ → Prop} (hm : m.AllData P) :
    Block.Eval (Memory.AllData P) smallCacheSourceBlock m 6 (smallCacheSource m) := by
  let a := m.putIndex 0 (m.index 83)
  let b := a.putIndex 1 (a.index 67)
  let c := b.putIndex 2 (b.index 81)
  let d := c.putIndex 3 (c.index 87)
  let e := d.putIndex 9 (d.index 88)
  have e₁ : Block.Eval (Memory.AllData P) (.op (.addrCopy 0 83)) m 1 a :=
    Block.Eval.op_addrCopy _ _ _ hm hm
  have e₂ : Block.Eval (Memory.AllData P) (.op (.addrCopy 1 67)) a 1 b :=
    Block.Eval.op_addrCopy _ _ _ hm hm
  have e₃ : Block.Eval (Memory.AllData P) (.op (.addrCopy 2 81)) b 1 c :=
    Block.Eval.op_addrCopy _ _ _ hm hm
  have e₄ : Block.Eval (Memory.AllData P) (.op (.addrCopy 3 87)) c 1 d :=
    Block.Eval.op_addrCopy _ _ _ hm hm
  have e₅ : Block.Eval (Memory.AllData P) (.op (.addrCopy 9 88)) d 1 e :=
    Block.Eval.op_addrCopy _ _ _ hm hm
  have e₆ := Block.Eval.op_load (safe := Memory.AllData P) e 8 86 hm (hm.putData 8 (hm _))
  exact e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq e₆))))

theorem smallCacheSource_index (m : Memory ℚ) (i : ℕ) (h : 10 ≤ i) :
    (smallCacheSource m).index i=m.index i := by
  simp [smallCacheSource,show i ≠ 0 by omega,show i ≠ 1 by omega,show i ≠ 2 by omega,
    show i ≠ 3 by omega,show i ≠ 9 by omega]

theorem smallCacheSource_data (m : Memory ℚ) (i : ℕ) (h : i ≠ 8) :
    (smallCacheSource m).data i=m.data i := Memory.putData_ne _ h _

def smallCacheRawBlock : Block := .seq smallCacheSourceBlock framedSmallProxyPackBlock

structure SmallCachePackFrame (n : ℕ) (m t : Memory ℚ) : Prop where
  scalars (i : ℕ) : i ≠ 0 → i ≠ 8 → (i < m.index 87 ∨ m.index 87+2*n+5 ≤ i) → t.data i=m.data i
  addresses (i : ℕ) : 10 ≤ i → i ≠ 55 → i ≠ 56 → i ≠ 57 → i ≠ 58 → i ≠ m.index 88 → t.index i=m.index i

/-- The query row begins at address 67 and ends in its offset. The cache's
pointers 81, 83, 86 designate grid, dimension and scale. The caller supplies
its disjoint scalar and address staging areas via 87 and 88. -/
theorem smallCacheRawTapes_spec {P : ℚ → Prop} (m : Memory ℚ) (n D C : ℕ) (c : ℤ)
    (a grid : Fin n → ℤ) (hm : m.AllData P) (hz : P 0) (size : m.index 83=n)
    (scale : m.data (m.index 86)=(D:ℚ)) (capacity : m.index 60=C+1)
    (hrow : 128 ≤ m.index 67) (hgrid : 128 ≤ m.index 81) (hout : 128 ≤ m.index 87)
    (hslot : 128 ≤ m.index 88)
    (sr : m.index 67+n < m.index 87 ∨ m.index 87+2*n+5 ≤ m.index 67)
    (sg : m.index 81+n ≤ m.index 87 ∨ m.index 87+2*n+5 ≤ m.index 81)
    (coeff : ∀ i : Fin n, m.data (m.index 67+i)=(a i:ℚ)) (rhs : m.data (m.index 67+n)=(c:ℚ))
    (numer : ∀ i : Fin n, m.data (m.index 81+i)=(grid i:ℚ)) :
    ∃ t, Block.Eval (Memory.AllData P) smallCacheRawBlock m (21*n+57) t ∧
      RawTapes t (m.index 87) (m.index 88) (C+1) (smallProxyScalarTape D c a grid) [n+1] ∧
      SmallCachePackFrame n m t := by
  let s := smallCacheSource m
  have hs := smallCacheSource_eval m hm
  have s0 : s.index 0=n := by simp [s,smallCacheSource,size]
  have s1 : s.index 1=m.index 67 := by simp [s,smallCacheSource]
  have s2 : s.index 2=m.index 81 := by simp [s,smallCacheSource]
  have s3 : s.index 3=m.index 87 := by simp [s,smallCacheSource]
  have s9 : s.index 9=m.index 88 := by simp [s,smallCacheSource]
  have s8 : s.data 8=(D:ℚ) := by simp [s,smallCacheSource,scale]
  obtain ⟨t,run,w,base,len,abase,alen,dim,sf,af⟩ := framedSmallProxyPackBlock_spec s n D c a grid
    hs.safe_end hz s0 s8 (by rw [s1]; omega) (by rw [s2]; omega) (by rw [s3]; omega)
    (by rw [s9]; omega) (by simpa only [s1,s3] using sr) (by simpa only [s2,s3] using sg)
    (fun i => by rw [s1,smallCacheSource_data m _ (by omega)]; exact coeff i)
    (by rw [s1,smallCacheSource_data m _ (by omega)]; exact rhs)
    (fun i => by rw [s2,smallCacheSource_data m _ (by omega)]; exact numer i)
  have keep (i : ℕ) (lo : 10 ≤ i) (h55 : i ≠ 55) (h56 : i ≠ 56) (h57 : i ≠ 57) (h58 : i ≠ 58)
      (hslot' : i ≠ m.index 88) : t.index i=m.index i :=
    (af i (Or.inr (by omega)) h55 h56 h57 h58 (s9 ▸ hslot')).trans (smallCacheSource_index m i lo)
  refine ⟨t,?_,⟨base.trans s3,len,abase.trans s9,alen,
    (keep 60 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)).trans capacity,?_,?_⟩,
    ⟨?_,keep⟩⟩
  · rw [show 21*n+57=6+(21*n+51) by omega]
    exact hs.seq run
  · intro j hj
    simpa only [s3,List.getElem?_eq_getElem hj,Option.getD_some] using w j hj
  · intro j hj
    have eq : j=0 := by simpa using hj
    subst j
    simpa only [s9,Nat.add_zero,List.getElem_cons_zero] using dim
  · intro i h0 h8 hwin
    exact (sf i h0 (by simpa only [s3] using hwin)).trans (smallCacheSource_data m i h8)

end Compression
end LinearProgramming
end Optimization
end OAI
