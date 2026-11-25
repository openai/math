import OAI.Optimization.LinearProgramming.Compression.ProxyResidentEncode

/-! A descending in-place expansion of one logical numerical cache word into the
two separate even physical lanes. The still-unread logical prefix is preserved. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ResidentInstall

open RAM GeneratorTable

structure Cursor {K : Type*} [Zero K] (j : ℕ) (s : Memory K) : Prop where
  source : s.index 0 = j
  outer : s.index 1 = 4*j+2
  inner : s.index 2 = 4*j
  zeroIndex : s.index 3 = 0
  stop : s.index 8 = 15
  cutoff : s.index 14 = 60
  zeroScalar : s.data 1 = 0

private def written {K : Type*} [Zero K] (s : Memory K) (j value : ℕ) : Memory K :=
  let a := (s.putIndex (4*j+2) (4*value+2)).putIndex (4*j) 0
  ((a.putData 0 (s.data j)).putData (4*j+2) (s.data j)).putData (4*j) 0

private theorem writePair_eval {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (P : K → Prop) (s : Memory K) (j value : ℕ) (hj : 16 ≤ j)
    (hs : s.AllData P) (hc : Cursor j s) (he : s.index 7 = 4*value+2) :
    Block.Eval (Memory.AllData P) writePair s 5 (written s j value) := by
  let a := s.putIndex (4*j+2) (4*value+2)
  let b := a.putIndex (4*j) 0
  let c := b.putData 0 (s.data j)
  let d := c.putData (4*j+2) (s.data j)
  let e := d.putData (4*j) 0
  have ea : Block.Eval (Memory.AllData P) (.op (.addrStore 1 7)) s 1 a := by
    simpa only [hc.outer,he,a] using
      (Block.Eval.op_addrStore (safe := Memory.AllData P) s 1 7 hs hs)
  have alo (i : ℕ) (hi : i<16) : a.index i = s.index i := by
    simp [a,show i≠4*j+2 by omega]
  have blo (i : ℕ) (hi : i<16) : b.index i = s.index i := by
    simpa [b,show i≠4*j by omega] using alo i hi
  have a2 := (alo 2 (by decide)).trans hc.inner
  have a3 := (alo 3 (by decide)).trans hc.zeroIndex
  have eb : Block.Eval (Memory.AllData P) (.op (.addrStore 2 3)) a 1 b := by
    simpa only [b,a2,a3] using (Block.Eval.op_addrStore (safe := Memory.AllData P) a 2 3 hs hs)
  have b0 := (blo 0 (by decide)).trans hc.source
  have b1 := (blo 1 (by decide)).trans hc.outer
  have b2 := (blo 2 (by decide)).trans hc.inner
  have cSafe : c.AllData P := hs.putData 0 (hs j)
  have ec : Block.Eval (Memory.AllData P) (.op (.load 0 0)) b 1 c := by
    have read := Block.Eval.op_load (safe := Memory.AllData P) b 0 0 eb.safe_end
      (eb.safe_end.putData 0 (eb.safe_end (b.index 0)))
    simpa only [c,b0,show b.data = s.data from rfl] using read
  have dSafe : d.AllData P := cSafe.putData (4*j+2) (hs j)
  have cp : c.index 1 = 4*j+2 := b1
  have cd : c.data 0 = s.data j := by simp [c]
  have ed : Block.Eval (Memory.AllData P) (.op (.store 1 0)) c 1 d := by
    simpa only [cp,cd] using (Block.Eval.op_store (safe := Memory.AllData P) c 1 0 cSafe
      (by simpa only [cp,cd] using dSafe))
  have dp : d.index 2 = 4*j := b2
  have dz : d.data 1 = 0 := by simpa [d,c,b,a,show 1≠4*j+2 by omega] using hc.zeroScalar
  have eSafe : e.AllData P := dSafe.putData _ (hc.zeroScalar ▸ hs 1)
  have ee : Block.Eval (Memory.AllData P) (.op (.store 2 1)) d 1 e := by
    simpa only [dp,dz] using (Block.Eval.op_store (safe := Memory.AllData P) d 2 1 dSafe
      (by simpa only [dp,dz] using eSafe))
  exact ea.seq (eb.seq (ec.seq (ed.seq ee)))

structure Row {K : Type*} [Zero K] (j value : ℕ) (s t : Memory K) : Prop where
  cursor : Cursor (j-1) t
  innerData : t.data (4*j) = 0
  innerIndex : t.index (4*j) = 0
  outerData : t.data (4*j+2) = s.data j
  outerIndex : t.index (4*j+2) = 4*value+2
  scalar : ∀ i, i≠0 → i≠4*j → i≠4*j+2 → t.data i = s.data i
  address : ∀ i, 10 ≤ i → i≠4*j → i≠4*j+2 → t.index i = s.index i

/-- One complete pair of nested memory cells is constructed, including both field
writes, both encoded address writes, and the movement of the three descending pointers. -/
theorem scatterResidentRow_eval {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (P : K → Prop) (s : Memory K) (j : ℕ) (hj : 16 ≤ j)
    (hs : s.AllData P) (hc : Cursor j s) :
    ∃ t k, k ≤ 12*sourceAddress j s+25 ∧
      Block.Eval (Memory.AllData P) scatterResidentRow s k t ∧ Row j (sourceAddress j s) s t := by
  let x := sourceAddress j s
  obtain ⟨a,k,hk,ea,ad,a7,ai⟩ := encodeResidentAddress_spec P s j hs hc.source hc.cutoff
  have keep (i : ℕ) (hm : i<4 ∨ 7 < i) : a.index i = s.index i :=
    ai i (by omega) (by omega) (by omega) (by omega)
  have ac : Cursor j a := ⟨(keep 0 (by decide)).trans hc.source,(keep 1 (by decide)).trans hc.outer,
    (keep 2 (by decide)).trans hc.inner,(keep 3 (by decide)).trans hc.zeroIndex,
    (keep 8 (by decide)).trans hc.stop,(keep 14 (by decide)).trans hc.cutoff,(congrFun ad 1).trans hc.zeroScalar⟩
  let b := written a j x
  have eb : Block.Eval (Memory.AllData P) writePair a 5 b := writePair_eval P a j x hj ea.safe_end ac a7
  let t := moveAddresses b retreat
  have et : Block.Eval (Memory.AllData P) (slotMoves retreat) b 9 t :=
    runAddressMoves P b retreat eb.safe_end
  have tdata : t.data = b.data := moveAddresses_data b retreat
  have bl (i : ℕ) (hi : i<16) : b.index i = a.index i := by
    simp [b,written,show i≠4*j by omega,show i≠4*j+2 by omega]
  have tl (i : ℕ) (hi : 3 ≤ i) : t.index i = b.index i := by
    simp [t,retreat,moveAddresses,applyAddressMove,show i≠0 by omega,show i≠1 by omega,show i≠2 by omega]
  have tLo (i : ℕ) (h3 : 3 ≤ i) (h16 : i<16) := (tl i h3).trans (bl i h16)
  have h0 := (bl 0 (by decide)).trans ac.source
  have h1 := (bl 1 (by decide)).trans ac.outer
  have h2 := (bl 2 (by decide)).trans ac.inner
  have r0 : t.index 0 = j-1 := by simp [t,retreat,moveAddresses,applyAddressMove,h0]
  have r1 : t.index 1 = 4*j+2-1-1-1-1 := by simp [t,retreat,moveAddresses,applyAddressMove,h1]
  have r2 : t.index 2 = 4*j-1-1-1-1 := by simp [t,retreat,moveAddresses,applyAddressMove,h2]
  have rData1 : t.data 1 = 0 := by
    rw [tdata]
    simpa [b,written,show 1≠4*j by omega,show 1≠4*j+2 by omega] using ac.zeroScalar
  refine ⟨t,k+(5+9),by omega,ea.seq (eb.seq et),?_⟩
  constructor
  · exact ⟨r0,r1.trans (by omega),r2.trans (by omega),(tLo 3 (by decide) (by decide)).trans ac.zeroIndex,
      (tLo 8 (by decide) (by decide)).trans ac.stop,(tLo 14 (by decide) (by decide)).trans ac.cutoff,rData1⟩
  · rw [tdata]; simp [b,written]
  · rw [tl _ (by omega)]; simp [b,written]
  · rw [tdata]; simpa [b,written,show 4*j+2≠4*j by omega] using congrFun ad j
  · rw [tl _ (by omega)]; simp [b,written,x]
  · intro i h0' h1' h2'
    rw [tdata]
    simpa [b,written,h0',h1',h2'] using congrFun ad i
  · intro i hi h1' h2'
    rw [tl _ (by omega)]
    simpa [b,written,h1',h2'] using keep i (Or.inr (by omega))

end ResidentInstall
end Compression
end LinearProgramming
end Optimization
end OAI
