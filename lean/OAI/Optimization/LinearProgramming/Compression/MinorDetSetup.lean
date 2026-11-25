import OAI.Optimization.LinearProgramming.Compression.UniformBirdInput

/-! Translate the loader’s output registers into the input convention of the fixed
Bird determinant subroutine. No scalar data is read or changed by this block. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorLoad

open RAM

def prepareDeterminant : Block :=
  .seq (.op (.addrCopy 0 2)) (.seq (.op (.addrCopy 1 5)) (.seq (.op (.addrConst 14 0))
    (.seq (cellAddress 11 8 9 1 0 0 14) (cellAddress 12 8 9 11 0 0 14))))

def prepareCost (n : ℕ) : ℕ := 3 + 2*reserveCost n

theorem prepareDeterminant_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (n base : ℕ) (hn : m.index 2 = n) (hb : m.index 5 = base)
    (hs : ∀ j, P (m.data j)) :
    ∃ t, Block.Eval (fun z => ∀ j, P (z.data j)) prepareDeterminant m (prepareCost n) t ∧
      t.data = m.data ∧ t.index 0=n ∧ t.index 1=base ∧ t.index 11=base+n*n ∧
      t.index 12=base+n*n+n*n ∧ t.index 14=0 := by
  let a := m.putIndex 0 (m.index 2)
  let b := a.putIndex 1 (a.index 5)
  let c := b.putIndex 14 0
  have ea : Block.Eval (fun z => ∀ j, P (z.data j)) (.op (.addrCopy 0 2)) m 1 a :=
    Block.Eval.op_addrCopy _ _ _ hs hs
  have eb : Block.Eval (fun z => ∀ j, P (z.data j)) (.op (.addrCopy 1 5)) a 1 b :=
    Block.Eval.op_addrCopy _ _ _ hs hs
  have ec : Block.Eval (fun z => ∀ j, P (z.data j)) (.op (.addrConst 14 0)) b 1 c :=
    Block.Eval.op_addrConst _ _ _ hs hs
  have c0 : c.index 0 = n := by simp [c,b,a,Memory.putIndex,hn]
  have c1 : c.index 1 = base := by simp [c,b,a,Memory.putIndex,hb]
  have c14 : c.index 14 = 0 := by simp [c,Memory.putIndex]
  obtain ⟨u,hu,ud,uf,u11⟩ := reserve_one P c n 11 1 c0 c14 hs (by simp [CellScratchOK])
  have u0 := (uf 0 (by decide) (by decide) (by decide)).trans c0
  have u1 := (uf 1 (by decide) (by decide) (by decide)).trans c1
  have u14 := (uf 14 (by decide) (by decide) (by decide)).trans c14
  rw [c1] at u11
  obtain ⟨t,ht,td,tf,t12⟩ := reserve_one P u n 12 11 u0 u14 hu.safe_end (by simp [CellScratchOK])
  refine ⟨t, ?_, td.trans ud, (tf 0 (by decide) (by decide) (by decide)).trans u0,
    (tf 1 (by decide) (by decide) (by decide)).trans u1,
    (tf 11 (by decide) (by decide) (by decide)).trans u11, ?_,
    (tf 14 (by decide) (by decide) (by decide)).trans u14⟩
  · convert ea.seq (eb.seq (ec.seq (hu.seq ht))) using 1
    · rfl
    · unfold prepareCost; omega
  · rw [t12,u11]

end MinorLoad
end Compression
end LinearProgramming
end Optimization
end OAI
