import OAI.Optimization.LinearProgramming.Elimination.UniformInitialize
import OAI.Optimization.LinearProgramming.Elimination.UniformProbe
import OAI.Optimization.LinearProgramming.Geometry.UniformGramLayout

/-! An existing rectangular-matrix allocation contains the entire rank-scan workspace. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM Compression _root_.OAI.Optimization.LinearProgramming.Geometry Matrix

/-- Reuse the inverse and minor buffers for the active flags and masked Gram matrix. -/
def layoutForGram {r n : ℕ} (l : GramLayout r n) : BasisLayout r where
  gram := l.g
  flags := l.inv
  mask := l.sub
  workA := l.workA
  workB := l.workB
  low := by have a:=l.minimum; have b:=l.d_tr; have c:=l.tr_g; omega
  beforeFlags := l.g_inv
  beforeMask := by
    have a:=l.inv_left; have b:=l.left_out; have c:=l.out_sub; have h:=Nat.le_mul_self r; omega
  beforeA := l.sub_workA
  beforeB := l.workA_workB

def basisSettings : List (ℕ × ℕ) := [(0,50),(1,58),(11,59),(12,60),(17,54),(18,55)]

def prepareBasis : Block := .seq (indexMoves basisSettings) clearFlags

/-- Initialize the scalar-bank flags without changing the input matrix or its allocation. -/
theorem prepareBasis_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {r n : ℕ} (l : GramLayout r n) (G : Matrix (Fin r) (Fin r) K) (P : K→Prop) (m : Memory K)
    (h : GramHeader l m) (hg : uniformMatrix r l.g m = G) (hm : m.AllData P) (h0 : P 0) :
    ∃ t c, c ≤ 6+clearFlagsCost r ∧ Block.Eval (Memory.AllData P) prepareBasis m c t ∧
      BasisState (layoutForGram l) G ∅ t ∧ GramHeader l t ∧
      ∀ p,7≤p → p<l.inv → t.data p=m.data p := by
  let u := movedIndices m basisSettings
  have eu : Block.Eval (Memory.AllData P) (indexMoves basisSettings) m 6 u := indexMoves_eval P m hm _
  have params : u.index 0=r ∧ u.index 1=l.sub ∧ u.index 11=l.workA ∧ u.index 12=l.workB ∧
      u.index 14=0 ∧ u.index 17=l.g ∧ u.index 18=l.inv := by
    simp [u,basisSettings,movedIndices,h.rows,h.sub,h.a,h.b,h.zero,h.g,h.inv]
  obtain ⟨p0,p1,p11,p12,p14,p17,p18⟩ := params
  have h7 := (layoutForGram l).low
  change 7≤l.g at h7
  have hbase := l.g_inv
  obtain ⟨t,c,hc,et,flags,ha,hd⟩ := clearFlags_spec P u r l.inv p0 p14 p18 (by omega) eu.safe_end h0
  have frame (p : ℕ) (hp : 7≤p) (hl : p<l.inv) : t.data p=m.data p :=
    (hd p hp (Or.inl hl)).trans (congrFun (movedIndices_data m basisSettings) p)
  refine ⟨t,6+c,Nat.add_le_add_left hc 6,eu.seq et,⟨(ha 0 (by decide) (by decide) (by decide) (by decide)).trans p0,
    (ha 1 (by decide) (by decide) (by decide) (by decide)).trans p1,
    (ha 11 (by decide) (by decide) (by decide) (by decide)).trans p11,
    (ha 12 (by decide) (by decide) (by decide) (by decide)).trans p12,
    (ha 14 (by decide) (by decide) (by decide) (by decide)).trans p14,
    (ha 17 (by decide) (by decide) (by decide) (by decide)).trans p17,
    (ha 18 (by decide) (by decide) (by decide) (by decide)).trans p18,?_,fun i=>by simpa [flag,layoutForGram] using flags i⟩,?_,frame⟩
  · rw [←hg]; ext i j
    have off : i.val*r+j.val < r*r := by
      simpa [finProdFinEquiv,Nat.add_comm,Nat.mul_comm] using (finProdFinEquiv (i,j)).isLt
    change t.data (l.g+i.val*r+j.val)=m.data (l.g+i.val*r+j.val)
    exact frame _ (by omega) (by omega)
  · apply h.of_frame
    intro p hp
    exact (ha p (by omega) (by omega) (by omega) (by omega)).trans <|
      movedIndices_other m basisSettings p (by simp [basisSettings];omega)

end Elimination
end LinearProgramming
end Optimization
end OAI
