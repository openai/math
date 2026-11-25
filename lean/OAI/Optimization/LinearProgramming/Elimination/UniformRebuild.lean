import OAI.Optimization.LinearProgramming.Elimination.UniformBasisLayout
import OAI.Optimization.LinearProgramming.Elimination.UniformInverseLayout

/-! Rebuild the final mask after a scan, before computing the inverse. An unsuccessful
last probe may have temporarily written a different table. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM _root_.OAI.Optimization.LinearProgramming.Geometry Compression Matrix

structure RebuiltMask {K : Type} [Field K] {r n : ℕ} (l : GramLayout r n)
    (G : Matrix (Fin r) (Fin r) K) (S : Finset (Fin r)) (s : Memory K) : Prop where
  source : InverseSource l s
  masked : uniformRect r r l.sub s=maskGram G (flag S)
  gram : uniformRect r r l.g s=G
  flags : ∀i : Fin r,s.data (l.inv+i.val)=flag S i

def rebuildMask : Block := .seq uniformMaskTable (gramAllocCode inverseAlloc)

theorem rebuildMask_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {r n : ℕ}
    (l : GramLayout r n) (G : Matrix (Fin r) (Fin r) K) (S : Finset (Fin r)) (P : K→Prop)
    (m : Memory K) (hs : BasisState (layoutForGram l) G S m) (hh : GramHeader l m)
    (hm : m.AllData P) (h0 : P 0) (h1 : P 1) :
    ∃t c,c ≤ maskTableCost r+100*(r+1)^2 ∧ Block.Eval (Memory.AllData P) rebuildMask m c t ∧
      RebuiltMask l G S t := by
  have lo:=l.minimum;have dt:=l.d_tr;have tg:=l.tr_g;have gi:=l.g_inv;have il:=l.inv_left
  have lr:=l.left_out;have os:=l.out_sub;have r2:=Nat.le_mul_self r
  have mg : m.index 17=l.g := hs.gramPtr
  have mf : m.index 18=l.inv := hs.flagsPtr
  have mo : m.index 1=l.sub := hs.maskPtr
  obtain ⟨u,k,hk,e,um,uf,ui⟩ := uniformMaskTable_spec P m r S hs.dim hs.zeroIdx (by omega) (by omega)
    (by omega) (by omega) (by omega) hm h0 h1 (by rw [mf];exact hs.flags)
  rw [mg,mo,show uniformMatrix r l.g m=G from hs.gram] at um
  rw [mo] at uf
  have uh : GramHeader l u := hh.of_frame (fun p hp=>ui p (by
    simp only [Finset.mem_insert,Finset.mem_singleton];omega))
  obtain ⟨t,c,hc,et,head,dat⟩ := inverseAlloc_spec l P u uh e.safe_end
  refine ⟨t,k+c,Nat.add_le_add hk hc,e.seq et,head,?_,?_,?_⟩
  · ext i j
    exact (congrFun dat _).trans (congrFun (congrFun um i) j)
  · ext i j
    have h:=rectOffset_lt i j
    exact (congrFun dat _).trans ((uf (l.g+i.val*r+j.val) (by omega) (Or.inl (by omega))).trans
      (congrFun (congrFun hs.gram i) j))
  · intro i
    exact (congrFun dat _).trans ((uf _ (by omega) (Or.inl (by omega))).trans (hs.flags i))

end Elimination
end LinearProgramming
end Optimization
end OAI
