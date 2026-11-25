import OAI.Optimization.LinearProgramming.Elimination.UniformRebuild
import OAI.Optimization.LinearProgramming.Elimination.UniformVectorMask
import OAI.Optimization.LinearProgramming.Geometry.UniformInverse

/-! Apply the masked inverse to the first row of the original symmetric Gram matrix,
then clear the inactive output coordinates in place. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM _root_.OAI.Optimization.LinearProgramming.Geometry Compression Matrix
open scoped Matrix BigOperators

def solveProductSettings : List (ℕ × ℕ) := [(31,50),(33,64),(42,50),(40,55),(41,61),(35,63)]

def uniformInverseVector : Block := .seq (indexMoves solveProductSettings) (.seq uniformRowProductBlock uniformVectorMask)

def inverseVectorTime (r : ℕ) := 6+(uniformTableTime r 1 (uniformRowDotCost r 1 r)+(2+(r*(6+3)+2)))

theorem uniformInverseVector_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {r n : ℕ}
    (l : GramLayout r n) (G H : Matrix (Fin r) (Fin r) K) (S : Finset (Fin r)) (P : K→Prop)
    (m : Memory K) (first : Fin r) (fz : first.val=0) (hh : InverseSource l m) (hm : m.AllData P)
    (hG : uniformRect r r l.g m=G) (hH : uniformRect r r l.workA m=H)
    (hS : ∀i : Fin r,m.data (l.inv+i.val)=flag S i) (h0 : P 0)
    (hparts : ∀i : Fin r,∀s : Finset (Fin r),P (∑ z∈s, H i z * G first z)) :
    ∃t c,c ≤ inverseVectorTime r ∧ Block.Eval (Memory.AllData P) uniformInverseVector m c t ∧
      (∀i : Fin r,t.data (l.workB+i.val)=flag S i*(H*ᵥG first) i) ∧
      (∀i : Fin r,t.data (l.inv+i.val)=flag S i) ∧ InverseSource l t := by
  let u := movedIndices m solveProductSettings
  have eu : Block.Eval (Memory.AllData P) (indexMoves solveProductSettings) m 6 u := indexMoves_eval P m hm _
  have prs : u.index 31=r ∧ u.index 33=1 ∧ u.index 35=l.workB ∧ u.index 40=l.workA ∧ u.index 41=l.g ∧ u.index 42=r := by
    simp [u,solveProductSettings,movedIndices,hh.layout.rows,hh.one,hh.layout.inv,hh.gram,hh.result,inverseLayout]
  obtain ⟨p31,p33,p35,p40,p41,p42⟩:=prs
  have uh (p : ℕ) (hp : p=14 ∨ 50 ≤ p) : u.index p=m.index p :=
    movedIndices_other m _ p (by simp [solveProductSettings];omega)
  have moved (base : ℕ) : uniformRect r r base u=uniformRect r r base m := by
    ext i j;exact congrFun (movedIndices_data m solveProductSettings) _
  have ug : uniformRect r r l.g u=G := (moved _).trans hG
  have uH : uniformRect r r l.workA u=H := (moved _).trans hH
  have urow : uniformRect 1 r l.g u=(fun _ j=> G first j) := by
    ext i j
    have e := congrFun (congrFun ug first) j
    have iz : i.val=0 := by omega
    simpa [uniformRect,iz,fz] using e
  have lo:=l.minimum;have dt:=l.d_tr;have tg:=l.tr_g;have gi:=l.g_inv;have il:=l.inv_left
  have ll:=l.left_out;have os:=l.out_sub;have sa:=l.sub_workA;have ab:=l.workA_workB;have r2:=Nat.le_mul_self r
  obtain ⟨w,k,hk,ew,out,fd,fi⟩ := uniformRowProductBlock_spec P u r 1 r l.workA l.g l.workB
    p31 p33 p35 p40 p41 p42 (by omega) (by omega) (by omega) (Or.inl ab)
    (Or.inl (by simp;omega)) eu.safe_end (by rw [uH,urow];exact fun i _ s=>hparts i s)
  rw [uH,urow] at out
  have wh := hh.of_frame fun p hp=>(fi p (by unfold TableScratch;omega) (by unfold RowDotIndexScratch;omega)).trans (uh p hp)
  have vmem (j : Fin r) : w.data (l.workB+j.val)=(H*ᵥG first) j := by
    have e:=congrFun (congrFun out j) (0:Fin 1)
    have rowEntry (q : Fin r) : (fun _ k=>G first k : Matrix (Fin 1) (Fin r) K)ᵀ q 0=G first q := rfl
    rw [Matrix.mul_apply] at e
    simpa only [uniformRect,rowEntry,Nat.mul_one,Fin.val_zero,Nat.add_zero,Matrix.mulVec,dotProduct] using e
  have flags (j : Fin r) : w.data (l.inv+j.val)=flag S j :=
    (fd _ (by omega) (Or.inl (by omega))).trans ((congrFun (movedIndices_data m _) _).trans (hS j))
  obtain ⟨t,c,hc,ec,vals,keep,idx⟩ := uniformVectorMask_spec P w r l.inv l.workB S (H*ᵥG first)
    wh.layout.rows wh.flags wh.result (by omega) (by omega) ew.safe_end h0 flags vmem
  refine ⟨t,6+(k+c),Nat.add_le_add_left (Nat.add_le_add hk hc) 6,eu.seq (ew.seq ec),vals,?_,?_⟩
  · intro j;exact (keep _ (by omega) (Or.inl (by omega))).trans (flags j)
  · refine ⟨wh.layout.of_frame (fun p hp=>idx p (by omega) (by omega) (by omega)),?_,?_,?_,?_⟩
    · exact (idx 61 (by decide) (by decide) (by decide)).trans wh.gram
    · exact (idx 62 (by decide) (by decide) (by decide)).trans wh.flags
    · exact (idx 63 (by decide) (by decide) (by decide)).trans wh.result
    · exact (idx 64 (by decide) (by decide) (by decide)).trans wh.one

end Elimination
end LinearProgramming
end Optimization
end OAI
