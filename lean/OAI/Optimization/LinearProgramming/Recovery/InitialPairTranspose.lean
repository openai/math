import OAI.Optimization.LinearProgramming.Recovery.InitialPairHeaders
import OAI.Optimization.LinearProgramming.Recovery.InitialPairCopy

/-! One row-major traversal copies the slack tableau into the column-basis orientation.
All protected source words remain readable after the traversal. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialPair

open RAM Geometry
open scoped Matrix

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def transposeBlock : Block := .seq headerBlock copyBlock
noncomputable def transposeTime (g h n : ℕ) :=
  headers.budget.eval (g+h+n) + uniformTableTime h n (readBound h n)

theorem copy_spec (P : K → Prop) (s : Memory K) (g h n : ℕ) (hg : 7 ≤ g)
    (hs : s.AllData P) (hh : Header g h n s) :
    ∃ t k, k ≤ uniformTableTime h n (readBound h n) ∧
      Block.Eval (Memory.AllData P) copyBlock s k t ∧
      uniformRect h n (cBase g h n) t = (uniformRect n h g s)ᵀ ∧ Header g h n t ∧
      (∀ a, 7 ≤ a → (a < cBase g h n ∨ outBase g h n ≤ a) → t.data a=s.data a) ∧ Protected s t := by
  obtain ⟨t,k,clock,run,val,frame,idx⟩ :=
    copy_to_spec P s g (cBase g h n) h n hg (Nat.le_refl _) hs hh.rows hh.cols hh.dest hh.source hh.stride
  have header : Header g h n t :=
    ⟨(idx 14 (by decide)).trans hh.zero,(idx 31 (by decide)).trans hh.rows,
     (idx 33 (by decide)).trans hh.cols,(idx 35 (by decide)).trans hh.dest,
     (idx 40 (by decide)).trans hh.source,(idx 41 (by decide)).trans hh.stride,
     (idx 200 (by decide)).trans hh.height,(idx 201 (by decide)).trans hh.dimension,
     (idx 202 (by decide)).trans hh.input,(idx 203 (by decide)).trans hh.output,
     (idx 204 (by decide)).trans hh.scratch,(idx 205 (by decide)).trans hh.clean⟩
  refine ⟨t,k,clock,run,val,header,frame,idx 24 (by decide),idx 28 (by decide),
    idx 29 (by decide),?_⟩
  intro p hp
  exact idx p (by unfold CopyIndex; omega)

theorem transpose_spec (P : K → Prop) (s : Memory K) (g h n : ℕ) (hg : 7 ≤ g) (hs : s.AllData P)
    (sr : s.index 31=n) (sc : s.index 33=h) (sg : s.index 35=g) :
    ∃ t k, k ≤ transposeTime g h n ∧ Block.Eval (Memory.AllData P) transposeBlock s k t ∧
      uniformRect h n (cBase g h n) t = (uniformRect n h g s)ᵀ ∧ Header g h n t ∧
      (∀ a, 7 ≤ a → (a < cBase g h n ∨ outBase g h n ≤ a) → t.data a=s.data a) ∧ Protected s t := by
  obtain ⟨u,j,hj,install,uh,ud,u24,u28,u29,uf⟩ := header_spec P s g h n hs sr sc sg
  obtain ⟨t,k,hk,copy,val,th,td,t24,t28,t29,tf⟩ := copy_spec P u g h n hg install.safe_end uh
  have mat : uniformRect n h g u = uniformRect n h g s := by
    ext i l
    exact congrFun ud _
  refine ⟨t,j+k,Nat.add_le_add hj hk,install.seq copy,?_,th,?_,
    t24.trans u24,t28.trans u28,t29.trans u29,fun p hp => (tf p hp).trans (uf p hp)⟩
  · simpa only [mat] using val
  · intro a ha outside
    exact (td a ha outside).trans (congrFun ud a)

end InitialPair
end Recovery
end LinearProgramming
end Optimization
end OAI
