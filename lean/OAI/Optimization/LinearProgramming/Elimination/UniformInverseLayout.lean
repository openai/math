import OAI.Optimization.LinearProgramming.Geometry.UniformGramInput

/-! Reuse the completed mask as the general matrix input to the uniform inverse program. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM _root_.OAI.Optimization.LinearProgramming.Geometry Compression

/-- The determinant work area becomes the output and temporary area for the masked inverse. -/
def inverseLayout {r n : ℕ} (l : GramLayout r n) : GramLayout r 0 where
  d:=l.g
  tr:=l.g
  g:=l.sub
  inv:=l.workA
  left:=l.workB
  out:=l.workB
  sub:=l.workB
  workA:=l.workB+r*r
  workB:=l.workB+r*r+r*r
  minimum:=by have h:=l.minimum;have ht:=l.d_tr;have hg:=l.tr_g;omega
  d_tr:=by simp
  tr_g:=by have a:=l.g_inv;have b:=l.inv_left;have c:=l.left_out;have d:=l.out_sub;omega
  g_inv:=l.sub_workA
  inv_left:=l.workA_workB
  left_out:=by simp
  out_sub:=by simp
  sub_workA:=le_rfl
  workA_workB:=le_rfl

def inverseAlloc : List GramAllocOp :=
  [.copy 61 54,.copy 62 55,.copy 63 60,.set 64 1,.copy 52 54,.copy 53 54,.copy 54 58,
   .copy 55 59,.copy 56 60,.copy 57 60,.copy 58 60,.reserve 59 60 50 50,.reserve 60 59 50 50,.set 51 0]

/-- Retain the original Gram pointer and flags while the inverse subroutine uses its own header. -/
structure InverseSource {K : Type} {r n : ℕ} (l : GramLayout r n) (m : Memory K) : Prop where
  layout : GramHeader (inverseLayout l) m
  gram : m.index 61=l.g
  flags : m.index 62=l.inv
  result : m.index 63=l.workB
  one : m.index 64=1

theorem InverseSource.of_frame {K : Type} {r n : ℕ} {l : GramLayout r n} {s t : Memory K}
    (h : InverseSource l s) (hi : ∀p,p=14 ∨ 50≤p → t.index p=s.index p) : InverseSource l t :=
  ⟨h.layout.of_frame (fun p hp=>hi p (hp.imp_right And.left)),(hi 61 (by decide)).trans h.gram,
    (hi 62 (by decide)).trans h.flags,(hi 63 (by decide)).trans h.result,(hi 64 (by decide)).trans h.one⟩

theorem inverseAlloc_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {r n : ℕ}
    (l : GramLayout r n) (P : K→Prop) (s : Memory K) (h : GramHeader l s) (hs : s.AllData P) :
    ∃t c,c≤100*(r+1)^2 ∧ Block.Eval (Memory.AllData P) (gramAllocCode inverseAlloc) s c t ∧
      InverseSource l t ∧ t.data=s.data := by
  obtain ⟨t,e,hd,hi⟩ := gramAllocCode_eval P s s.index inverseAlloc
    (by simp [inverseAlloc,GramAllocOp.allowed,CellScratchOK]) hs (fun _ _ _=>rfl)
  refine ⟨t,_,?_,e,?_,hd⟩
  · simp [inverseAlloc,gramAllocCost,GramAllocOp.cost,GramAllocOp.indexAfter,h.rows,h.zero]
    nlinarith [Nat.zero_le (r^2)]
  · refine ⟨?_,?_,?_,?_,?_⟩
    · constructor <;> rw [hi _ (by decide) (by decide)] <;>
        simp [inverseLayout,inverseAlloc,gramAllocIndex,GramAllocOp.indexAfter,h.rows,h.zero,h.g,h.sub,h.inv,h.a,h.b]
    all_goals
      rw [hi _ (by decide) (by decide)]
      simp [inverseAlloc,gramAllocIndex,GramAllocOp.indexAfter,h.g,h.inv,h.b]

end Elimination
end LinearProgramming
end Optimization
end OAI
