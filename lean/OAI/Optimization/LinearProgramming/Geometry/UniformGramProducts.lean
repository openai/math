import OAI.Optimization.LinearProgramming.Geometry.UniformProduct
import OAI.Optimization.LinearProgramming.Geometry.UniformGramLayout

/-! The common fixed product phase for the Gram matrix, Dᵀ G⁻¹, and the output. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM
open scoped Matrix BigOperators

inductive ProjectionProductStage
  | gram | left | result

structure GramProductCall where
  rows : ℕ
  cols : ℕ
  shared : ℕ
  a : ℕ
  b : ℕ
  dst : ℕ

def GramLayout.productCall {r n : ℕ} (l : GramLayout r n) : ProjectionProductStage → GramProductCall
  | .gram => ⟨r,r,n,l.d,l.d,l.g⟩
  | .left => ⟨n,r,r,l.tr,l.inv,l.left⟩
  | .result => ⟨n,n,r,l.left,l.tr,l.out⟩

def gramProductSettings : ProjectionProductStage → List (ℕ × ℕ)
  | .gram => [(31,50),(33,50),(42,51),(40,52),(41,52),(35,54)]
  | .left => [(31,51),(33,50),(42,50),(40,53),(41,55),(35,56)]
  | .result => [(31,51),(33,51),(42,50),(40,56),(41,53),(35,57)]

theorem gramProductSettings_length (t : ProjectionProductStage) : (gramProductSettings t).length = 6 := by
  cases t <;> rfl

def gramProductPhase (stage : ProjectionProductStage) : Block :=
  .seq (indexMoves (gramProductSettings stage)) uniformRowProductBlock

/-- Array and address frames common to all the phases. Only the current
output area, the preallocated scratch band, and low scalar scratch may change. -/
structure GramPhaseFrame {K : Type} {r n : ℕ} (l : GramLayout r n) (dst count : ℕ)
    (s t : Memory K) : Prop where
  data : ∀ q, 64≤q → (q<dst ∨ dst+count≤q) → (q<l.sub ∨ l.workB+r*r≤q) →
    t.data q=s.data q
  index : ∀ q, q=14 ∨ 50≤q → t.index q=s.index q

theorem GramPhaseFrame.header {K : Type} {r n d k : ℕ} {l : GramLayout r n} {s t : Memory K}
    (h : GramPhaseFrame l d k s t) (hs : GramHeader l s) : GramHeader l t :=
  hs.of_frame (fun p hp => h.index p (hp.imp_right And.left))

theorem GramPhaseFrame.read {K : Type} {r n d count m p src : ℕ} {l : GramLayout r n}
    {s t : Memory K} (h : GramPhaseFrame l d count s t) (hsrc : 64≤src)
    (hdis : src+m*p ≤ d ∨ d+count ≤ src) (hbelow : src+m*p ≤ l.sub) :
    uniformRect m p src t = uniformRect m p src s := by
  ext i j
  have hi := rectOffset_lt i j
  exact h.data _ (by omega) (by rcases hdis with h | h <;> omega) (Or.inl (by omega))

theorem gramProductPhase_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {r n : ℕ} (l : GramLayout r n) (stage : ProjectionProductStage) (P : K → Prop)
    (s : Memory K) (hh : GramHeader l s) (hs : s.AllData P)
    (hparts : ∀ (i : Fin (l.productCall stage).rows) (j : Fin (l.productCall stage).cols)
      (u : Finset (Fin (l.productCall stage).shared)),
      let v := l.productCall stage
      P (∑ z ∈ u, uniformRect v.rows v.shared v.a s i z * uniformRect v.cols v.shared v.b s j z)) :
    let v := l.productCall stage
    ∃ t k, k≤6 + uniformTableTime v.rows v.cols (uniformRowDotCost v.rows v.cols v.shared) ∧
      Block.Eval (Memory.AllData P) (gramProductPhase stage) s k t ∧
      uniformRect v.rows v.cols v.dst t =
        uniformRect v.rows v.shared v.a s * (uniformRect v.cols v.shared v.b s)ᵀ ∧
      GramPhaseFrame l v.dst (v.rows*v.cols) s t := by
  let v := l.productCall stage
  let u := movedIndices s (gramProductSettings stage)
  have he : Block.Eval (Memory.AllData P) (indexMoves (gramProductSettings stage)) s 6 u :=
    gramProductSettings_length stage ▸ indexMoves_eval P s hs (gramProductSettings stage)
  have params : u.index 31=v.rows ∧ u.index 33=v.cols ∧ u.index 35=v.dst ∧
      u.index 40=v.a ∧ u.index 41=v.b ∧ u.index 42=v.shared := by
    cases stage <;> simp [u,v,GramLayout.productCall,gramProductSettings,movedIndices,
      hh.rows,hh.cols,hh.d,hh.tr,hh.g,hh.inv,hh.left,hh.out]
  obtain ⟨h31,h33,h35,h40,h41,h42⟩ := params
  have hi (q : ℕ) (hq : q=14 ∨ 50≤q) : u.index q=s.index q := by
    apply movedIndices_other
    cases stage <;> simp [gramProductSettings] <;> omega
  have ha := l.minimum; have hdt := l.d_tr; have htg := l.tr_g
  have hgi := l.g_inv; have hil := l.inv_left; have hlo := l.left_out
  have hshape : 23<v.a ∧ 23<v.b ∧ 23<v.dst ∧ v.a+v.rows*v.shared ≤ v.dst ∧
      v.b+v.cols*v.shared ≤ v.dst := by
    cases stage <;> simp only [v,GramLayout.productCall] <;> omega
  obtain ⟨a,b,o,da,db⟩ := hshape
  obtain ⟨t,k,hk,er,val,fd,fi⟩ := uniformRowProductBlock_spec P u v.rows v.cols v.shared
    v.a v.b v.dst h31 h33 h35 h40 h41 h42 a b o (Or.inl da) (Or.inl db) he.safe_end
    (by simpa only [uniformRect,u,movedIndices_data] using hparts)
  refine ⟨t,_,Nat.add_le_add_left hk 6,he.seq er,?_,?_,?_⟩
  · have ea : uniformRect v.rows v.shared v.a u = uniformRect v.rows v.shared v.a s := by
      ext i j; exact congrFun (movedIndices_data s (gramProductSettings stage)) _
    have eb : uniformRect v.cols v.shared v.b u = uniformRect v.cols v.shared v.b s := by
      ext i j; exact congrFun (movedIndices_data s (gramProductSettings stage)) _
    rw [ea,eb] at val
    exact val
  · intro q hq hdis _
    exact (fd q (by omega) hdis).trans (congrFun (movedIndices_data s _) q)
  · intro q hq
    apply Eq.trans (fi q ?_ ?_) (hi q hq)
    · unfold TableScratch; omega
    · unfold RowDotIndexScratch; omega

end Geometry
end LinearProgramming
end Optimization
end OAI
