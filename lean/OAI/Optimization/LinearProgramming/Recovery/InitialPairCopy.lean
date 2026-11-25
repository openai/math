import OAI.Optimization.LinearProgramming.Geometry.UniformCopyTable

/-! A single RAM traversal transposes a rectangular table from a read-only source
to any later destination window. It frames all other data above the six low
scalar working registers and all nonworking index registers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace InitialPair

open RAM Geometry
open scoped Matrix

def copyBlock : Block := uniformTableBlock (GramCopy.cell true)

def readBound (h n : ℕ) := (h+n)*(4*(h+n)+5)+4*(h+n)+6

/-- Address registers outside the traversal and address arithmetic scratch. -/
def CopyIndex (p : ℕ) : Prop :=
  p≠30 ∧ p≠32 ∧ p≠34 ∧ p≠36 ∧ p≠37 ∧ p≠38 ∧ p≠39 ∧ p≠42

instance (p : ℕ) : Decidable (CopyIndex p) := by unfold CopyIndex; infer_instance

theorem copy_to_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (x y h n : ℕ) (hx : 7 ≤ x) (hxy : x+n*h ≤ y)
    (hs : s.AllData P) (rows : s.index 31=h) (cols : s.index 33=n)
    (dest : s.index 35=y) (src : s.index 40=x) (stride : s.index 41=h) :
    ∃ t k, k ≤ uniformTableTime h n (readBound h n) ∧
      Block.Eval (Memory.AllData P) copyBlock s k t ∧
      uniformRect h n y t = (uniformRect n h x s)ᵀ ∧
      (∀ a, 7 ≤ a → (a < y ∨ y+h*n ≤ a) → t.data a=s.data a) ∧
      ∀ p, CopyIndex p → t.index p=s.index p := by
  have sources (i : Fin h) (j : Fin n) :
      let a := GramCopy.tableSource true (s.index 40) (s.index 41) i j
      7 ≤ a ∧ (a < y ∨ y+h*n ≤ a) := by
    change 7 ≤ s.index 40 + j.val*s.index 41 + i.val ∧
      (s.index 40 + j.val*s.index 41 + i.val < y ∨ _)
    rw [src,stride]
    have ho := rectOffset_lt j i
    exact ⟨by omega,Or.inl (by omega)⟩
  have hc := GramCopy.cell_callback true P (fun a => 7 ≤ a) CopyIndex s h n y (h+n)
    (by omega) (by omega) (stride.trans_le (by omega)) (by decide)
    (fun _ hq => hq.2.2.2.2.2)
    (by decide) (by decide) sources
  obtain ⟨t,k,clock,run,val,frame,idx⟩ := uniformTableBlock_spec (GramCopy.cell true) P
    (fun a => 7 ≤ a) CopyIndex s h n y _ _ hc
    (fun q hq => by unfold CopyIndex at hq; unfold TableScratch; omega)
    (fun _ _ => by omega) rows cols dest hs
  refine ⟨t,k,clock,run,?_,frame,fun p hp => idx p (Or.inr hp)⟩
  ext i j
  simpa [GramCopy.tableSource,src,stride,uniformRect] using congrFun (congrFun val i) j

end InitialPair
end Recovery
end LinearProgramming
end Optimization
end OAI
