import OAI.Optimization.LinearProgramming.Compression.UniformIndex
import OAI.Optimization.LinearProgramming.Compression.Elimination

/-! Hoare proof for the two row-major loops of one uniform Bird determinant stage. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- The half-open regions used by the two row-major tables are disjoint. -/
def disjointTables (n left right : ℕ) : Prop := left + n*n ≤ right ∨ right + n*n ≤ left

/-- Semantics of the fixed cell block, including its precise write footprint. -/
def BirdCellSpec (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] (cell : Block) : Prop :=
  ∀ (P : K → Prop) (m : Memory K) (n : ℕ) (i j : Fin n),
    m.index 0 = n → m.index 4 = i.val → m.index 5 = j.val →
    7 ≤ m.index 1 → 7 ≤ m.index 2 → 7 ≤ m.index 3 → (∀ p, P (m.data p)) →
    (∀ r : BirdRegister n, P (r.read (uniformMatrix n (m.index 1) m) (uniformMatrix n (m.index 2) m))) →
    ∃ cost t, cost ≤ 1000*(n+1)^4 ∧ Block.Eval (fun s => ∀ p, P (s.data p)) cell m cost t ∧
      t.data (m.index 3 + i.val*n + j.val) =
        BirdDet.Spec.stepEntry (uniformMatrix n (m.index 1) m) (uniformMatrix n (m.index 2) m) i j ∧
      (∀ p, 7 ≤ p → p ≠ m.index 3 + i.val*n + j.val → t.data p = m.data p) ∧
      (∀ p, p ≠ 6 → p ≠ 8 → p ≠ 9 → p ≠ 10 → t.index p = m.index p)

/-- Writing a stage may change the row, column and arithmetic address scratch. -/
def StageScratch (p : ℕ) : Prop := p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 8 ∨ p = 9 ∨ p = 10

instance (p : ℕ) : Decidable (StageScratch p) := by unfold StageScratch; infer_instance

private structure StageFrame {K : Type} (P : K → Prop) {n : ℕ} (out filled : ℕ)
    (M : Matrix (Fin n) (Fin n) K) (start now : Memory K) : Prop where
  safe : ∀ a, P (now.data a)
  index : ∀ a, ¬ StageScratch a → now.index a = start.index a
  done : ∀ i j, i.val*n + j.val < filled → now.data (out + i.val*n + j.val) = M i j
  other : ∀ a, 7 ≤ a → (a < out ∨ out+filled ≤ a) → now.data a = start.data a

private theorem StageFrame.putScratch {K : Type} {P : K → Prop} {n out filled : ℕ}
    {M : Matrix (Fin n) (Fin n) K} {start now : Memory K}
    (h : StageFrame P out filled M start now) {a : ℕ} (ha : StageScratch a) (value : ℕ) :
    StageFrame P out filled M start (now.putIndex a value) := by
  refine ⟨h.safe, ?_, h.done, h.other⟩
  intro b hb
  have hba : b ≠ a := by rintro rfl; exact hb ha
  simpa [hba] using h.index b hb

private theorem offset_lt {n : ℕ} (i j : Fin n) : i.val*n+j.val < n*n := by
  simpa [finProdFinEquiv, Nat.add_comm, Nat.mul_comm] using (finProdFinEquiv (i,j)).isLt

private theorem offset_inj {n : ℕ} {i j p q : Fin n} (h : i.val*n+j.val = p.val*n+q.val) :
    i = p ∧ j = q := by
  have he : finProdFinEquiv (i,j) = finProdFinEquiv (p,q) := by
    apply Fin.ext
    simpa [finProdFinEquiv, Nat.add_comm, Nat.mul_comm] using h
  exact Prod.mk.inj (finProdFinEquiv.injective he)

private theorem StageFrame.readTable {K : Type} {P : K → Prop} {n out filled : ℕ}
    {M : Matrix (Fin n) (Fin n) K} {start now : Memory K} (h : StageFrame P out filled M start now)
    {base : ℕ} (hb : 7 ≤ base) (hd : disjointTables n base out) (hk : filled ≤ n*n) :
    uniformMatrix n base now = uniformMatrix n base start := by
  ext i j
  exact h.other _ (by omega) (by rcases hd with h | h <;> have := offset_lt i j <;> omega)

/-- The same two bounded loops are used for every matrix dimension. -/
def birdStageBlock (cell : Block) : Block := Block.forRowsCols 4 0 5 0 cell

def birdStageCost (n : ℕ) : ℕ := n*(n*(1000*(n+1)^4+3)+5)+2

/-- Starting from disjoint input/output regions, consecutive row/column writes materialize
exactly one Bird iteration and preserve both input matrices. -/
theorem birdStageBlock_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (cell : Block) (hcell : BirdCellSpec K cell) (P : K → Prop) (m : Memory K) (n : ℕ)
    (hN : m.index 0 = n) (hbA : 7 ≤ m.index 1) (hbF : 7 ≤ m.index 2) (hbW : 7 ≤ m.index 3)
    (hAW : disjointTables n (m.index 1) (m.index 3))
    (hFW : disjointTables n (m.index 2) (m.index 3)) (hm : ∀ p, P (m.data p))
    (hreg : ∀ r : BirdRegister n, P (r.read (uniformMatrix n (m.index 1) m) (uniformMatrix n (m.index 2) m))) :
    ∃ t cost, cost ≤ birdStageCost n ∧ Block.Eval (fun s => ∀ p, P (s.data p)) (birdStageBlock cell) m cost t ∧
      uniformMatrix n (m.index 3) t =
        BirdDet.Spec.stepEntry (uniformMatrix n (m.index 1) m) (uniformMatrix n (m.index 2) m) ∧
      (∀ a, 7 ≤ a → (a < m.index 3 ∨ m.index 3 + n*n ≤ a) → t.data a = m.data a) ∧
      (∀ a, ¬ StageScratch a → t.index a = m.index a) := by
  let W := BirdDet.Spec.stepEntry (uniformMatrix n (m.index 1) m) (uniformMatrix n (m.index 2) m)
  let frame (filled : ℕ) := StageFrame P (m.index 3) filled W m
  let R (r : ℕ) (s : Memory K) := frame (r*n) s ∧ s.index 4 = r
  let C (r j : ℕ) (s : Memory K) := frame (r*n+j) s ∧ s.index 4 = r ∧ s.index 5 = j
  have initial : R 0 (m.putIndex 4 0) := by
    have h : frame 0 m := ⟨hm, fun _ _ => rfl, by simp, fun _ _ _ => rfl⟩
    exact ⟨by simpa using h.putScratch (a := 4) (by decide) 0, by simp⟩
  have beginRow (r : ℕ) (_ : r < n) (s : Memory K) (h : R r s) : C r 0 (s.putIndex 5 0) :=
    ⟨by simpa using h.1.putScratch (a := 5) (by decide) 0, by simpa using h.2, by simp⟩
  have endRow (r : ℕ) (_ : r < n) (s : Memory K) (h : C r n s) :
      R (r+1) (s.putIndex 4 (s.index 4+1)) :=
    ⟨by simpa [Nat.succ_mul] using h.1.putScratch (a := 4) (by decide) (s.index 4+1), by simp [h.2.1]⟩
  have advance (r : ℕ) (hr : r < n) (j : ℕ) (hj : j < n) (s : Memory K) (h : C r j s) :
      ∃ t cost, cost ≤ 1000*(n+1)^4 ∧ Block.Eval (fun z => ∀ p, P (z.data p)) cell s cost t ∧
        C r (j+1) (t.putIndex 5 (t.index 5+1)) := by
    let ri : Fin n := ⟨r,hr⟩
    let cj : Fin n := ⟨j,hj⟩
    have hz := h.1.index 0 (by decide)
    have ha := h.1.index 1 (by decide)
    have hf := h.1.index 2 (by decide)
    have hw := h.1.index 3 (by decide)
    have hk : r*n+j < n*n := offset_lt ri cj
    have ha' := h.1.readTable hbA hAW hk.le
    have hf' := h.1.readTable hbF hFW hk.le
    obtain ⟨cost,t,hcost,he,write,unchanged,hidx⟩ := hcell P s n ri cj (hz.trans hN) h.2.1 h.2.2
      (ha ▸ hbA) (hf ▸ hbF) (hw ▸ hbW) h.1.safe (by simpa [ha,hf,ha',hf'] using hreg)
    rw [hw, ha, hf, ha', hf'] at write
    rw [hw] at unchanged
    have hnew : frame (r*n+(j+1)) t := by
      refine ⟨he.safe_end, ?_, ?_, ?_⟩
      · intro a hs
        exact (hidx a (by simp_all [StageScratch]) (by simp_all [StageScratch])
          (by simp_all [StageScratch]) (by simp_all [StageScratch])).trans (h.1.index a hs)
      · intro i' j' hlt
        by_cases earlier : i'.val*n+j'.val < r*n+j
        · have hne : m.index 3+i'.val*n+j'.val ≠ m.index 3+ri.val*n+cj.val := by
            dsimp [ri,cj]; omega
          exact (unchanged _ (by omega) hne).trans (h.1.done i' j' earlier)
        · have heq : i'.val*n+j'.val = ri.val*n+cj.val := by dsimp [ri,cj]; omega
          obtain ⟨rfl,rfl⟩ := offset_inj heq
          exact write
      · intro a ha hout
        have hn : a ≠ m.index 3+ri.val*n+cj.val := by dsimp [ri,cj]; omega
        exact (unchanged a ha hn).trans (h.1.other a ha (by omega))
    have hr' := hidx 4 (by decide) (by decide) (by decide) (by decide)
    have hj' := hidx 5 (by decide) (by decide) (by decide) (by decide)
    exact ⟨t,cost,hcost,he,hnew.putScratch (a := 5) (by decide) _,
      by simpa using hr'.trans h.2.1, by simp [hj',h.2.2]⟩
  obtain ⟨t,cost,hcost,he,h⟩ := Block.Eval.forRowsCols_invariant (body := cell)
    4 0 5 0 n n (1000*(n+1)^4) R C m hm initial
    (fun _ _ h => ⟨h.1.safe,h.2,(h.1.index 0 (by decide)).trans hN⟩) beginRow
    (fun _ _ _ h => ⟨h.1.safe,h.2.2,(h.1.index 0 (by decide)).trans hN⟩) advance endRow
  refine ⟨t,cost,hcost,he,?_,h.1.other,h.1.index⟩
  ext i j
  exact h.1.done i j (offset_lt i j)

end Compression
end LinearProgramming
end Optimization
end OAI
