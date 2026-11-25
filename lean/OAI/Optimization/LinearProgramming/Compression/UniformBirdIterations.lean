import OAI.Optimization.LinearProgramming.Compression.UniformBirdStage

/-! Alternate two disjoint working matrices while keeping the original operand accessible. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

@[simp] theorem uniformMatrix_putIndex {K : Type} (m : Memory K) (n base a v : ℕ) :
    uniformMatrix n base (m.putIndex a v) = uniformMatrix n base m := rfl

def nextTable (workA workB r : ℕ) := if Even r then workA else workB

def previousTable (input workA workB : ℕ) : ℕ → ℕ
  | 0 => input
  | k+1 => nextTable workA workB k

private theorem nextTable_succ {a b : ℕ} (hab : a < b) (r : ℕ) :
    (if nextTable a b r < b then b else a) = nextTable a b (r+1) := by
  by_cases h : Even r <;> simp [nextTable, Nat.even_add_one, h, hab]

private theorem nextTable_bounds {a b n : ℕ} (ha : 7 ≤ a) (hab : a + n*n ≤ b) (r : ℕ) :
    7 ≤ nextTable a b r := by unfold nextTable; split <;> omega

private theorem previousTable_bounds {input a b n : ℕ} (hi : 7 ≤ input) (hia : input+n*n ≤ a)
    (hab : a+n*n ≤ b) (r : ℕ) : 7 ≤ previousTable input a b r := by
  cases r with
  | zero => exact hi
  | succ r => exact nextTable_bounds (by omega) hab r

private theorem readWrite_disjoint {input a b n : ℕ} (hia : input+n*n ≤ a) (hab : a+n*n ≤ b)
    (r : ℕ) : disjointTables n input (nextTable a b r) ∧
      disjointTables n (previousTable input a b r) (nextTable a b r) := by
  constructor
  · left; unfold nextTable; split <;> omega
  · cases r with
    | zero => exact Or.inl (by simpa [nextTable, previousTable] using hia)
    | succ r =>
      by_cases hv : Even r
      · exact Or.inl (by simpa [nextTable, previousTable, Nat.even_add_one, hv] using hab)
      · exact Or.inr (by simpa [nextTable, previousTable, Nat.even_add_one, hv] using hab)

/-- Register 2 names the completed stage and register 3 names the other output buffer. -/
def rotateTables : Block := .seq (.op (.addrCopy 2 3))
  (.branch (.addrLT 3 12) (.op (.addrCopy 3 12)) (.op (.addrCopy 3 11)))

private theorem rotateTables_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (hs : ∀ p, P (s.data p)) :
    ∃ t k, k ≤ 4 ∧ Block.Eval (fun z => ∀ p, P (z.data p)) rotateTables s k t ∧
      t.data = s.data ∧ t.index 2 = s.index 3 ∧
      t.index 3 = (if s.index 3 < s.index 12 then s.index 12 else s.index 11) ∧
      ∀ p, p ≠ 2 → p ≠ 3 → t.index p = s.index p := by
  let u := s.putIndex 2 (s.index 3)
  have he : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.addrCopy 2 3)) s 1 u :=
    Block.Eval.op_addrCopy _ _ _ hs hs
  by_cases h : s.index 3 < s.index 12
  · let t := u.putIndex 3 (u.index 12)
    have hw : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.addrCopy 3 12)) u 1 t :=
      Block.Eval.op_addrCopy _ _ _ hs hs
    refine ⟨t,4,by decide,he.seq (.branchTrue (by simp [Cond.test,u,h]) hw),rfl,?_,?_,?_⟩
    · simp [u,t]
    · simp [u,t,h]
    · intro p h₂ h₃; simp [u,t,h₂,h₃]
  · let t := u.putIndex 3 (u.index 11)
    have hw : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.addrCopy 3 11)) u 1 t :=
      Block.Eval.op_addrCopy _ _ _ hs hs
    refine ⟨t,3,by decide,he.seq (.branchFalse (by simp [Cond.test,u,h]) hw),rfl,?_,?_,?_⟩
    · simp [u,t]
    · simp [u,t,h]
    · intro p h₂ h₃; simp [u,t,h₂,h₃]

def loopScratch (p : ℕ) : Prop := p = 2 ∨ p = 3 ∨ p = 7 ∨ StageScratch p

instance (p : ℕ) : Decidable (loopScratch p) := by unfold loopScratch; infer_instance

private structure BirdLoopFrame {K : Type} [CommRing K] (P : K → Prop) (n rounds : ℕ)
    (start now : Memory K) : Prop where
  safe : ∀ a, P (now.data a)
  counter : now.index 7 = rounds
  index : ∀ a, ¬ loopScratch a → now.index a = start.index a
  prev : now.index 2 = previousTable (start.index 1) (start.index 11) (start.index 12) rounds
  next : now.index 3 = nextTable (start.index 11) (start.index 12) rounds
  state : uniformMatrix n (now.index 2) now = birdLayer (uniformMatrix n (start.index 1) start) rounds
  other : ∀ a, 7 ≤ a → (a < start.index 11 ∨ start.index 11+n*n ≤ a) →
    (a < start.index 12 ∨ start.index 12+n*n ≤ a) → now.data a = start.data a

private theorem BirdLoopFrame.source {K : Type} [CommRing K] {P : K → Prop} {n r : ℕ}
    {m s : Memory K} (h : BirdLoopFrame P n r m s) (hI : 7 ≤ m.index 1)
    (hIA : m.index 1+n*n ≤ m.index 11) (hAB : m.index 11+n*n ≤ m.index 12) :
    uniformMatrix n (s.index 1) s = uniformMatrix n (m.index 1) m := by
  rw [h.index 1 (by decide)]
  ext i j
  have hoff := (finProdFinEquiv (i,j)).isLt
  have hbound : i.val*n+j.val < n*n := by
    simpa [finProdFinEquiv, Nat.add_comm, Nat.mul_comm] using hoff
  exact h.other _ (by omega) (by omega) (by omega)

/-- The time loop calls the fixed row/column loops `n-1` times. -/
def birdIterations (cell : Block) : Block := .forRange 7 13 (.seq (birdStageBlock cell) rotateTables)

def birdIterationsCost (n : ℕ) := (n-1)*(birdStageCost n+4+3)+2

theorem birdIterations_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (cell : Block) (hcell : BirdCellSpec K cell) (P : K → Prop) (m : Memory K) (n : ℕ) (hn : 0<n)
    (hN : m.index 0=n) (hI : 7 ≤ m.index 1) (hIA : m.index 1+n*n ≤ m.index 11)
    (hAB : m.index 11+n*n ≤ m.index 12) (hprev : m.index 2=m.index 1) (hnext : m.index 3=m.index 11)
    (hstop : m.index 13=n-1) (hm : ∀ p, P (m.data p))
    (hreg : ∀ k<n, ∀ r : BirdRegister n, P (r.read (uniformMatrix n (m.index 1) m)
      (birdLayer (uniformMatrix n (m.index 1) m) k))) :
    ∃ t k, k ≤ birdIterationsCost n ∧ Block.Eval (fun z => ∀ p, P (z.data p)) (birdIterations cell) m k t ∧
      uniformMatrix n (t.index 2) t = birdLayer (uniformMatrix n (m.index 1) m) (n-1) ∧
      t.index 3 = nextTable (m.index 11) (m.index 12) (n-1) ∧ t.index 11=m.index 11 ∧
      (∀ a, 7 ≤ a → (a<m.index 11 ∨ m.index 11+n*n≤a) → (a<m.index 12 ∨ m.index 12+n*n≤a) →
        t.data a = m.data a) := by
  let I := fun r s => BirdLoopFrame P n r m s
  have initial : I 0 (m.putIndex 7 0) := by
    refine ⟨hm, by simp, ?_, by simp [previousTable,hprev], by simp [nextTable,hnext], ?_, fun _ _ _ _ => rfl⟩
    · intro a ha
      have hne : a ≠ 7 := by simp_all [loopScratch]
      simp [hne]
    · simp [birdLayer,hprev]
  have next (r : ℕ) (hr : r<n-1) (s : Memory K) (h : I r s) :
      ∃ t k, k ≤ birdStageCost n+4 ∧
        Block.Eval (fun z => ∀ p, P (z.data p)) (.seq (birdStageBlock cell) rotateTables) s k t ∧
        I (r+1) (t.putIndex 7 (t.index 7+1)) := by
    have h0 := h.index 0 (by decide)
    have h1 := h.index 1 (by decide)
    have h11 := h.index 11 (by decide)
    have h12 := h.index 12 (by decide)
    have hA := h.source hI hIA hAB
    obtain ⟨dI,dF⟩ := readWrite_disjoint hIA hAB r
    obtain ⟨v,k,hk,he,hw,ho,hi⟩ := birdStageBlock_spec cell hcell P s n (h0.trans hN)
      (h1 ▸ hI) (h.prev ▸ previousTable_bounds hI hIA hAB r) (h.next ▸ nextTable_bounds (by omega) hAB r)
      (by simpa only [h1,h.next] using dI) (by simpa only [h.prev,h.next] using dF) h.safe
      (by simpa only [hA,h.state] using hreg r (by omega))
    obtain ⟨t,l,hl,er,ed,ep,en,ei⟩ := rotateTables_spec P v he.safe_end
    have h3' := hi 3 (by decide)
    have h11' := hi 11 (by decide)
    have h12' := hi 12 (by decide)
    have hprev' : t.index 2 = nextTable (m.index 11) (m.index 12) r := ep.trans (h3'.trans h.next)
    have hab' : m.index 11 < m.index 12 := by have := Nat.mul_pos hn hn; omega
    have hnext' : t.index 3 = nextTable (m.index 11) (m.index 12) (r+1) := by
      rw [en,h3',h11',h12',h11,h12,h.next,nextTable_succ hab']
    have hend : t.index 7 = r := (ei _ (by decide) (by decide)).trans ((hi _ (by decide)).trans h.counter)
    refine ⟨t,k+l,Nat.add_le_add hk hl,he.seq er,er.safe_end,by simp [hend],?_,?_,?_,?_,?_⟩
    · intro a ha
      have h2 : a ≠ 2 := by simp_all [loopScratch]
      have h3 : a ≠ 3 := by simp_all [loopScratch]
      have h7 : a ≠ 7 := by simp_all [loopScratch]
      have hS : ¬ StageScratch a := by simp_all [loopScratch]
      simpa [h7] using (ei a h2 h3).trans ((hi a hS).trans (h.index a ha))
    · simpa [previousTable] using hprev'
    · simpa using hnext'
    · rw [hA,h.state] at hw
      have hsame : uniformMatrix n (t.index 2) t = uniformMatrix n (s.index 3) v := by
        rw [ep,h3']
        ext i j
        exact congrFun ed _
      simpa [birdLayer] using hsame.trans hw
    · intro a ha ha' hb'
      have hside : a<s.index 3 ∨ s.index 3+n*n≤a := by
        rw [h.next]; unfold nextTable; split <;> assumption
      exact (congrFun ed a).trans ((ho a ha hside).trans (h.other a ha ha' hb'))
  obtain ⟨t,k,hk,he,ht⟩ := Block.Eval.forRange_invariant 7 13 (n-1) (birdStageCost n+4) I m hm initial
    (fun _ _ h => ⟨h.safe,h.counter,(h.index 13 (by decide)).trans hstop⟩) next
  exact ⟨t,k,hk,he,ht.state,ht.next,ht.index 11 (by decide),ht.other⟩

end Compression
end LinearProgramming
end Optimization
end OAI
