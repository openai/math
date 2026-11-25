import OAI.Optimization.LinearProgramming.Elimination.UniformAccess

/-! A fixed row-major table writer. The callback may inspect the original input registers
outside the output interval and the cells in the prefix already written. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM

/-- The first `filled` cells have their prescribed values; other scalar memory outside
the low arithmetic scratch registers still agrees with the caller's memory. -/
structure FillState {K : Type} (P : K → Prop) (scratch : Finset ℕ) {m n : ℕ} (out filled : ℕ)
    (T : Matrix (Fin m) (Fin n) K) (origin now : Memory K) : Prop where
  valid : ∀ a, P (now.data a)
  index : ∀ a ∉ insert 4 (insert 5 scratch), now.index a = origin.index a
  done_ : ∀ i j, i.val*n+j.val < filled → now.data (out+i.val*n+j.val) = T i j
  other : ∀ a, 7 ≤ a → (a < out ∨ out+filled ≤ a) → now.data a = origin.data a

private theorem FillState.bump {K : Type} {P : K → Prop} {scratch : Finset ℕ} {m n out filled : ℕ}
    {T : Matrix (Fin m) (Fin n) K} {origin now : Memory K} (h : FillState P scratch out filled T origin now)
    {a : ℕ} (ha : a ∈ insert 4 (insert 5 scratch)) (x : ℕ) :
    FillState P scratch out filled T origin (now.putIndex a x) := by
  refine ⟨h.valid,?_,h.done_,h.other⟩
  intro b hb
  have hba : b ≠ a := by rintro rfl; exact hb ha
  simpa [hba] using h.index b hb

private theorem offset_lt {m n : ℕ} (i : Fin m) (j : Fin n) : i.val*n+j.val < m*n := by
  simpa [finProdFinEquiv,Nat.add_comm,Nat.mul_comm] using (finProdFinEquiv (i,j)).isLt

private theorem offset_inj {m n : ℕ} {i p : Fin m} {j q : Fin n}
    (h : i.val*n+j.val = p.val*n+q.val) : i=p ∧ j=q := by
  have h' : finProdFinEquiv (i,j) = finProdFinEquiv (p,q) := by
    apply Fin.ext; simpa [finProdFinEquiv,Nat.add_comm,Nat.mul_comm] using h
  exact Prod.mk.inj (finProdFinEquiv.injective h')

/-- Lift verified single-cell writes to a dimension-independent double loop. The output
interval is fixed while all callback decisions may depend on its rows, columns, and inputs. -/
theorem uniform_tabulate {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (cell : Block) (scratch : Finset ℕ) {m n : ℕ} (rows cols out B : ℕ)
    (T : Matrix (Fin m) (Fin n) K) (orig : Memory K) (hstart : ∀a,P (orig.data a))
    (ho : 7 ≤ out) (hr : orig.index rows = m) (hc : orig.index cols = n)
    (hrows : rows ∉ insert 4 (insert 5 scratch)) (hcols : cols ∉ insert 4 (insert 5 scratch))
    (hfour : 4 ∉ scratch) (hfive : 5 ∉ scratch)
    (hcell : ∀ (i : Fin m) (j : Fin n) (s : Memory K),
      FillState P scratch out (i.val*n+j.val) T orig s → s.index 4=i.val → s.index 5=j.val →
      ∃ cost t, cost ≤ B ∧ Block.Eval (fun w => ∀a,P (w.data a)) cell s cost t ∧
        t.data (out+i.val*n+j.val)=T i j ∧
        (∀ a,7≤a → a≠out+i.val*n+j.val → t.data a = s.data a) ∧
        (∀ a ∉ scratch, t.index a = s.index a)) :
    ∃ t k, k ≤ m*(n*(B+3)+5)+2 ∧
      Block.Eval (fun w => ∀a,P (w.data a)) (.forRowsCols 4 rows 5 cols cell) orig k t ∧
      FillState P scratch out (m*n) T orig t := by
  let frame (filled : ℕ) := FillState P scratch out filled T orig
  let R (i : ℕ) (s : Memory K) := frame (i*n) s ∧ s.index 4=i
  let C (i j : ℕ) (s : Memory K) := frame (i*n+j) s ∧ s.index 4=i ∧ s.index 5=j
  have initial : R 0 (orig.putIndex 4 0) := by
    have h : frame 0 orig := ⟨hstart, fun _ _ => rfl, by simp, fun _ _ _ => rfl⟩
    exact ⟨by simpa using h.bump (a := 4) (by simp) 0, by simp⟩
  have beginRow (i : ℕ) (_ : i < m) (s : Memory K) (h : R i s) : C i 0 (s.putIndex 5 0) :=
    ⟨by simpa using h.1.bump (a := 5) (by simp) 0, by simpa using h.2, by simp⟩
  have endRow (i : ℕ) (_ : i < m) (s : Memory K) (h : C i n s) : R (i+1) (s.putIndex 4 (s.index 4+1)) :=
    ⟨by simpa [Nat.succ_mul] using h.1.bump (a := 4) (by simp) (s.index 4+1), by simp [h.2.1]⟩
  have advance (i : ℕ) (hi : i<m) (j : ℕ) (hj : j<n) (s : Memory K) (h : C i j s) :
      ∃ t k, k ≤ B ∧ Block.Eval (fun w => ∀a,P (w.data a)) cell s k t ∧
        C i (j+1) (t.putIndex 5 (t.index 5+1)) := by
    let ri : Fin m := ⟨i,hi⟩
    let cj : Fin n := ⟨j,hj⟩
    obtain ⟨k,t,hk,he,hw,hp,hidx⟩ := hcell ri cj s h.1 h.2.1 h.2.2
    have hn : frame (i*n+(j+1)) t := by
      refine ⟨he.safe_end, ?_, ?_, ?_⟩
      · intro a ha
        exact (hidx a (fun hh => ha (by simp [hh]))).trans (h.1.index a ha)
      · intro i' j' hlt
        by_cases earlier : i'.val*n+j'.val < i*n+j
        · have hne : out+i'.val*n+j'.val ≠ out+ri.val*n+cj.val := by dsimp [ri,cj]; omega
          exact (hp _ (by omega) hne).trans (h.1.done_ i' j' earlier)
        · have eq : i'.val*n+j'.val = ri.val*n+cj.val := by dsimp [ri,cj]; omega
          obtain ⟨rfl,rfl⟩ := offset_inj eq
          exact hw
      · intro a ha gap
        have hne : a ≠ out+ri.val*n+cj.val := by dsimp [ri,cj]; omega
        exact (hp a ha hne).trans (h.1.other a ha (by omega))
    exact ⟨t,k,hk,he,hn.bump (a:=5) (by simp) _,
      by simpa using (hidx 4 hfour).trans h.2.1, by simp [hidx 5 hfive,h.2.2]⟩
  obtain ⟨t,k,hk,he,h⟩ := Block.Eval.forRowsCols_invariant (body:=cell) 4 rows 5 cols m n B R C orig
    hstart initial (fun _ _ h => ⟨h.1.valid,h.2,(h.1.index rows hrows).trans hr⟩) beginRow
    (fun _ _ _ h => ⟨h.1.valid,h.2.2,(h.1.index cols hcols).trans hc⟩) advance endRow
  exact ⟨t,k,hk,he,h.1⟩

end Elimination
end LinearProgramming
end Optimization
end OAI
