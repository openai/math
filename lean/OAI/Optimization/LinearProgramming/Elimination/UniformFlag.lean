import OAI.Optimization.LinearProgramming.Elimination.UniformAccess

/-! Fixed active-flag routines for the adaptive basis scan. The determinant is in scalar
register 6. Index registers 18 and 19 give the flag array and the current candidate. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM Compression

private theorem flagSafeWrite {K : Type*} {P : K → Prop} {m : Memory K} (h : ∀ i,P (m.data i))
    (r : ℕ) {x : K} (hx : P x) : ∀ i,P ((m.putData r x).data i) := by
  intro i; by_cases hi : i=r <;> simp [Memory.putData,hi,h,hx]

/-- Update exactly one flag, using the candidate counter held in address register 19. -/
def writeFlag (value : ℚ) : Block :=
  .seq (.op (.const 3 value)) (indexedStore 3 18 14 19)

theorem writeFlag_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (q : ℚ) (n : ℕ) (j : Fin n) (h14 : m.index 14=0)
    (h19 : m.index 19=j.val) (hm : ∀a,P (m.data a)) (hval : P (q : K)) :
    ∃ t k, k ≤ 4*n+7 ∧ Block.Eval (fun w => ∀a,P (w.data a)) (writeFlag q) m k t ∧
      t.data (m.index 18+j.val)=(q:K) ∧
      (∀ p,7≤p → p≠m.index 18+j.val → t.data p = m.data p) ∧ accessFrame m t := by
  let u := m.putData 3 (q:K)
  have hu : ∀ a,P (u.data a) := flagSafeWrite hm _ hval
  have hwrite : Block.Eval (fun w => ∀a,P (w.data a)) (.op (.const 3 q)) m 1 u :=
    Block.Eval.op_const m 3 q hm hu
  have ok : CellScratchOK 8 9 10 0 14 19 := by
    refine ⟨by decide,by decide,by decide,?_⟩
    intro i hi; simp only [List.mem_cons,List.not_mem_nil,or_false] at hi; omega
  obtain ⟨t,he,hd,hf⟩ := indexedStore_spec P u 3 18 14 19 hu ok
  have haddr : u.index 18+u.index 14*u.index 0+u.index 19 = m.index 18+j.val := by
    change m.index 18+m.index 14*m.index 0+m.index 19 = _; rw [h14,h19,zero_mul,Nat.add_zero]
  rw [haddr] at hd
  refine ⟨t,_,?_,hwrite.seq he,?_,?_,hf⟩
  · change 1+(m.index 14*(4*m.index 0+5)+4*m.index 19+6) ≤ 4*n+7
    rw [h14,h19,zero_mul,Nat.zero_add]; omega
  · simp [hd,u,Memory.putData]
  · intro p hp hne; rw [hd,Function.update_of_ne hne]
    simp [u,Memory.putData,show p ≠ 3 by omega]

/-- Drop the flagged candidate exactly when the determinant in scalar register 6 is zero. -/
def clearIfZero : Block := .seq (.op (.const 0 0))
  (.branch (.scalarLT 6 0) .skip (.branch (.scalarLT 0 6) .skip (writeFlag 0)))

theorem clearIfZero_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (n : ℕ) (j : Fin n) (h14 : m.index 14=0)
    (h19 : m.index 19=j.val) (hF : 7 ≤ m.index 18) (hm : ∀a,P (m.data a)) (h0 : P 0) :
    ∃ t k, k ≤ 4*n+11 ∧ Block.Eval (fun w => ∀a,P (w.data a)) clearIfZero m k t ∧
      t.data (m.index 18+j.val)=(if m.data 6=0 then 0 else m.data (m.index 18+j.val)) ∧
      (∀ p,7≤p → p≠m.index 18+j.val → t.data p = m.data p) ∧ accessFrame m t := by
  let safe := fun w : Memory K => ∀a, P (w.data a)
  let u := m.putData 0 0
  have hu : safe u := flagSafeWrite hm _ h0
  have ez : Block.Eval safe (.op (.const 0 0)) m 1 u := by
    simpa [u] using Block.Eval.op_const (safe:=safe) m 0 0 hm (by simpa using hu)
  have uz : u.data 0 = 0 := by simp [u,Memory.putData]
  have u6 : u.data 6 = m.data 6 := by simp [u,Memory.putData]
  have high (p : ℕ) (hp : 7 ≤ p) : u.data p = m.data p := by simp [u,Memory.putData,show p ≠ 0 by omega]
  have keep (p : ℕ) (hp : 7 ≤ p) (_ : p≠m.index 18+j.val) := high p hp
  rcases lt_trichotomy (m.data 6) 0 with hn | he | hp
  · refine ⟨u,3,by omega,ez.seq (.branchTrue (by simp [Cond.test,uz,u6,hn]) (.skip hu)),?_,keep,fun _ _ _ _ => rfl⟩
    simpa [hn.ne] using high (m.index 18+j.val) (by omega)
  · obtain ⟨t,k,hk,hw,hwval,hwkeep,hwidx⟩ := writeFlag_spec P u 0 n j h14 h19 hu (by simpa using h0)
    refine ⟨t,1+(1+(1+k)),by omega,ez.seq (.branchFalse (by simp [Cond.test,uz,u6,he])
      (.branchFalse (by simp [Cond.test,uz,u6,he]) hw)),?_,fun p h hn => (hwkeep p h hn).trans (high p h),hwidx⟩
    change t.data (m.index 18 + j.val) = _ at hwval
    simpa [he] using hwval
  · refine ⟨u,4,by omega,ez.seq (.branchFalse (by simp [Cond.test,uz,u6,hp.not_gt])
      (.branchTrue (by simp [Cond.test,uz,u6,hp]) (.skip hu))),?_,keep,fun _ _ _ _ => rfl⟩
    simpa [hp.ne'] using high (m.index 18+j.val) (by omega)

end Elimination
end LinearProgramming
end Optimization
end OAI
