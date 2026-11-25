import OAI.Optimization.LinearProgramming.Compression.UniformBirdIterations
import OAI.Optimization.LinearProgramming.Compression.DetCircuit

/-! Join the dimension-independent stage loops and final sign correction. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

private def initializeBird : Block := .seq (.op (.addrCopy 2 1))
  (.seq (.op (.addrCopy 3 11)) (.op (.decr 13 0)))

private def finishBird : Block := .seq (.op (.load 6 2))
  (.branch (.addrLT 11 3) (.seq (.op (.const 0 0)) (.op (.sub 6 0 6))) .skip)

private theorem safe_write {K : Type} (P : K → Prop) {m : Memory K} (hm : ∀ a, P (m.data a))
    (dst : ℕ) {x : K} (hx : P x) : ∀ a, P ((m.putData dst x).data a) := by
  intro a
  by_cases ha : a = dst
  · simpa [ha] using hx
  · simpa [ha] using hm a

private theorem finishBird_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (r a b : ℕ) (hab : a<b) (h11 : s.index 11=a)
    (h3 : s.index 3=nextTable a b r) (hs : ∀ p, P (s.data p)) (hp0 : P 0)
    (hpneg : ∀ x, P x → P (-x)) :
    ∃ t k, k ≤ 5 ∧ Block.Eval (fun w => ∀ p, P (w.data p)) finishBird s k t ∧
      t.data 6=(-1 : K)^r*s.data (s.index 2) ∧ ∀ p, 7 ≤ p → t.data p = s.data p := by
  let u := s.putData 6 (s.data (s.index 2))
  have hu : ∀ p, P (u.data p) := safe_write P hs _ (hs _)
  have load : Block.Eval (fun w => ∀ p, P (w.data p)) (.op (.load 6 2)) s 1 u :=
    Block.Eval.op_load _ _ _ hs hu
  by_cases h : Even r
  · refine ⟨u,2,by decide,load.seq (.branchFalse (by simp [Cond.test,u,h3,h11,nextTable,h]) (.skip hu)), ?_, ?_⟩
    · simp [u, h]
    · intro p hp; simp [u, show p ≠ 6 by omega]
  · let v := u.putData 0 0
    let t := v.putData 6 (v.data 0-v.data 6)
    have hv : ∀ p, P (v.data p) := safe_write P hu _ hp0
    have hval : v.data 0-v.data 6 = -s.data (s.index 2) := by simp [v,u]
    have ht : ∀ p, P (t.data p) := safe_write P hv _ (hval ▸ hpneg _ (hs _))
    have z : Block.Eval (fun w => ∀ p, P (w.data p)) (.op (.const 0 0)) u 1 v := by
      simpa [v] using Block.Eval.op_const (safe := fun w : Memory K => ∀ p, P (w.data p)) u 0 0 hu (by simpa using hv)
    have sub : Block.Eval (fun w => ∀ p, P (w.data p)) (.op (.sub 6 0 6)) v 1 t :=
      Block.Eval.op_sub _ _ _ _ hv ht
    refine ⟨t,5,by decide,load.seq (.branchTrue (by simp [Cond.test,u,h3,h11,nextTable,h,hab]) (z.seq sub)),?_,?_⟩
    · simp [t,hval,neg_one_pow_eq_ite,h]
    · intro p hp; simp [t,v,u,show p ≠ 0 by omega, show p ≠ 6 by omega]

/-- Register 14 holds zero. The initial header holds the dimension, input base, and the
bases of two nonoverlapping working arrays at 0, 1, 11, 12 respectively. -/
def uniformDetBlock (cell : Block) : Block :=
  .branch (.addrLT 14 0) (.seq initializeBird (.seq (birdIterations cell) finishBird)) (.op (.const 6 1))

private theorem uniform_time_bound (n : ℕ) : birdIterationsCost n+10 ≤ 2000*(n+1)^7 := by
  unfold birdIterationsCost birdStageCost
  have h := Nat.mul_le_mul_right (n*(n*(1000*(n+1)^4+3)+5)+2+4+3) (Nat.sub_le n 1)
  calc
    _ ≤ n*(n*(n*(1000*(n+1)^4+3)+5)+2+4+3)+2+10 := by omega
    _ ≤ _ := by nlinarith [Nat.zero_le (n^6), Nat.zero_le (n^5), Nat.zero_le (n^4),
                              Nat.zero_le (n^3), Nat.zero_le (n^2)]

/-- One fixed structured block computes a determinant in dimension-polynomial steps. Its
safety premise concerns only the actual Bird register values for the supplied matrix. -/
theorem uniformDetBlock_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (cell : Block) (hcell : BirdCellSpec K cell) (P : K → Prop) (m : Memory K) (n : ℕ)
    (hN : m.index 0=n) (hI : 7 ≤ m.index 1) (hIA : m.index 1+n*n ≤ m.index 11)
    (hAB : m.index 11+n*n ≤ m.index 12) (hZ : m.index 14=0) (hm : ∀ p, P (m.data p))
    (hp0 : P 0) (hp1 : P 1) (hpneg : ∀ x, P x → P (-x))
    (hreg : ∀ k<n, ∀ r : BirdRegister n, P (r.read (uniformMatrix n (m.index 1) m)
      (birdLayer (uniformMatrix n (m.index 1) m) k))) :
    ∃ t k, k ≤ 2000*(n+1)^7 ∧ Block.Eval (fun z => ∀ p, P (z.data p)) (uniformDetBlock cell) m k t ∧
      t.data 6=(uniformMatrix n (m.index 1) m).det ∧
      (∀ p, 7 ≤ p → (p<m.index 11 ∨ m.index 11+n*n≤p) → (p<m.index 12 ∨ m.index 12+n*n≤p) →
        t.data p=m.data p) := by
  cases n with
  | zero =>
    let t := m.putData 6 1
    have ht : ∀p, P (t.data p) := safe_write P hm _ hp1
    have hw : Block.Eval (fun w => ∀ p, P (w.data p)) (.op (.const 6 1)) m 1 t := by
      simpa [t] using Block.Eval.op_const (safe := fun w : Memory K => ∀ p, P (w.data p)) m 6 1 hm (by simpa using ht)
    refine ⟨t,2,by decide,.branchFalse (by simp [Cond.test,hZ,hN]) hw, ?_,?_⟩
    · simp [t]
    · intro p hp _ _; simp [t,show p ≠ 6 by omega]
  | succ r =>
    let n := r+1
    let m₁ := m.putIndex 2 (m.index 1)
    let m₂ := m₁.putIndex 3 (m₁.index 11)
    let m₃ := m₂.putIndex 13 (m₂.index 0-1)
    have setup : Block.Eval (fun w => ∀ p, P (w.data p)) initializeBird m 3 m₃ :=
      (Block.Eval.op_addrCopy _ _ _ hm hm).seq ((Block.Eval.op_addrCopy _ _ _ hm hm).seq
        (Block.Eval.op_decr _ _ _ hm hm))
    have hstart : uniformMatrix n (m₃.index 1) m₃ = uniformMatrix n (m.index 1) m := by
      simp [m₃,m₂,m₁]
    obtain ⟨u,k,hk,run,hu,hnext,hfixed,huother⟩ := birdIterations_spec cell hcell P m₃ n (Nat.zero_lt_succ r)
      (by simpa [m₃,m₂,m₁] using hN) (by simpa [m₃,m₂,m₁] using hI)
      (by simpa [m₃,m₂,m₁] using hIA) (by simpa [m₃,m₂,m₁] using hAB)
      (by simp [m₃,m₂,m₁]) (by simp [m₃,m₂,m₁]) (by simp [m₃,m₂,m₁,hN,n]) hm
      (by simpa only [hstart] using hreg)
    have h3_11 : m₃.index 11=m.index 11 := by simp [m₃,m₂,m₁]
    have h3_12 : m₃.index 12=m.index 12 := by simp [m₃,m₂,m₁]
    rw [h3_11,h3_12,show n-1 = r by simp [n]] at hnext
    have hab : m.index 11 < m.index 12 := (Nat.lt_add_of_pos_right (Nat.mul_pos (Nat.zero_lt_succ r) (Nat.zero_lt_succ r))).trans_le hAB
    obtain ⟨t,l,hl,finish,hanswer,htother⟩ := finishBird_spec P u r _ _ hab (hfixed.trans h3_11)
      hnext run.safe_end hp0 hpneg
    have v0 := congrFun (congrFun hu (0 : Fin n)) (0 : Fin n)
    rw [hstart, show n-1 = r by simp [n]] at v0
    have hv : u.data (u.index 2) = birdLayer (uniformMatrix n (m.index 1) m) r 0 0 := by
      simpa [uniformMatrix] using v0
    have det := det_from_birdStages (uniformMatrix n (m.index 1) m)
    have hstep (A : Matrix (Fin n) (Fin n) K) : birdStage A = BirdDet.Spec.stepEntry A := funext (birdStage_eq A)
    rw [hstep, ← birdLayer_eq_iterate] at det
    refine ⟨t,1+(3+(k+l))+1,?_,.branchTrue (by simp [Cond.test,hZ,hN]) (setup.seq (run.seq finish)),?_,?_⟩
    · exact (show 1+(3+(k+l))+1 ≤ birdIterationsCost n+10 by omega).trans (uniform_time_bound n)
    · rw [hanswer,hv,← det]
    · intro p hp hwa hwb
      exact (htother p hp).trans (huother p hp (h3_11 ▸ hwa) (h3_12 ▸ hwb))

end Compression
end LinearProgramming
end Optimization
end OAI
