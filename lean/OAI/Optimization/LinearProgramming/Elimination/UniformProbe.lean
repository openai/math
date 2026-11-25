import OAI.Optimization.LinearProgramming.Elimination.UniformDecision
import OAI.Optimization.LinearProgramming.Elimination.UniformFlag

/-! A single fixed scalar/address-RAM probe inserts one candidate, tests its masked Gram
determinant and erases it on dependence. Its workspace layout is independent of all answers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM Compression Matrix

structure BasisLayout (n : ℕ) where
  gram : ℕ
  flags : ℕ
  mask : ℕ
  workA : ℕ
  workB : ℕ
  low : 7 ≤ gram
  beforeFlags : gram+n*n ≤ flags
  beforeMask : flags+n ≤ mask
  beforeA : mask+n*n ≤ workA
  beforeB : workA+n*n ≤ workB

/-- The live basis workspace and its fixed header registers. -/
structure BasisState {K : Type} [Field K] {n : ℕ} (l : BasisLayout n)
    (G : Matrix (Fin n) (Fin n) K) (S : Finset (Fin n)) (m : Memory K) : Prop where
  dim : m.index 0=n
  maskPtr : m.index 1=l.mask
  workAPtr : m.index 11=l.workA
  workBPtr : m.index 12=l.workB
  zeroIdx : m.index 14=0
  gramPtr : m.index 17=l.gram
  flagsPtr : m.index 18=l.flags
  gram : uniformMatrix n l.gram m=G
  flags : ∀ i : Fin n, m.data (l.flags+i.val)=flag S i

private def header : Finset ℕ := {0,1,11,12,14,17,18}

private theorem BasisState.transport {K : Type} [Field K] {n : ℕ} {l : BasisLayout n}
    {G : Matrix (Fin n) (Fin n) K} {S S' : Finset (Fin n)} {m t : Memory K} (s : BasisState l G S m)
    (idx : ∀ p ∈ header, t.index p = m.index p)
    (data : ∀ p, 7≤p → p<l.flags → t.data p=m.data p)
    (flags : ∀ i : Fin n, t.data (l.flags+i.val) = flag S' i) : BasisState l G S' t := by
  refine ⟨(idx 0 (by decide)).trans s.dim,(idx 1 (by decide)).trans s.maskPtr,
    (idx 11 (by decide)).trans s.workAPtr,(idx 12 (by decide)).trans s.workBPtr,
    (idx 14 (by decide)).trans s.zeroIdx,(idx 17 (by decide)).trans s.gramPtr,
    (idx 18 (by decide)).trans s.flagsPtr,?_,flags⟩
  rw [← s.gram]; ext i j
  have off : i.val*n+j.val < n*n := by
    simpa [finProdFinEquiv,Nat.add_comm,Nat.mul_comm] using (finProdFinEquiv (i,j)).isLt
  have hb := l.beforeFlags; have hl := l.low
  exact data _ (by omega) (by omega)

private theorem BasisState.updated {K : Type} [Field K] {n : ℕ} {l : BasisLayout n}
    {G : Matrix (Fin n) (Fin n) K} {S S' : Finset (Fin n)} {m t : Memory K} (s : BasisState l G S m)
    (j : Fin n) (idx : accessFrame m t)
    (data : ∀ p,7≤p → p≠l.flags+j.val → t.data p=m.data p)
    (hn : t.data (l.flags+j.val)=flag S' j)
    (hother : ∀i≠j, flag S' i = (flag S i : K)) : BasisState l G S' t := by
  apply s.transport (fun p hp => by
    simp only [header,Finset.mem_insert,Finset.mem_singleton] at hp
    exact idx p (by omega) (by omega) (by omega))
    (fun p h hp => data p h (by omega))
  intro i
  by_cases he : i=j
  · simpa [he] using hn
  · have hf := l.beforeFlags; have hl := l.low
    rw [data _ (by omega) (fun h => he (Fin.ext (Nat.add_left_cancel h))),s.flags,hother i he]

def uniformBasisProbe : Block :=
  .seq (writeFlag 1) (.seq uniformMaskedDecision clearIfZero)

def basisProbeCost (n : ℕ) := decisionCost n+8*n+18

/-- The same finite block processes every fresh column in every dimension. All actual scalar
values satisfy `P`, including cells inside both of the determinant's scratch tables. -/
theorem uniformBasisProbe_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n : ℕ} (l : BasisLayout n) (G : Matrix (Fin n) (Fin n) K) (S : Finset (Fin n))
    (P : K → Prop) (m : Memory K) (j : Fin n) (hs : BasisState l G S m)
    (hj : m.index 19=j.val) (fresh : j∉S) (hm : ∀i,P (m.data i))
    (h0 : P 0) (h1 : P 1) (hneg : ∀ x,P x → P (-x))
    (hreg : let T := maskGram G (flag (insert j S))
      ∀ k<n,∀ r : BirdRegister n, P (r.read T (birdLayer T k))) :
    let selected := if determinant (maskGram G (flag (insert j S)))=0 then S else insert j S
    ∃ t k, k ≤ basisProbeCost n ∧ Block.Eval (fun w => ∀i,P (w.data i)) uniformBasisProbe m k t ∧
      BasisState l G selected t ∧ t.index 19=j.val ∧ (∀ p, 15 ≤ p → t.index p = m.index p) ∧
      ∀ p, 7 ≤ p → p < l.flags → t.data p = m.data p := by
  let V := insert j S
  let D := (maskGram G (flag V)).det
  let R := if D=0 then S else V
  have hfg : 7 ≤ l.flags := l.low.trans ((Nat.le_add_right l.gram _).trans l.beforeFlags)
  have hmo : 7 ≤ l.mask := hfg.trans ((Nat.le_add_right l.flags _).trans l.beforeMask)
  obtain ⟨u,k,hk,e₁,val₁,data₁,idx₁⟩ := writeFlag_spec P m 1 n j hs.zeroIdx hj
    hm (by simpa using h1)
  rw [hs.flagsPtr] at val₁ data₁
  have us : BasisState l G V u := hs.updated j idx₁ data₁
    (by simpa [V,flag] using val₁) (fun i hi => by simp [V,flag,hi])
  have uj : u.index 19=j.val := (idx₁ 19 (by decide) (by decide) (by decide)).trans hj
  have ug : uniformMatrix n (u.index 17) u=G := by rw [us.gramPtr,us.gram]
  obtain ⟨v,k',hk',e₂,val₂,data₂,idx₂⟩ := uniformMaskedDecision_spec P u n V us.dim us.zeroIdx
    (us.gramPtr ▸ l.low) (us.flagsPtr ▸ hfg) (us.maskPtr ▸ hmo)
    (by rw [us.gramPtr,us.maskPtr]; exact l.beforeFlags.trans ((Nat.le_add_right l.flags _).trans l.beforeMask))
    (by rw [us.flagsPtr,us.maskPtr]; exact l.beforeMask) (by rw [us.maskPtr,us.workAPtr]; exact l.beforeA)
    (by rw [us.workAPtr,us.workBPtr]; exact l.beforeB) e₁.safe_end h0 h1 hneg
    (by rw [us.flagsPtr]; exact us.flags) (by rw [ug]; exact hreg)
  rw [ug] at val₂
  rw [us.maskPtr] at data₂
  have vf (p : ℕ) (hp : p ∈ header) : v.index p=u.index p := idx₂ p (by
    simp only [header,Finset.mem_insert,Finset.mem_singleton] at hp ⊢; omega)
  have vs : BasisState l G V v := us.transport vf
    (fun p h hp => data₂ p h (hp.trans_le ((Nat.le_add_right l.flags _).trans l.beforeMask)))
    (fun i => (data₂ _ (by omega) (by have h:=l.beforeMask; omega)).trans (us.flags i))
  have vj : v.index 19=j.val := (idx₂ 19 (by decide)).trans uj
  obtain ⟨t,k'',hk'',e₃,val₃,data₃,idx₃⟩ := clearIfZero_spec P v n j vs.zeroIdx vj
    (vs.flagsPtr ▸ hfg) e₂.safe_end h0
  rw [vs.flagsPtr] at val₃ data₃
  have vr : v.data 6=D := val₂
  have ts : BasisState l G R t := vs.updated j idx₃ data₃ (by
    rw [val₃,vr,vs.flags]; by_cases h : D=0 <;> simp [R,V,flag,h,fresh]) (fun i hi => by
      by_cases h : D=0 <;> simp [R,V,flag,h,hi])
  refine ⟨t,k+(k'+k''),?_,e₁.seq (e₂.seq e₃),?_,(idx₃ 19 (by decide) (by decide) (by decide)).trans vj,?_,?_⟩
  · unfold basisProbeCost; omega
  · simpa only [determinant_eq] using (show BasisState l G (if D=0 then S else V) t from ts)

  · intro p hp
    have hnd : p ∉ ({2,3,4,5,6,7,8,9,10,13} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    exact (idx₃ p (by omega) (by omega) (by omega)).trans
      ((idx₂ p hnd).trans (idx₁ p (by omega) (by omega) (by omega)))
  · intro p hp hf
    have hm' := l.beforeMask
    exact (data₃ p hp (by omega)).trans ((data₂ p hp (by omega)).trans (data₁ p hp (by omega)))

end Elimination
end LinearProgramming
end Optimization
end OAI
