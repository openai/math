import OAI.Optimization.LinearProgramming.Elimination.UniformAccess
import OAI.Optimization.LinearProgramming.Elimination.UniformChoose
import OAI.Optimization.LinearProgramming.Elimination.Mask

/-! Materialization of a masked Gram cell by one fixed RAM block. Memory above the scalar
scratch bank is only copied, and the caller may impose any predicate containing 0 and 1. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM Compression Matrix
open scoped Matrix

/-- Index registers 0, 17, 18 and 1 hold dimension, Gram base, flags base and output base.
Registers 4 and 5 are row and column. Register 14 holds zero. -/
def uniformMaskCell : Block :=
  .seq (.op (.const 4 0)) (.seq (indexedLoad 0 18 14 4) (.seq (indexedLoad 1 18 14 5)
    (.seq (indexedLoad 2 17 4 5) (.seq chooseMaskEntry (indexedStore 3 1 4 5)))))

private theorem scratchOK (r c : ℕ) (hr : r=4 ∨ r=5 ∨ r=14) (hc : c=4 ∨ c=5 ∨ c=14) :
    CellScratchOK 8 9 10 0 r c := by
  refine ⟨by decide,by decide,by decide,?_⟩
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  omega

private theorem high_after_load {K : Type*} {s t : Memory K} {dst : ℕ} {v : K}
    (h : t.data = Function.update s.data dst v) (hd : dst < 7) (a : ℕ) (ha : 7 ≤ a) :
    t.data a = s.data a := by rw [h,Function.update_of_ne (by omega : a ≠ dst)]

private theorem entry_cost_le {r c n : ℕ} (hr : r ≤ n) (hc : c ≤ n) :
    r*(4*n+5)+4*c+6 ≤ 20*(n+1)^2 := by
  have h := Nat.mul_le_mul_right (4*n+5) hr
  nlinarith

/-- Reading an index outside the three scratch registers is invariant under indexed access. -/
private theorem frame_read {K : Type*} {s t : Memory K} (h : accessFrame s t) (p : ℕ)
    (hp : p < 8 ∨ 10 < p) : t.index p = s.index p := h p (by omega) (by omega) (by omega)

theorem uniformMaskCell_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (n : ℕ) (S : Finset (Fin n)) (i j : Fin n)
    (hN : m.index 0=n) (hi : m.index 4=i.val) (hj : m.index 5=j.val) (hzero : m.index 14=0)
    (hg : 7 ≤ m.index 17) (hf : 7 ≤ m.index 18)
    (hm : ∀ p, P (m.data p)) (h0 : P 0) (h1 : P 1)
    (hflag : ∀ k : Fin n, m.data (m.index 18+k.val) = flag S k) :
    let q := m.index 1+i.val*n+j.val
    let G := uniformMatrix n (m.index 17) m
    ∃ cost t, cost ≤ 90*(n+1)^2 ∧ Block.Eval (fun s => ∀ p, P (s.data p)) uniformMaskCell m cost t ∧
      t.data q = maskGram G (flag S) i j ∧
      (∀ p, 7 ≤ p → p ≠ q → t.data p = m.data p) ∧ accessFrame m t := by
  let safe := fun w : Memory K => ∀ p, P (w.data p)
  let z := m.putData 4 0
  have hz : safe z := by intro p; by_cases hp : p=4 <;> simp [z,Memory.putData,hp,hm,h0]
  have ez : Block.Eval safe (.op (.const 4 0)) m 1 z := by
    simpa [z] using Block.Eval.op_const (safe := safe) m 4 0 hm (by simpa using hz)
  have zhigh (p : ℕ) (hp : 7 ≤ p) : z.data p = m.data p := by
    simp [z,Memory.putData,show p ≠ 4 by omega]
  obtain ⟨u,e₁,d₁,f₁⟩ := indexedLoad_spec P z 0 18 14 4 hz (scratchOK _ _ (by decide) (by decide))
  have fu : accessFrame m u := f₁
  have highU (p : ℕ) (hp : 7 ≤ p) : u.data p = m.data p :=
    (high_after_load d₁ (by decide) p hp).trans (zhigh p hp)
  have u0 : u.data 0 = flag S i := by
    rw [d₁, Function.update_self]
    change z.data (m.index 18 + m.index 14*m.index 0 + m.index 4) = _
    rw [hzero,zero_mul,Nat.add_zero,hi,zhigh _ (by omega),hflag]
  obtain ⟨v,e₂,d₂,f₂⟩ := indexedLoad_spec P u 1 18 14 5 e₁.safe_end (scratchOK _ _ (by decide) (by decide))
  have fv := accessFrame_trans fu f₂
  have highV (p : ℕ) (hp : 7 ≤ p) : v.data p = m.data p :=
    (high_after_load d₂ (by decide) p hp).trans (highU p hp)
  have v1 : v.data 1 = flag S j := by
    rw [d₂, Function.update_self,frame_read fu 14 (by decide),hzero,zero_mul,Nat.add_zero,
      frame_read fu 18 (by decide),frame_read fu 5 (by decide),hj,highU _ (by omega),hflag]
  obtain ⟨w,e₃,d₃,f₃⟩ := indexedLoad_spec P v 2 17 4 5 e₂.safe_end (scratchOK _ _ (by decide) (by decide))
  have fw := accessFrame_trans fv f₃
  have highW (p : ℕ) (hp : 7 ≤ p) : w.data p = m.data p :=
    (high_after_load d₃ (by decide) p hp).trans (highV p hp)
  let G := uniformMatrix n (m.index 17) m
  have w2 : w.data 2 = G i j := by
    rw [d₃, Function.update_self,frame_read fv 17 (by decide),frame_read fv 4 (by decide),
      frame_read fv 0 (by decide),frame_read fv 5 (by decide),hi,hN,hj]
    exact highV _ (by omega)
  have w1 : w.data 1 = flag S j := by simpa [d₃] using v1
  have w0 : w.data 0 = flag S i := by simpa [d₃,d₂] using u0
  have w4 : w.data 4 = 0 := by simp [d₃,d₂,d₁,z,Memory.putData]
  obtain ⟨c,hc,ec⟩ := chooseMaskEntry_spec P w (i ∈ S) (j ∈ S) e₃.safe_end h0 h1 w4 w0 w1
  let val := maskGram G (flag S) i j
  have vi : (if i ∈ S then (if j ∈ S then w.data 2 else 0) else
      (if w.index 4 = w.index 5 then 1 else 0)) = val := by
    rw [frame_read fw 4 (by decide),frame_read fw 5 (by decide),hi,hj,w2]
    by_cases heq : i=j
    · subst j; by_cases hir : i ∈ S <;> simp [val,maskGram,flag,hir]
    · have hv : i.val ≠ j.val := fun h => heq (Fin.ext h)
      by_cases hir : i ∈ S <;> by_cases hjr : j ∈ S <;> simp [val,maskGram,flag,heq,hv,hir,hjr]
  rw [vi] at ec
  let a := w.putData 3 val
  have fa : accessFrame m a := fw
  obtain ⟨t,es,ds,fs⟩ := indexedStore_spec P a 3 1 4 5 ec.safe_end (scratchOK _ _ (by decide) (by decide))
  have out : a.index 1 + a.index 4*a.index 0 + a.index 5 = m.index 1+i.val*n+j.val := by
    rw [frame_read fa 1 (by decide),frame_read fa 4 (by decide),frame_read fa 0 (by decide),
      frame_read fa 5 (by decide),hi,hj,hN]
  rw [out] at ds
  have cost₁ : z.index 14*(4*z.index 0+5)+4*z.index 4+6 ≤ 20*(n+1)^2 := by
    change m.index 14*(4*m.index 0+5)+4*m.index 4+6 ≤ _
    rw [hzero,hN,hi]; exact entry_cost_le (Nat.zero_le _) i.isLt.le
  have cost₂ : u.index 14*(4*u.index 0+5)+4*u.index 5+6 ≤ 20*(n+1)^2 := by
    rw [frame_read fu 14 (by decide),frame_read fu 0 (by decide),frame_read fu 5 (by decide),hzero,hN,hj]
    exact entry_cost_le (Nat.zero_le _) j.isLt.le
  have cost₃ : v.index 4*(4*v.index 0+5)+4*v.index 5+6 ≤ 20*(n+1)^2 := by
    rw [frame_read fv 4 (by decide),frame_read fv 0 (by decide),frame_read fv 5 (by decide),hi,hN,hj]
    exact entry_cost_le i.isLt.le j.isLt.le
  have cost₄ : a.index 4*(4*a.index 0+5)+4*a.index 5+6 ≤ 20*(n+1)^2 := by
    rw [frame_read fa 4 (by decide),frame_read fa 0 (by decide),frame_read fa 5 (by decide),hi,hN,hj]
    exact entry_cost_le i.isLt.le j.isLt.le
  refine ⟨_,t,?_,ez.seq (e₁.seq (e₂.seq (e₃.seq (ec.seq es)))),?_,?_,accessFrame_trans fa fs⟩
  · have hb : 0 < (n+1)^2 := by positivity
    omega
  · simp [ds,a,Memory.putData,val,G]
  · intro p hp hne
    rw [ds,Function.update_of_ne hne]
    exact (high_after_load (show a.data = Function.update w.data 3 val from rfl) (by decide) p hp).trans (highW p hp)

end Elimination
end LinearProgramming
end Optimization
end OAI
