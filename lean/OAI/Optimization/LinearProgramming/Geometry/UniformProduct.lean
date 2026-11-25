import OAI.Optimization.LinearProgramming.Geometry.UniformTable

/-! Uniform multiplication of one row matrix by the transpose of another.
The same fixed dot-product loop serves all dimensions. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Compression
open scoped Matrix BigOperators

def RowDotIndexScratch (q : ℕ) : Prop := q=20 ∨ q=21 ∨ q=22 ∨ q=23 ∨ q=38 ∨ q=39 ∨ q=43
instance (q : ℕ) : Decidable (RowDotIndexScratch q) := by unfold RowDotIndexScratch; infer_instance

/-- Input row table bases in indexes 40 and 41 and common row length in index 42.
Outer table cursors 30 and 32 select the two rows. Scalar 6 receives their dot product. -/
def uniformRowDotCell : Block :=
  .seq (.op (.addrConst 43 0))
    (.seq (cellAddress 20 38 39 40 42 30 43)
      (.seq (cellAddress 21 38 39 41 42 32 43)
        (.seq (.op (.addrCopy 23 42)) (.seq Dense.dotBlock (.op (.copy 6 20))))))

def uniformRowDotCost (m p k : ℕ) := (m+p)*(4*k+5)+9*k+18

private theorem finRangeDot {K : Type} [CommRing K] (k t : ℕ) (ht : t ≤ k) (f : ℕ → K) :
    (∑ a ∈ Finset.range t, f a) = ∑ i ∈ Finset.univ.filter (fun j : Fin k => j.val < t), f i.val := by
  rw [Finset.sum_filter]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < t then f i else 0)]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr _ fun _ _ => rfl
  ext a
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

theorem uniformRowDotCell_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (m p k a b : ℕ) (i : Fin m) (j : Fin p)
    (hs : s.AllData P) (h30 : s.index 30=i.val) (h32 : s.index 32=j.val)
    (h40 : s.index 40=a) (h41 : s.index 41=b) (h42 : s.index 42=k)
    (ha : 23<a) (hb : 23<b)
    (hpartial : ∀ u : Finset (Fin k),
      P (∑ v ∈ u, uniformRect m k a s i v * uniformRect p k b s j v)) :
    ∃ t cost, cost ≤ uniformRowDotCost m p k ∧ Block.Eval (Memory.AllData P) uniformRowDotCell s cost t ∧
      t.data 6 = (uniformRect m k a s * (uniformRect p k b s)ᵀ) i j ∧
      (∀ q, q ≠ 6 → 23<q → t.data q=s.data q) ∧
      ∀ q, ¬ RowDotIndexScratch q → t.index q=s.index q := by
  let s₀ := s.putIndex 43 0
  have e₀ : Block.Eval (Memory.AllData P) (.op (.addrConst 43 0)) s 1 s₀ :=
    Block.Eval.op_addrConst _ _ _ hs hs
  obtain ⟨s₁,e₁,d₁,f₁,h₁⟩ := cellAddress_spec (fun v => ∀ u, P (v u)) s₀ hs
    20 38 39 40 42 30 43 (by simp [CellScratchOK])
  have hs₁ : s₁.AllData P := e₁.safe_end
  have i₁ (q : ℕ) (h20 : q≠20) (h38 : q≠38) (h39 : q≠39) (h43 : q≠43) :
      s₁.index q = s.index q := by simpa [s₀,h43] using f₁ q h20 h38 h39
  have first : s₁.index 20 = a+i.val*k := by simpa [s₀,h40,h30,h42] using h₁
  have z₁ : s₁.index 43 = 0 := by simpa [s₀] using f₁ 43 (by decide) (by decide) (by decide)
  have c₁ : s₁.index 32 = j.val := (i₁ 32 (by decide) (by decide) (by decide) (by decide)).trans h32
  have len₁ : s₁.index 42 = k := (i₁ 42 (by decide) (by decide) (by decide) (by decide)).trans h42
  have base₁ : s₁.index 41 = b := (i₁ 41 (by decide) (by decide) (by decide) (by decide)).trans h41
  obtain ⟨s₂,e₂,d₂,f₂,h₂⟩ := cellAddress_spec (fun v => ∀ u, P (v u)) s₁ hs₁
    21 38 39 41 42 32 43 (by simp [CellScratchOK])
  have second : s₂.index 21 = b+j.val*k := by simpa [base₁,c₁,len₁,z₁] using h₂
  have first₂ : s₂.index 20 = a+i.val*k :=
    (f₂ 20 (by decide) (by decide) (by decide)).trans first
  have len₂ : s₂.index 42 = k :=
    (f₂ 42 (by decide) (by decide) (by decide)).trans len₁
  let s₃ := s₂.putIndex 23 (s₂.index 42)
  have e₃ : Block.Eval (Memory.AllData P) (.op (.addrCopy 23 42)) s₂ 1 s₃ :=
    Block.Eval.op_addrCopy _ _ _ e₂.safe_end e₂.safe_end
  have d₃ : s₃.data = s.data := d₂.trans d₁
  have xa : s₃.index 20 = a+i.val*k := by simp [s₃,first₂]
  have xb : s₃.index 21 = b+j.val*k := by simp [s₃,second]
  have hterm (v : ℕ) (hv : v < k) : P (Dense.dotTerm s₃ v) := by
    simpa [Dense.dotTerm, xa, xb, d₃, uniformRect] using hpartial {⟨v,hv⟩}
  have hsum (t : ℕ) (ht : t≤k) : P (Dense.dotPrefix s₃ t) := by
    simp only [Dense.dotPrefix, Dense.dotTerm, xa, xb, d₃]
    rw [finRangeDot k t ht]
    exact hpartial _
  obtain ⟨s₄,e₄,dot⟩ := Dense.dotBlock_correct P s₃ k e₃.safe_end (xa ▸ by omega)
    (xb ▸ by omega) (by simp [s₃,len₂]) hterm hsum
  let t := s₄.putData 6 (s₄.data 20)
  have e₅ : Block.Eval (Memory.AllData P) (.op (.copy 6 20)) s₄ 1 t :=
    Block.Eval.op_copy _ _ _ e₄.safe_end (e₄.safe_end.putData _ (e₄.safe_end 20))
  have cost₁ : s₀.index 30*(4*s₀.index 42+5)+4*s₀.index 43+5 = i.val*(4*k+5)+5 := by
    simp [s₀,h30,h42]
  rw [cost₁] at e₁
  rw [c₁,len₁,z₁] at e₂
  have boundI := Nat.mul_le_mul_right (4*k+5) i.isLt.le
  have boundJ := Nat.mul_le_mul_right (4*k+5) j.isLt.le
  refine ⟨t,_,?_,e₀.seq (e₁.seq (e₂.seq (e₃.seq (e₄.seq e₅)))),?_,?_,?_⟩
  · unfold uniformRowDotCost
    rw [Nat.add_mul]
    omega
  · rw [show t.data 6 = s₄.data 20 from by simp [t], dot.sum]
    simp only [Dense.dotPrefix, Dense.dotTerm, xa, xb, d₃, Matrix.mul_apply, Matrix.transpose_apply,
      uniformRect]
    exact (Fin.sum_univ_eq_sum_range _ k).symm
  · intro q h6 h23
    calc
      t.data q = s₄.data q := Memory.putData_ne _ h6 _
      _ = s₃.data q := dot.dataFrame q (Or.inr h23)
      _ = s.data q := congrFun d₃ q
  · intro q hq
    have ha' : q≠21 ∧ q≠38 ∧ q≠39 ∧ q≠23 ∧ q≠20 ∧ q≠43 := by
      unfold RowDotIndexScratch at hq; omega
    have hend := dot.indexFrame q (by unfold RowDotIndexScratch at hq; omega)
    change s₄.index q = _
    rw [hend]
    change Function.update s₂.index 23 _ q = _
    rw [Function.update_of_ne ha'.2.2.2.1, f₂ q ha'.1 ha'.2.1 ha'.2.2.1]
    exact i₁ q ha'.2.2.2.2.1 ha'.2.1 ha'.2.2.1 ha'.2.2.2.2.2

/-- Materialize A Bᵀ for two row-contiguous matrices of any runtime dimensions. -/
def uniformRowProductBlock : Block := uniformTableBlock uniformRowDotCell

/-- Unit-cost runtime, memory frame, exact result, and arbitrary scalar-value
invariant for the fixed rectangular matrix multiplication code. The source
arrays may coincide, as in the construction of a Gram matrix. -/
theorem uniformRowProductBlock_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (s : Memory K) (m p k a b out : ℕ)
    (hm : s.index 31 = m) (hp : s.index 33 = p) (ho : s.index 35 = out)
    (hA : s.index 40 = a) (hB : s.index 41 = b) (hK : s.index 42 = k)
    (ha : 23 < a) (hb : 23 < b) (hout : 23 < out)
    (hdisA : a + m*k ≤ out ∨ out + m*p ≤ a)
    (hdisB : b + p*k ≤ out ∨ out + m*p ≤ b)
    (hs : s.AllData P)
    (hpartial : ∀ (i : Fin m) (j : Fin p) (u : Finset (Fin k)),
      P (∑ v ∈ u, uniformRect m k a s i v * uniformRect p k b s j v)) :
    ∃ t cost, cost ≤ uniformTableTime m p (uniformRowDotCost m p k) ∧
      Block.Eval (Memory.AllData P) uniformRowProductBlock s cost t ∧
      uniformRect m p out t = uniformRect m k a s * (uniformRect p k b s)ᵀ ∧
      (∀ q, 23 < q → (q < out ∨ out + m*p ≤ q) → t.data q = s.data q) ∧
      ∀ q, ¬TableScratch q → ¬RowDotIndexScratch q → t.index q = s.index q := by
  let keep := fun q => ¬ TableScratch q ∧ ¬ RowDotIndexScratch q
  let A := uniformRect m k a s
  let B := uniformRect p k b s
  have callback : TableCallbackSpec uniformRowDotCell P (fun q => 23<q) keep s m p out (A*Bᵀ)
      (uniformRowDotCost m p k) := by
    intro i j z hz hrow hcol hidx hmem
    have ea : uniformRect m k a z = A := by
      ext u v
      have off := rectOffset_lt u v
      exact hmem _ (by omega) (by rcases hdisA with H|H <;> omega)
    have eb : uniformRect p k b z = B := by
      ext u v
      have off := rectOffset_lt u v
      exact hmem _ (by omega) (by rcases hdisB with H|H <;> omega)
    obtain ⟨t,c,hc,he,hv,hf,hi⟩ := uniformRowDotCell_spec P z m p k a b i j hz hrow hcol
      ((hidx 40 (Or.inr (by decide : ¬ TableScratch 40 ∧ ¬ RowDotIndexScratch 40))).trans hA)
      ((hidx 41 (Or.inr (by decide : ¬ TableScratch 41 ∧ ¬ RowDotIndexScratch 41))).trans hB)
      ((hidx 42 (Or.inr (by decide : ¬ TableScratch 42 ∧ ¬ RowDotIndexScratch 42))).trans hK)
      ha hb (by rw [ea,eb]; exact hpartial i j)
    rw [ea,eb] at hv
    refine ⟨t,c,hc,he,hv,fun q hq => hf q (by omega) hq,?_⟩
    intro q hq
    apply hi q
    rcases hq with hq | hq
    · unfold TableControl at hq; unfold RowDotIndexScratch; omega
    · exact hq.2
  obtain ⟨t,c,hc,he,hv,hf,hi⟩ := uniformTableBlock_spec uniformRowDotCell P (fun q => 23 < q)
    keep s m p out (A*Bᵀ) _ callback (fun _ h => h.1) (fun i j => by omega) hm hp ho hs
  exact ⟨t,c,hc,he,hv,hf,fun q h₁ h₂ => hi q (Or.inr ⟨h₁,h₂⟩)⟩

end Geometry
end LinearProgramming
end Optimization
end OAI
