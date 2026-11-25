import OAI.Optimization.LinearProgramming.PrimalDual.OracleRAM
import OAI.Optimization.LinearProgramming.PrimalDual.Layout

/-! Direct transcript theorem for the two-call reduction. Both witnesses, both
multipliers, the normalization divisor and the optimal value are read from the
particular halted traces; there is no existential choice of an optimizer. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM Matrix

theorem raw_joint_optimum {m d : Nat} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c : Fin d → ℚ) (s : State ℚ)
    (h : Feasible (finJointMatrix A b c) (finJointRhs b c) (readVector s 0 (d+m))) :
    let x := readVector s 0 d
    let y := readVector s d m
    Feasible A b x ∧ 0 ≤ y ∧ Aᵀ *ᵥ y = c ∧ b ⬝ᵥ y = c ⬝ᵥ x ∧
      (∀ z, Feasible A b z → c ⬝ᵥ z ≤ c ⬝ᵥ x) ∧
      (∀ w, 0 ≤ w → Aᵀ *ᵥ w = c → b ⬝ᵥ y ≤ b ⬝ᵥ w) := by
  let v := readVector s 0 (d+m) ∘ finSumFinEquiv
  have hv : jointMatrix A b c *ᵥ v ≤ jointRhs b c := by
    change (jointMatrix A b c).submatrix _ _ *ᵥ _ ≤ _ at h
    rw [submatrix_mulVec_equiv] at h
    exact fun i => by simpa [v,finJointRhs] using h (jointRowEquiv m d i)
  obtain ⟨hx,hy,hdual,hgap⟩ := (joint_feasible_iff A b c v).1 hv
  have ex : v ∘ Sum.inl = readVector s 0 d := rfl
  have ey : v ∘ Sum.inr = readVector s d m := by funext i; simp [v,readVector]
  rw [ex] at hx hgap; rw [ey] at hy hdual hgap
  have heq := le_antisymm hgap (weak_duality hx hy hdual)
  exact ⟨hx,hy,hdual,heq,fun z hz => (weak_duality hz hy hdual).trans_eq heq,
    fun w hw hwt => heq.le.trans (weak_duality hx hw hwt)⟩

theorem raw_joint_ray {m d : Nat} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c x₀ : Fin d → ℚ) (hx₀ : Feasible A b x₀) (s : State ℚ)
    (hs : Certificate (finJointMatrix A b c) (finJointRhs b c)
      (readVector s 0 (m+(m+(d+(d+1)))))) :
    let f := fun j : Fin d => s.data (2*m+j.val) - s.data (2*m+d+j.val)
    let den := c ⬝ᵥ f
    den < 0 ∧ A *ᵥ (fun j => f j / den) ≤ 0 ∧ c ⬝ᵥ (fun j => f j / den) = 1 := by
  let y := readVector s 0 (m+(m+(d+(d+1))))
  let u := y ∘ jointRowEquiv m d
  rcases hs with ⟨hy,hz,hb,_⟩
  have nonneg : 0 ≤ u := fun i => hy _
  have ann : (jointMatrix A b c)ᵀ *ᵥ u = 0 := by
    change (jointMatrix A b c)ᵀ.submatrix finSumFinEquiv.symm (jointRowEquiv m d).symm *ᵥ y = 0 at hz
    rw [submatrix_mulVec_equiv] at hz
    funext j; simpa [u] using congrFun hz (finSumFinEquiv j)
  have neg : jointRhs b c ⬝ᵥ u < 0 := by simpa [finJointRhs,u,y] using hb
  obtain ⟨hdual,hprimal,hneg⟩ := joint_certificate A b c u ann neg
  have hl := fun i => nonneg (.inl i)
  have hm := fun i => nonneg (.inr (.inl i))
  have ht := nonneg (.inr (.inr (.inr (.inr ()))))
  have den := (negative_ray_denominator hx₀ hl hm ht hdual hprimal hneg).2
  have hr := ray_of_multipliers hx₀ hl hm ht hdual hprimal hneg
  have ef : equationMultiplier u = fun j : Fin d => s.data (2*m+j.val)-s.data (2*m+d+j.val) := by
    funext j; simp [equationMultiplier,u,y,readVector,two_mul]
  rw [ef] at den hr
  exact ⟨den,by simpa only [div_eq_inv_mul,Pi.smul_def,smul_eq_mul] using hr⟩

/-- Corollary 1.2 as a transcript of the concrete fixed RAM that solves feasibility.
The first certificate or point comes from its first run. Both other outcomes come
from its second run on the actual dense joint matrix; the raw negative multiplier
determines the specific improving ray. -/
theorem twoCall_trace (p : Program) (C E : Nat) (h : ValidProgram p C E)
    (m d : Nat) (hm : 0 < m) (hd : 0 < d) (A : Matrix (Fin m) (Fin d) ℚ)
    (b : Fin m → ℚ) (c : Fin d → ℚ) :
    ∃ (k : Nat) (t : Fin (k+1) → State ℚ),
      Trace p (start [m,d] (lpInput A b)) k t ∧ k ≤ polyBound C E (m+d) ∧
      let first := t (Fin.last k)
      (first.output = some 1 ∧ Certificate A b (readVector first 0 m)) ∨
      (first.output = some 0 ∧ Feasible A b (readVector first 0 d) ∧
        ∃ (l : Nat) (u : Fin (l+1) → State ℚ),
          Trace p (start [m+(m+(d+(d+1))),d+m] (lpInput (finJointMatrix A b c) (finJointRhs b c))) l u ∧
          l ≤ polyBound C E ((m+(m+(d+(d+1))))+(d+m)) ∧
          let second := u (Fin.last l)
          (second.output = some 0 ∧
            let x := readVector second 0 d
            let y := readVector second d m
            Feasible A b x ∧ 0 ≤ y ∧ Aᵀ *ᵥ y = c ∧ b ⬝ᵥ y = c ⬝ᵥ x ∧
              (∀ z, Feasible A b z → c ⬝ᵥ z ≤ c ⬝ᵥ x) ∧
              (∀ w, 0 ≤ w → Aᵀ *ᵥ w = c → b ⬝ᵥ y ≤ b ⬝ᵥ w)) ∨
          (second.output = some 1 ∧
            let f := fun j : Fin d => second.data (2*m+j.val)-second.data (2*m+d+j.val)
            let den := c ⬝ᵥ f
            den < 0 ∧ A *ᵥ (fun j => f j / den) ≤ 0 ∧ c ⬝ᵥ (fun j => f j / den) = 1)) := by
  obtain ⟨k,t,ht,hk,hout⟩ := h m d hm hd A b
  refine ⟨k,t,ht,hk,?_⟩
  rcases hout with ⟨tag,hx⟩ | ⟨tag,hy⟩
  · right; refine ⟨tag,hx,?_⟩
    obtain ⟨l,u,hu,hl,hout'⟩ := h _ _ (by omega) (by omega) (finJointMatrix A b c) (finJointRhs b c)
    refine ⟨l,u,hu,hl,?_⟩
    rcases hout' with ⟨tag',hz⟩ | ⟨tag',hs⟩
    · exact Or.inl ⟨tag',raw_joint_optimum A b c _ hz⟩
    · exact Or.inr ⟨tag',raw_joint_ray A b c _ hx _ hs⟩
  · exact Or.inl ⟨tag,hy⟩

end PrimalDual
end LinearProgramming
end Optimization
end OAI
