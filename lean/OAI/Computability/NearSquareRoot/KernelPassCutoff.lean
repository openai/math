import OAI.Computability.NearSquareRoot.KernelPassCertificate

/-! # Finite width bound for direct evaluation of normalized templates

It suffices to check the rational matrices of the program on inputs up to a
width computed from its syntax and row dimensions. This uses no arithmetic
on weighted-automaton transition matrices in the decision procedure. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

open KernelAutomatonEquiv Matrix Finset

/-- Common dimension bound for all row-pair series of one program. -/
def Plan.stateBound {A i o : ℕ} : Plan A i o → ℕ
  | .mix _ | .xor _ | .child _ => 1
  | .scale q _ _ => 2^q
  | @Plan.seq _ _ j _ p q => j*(p.stateBound*q.stateBound) + 1
  | .parallel p q => max 1 (max p.stateBound q.stateBound)

theorem Plan.series_dim_le {A i o : ℕ} (p : Plan A i o) (b : Fin o) (a : Fin i) :
    (p.series b a).dim ≤ p.stateBound := by
  induction p with
  | mix c => exact le_rfl
  | xor g => exact le_rfl
  | child d => exact le_rfl
  | scale n test table => exact le_rfl
  | @seq i j o p q ihp ihq =>
    rw [series_seq_dim]
    change _ ≤ j*(p.stateBound*q.stateBound)+1
    apply Nat.add_le_add_right
    calc
      _ ≤ ∑ _ : Fin j, p.stateBound*q.stateBound := sum_le_sum fun c _ =>
        Nat.mul_le_mul (ihp b c) (ihq c a)
      _ = _ := by simp
  | @parallel i j o u p q ihp ihq =>
    refine Fin.addCases (fun l => ?_) (fun r => ?_) b <;>
      refine Fin.addCases (fun k => ?_) (fun k => ?_) a
    · simp only [series, Fin.addCases_left, stateBound]
      exact (ihp _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
    · simp only [series, Fin.addCases_left, Fin.addCases_right, stateBound]
      exact le_max_left _ _
    · simp only [series, Fin.addCases_left, Fin.addCases_right, stateBound]
      exact le_max_left _ _
    · simp only [series, Fin.addCases_right, stateBound]
      exact (ihq _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

private theorem targetSeries_dim {A W : ℕ} (b a : Fin W) :
    (targetSeries A b a).dim = 1 := by
  unfold targetSeries
  split <;> rfl

theorem correct_iff_bounded {A W : ℕ} (p : Plan A W W) :
    Correct p ↔ ∀ h ≤ p.stateBound, p.eval h = target A W h := by
  refine ⟨fun h j _ => h j, fun hc => p.certified_iff.mp ?_⟩
  simp only [Plan.certified, decide_eq_true_eq]
  intro b a
  change equalBelow ((p.series b a).dim + (targetSeries A b a).dim)
    (p.series b a).eval (targetSeries A b a).eval = true
  rw [equalBelow_iff, targetSeries_dim]
  intro w hw
  let y : Addr A w.length := fun c => (w.get c).1
  let x : Addr A w.length := fun c => (w.get c).2
  have rebuild : Series.columns y x = w := by simp [Series.columns, y, x]
  have bh := p.series_dim_le b a
  rw [← rebuild, Plan.eval_series, eval_targetSeries, hc w.length (by omega)]

end KernelPass

end NearSquareRoot
end Computability
end OAI
