import OAI.Hierarchy.Models

namespace OAI
/-! # Squarefree coefficient transitions for affine branching programs -/

namespace Hierarchy.ABPFirstCut
open scoped BigOperators
noncomputable section

variable {F : Type*} {V : Type} {τ : V → Type} [Field F] [DecidableEq V] {n : ℕ}

/-- A single incoming row propagates squarefree coefficients indexed by vertex slots. -/
def step (a : ∀ i, τ i) (E : List (Fin n × Affine F (Σ i, τ i)))
    (v : Fin n → Finset V → F) (S : Finset V) : F :=
  (E.map fun e => v e.1 S * e.2.constant +
    ∑ i ∈ S, v e.1 (S.erase i) * e.2.coeff ⟨i, a i⟩).sum

@[simp] theorem step_nil (a : ∀ i, τ i) (v : Fin n → Finset V → F) (S : Finset V) :
    step a [] v S = 0 := rfl

theorem step_cons (a : ∀ i, τ i) (e : Fin n × Affine F (Σ i, τ i))
    (E : List (Fin n × Affine F (Σ i, τ i))) (v : Fin n → Finset V → F) (S : Finset V) :
    step a (e :: E) v S = (v e.1 S * e.2.constant +
      ∑ i ∈ S, v e.1 (S.erase i) * e.2.coeff ⟨i, a i⟩) + step a E v S := by
  simp [step]

/-- Insert slots already consumed by a marked edge on a path. -/
def shift (U : Finset V) (z : Finset V → F) (S : Finset V) : F :=
  if U ⊆ S then z (S \ U) else 0

theorem step_congr (E : List (Fin n × Affine F (Σ i, τ i))) (S : Finset V)
    {a b : ∀ i, τ i} {v z : Fin n → Finset V → F}
    (ha : ∀ i ∈ S, a i = b i) (hv : ∀ t T, T ⊆ S → v t T = z t T) :
    step a E v S = step b E z S := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    rw [step_cons, step_cons, ih, hv _ _ (Finset.Subset.refl _)]
    apply congrArg (fun y : F => (z e.1 S * e.2.constant + y) + step b E z S)
    exact Finset.sum_congr rfl fun i hi => by rw [ha i hi, hv _ _ (Finset.erase_subset ..)]

@[simp] theorem step_zero (a : ∀ i, τ i) (E : List (Fin n × Affine F (Σ i, τ i)))
    (S : Finset V) : step a E (fun _ _ => 0) S = 0 := by
  induction E with
  | nil => rfl
  | cons e E ih => simp [step_cons, ih]

theorem step_eq_zero_of_local (a : ∀ i, τ i) (E : List (Fin n × Affine F (Σ i, τ i)))
    (v : Fin n → Finset V → F) (S : Finset V) (h0 : ∀ t, v t S = 0)
    (h1 : ∀ t i, i ∈ S → v t (S.erase i) = 0) : step a E v S = 0 := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    rw [step_cons, h0, zero_mul, zero_add, ih, add_zero]
    apply Finset.sum_eq_zero
    intro i hi
    rw [h1 _ i hi, zero_mul]

theorem step_add (a : ∀ i, τ i) (E : List (Fin n × Affine F (Σ i, τ i)))
    (v z : Fin n → Finset V → F) (S : Finset V) :
    step a E (fun t T => v t T + z t T) S = step a E v S + step a E z S := by
  induction E with
  | nil => simp
  | cons e E ih =>
    simp only [step_cons, add_mul, Finset.sum_add_distrib, ih]
    ac_rfl

theorem step_const_mul (a : ∀ i, τ i) (E : List (Fin n × Affine F (Σ i, τ i)))
    (c : F) (v : Fin n → Finset V → F) (S : Finset V) :
    step a E (fun t T => c * v t T) S = c * step a E v S := by
  induction E with
  | nil => simp
  | cons e E ih => simp only [step_cons, mul_assoc, ← Finset.mul_sum, ih, mul_add]

theorem step_sum {ι : Type*} (a : ∀ i, τ i) (E : List (Fin n × Affine F (Σ i, τ i)))
    (t : Finset ι) (f : ι → Fin n → Finset V → F) (S : Finset V) :
    step a E (fun p T => ∑ j ∈ t, f j p T) S = ∑ j ∈ t, step a E (f j) S := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj ih => simp only [Finset.sum_insert hj, step_add, ih]

/-- Moving a set of already consumed slots past an affine row leaves coefficients unchanged. -/
theorem step_shift (a : ∀ i, τ i) (E : List (Fin n × Affine F (Σ i, τ i)))
    (U : Finset V) (v : Fin n → Finset V → F) (S : Finset V) :
    step a E (fun t => shift U (v t)) S = shift U (step a E v) S := by
  by_cases h : U ⊆ S
  · have hsum (e : Fin n × Affine F (Σ i, τ i)) :
        (∑ i ∈ S, shift U (v e.1) (S.erase i) * e.2.coeff ⟨i, a i⟩) =
        ∑ i ∈ S \ U, v e.1 ((S \ U).erase i) * e.2.coeff ⟨i, a i⟩ := by
      calc
        _ = ∑ i ∈ S \ U, shift U (v e.1) (S.erase i) * e.2.coeff ⟨i, a i⟩ := by
          symm
          apply Finset.sum_subset Finset.sdiff_subset
          intro i hi hmiss
          have hiU : i ∈ U := by simpa [hi] using hmiss
          have hn : ¬ U ⊆ S.erase i := fun hs => Finset.notMem_erase i S (hs hiU)
          simp [shift, hn]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro i hi
          have hiU := (Finset.mem_sdiff.mp hi).2
          have hs : U ⊆ S.erase i := fun j hj =>
            Finset.mem_erase.mpr ⟨fun hji => hiU (hji ▸ hj), h hj⟩
          have hd : S.erase i \ U = (S \ U).erase i := by
            ext j
            simp only [Finset.mem_sdiff, Finset.mem_erase, and_assoc]
          simp [shift, hs, hd]
    induction E with
    | nil => simp [shift]
    | cons e E ih =>
      rw [show shift U (step a (e :: E) v) S = step a (e :: E) v (S \ U) from ite_eq_left h,
        step_cons, step_cons, hsum e, ih]
      rw [show shift U (v e.1) S = v e.1 (S \ U) from ite_eq_left h,
        show shift U (step a E v) S = step a E v (S \ U) from ite_eq_left h]
  · have hz : step a E (fun t => shift U (v t)) S = step a E (fun _ _ => 0) S := by
      apply step_congr E S (fun _ _ => rfl)
      intro t T hT
      exact ite_eq_right fun hU => h (hU.trans hT)
    rw [hz, step_zero, show shift U (step a E v) S = 0 from ite_eq_right h]

end
end Hierarchy.ABPFirstCut

end OAI
