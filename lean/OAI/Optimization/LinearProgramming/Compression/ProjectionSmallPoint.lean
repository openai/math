import OAI.Optimization.LinearProgramming.Compression.ProjectionCramer
import OAI.Optimization.LinearProgramming.Compression.ProjectionVertex

/-! Small rational witnesses for finite rational systems over ordered fields. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

variable {K : Type*}

open scoped BigOperators Matrix

/-- A nonempty rational polyhedron over any ordered field contains a rational point.
The height bound uses only the number of variables and the maximum row-entry
height, so it applies even when the number of inequalities is exponential. -/
theorem exists_small_rat_feasible
    {K ι κ : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℚ) (b : ι → ℚ) {B : ℕ} (hB : 1 ≤ B)
    (hA : ∀ i j, (A i j).num.natAbs ≤ B ∧ (A i j).den ≤ B)
    (hb : ∀ i, (b i).num.natAbs ≤ B ∧ (b i).den ≤ B)
    (hne : ∃ x : κ → K, (A.map (fun z : ℚ => (z : K))) *ᵥ x ≤ fun i => (b i : K)) :
    ∃ q : κ → ℚ, A *ᵥ q ≤ b ∧ ∀ j,
      (q j).num.natAbs ≤ (Fintype.card κ).factorial *
        (B ^ (Fintype.card κ + 2)) ^ Fintype.card κ ∧
      (q j).den ≤ (Fintype.card κ).factorial *
        (B ^ (Fintype.card κ + 2)) ^ Fintype.card κ := by
  classical
  let A' := A.map (fun z : ℚ => (z : K))
  obtain ⟨p, x, hx, sel, _, hdet, ht⟩ := exists_orthant_tight_submatrix A' _ hne
  let M := (orthantCutRows A p).submatrix sel id
  let r : κ → ℚ := fun j => (sel j).elim b (fun _ => 0)
  have hC : M.map (fun z : ℚ => (z : K)) = (orthantCutRows A' p).submatrix sel id := by
    ext i j
    cases hi : sel i with
    | inl k => simp [M, orthantCutRows, hi, A']
    | inr k =>
      by_cases hj : j = k <;> cases hp : p k <;> simp [M, orthantCutRows, hi, hj, hp]
  have hM : ∀ i j, (M i j).num.natAbs ≤ B ∧ (M i j).den ≤ B := by
    intro i j
    cases hi : sel i with
    | inl k => simpa [M, orthantCutRows, hi] using hA k j
    | inr k =>
      by_cases hj : j = k <;> cases hp : p k <;> simpa [M, orthantCutRows, hi, hj, hp] using hB
  have hr : ∀ i, (r i).num.natAbs ≤ B ∧ (r i).den ≤ B := by
    intro i
    cases hi : sel i with
    | inl k => simpa [r, hi] using hb k
    | inr k => simpa [r, hi] using hB
  have hdetQ : M.det ≠ 0 := by
    intro hz
    apply hdet
    rw [← hC, ← Rat.cast_det, hz, Rat.cast_zero]
  have hMx : (M.map (fun z : ℚ => (z : K))) *ᵥ x = fun j => (r j : K) := by
    rw [hC]
    funext i
    change (orthantCutRows A' p *ᵥ x) (sel i) = (r i : K)
    rw [ht i]
    cases hi : sel i <;> simp [r, hi]
  obtain ⟨q, hq⟩ := exists_small_rat_of_tight_system M r hM hr hdetQ x hMx
  refine ⟨q, ?_, fun j => (hq j).2⟩
  intro i
  have hqx : (fun j => (q j : K)) = x := funext fun j => (hq j).1
  have hqi : ((A *ᵥ q) i : K) ≤ (b i : K) := by
    calc
      ((A *ᵥ q) i : K) = (A' *ᵥ x) i := by
        rw [← hqx]
        change ((∑ j, A i j * q j : ℚ) : K) = ∑ j, (A i j : K) * (q j : K)
        push_cast; rfl
      _ ≤ _ := hx i
  exact_mod_cast hqi

section Pins

variable {K ι κ σ : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Fintype κ] [DecidableEq κ]

private def pinRows (A : Matrix ι κ K) (idx : σ → κ) : Matrix (ι ⊕ (σ × Bool)) κ K :=
  Matrix.of fun row j => row.elim (fun i => A i j) (fun p =>
    if j = idx p.1 then (if p.2 then 1 else -1) else 0)

private def pinBounds (b : ι → K) (g : σ → K) : ι ⊕ (σ × Bool) → K :=
  Sum.elim b fun p => if p.2 then g p.1 else -g p.1

private theorem pinRows_spec (A : Matrix ι κ K) (b : ι → K) (idx : σ → κ)
    (g : σ → K) (x : κ → K) :
    pinRows A idx *ᵥ x ≤ pinBounds b g ↔ A *ᵥ x ≤ b ∧ ∀ i, x (idx i) = g i := by
  have pos (i : σ) : (pinRows A idx *ᵥ x) (.inr (i,true)) = x (idx i) := by
    simp [pinRows, Matrix.mulVec, dotProduct, ite_mul]
  have neg (i : σ) : (pinRows A idx *ᵥ x) (.inr (i,false)) = -x (idx i) := by
    simp [pinRows, Matrix.mulVec, dotProduct, ite_mul]
  constructor
  · intro h
    refine ⟨fun i => h (.inl i), fun i => le_antisymm ?_ ?_⟩
    · simpa only [pos, pinBounds, Sum.elim_inr, ite_true] using h (.inr (i,true))
    · have hneg := h (.inr (i,false))
      change (pinRows A idx *ᵥ x) (.inr (i,false)) ≤ -g i at hneg
      exact neg_le_neg_iff.mp ((neg i) ▸ hneg)
  · rintro ⟨h, fixed⟩ (i | ⟨i,s⟩)
    · exact h i
    · cases s <;> simp [pos, neg, fixed, pinBounds]

/-- The small rational point can be required to extend predetermined rational
coordinates. Each prescribed equality contributes two unit-coordinate rows. -/
theorem exists_small_rat_feasible_with_fixed [Fintype ι] [Fintype σ]
    (A : Matrix ι κ ℚ) (b : ι → ℚ) (idx : σ → κ) (g : σ → ℚ)
    {B : ℕ} (hB : 1 ≤ B)
    (hA : ∀ i j, (A i j).num.natAbs ≤ B ∧ (A i j).den ≤ B)
    (hb : ∀ i, (b i).num.natAbs ≤ B ∧ (b i).den ≤ B)
    (hg : ∀ i, (g i).num.natAbs ≤ B ∧ (g i).den ≤ B)
    (hne : ∃ x : κ → K, (A.map (fun z : ℚ => (z : K))) *ᵥ x ≤ (fun i => (b i : K)) ∧
      ∀ i, x (idx i) = (g i : K)) :
    ∃ q : κ → ℚ, A *ᵥ q ≤ b ∧ (∀ i, q (idx i) = g i) ∧ ∀ j,
      (q j).num.natAbs ≤ (Fintype.card κ).factorial *
        (B ^ (Fintype.card κ + 2)) ^ Fintype.card κ ∧
      (q j).den ≤ (Fintype.card κ).factorial *
        (B ^ (Fintype.card κ + 2)) ^ Fintype.card κ := by
  classical
  let M := pinRows A idx
  let r := pinBounds b g
  have hM : ∀ i j, (M i j).num.natAbs ≤ B ∧ (M i j).den ≤ B := by
    rintro (i | ⟨i,s⟩) j
    · exact hA i j
    · by_cases hj : j = idx i <;> cases s <;> simpa [M, pinRows, hj] using hB
  have hr : ∀ i, (r i).num.natAbs ≤ B ∧ (r i).den ≤ B := by
    rintro (i | ⟨i,s⟩)
    · exact hb i
    · cases s <;> simpa [r, pinBounds] using hg i
  have hcastM : M.map (fun z : ℚ => (z : K)) = pinRows (A.map (fun z : ℚ => (z : K))) idx := by
    ext i j
    rcases i with i | ⟨i,s⟩
    · rfl
    · by_cases hj : j = idx i <;> cases s <;> simp [M, pinRows, hj]
  have hcastR : (fun i => (r i : K)) = pinBounds (fun i => (b i : K)) (fun i => (g i : K)) := by
    funext i
    rcases i with i | ⟨i,s⟩
    · rfl
    · cases s <;> simp [r, pinBounds]
  obtain ⟨x, hx, hfixed⟩ := hne
  have hne' : ∃ y : κ → K, M.map (fun z : ℚ => (z : K)) *ᵥ y ≤ (fun i => (r i : K)) := by
    rw [hcastM, hcastR]
    exact ⟨x, (pinRows_spec _ _ _ _ _).mpr ⟨hx, hfixed⟩⟩
  obtain ⟨q, hq, hheight⟩ := exists_small_rat_feasible M r hB hM hr hne'
  obtain ⟨hineq, hpins⟩ := (pinRows_spec _ _ _ _ _).mp hq
  exact ⟨q, hineq, hpins, hheight⟩

end Pins

end Compression
end LinearProgramming
end Optimization
end OAI
