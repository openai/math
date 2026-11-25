import OAI.Optimization.LinearProgramming.PriceGame.ChargingTransferScores
import OAI.Optimization.LinearProgramming.PriceGame.ChargingSampling

/-! The exact active local/deeper decomposition of the expert score mass. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging
open scoped BigOperators

/-- Identify a tuple of current vertices with the depth-zero descendants. -/
def localTuple {V : Type*} {arity : ℕ} (x : Fin arity → V) : Fin arity → Descendant V 0 :=
  fun j => (x j, Fin.elim0)

private def localTupleEquiv (V : Type*) (arity : ℕ) :
    (Fin arity → V) ≃ (Fin arity → Descendant V 0) where
  toFun := localTuple
  invFun := fun x j => (x j).1
  left_inv _ := rfl
  right_inv x := by
    funext j
    change ((x j).1, (Fin.elim0 : Fin 0 → Bool)) = x j
    exact Prod.ext (by rfl) (Subsingleton.elim _ _)

/-- A tuple containing even one inactive vertex carries zero weight. -/
theorem slots_masked_zero {V : Type*} [DecidableEq V] (S : Finset V) (m : V → ℚ)
    {arity : ℕ} (x : Fin arity → V) (j : Fin arity) (hj : x j ∉ S) :
    slots arity (maskedMass S m) x = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ j) (by simp [maskedMass, hj])

/-- Summing the masked tuple weights is exactly summing over tuples of active
vertices; no positive mass is lost by replacing the type of slots by S. -/
theorem sum_masked_slots {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V)
    (m : V → ℚ) (arity : ℕ) (f : (Fin arity → V) → ℚ) :
    ∑ x, slots arity (maskedMass S m) x * f x =
      ∑ x : Fin arity → S, slots arity (fun i : S => m i) x * f (fun j => (x j : V)) := by
  classical
  let A := Fintype.piFinset (fun _ : Fin arity => S)
  calc
    _ = ∑ x ∈ A, slots arity (maskedMass S m) x * f x := by
      symm; apply Finset.sum_subset (Finset.subset_univ A)
      intro x _ hx
      have hn : ¬ ∀ j, x j ∈ S := fun ha => hx (Fintype.mem_piFinset.mpr ha)
      obtain ⟨j,hj⟩ := not_forall.mp hn
      rw [slots_masked_zero S m x j hj, zero_mul]
    _ = _ := by
      symm; apply Finset.sum_bij (fun x _ j => (x j : V))
      · intro x _; exact Fintype.mem_piFinset.mpr (fun j => (x j).property)
      · intro x _ y _ h; funext j; exact Subtype.ext (congrFun h j)
      · intro x hx
        refine ⟨fun j => ⟨x j, (Fintype.mem_piFinset.mp hx) j⟩, Finset.mem_univ _, rfl⟩
      · intro x _; simp [slots, maskedMass]

private theorem sum_local_pivots {V : Type*} [Fintype V] (m : V → ℚ) (arity : ℕ)
    (s : (Fin arity → Descendant V 0) → PivotChoice V 0 → ℚ) :
    ∑ x, ∑ ρ, expertWeight m arity 0 x ρ * s x ρ =
      (1 / 4 : ℚ) * ∑ x : Fin arity → V, slots arity m x * s (localTuple x) none := by
  classical
  let F := fun x : Fin arity → Descendant V 0 => ∑ ρ, expertWeight m arity 0 x ρ * s x ρ
  calc
    _ = ∑ x : Fin arity → V, F (localTuple x) := ((localTupleEquiv V arity).sum_comp F).symm
    _ = _ := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _
      dsimp only [F]
      rw [Fintype.sum_option, Fintype.sum_sigma]
      simp [expertWeight, pivotMass, spread, slots, localTuple]
      ring

/-- Scores on the active tuples at the state's own pivot. -/
def activeLocalScores {V : Type*} {arity levels : ℕ} (S : Finset V)
    (s : ScoreFamily V arity (levels + 1)) (x : Fin arity → S) : ℚ :=
  s 0 (localTuple (fun j => (x j : V))) none

/-- Splitting the total into local and deeper scores, valid also at zero mass. -/
theorem scoreMass_split_active_raw {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (m : V → ℚ) {arity levels : ℕ} (s : ScoreFamily V arity (levels+1)) :
    scoreMass (maskedMass S m) s =
      (1 / 4 : ℚ) * (∑ x : Fin arity → S, slots arity (fun i : S => m i) x *
        activeLocalScores S s x) + deeperScoreMass (maskedMass S m) s := by
  unfold scoreMass
  rw [Fin.sum_univ_succ]
  congr 1
  exact (sum_local_pivots (maskedMass S m) arity (s 0)).trans
    (congrArg (fun z : ℚ => (1/4 : ℚ) * z)
      (sum_masked_slots S m arity (fun x => s 0 (localTuple x) none)))

private theorem normalized_slots {V : Type*} [Fintype V] (m : V → ℚ) (hm : ∀ i, 0 ≤ m i)
    (arity : ℕ) (x : Fin arity → V) :
    slots arity m x = (∑ i, m i)^arity * drawWeight (fun i => m i / ∑ j, m j) x := by
  classical
  by_cases hM : ∑ i, m i = 0
  · have hz (i : V) : m i = 0 := by
      have h := Finset.single_le_sum (f := m) (fun j _ => hm j) (Finset.mem_univ i)
      exact le_antisymm (h.trans hM.le) (hm i)
    cases arity <;> simp [slots, drawWeight, hz]
  · simp only [slots, drawWeight, Finset.prod_div_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    field_simp

/-- The score mass equals the fixed local sampling weights used in Section 6
plus the deeper experts' mass. This identity covers empty active sets as well. -/
theorem scoreMass_split_active {V : Type*} [Fintype V] [DecidableEq V]
    (S : Finset V) (m : V → ℚ) (hm : ∀ i, 0 ≤ m i) {arity levels : ℕ}
    (s : ScoreFamily V arity (levels+1)) :
    let M := ∑ i : S, m i
    scoreMass (maskedMass S m) s =
      (∑ x : Fin arity → S, (M ^ arity / 4) * drawWeight (fun i : S => m i / M) x *
        activeLocalScores S s x) + deeperScoreMass (maskedMass S m) s := by
  dsimp only
  rw [scoreMass_split_active_raw, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [normalized_slots (fun i : S => m i) (fun i => hm i) arity x]
  ring



/-- One finite type for all of the parent's deeper experts. -/
abbrev DeeperSkeleton (V : Type*) (arity levels : ℕ) :=
  Σ k : Fin levels, (Fin arity → Descendant V (k.val+1)) × PivotChoice V (k.val+1)

def deeperWeight {V : Type*} {arity levels : ℕ} (m : V → ℚ) (e : DeeperSkeleton V arity levels) : ℚ :=
  expertWeight m arity (e.1.val+1) e.2.1 e.2.2

def deeperScores {V : Type*} {arity levels : ℕ} (s : ScoreFamily V arity (levels+1))
    (e : DeeperSkeleton V arity levels) : ℚ := s e.1.succ e.2.1 e.2.2

def childDeeperWeight {V : Type*} [DecidableEq V] {arity levels : ℕ} (w : V × Bool → ℚ)
    (pivot : Option V) (e : DeeperSkeleton V arity levels) : ℚ :=
  reindexedWeight w pivot e.2.1 e.2.2

theorem deeperScoreMass_eq_sum {V : Type*} [Fintype V] {arity levels : ℕ} (m : V → ℚ)
    (s : ScoreFamily V arity (levels+1)) :
    deeperScoreMass m s = ∑ e, deeperWeight m e * deeperScores s e := by
  simp [deeperScoreMass, deeperWeight, deeperScores, Fintype.sum_sigma, Fintype.sum_prod_type]

theorem deeperWeight_nonneg {V : Type*} {arity levels : ℕ} (m : V → ℚ) (hm : ∀ i, 0 ≤ m i)
    (e : DeeperSkeleton V arity levels) : 0 ≤ deeperWeight m e :=
  expertWeight_nonneg m hm _ _ _ _

theorem sum_deeperWeight_le_one {V : Type*} [Fintype V] (m : V → ℚ) (hm : ∀ i, 0 ≤ m i)
    (hM : ∑ i, m i ≤ 1) (arity levels : ℕ) :
    ∑ e : DeeperSkeleton V arity levels, deeperWeight m e ≤ 1 := by
  have h := deeperScoreMass_le m hm (arity := arity) (levels := levels) (fun _ _ _ => 1)
    (fun _ _ _ => zero_le_one)
  rw [deeperScoreMass_eq_sum] at h
  simp only [deeperScores, mul_one, scoreMass] at h
  exact h.trans (sum_expertWeight_le_one m hm hM arity (levels+1))

theorem sum_childDeeperWeight_scores {V : Type*} [DecidableEq V] [Fintype V] {arity levels : ℕ}
    (w : V × Bool → ℚ) (pivot : Option V) (s : ScoreFamily V arity (levels+1)) :
    ∑ e, childDeeperWeight w pivot e * deeperScores s e = scoreMass w (childScores pivot s) := by
  simpa only [childDeeperWeight, deeperScores, Fintype.sum_sigma, Fintype.sum_prod_type] using
    sum_reindexedWeight_all w pivot s

/-- Exact total local mass, including zero active mass or arity zero. -/
theorem sum_local_samplingWeight {V : Type*} [Fintype V] (m : V → ℚ) (hm : ∀ i, 0 ≤ m i) (d : ℕ) :
    let M := ∑ i, m i
    ∑ x : Fin d → V, (M ^ d / 4) * drawWeight (fun i => m i / M) x = M ^ d / 4 := by
  dsimp only
  calc
    _ = (1 / 4 : ℚ) * ∑ x : Fin d → V, slots d m x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [normalized_slots m hm d x]
      ring
    _ = _ := by rw [sum_slots]; ring

theorem sum_local_samplingWeight_le_one {V : Type*} [Fintype V] (m : V → ℚ) (hm : ∀ i, 0 ≤ m i)
    (hM : ∑ i, m i ≤ 1) (d : ℕ) :
    let M := ∑ i, m i
    ∑ x : Fin d → V, (M ^ d / 4) * drawWeight (fun i => m i / M) x ≤ 1 := by
  dsimp only
  rw [sum_local_samplingWeight m hm d]
  have hp : (∑ i, m i) ^ d ≤ 1 := pow_le_one₀ (Finset.sum_nonneg (fun i _ => hm i)) hM
  linarith

/-- The form of the score-mass split with precisely the two finite index types
used by the trial charging inequality. -/
theorem scoreMass_split_sums {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V)
    (m : V → ℚ) (hm : ∀ i, 0 ≤ m i) {arity levels : ℕ} (s : ScoreFamily V arity (levels+1)) :
    let M := ∑ i : S, m i
    scoreMass (maskedMass S m) s =
      (∑ x : Fin arity → S, (M ^ arity / 4) * drawWeight (fun i : S => m i / M) x *
        activeLocalScores S s x) +
      ∑ e : DeeperSkeleton V arity levels, deeperWeight (maskedMass S m) e * deeperScores s e := by
  rw [scoreMass_split_active S m hm s, deeperScoreMass_eq_sum]

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI
