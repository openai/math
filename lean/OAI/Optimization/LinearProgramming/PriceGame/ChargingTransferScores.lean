import OAI.Optimization.LinearProgramming.PriceGame.ChargingTransfer

/-! Transport a child's induction charge to the parent's complete expert list.
Every transition scores the same global experts even though its selected pivot
and active coordinates can differ. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging
open scoped BigOperators

/-- Scores on skeletons for the successive destinations in the remaining levels. -/
abbrev ScoreFamily (V : Type*) (arity levels : ℕ) :=
  (k : Fin levels) → (Fin arity → Descendant V k.val) → PivotChoice V k.val → ℚ

/-- The sum of weighted scores on all the active skeletons. -/
def scoreMass {V : Type*} [Fintype V] {arity levels : ℕ} (m : V → ℚ)
    (s : ScoreFamily V arity levels) : ℚ :=
  ∑ k, ∑ x, ∑ ρ, expertWeight m arity k.val x ρ * s k x ρ

/-- Exclude the parent's local experts, retaining each deeper score once. -/
def deeperScoreMass {V : Type*} [Fintype V] {arity levels : ℕ} (m : V → ℚ)
    (s : ScoreFamily V arity (levels+1)) : ℚ :=
  ∑ k : Fin levels, ∑ x, ∑ ρ, expertWeight m arity (k.val + 1) x ρ * s k.succ x ρ

/-- Look up the parent's score of an expert described in child coordinates. -/
def childScores {V : Type*} {arity levels : ℕ} (pivot : Option V)
    (s : ScoreFamily V arity (levels+1)) : ScoreFamily (V × Bool) arity levels :=
  fun k x ρ => s k.succ (fun c => joinDescendant (x c)) (joinPivot pivot ρ)

private def descendantEquiv (V : Type*) (k : ℕ) :
    Descendant V (k+1) ≃ Descendant (V × Bool) k where
  toFun := splitDescendant
  invFun := joinDescendant
  left_inv := join_splitDescendant
  right_inv := split_joinDescendant

/-- Exact change of variables in the child's induction charge. -/
theorem sum_reindexedWeight_all {V : Type*} [DecidableEq V] [Fintype V] {arity levels : ℕ}
    (w : V × Bool → ℚ) (pivot : Option V) (s : ScoreFamily V arity (levels+1)) :
    ∑ k : Fin levels, ∑ x, ∑ ρ, reindexedWeight w pivot x ρ * s k.succ x ρ =
      scoreMass w (childScores pivot s) := by
  classical
  unfold scoreMass
  apply Finset.sum_congr rfl; intro k _
  simp_rw [sum_reindexedWeight_mul]
  let e := Equiv.piCongrRight (fun (_ : Fin arity) => descendantEquiv V k.val)
  let F := fun y : Fin arity → Descendant (V × Bool) k.val =>
    ∑ ρ, expertWeight w arity k.val y ρ * childScores pivot s k y ρ
  trans ∑ x, F (e x)
  · apply Finset.sum_congr rfl; intro x _
    change (∑ ξ, expertWeight w arity k.val (fun j => splitDescendant (x j)) ξ *
      s k.succ x (joinPivot pivot ξ)) = ∑ ξ,
      expertWeight w arity k.val (fun j => splitDescendant (x j)) ξ *
        s k.succ (fun c => joinDescendant (splitDescendant (x c))) (joinPivot pivot ξ)
    simp only [join_splitDescendant]
  · exact e.sum_comp F

theorem expertWeight_nonneg {V : Type*} (m : V → ℚ) (hm : ∀ i, 0 ≤ m i) (arity k : ℕ)
    (x : Fin arity → Descendant V k) (ρ : PivotChoice V k) : 0 ≤ expertWeight m arity k x ρ := by
  have hv (v : Descendant V k) : 0 ≤ spread k (m v.1) := mul_nonneg (by positivity) (hm _)
  have hs : 0 ≤ slots arity (fun v : Descendant V k => spread k (m v.1)) x :=
    Finset.prod_nonneg (fun j _ => hv _)
  have hρ : 0 ≤ pivotMass m ρ := by
    cases ρ with
    | none => norm_num [pivotMass]
    | some a =>
      obtain ⟨j,v⟩ := a
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (hm _))
  exact mul_nonneg (mul_nonneg (by positivity) hs) hρ

theorem deeperScoreMass_le {V : Type*} [Fintype V] {arity levels : ℕ} (m : V → ℚ)
    (hm : ∀ i, 0 ≤ m i) (s : ScoreFamily V arity (levels+1))
    (hs : ∀ k x ρ, 0 ≤ s k x ρ) : deeperScoreMass m s ≤ scoreMass m s := by
  unfold scoreMass deeperScoreMass
  rw [Fin.sum_univ_succ]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun ρ _ =>
    mul_nonneg (expertWeight_nonneg m hm arity 0 x ρ) (hs 0 x ρ))

/-- The one-step transfer integrated against arbitrary nonnegative global
scores. Each sampled child may use a different pivot, hence a different
lookup of the same global score family. -/
theorem mixed_childScoreMass_le {V J : Type*} [DecidableEq V] [Fintype V] [Fintype J]
    (p : J → ℚ) (hp : ∀ t, 0 ≤ p t) (hprob : ∑ t, p t = 1)
    (h : Bool) (S : Finset V) (U : J → Finset V) (hU : ∀ t, U t ⊆ S)
    (m : V → ℚ) (hm : ∀ i, 0 ≤ m i) (pivot : J → Option V)
    (hnew : ∀ i, (∑ t, if pivot t = some i then p t else 0) ≤ 32 * maskedMass S m i)
    {arity levels : ℕ} (s : ScoreFamily V arity (levels+1))
    (hs : ∀ k x ρ, 0 ≤ s k x ρ) :
    ∑ t, p t * scoreMass (transitionMass h S (U t) m) (childScores (pivot t) s) ≤
      8 * 16 ^ (arity+1) * deeperScoreMass (maskedMass S m) s := by
  classical
  let w := fun t => transitionMass h S (U t) m
  let c : ℚ := 8 * 16 ^ (arity+1)
  simp_rw [← sum_reindexedWeight_all]
  calc
    _ = ∑ k : Fin levels, ∑ x, ∑ ρ,
        (∑ t, p t * reindexedWeight (w t) (pivot t) x ρ) * s k.succ x ρ := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro x _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro ρ _
      apply Finset.sum_congr rfl; intro t _
      dsimp [w]; ring
    _ ≤ ∑ k : Fin levels, ∑ x, ∑ ρ,
        c * expertWeight (maskedMass S m) arity (k.val+1) x ρ * s k.succ x ρ := by
      apply Finset.sum_le_sum; intro k _
      apply Finset.sum_le_sum; intro x _
      apply Finset.sum_le_sum; intro ρ _
      exact mul_le_mul_of_nonneg_right
        (reindexedWeight_transfer p hp hprob h S U hU m hm pivot hnew x ρ) (hs _ _ _)
    _ = _ := by simp only [deeperScoreMass, Finset.mul_sum, mul_assoc, c]

/-- If each positive-probability child state fails and incurs a unit charge,
the deeper parent experts carry at least 1/C₀ units of score on this call. -/
theorem child_failure_charge {V J : Type*} [DecidableEq V] [Fintype V] [Fintype J]
    (p : J → ℚ) (hp : ∀ t, 0 ≤ p t) (hprob : ∑ t, p t = 1)
    (h : Bool) (S : Finset V) (U : J → Finset V) (hU : ∀ t, U t ⊆ S)
    (m : V → ℚ) (hm : ∀ i, 0 ≤ m i) (pivot : J → Option V)
    (hnew : ∀ i, (∑ t, if pivot t = some i then p t else 0) ≤ 32 * maskedMass S m i)
    {arity levels : ℕ} (s : ScoreFamily V arity (levels+1))
    (hs : ∀ k x ρ, 0 ≤ s k x ρ)
    (hfail : ∀ t, 0 < p t → 1 ≤ scoreMass (transitionMass h S (U t) m) (childScores (pivot t) s)) :
    1 / (8 * 16 ^ (arity + 1)) ≤ deeperScoreMass (maskedMass S m) s := by
  apply (div_le_iff₀ (by positivity : (0:ℚ) < 8 * 16 ^ (arity+1))).mpr
  rw [mul_comm]
  apply le_trans _ (mixed_childScoreMass_le p hp hprob h S U hU m hm pivot hnew s hs)
  rw [← hprob]
  apply Finset.sum_le_sum
  intro t _
  rcases (hp t).eq_or_lt with ht | ht
  · simp [← ht]
  · simpa using mul_le_mul_of_nonneg_left (hfail t ht) (hp t)


/-- Relative skeletons with positive-weight pivot types, irrespective of their
chosen representative in the algorithm's full expert list. -/
abbrev SelectedSkeleton (V : Type*) (arity levels : ℕ) :=
  Σ k : Fin levels, (Fin arity → Descendant V k.val) × PivotChoice V k.val

/-- Push the fixed skeleton weights onto the actual expert identifiers.
All unselected identifiers automatically have zero weight. -/
def selectedWeight {V E : Type*} [Fintype V] [DecidableEq E]
    {arity levels : ℕ} (m : V → ℚ) (select : SelectedSkeleton V arity levels → E) (e : E) : ℚ :=
  ∑ a, if select a = e then expertWeight m arity a.1.val a.2.1 a.2.2 else 0

theorem selectedWeight_nonneg {V E : Type*} [Fintype V] [DecidableEq E]
    {arity levels : ℕ} (m : V → ℚ) (hm : ∀ i, 0 ≤ m i)
    (select : SelectedSkeleton V arity levels → E) (e : E) : 0 ≤ selectedWeight m select e := by
  apply Finset.sum_nonneg; intro a _
  split
  · exact expertWeight_nonneg m hm _ _ _ _
  · exact le_rfl

/-- Exact equality between charge on selected expert identifiers and the
native charge on the relative skeletons. This requires no injectivity
assumption on the identifier map. -/
theorem selectedWeight_scores {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {arity levels : ℕ} (m : V → ℚ) (select : SelectedSkeleton V arity levels → E)
    (s : E → ℚ) : ∑ e, selectedWeight m select e * s e =
      scoreMass m (fun k x ρ => s (select ⟨k, x, ρ⟩)) := by
  classical
  unfold selectedWeight scoreMass
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Fintype.sum_sigma,
    Fintype.sum_prod_type]

theorem sum_selectedWeight_le_one {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    {arity levels : ℕ} (m : V → ℚ) (hm : ∀ i, 0 ≤ m i) (hmass : ∑ i, m i ≤ 1)
    (select : SelectedSkeleton V arity levels → E) : ∑ e, selectedWeight m select e ≤ 1 := by
  have h := selectedWeight_scores m select (fun _ => 1)
  simp only [mul_one, scoreMass] at h
  rw [h]
  exact sum_expertWeight_le_one m hm hmass arity levels


/-- The same selected global expert identifier, expressed in child coordinates. -/
def childSelection {V E : Type*} {arity levels : ℕ} (pivot : Option V)
    (select : SelectedSkeleton V arity (levels+1) → E) (a : SelectedSkeleton (V × Bool) arity levels) : E :=
  select ⟨a.1.succ, (fun c => joinDescendant (a.2.1 c)), joinPivot pivot a.2.2⟩

private theorem selectedWeight_occupancy {V E : Type*} [Fintype V] [DecidableEq E]
    {arity levels : ℕ} (m : V → ℚ) (select : SelectedSkeleton V arity levels → E) (e : E) :
    selectedWeight m select e = scoreMass m (fun k x ρ => if select ⟨k, x, ρ⟩ = e then 1 else 0) := by
  classical
  simp [selectedWeight, scoreMass, Fintype.sum_sigma, Fintype.sum_prod_type, mul_ite]

/-- Transfer on the actual list of expert identifiers, including unselected entries.
This also handles two skeletons that happen to choose the same identifier. -/
theorem selectedWeight_transfer {V J E : Type*} [DecidableEq V] [Fintype V] [Fintype J]
    [DecidableEq E] (p : J → ℚ) (hp : ∀ t, 0 ≤ p t) (hprob : ∑ t, p t = 1)
    (h : Bool) (S : Finset V) (U : J → Finset V) (hU : ∀ t, U t ⊆ S)
    (m : V → ℚ) (hm : ∀ i, 0 ≤ m i) (pivot : J → Option V)
    (hnew : ∀ i, (∑ t, if pivot t = some i then p t else 0) ≤ 32 * maskedMass S m i)
    {arity levels : ℕ} (select : SelectedSkeleton V arity (levels+1) → E) (e : E) :
    ∑ t, p t * selectedWeight (transitionMass h S (U t) m) (childSelection (pivot t) select) e ≤
      8 * 16 ^ (arity+1) * selectedWeight (maskedMass S m) select e := by
  let s : ScoreFamily V arity (levels+1) := fun k x ρ => if select ⟨k,x,ρ⟩ = e then 1 else 0
  have hs (k) (x) (ρ) : 0 ≤ s k x ρ := by unfold s; split <;> norm_num
  calc
    _ = ∑ t, p t * scoreMass (transitionMass h S (U t) m) (childScores (pivot t) s) := by
      apply Finset.sum_congr rfl; intro t _
      rw [selectedWeight_occupancy]
      rfl
    _ ≤ 8 * 16 ^ (arity+1) * deeperScoreMass (maskedMass S m) s :=
      mixed_childScoreMass_le p hp hprob h S U hU m hm pivot hnew s hs
    _ ≤ 8 * 16 ^ (arity+1) * scoreMass (maskedMass S m) s :=
      mul_le_mul_of_nonneg_left (deeperScoreMass_le _ (maskedMass_nonneg S m hm) s hs) (by positivity)
    _ = _ := by rw [selectedWeight_occupancy]

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI
