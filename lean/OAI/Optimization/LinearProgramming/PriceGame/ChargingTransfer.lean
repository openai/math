import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import OAI.Optimization.LinearProgramming.PriceGame.StatesMass

/-! The subprobability on expert skeletons and its change under a single
transition (Section 6). Inactive vertices have mass zero. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Charging
open scoped BigOperators

/-- A descendant after `n` duplications records its ancestor and the successive signs. -/
abbrev Descendant (V : Type*) (n : ℕ) := V × (Fin n → Bool)

/-- Uniform splitting between the two copies at every level. -/
def spread (n : ℕ) (w : ℚ) : ℚ := (1 / 2 : ℚ) ^ n * w

private theorem spread_succ (n : ℕ) (w : ℚ) :
    spread (n + 1) w = (1 / 2 : ℚ) * spread n w := by
  simp only [spread, pow_succ]; ring

theorem sum_descendantMass {V : Type*} [Fintype V] (n : ℕ) (m : V → ℚ) :
    ∑ v : Descendant V n, spread n (m v.1) = ∑ i, m i := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [spread]

/-- Product weight for the ordered slots with repetitions. -/
def slots {V : Type*} (arity : ℕ) (m : V → ℚ) (x : Fin arity → V) : ℚ :=
  ∏ c, m (x c)

theorem sum_slots {V : Type*} [Fintype V] (arity : ℕ) (m : V → ℚ) :
    ∑ x : Fin arity → V, slots arity m x = (∑ i, m i) ^ arity := by
  classical
  simpa [slots] using (Fintype.prod_sum (fun (_ : Fin arity) (v : V) => m v)).symm

private theorem sum_depthWeight (n : ℕ) :
    ∑ j : Fin n, (1 / 2 : ℚ) ^ (j.val + 1) = 1 - (1 / 2 : ℚ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last, ih]
    ring

/-- Among the positive-weight descriptors, `none` is the state's current pivot
and `some (j,v)` is a later pivot. Other preceding descriptors have weight zero. -/
abbrev PivotChoice (V : Type*) (k : ℕ) := Option (Σ j : Fin k, Descendant V j.val)

def pivotMass {V : Type*} (m : V → ℚ) {k : ℕ} : PivotChoice V k → ℚ
  | none => 1 / 2
  | some ⟨j, v⟩ => (1 / 2 : ℚ) ^ (j.val + 2) * spread j.val (m v.1)

theorem sum_pivotMass {V : Type*} [Fintype V] (m : V → ℚ) (k : ℕ) :
    ∑ ρ : PivotChoice V k, pivotMass m ρ =
      1 / 2 + (1 / 2 : ℚ) * (1 - (1 / 2 : ℚ) ^ k) * ∑ i, m i := by
  classical
  rw [Fintype.sum_option, Fintype.sum_sigma]
  simp only [pivotMass]
  simp_rw [← Finset.mul_sum, sum_descendantMass]
  rw [← Finset.sum_mul]
  have h : ∑ j : Fin k, (1 / 2 : ℚ) ^ (j.val + 2) =
      (1 / 2 : ℚ) * (1 - (1 / 2 : ℚ) ^ k) := by
    rw [← sum_depthWeight, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show j.val + 2 = (j.val + 1) + 1 by omega, pow_succ]
    ring
  rw [h]

/-- The weight on one selected expert; `k` is the destination offset. -/
def expertWeight {V : Type*} (m : V → ℚ) (arity k : ℕ)
    (x : Fin arity → Descendant V k) (ρ : PivotChoice V k) : ℚ :=
  (1 / 2 : ℚ) ^ (k + 1) * slots arity (fun v : Descendant V k => spread k (m v.1)) x *
    pivotMass m ρ

theorem sum_expertWeight_le_one {V : Type*} [Fintype V] (m : V → ℚ)
    (hm : ∀ i, 0 ≤ m i) (hM : ∑ i, m i ≤ 1) (arity levels : ℕ) :
    ∑ k : Fin levels, ∑ x : Fin arity → Descendant V k.val,
      ∑ ρ : PivotChoice V k.val, expertWeight m arity k.val x ρ ≤ 1 := by
  classical
  have hM0 : 0 ≤ ∑ i, m i := Finset.sum_nonneg (fun i _ => hm i)
  calc
    _ ≤ ∑ k : Fin levels, (1 / 2 : ℚ) ^ (k.val + 1) := by
      apply Finset.sum_le_sum; intro k _
      simp_rw [expertWeight, ← Finset.mul_sum, sum_pivotMass, ← Finset.sum_mul,
        ← Finset.mul_sum, sum_slots, sum_descendantMass]
      have hP : 1 / 2 + (1 / 2 : ℚ) * (1 - (1 / 2 : ℚ) ^ k.val) * ∑ i, m i ≤ 1 := by
        nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℚ) ≤ 1/2) k.val) hM0]
      have hA : (∑ i, m i) ^ arity ≤ 1 := pow_le_one₀ hM0 hM
      have hn : 0 ≤ (1 / 2 : ℚ) ^ (k.val + 1) := by positivity
      calc
        _ ≤ (1 / 2 : ℚ) ^ (k.val + 1) * (∑ i, m i) ^ arity * 1 :=
          mul_le_mul_of_nonneg_left hP (mul_nonneg hn (pow_nonneg hM0 _))
        _ ≤ (1 / 2 : ℚ) ^ (k.val + 1) := by simpa using mul_le_mul_of_nonneg_left hA hn
    _ ≤ 1 := by rw [sum_depthWeight]; linarith [pow_nonneg (by norm_num : (0 : ℚ) ≤ 1/2) levels]

/-- Where an expert's pivot lies relative to a fixed parent-child step.
For a future pivot only its child's ancestor affects its mass. -/
inductive PivotSite (V : Type*)
  | current
  | otherPast
  | atParent (i : V)
  | later (offset : ℕ) (i : V × Bool)

def parentPivot {V : Type*} (m : V → ℚ) : PivotSite V → ℚ
  | .current => 1 / 2
  | .otherPast => 0
  | .atParent i => m i / 4
  | .later r i => (1 / 2 : ℚ) ^ (r + 3) * spread (r + 1) (m i.1)

def childPivot {V : Type*} [DecidableEq V] (w : V × Bool → ℚ)
    (newPivot : Option V) : PivotSite V → ℚ
  | .current => if newPivot = none then 1 / 2 else 0
  | .otherPast => 0
  | .atParent i => if newPivot = some i then 1 / 2 else 0
  | .later r i => (1 / 2 : ℚ) ^ (r + 2) * spread r (w i)

private theorem childPivot_nonneg {V : Type*} [DecidableEq V] (w : V × Bool → ℚ)
    (hw : ∀ i, 0 ≤ w i) (pivot : Option V) (ρ : PivotSite V) :
    0 ≤ childPivot w pivot ρ := by
  cases ρ <;> simp [childPivot, spread, *] <;> positivity

/-- The signed duplication gives a factor of at most eight in mass; spreading the
child's mass over half as many descendants costs one additional factor of two. -/
theorem spread_le_sixteen (n : ℕ) {u v : ℚ} (h : v ≤ 8 * u) :
    spread n v ≤ 16 * spread (n + 1) u := by
  rw [spread_succ]
  unfold spread
  have h' := mul_le_mul_of_nonneg_left h (pow_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 2) n)
  linarith only [h']

theorem sum_childPivot_le {V J : Type*} [DecidableEq V] [Fintype J]
    (p : J → ℚ) (hp : ∀ t, 0 ≤ p t) (hprob : ∑ t, p t = 1)
    (m : V → ℚ) (hm : ∀ i, 0 ≤ m i) (w : J → V × Bool → ℚ)
    (hw : ∀ t i, w t i ≤ 8 * m i.1)
    (newPivot : J → Option V)
    (hnew : ∀ i, (∑ t, if newPivot t = some i then p t else 0) ≤ 32 * m i)
    (ρ : PivotSite V) :
    ∑ t, p t * childPivot (w t) (newPivot t) ρ ≤ 64 * parentPivot m ρ := by
  classical
  cases ρ with
  | otherPast => simp [parentPivot, childPivot]
  | current =>
    calc
      _ ≤ ∑ t, p t * (1 / 2 : ℚ) := by
        apply Finset.sum_le_sum; intro t _
        apply mul_le_mul_of_nonneg_left _ (hp t)
        simp only [childPivot]; split <;> norm_num
      _ ≤ _ := by rw [← Finset.sum_mul, hprob]; norm_num [parentPivot]
  | atParent i =>
    calc
      _ = (∑ t, if newPivot t = some i then p t else 0) * (1 / 2 : ℚ) := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro t _
        by_cases h : newPivot t = some i <;> simp [h, childPivot]
      _ ≤ _ := by simp only [parentPivot]; linarith [hnew i]
  | later r i =>
    have hv : ∀ t, childPivot (w t) (newPivot t) (.later r i) ≤
        64 * parentPivot m (.later r i) := by
      intro t
      simp only [childPivot, parentPivot]
      have h1 := spread_le_sixteen r (hw t i)
      have h2 := mul_le_mul_of_nonneg_left h1
        (pow_nonneg (by norm_num : (0 : ℚ) ≤ 1 / 2) (r+2))
      have h3 : 0 ≤ (1 / 2 : ℚ) ^ (r + 2) * spread (r + 1) (m i.1) :=
        mul_nonneg (by positivity) (mul_nonneg (by positivity) (hm _))
      rw [pow_succ (1 / 2 : ℚ) (r+2)]
      linarith only [h2, h3]
    calc
      _ ≤ ∑ t, p t * (64 * parentPivot m (.later r i)) := by
        exact Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hv t) (hp t))
      _ = _ := by rw [← Finset.sum_mul, hprob, one_mul]

/-- One-step transfer, including a random pivot or a single inherited pivot.
The child weights may depend on the sampled transition. Each destination
tuple is specified by its ancestor at the child level; its later signs do
not affect its mass. The bound is the paper's C₀ at δ = 1/16. -/
theorem one_step_transfer {V J : Type*} [DecidableEq V] [Fintype J]
    (p : J → ℚ) (hp : ∀ t, 0 ≤ p t) (hprob : ∑ t, p t = 1)
    (m : V → ℚ) (hm : ∀ i, 0 ≤ m i) (w : J → V × Bool → ℚ)
    (hw₀ : ∀ t i, 0 ≤ w t i) (hw : ∀ t i, w t i ≤ 8 * m i.1)
    (newPivot : J → Option V)
    (hnew : ∀ i, (∑ t, if newPivot t = some i then p t else 0) ≤ 32 * m i)
    (arity r : ℕ) (x : Fin arity → V × Bool) (ρ : PivotSite V) :
    ∑ t, p t * ((1 / 2 : ℚ) ^ (r + 1) *
        slots arity (fun i => spread r (w t i)) x * childPivot (w t) (newPivot t) ρ) ≤
      8 * 16 ^ (arity + 1) * ((1 / 2 : ℚ) ^ (r + 2) *
        slots arity (fun i : V × Bool => spread (r + 1) (m i.1)) x * parentPivot m ρ) := by
  classical
  let a := slots arity (fun i : V × Bool => spread (r + 1) (m i.1)) x
  let b := fun t => slots arity (fun i => spread r (w t i)) x
  have ha : 0 ≤ a := Finset.prod_nonneg (fun c _ => mul_nonneg (by positivity) (hm _))
  have hb : ∀ t, b t ≤ 16 ^ arity * a := by
    intro t
    calc
      _ ≤ ∏ c, 16 * spread (r + 1) (m (x c).1) := by
        apply Finset.prod_le_prod₀
        · intro c _; exact mul_nonneg (by positivity) (hw₀ t _)
        · intro c _; exact spread_le_sixteen r (hw t _)
      _ = _ := by simp [a, slots, Finset.prod_mul_distrib]
  let D := (1 / 2 : ℚ) ^ (r + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hP := sum_childPivot_le p hp hprob m hm w hw newPivot hnew ρ
  calc
    _ ≤ ∑ t, (D * (16 ^ arity * a)) * (p t * childPivot (w t) (newPivot t) ρ) := by
      apply Finset.sum_le_sum; intro t _
      calc
        _ ≤ p t * (D * (16 ^ arity * a) * childPivot (w t) (newPivot t) ρ) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hb t) hD) (childPivot_nonneg _ (hw₀ t) _ _)) (hp t)
        _ = _ := by ring
    _ = D * (16 ^ arity * a) * (∑ t, p t * childPivot (w t) (newPivot t) ρ) := by
      rw [Finset.mul_sum]
    _ ≤ D * (16 ^ arity * a) * (64 * parentPivot m ρ) :=
      mul_le_mul_of_nonneg_left hP (mul_nonneg hD (mul_nonneg (by positivity) ha))
    _ = _ := by simp only [a, D, pow_succ]; ring


/-- At the local depth, a tuple/pivot expert carries precisely M^d/4 times
its probability under d independent draws from normalized active mass. -/
theorem local_expertWeight {V : Type*} [Fintype V] (m : V → ℚ) (arity : ℕ)
    (x : Fin arity → Descendant V 0) (hM : ∑ i, m i ≠ 0) :
    expertWeight m arity 0 x none = ((∑ i, m i) ^ arity / 4) *
      slots arity (fun i : Descendant V 0 => m i.1 / (∑ j, m j)) x := by
  simp [expertWeight, pivotMass, slots, spread, Finset.prod_div_distrib]
  field_simp
  ring

/-- Restrict the vertex masses to the active coordinates of a state. -/
def maskedMass {V : Type*} [DecidableEq V] (S : Finset V) (m : V → ℚ) (i : V) : ℚ :=
  if i ∈ S then m i else 0

theorem sum_maskedMass {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) (m : V → ℚ) :
    ∑ i, maskedMass S m i = ∑ i ∈ S, m i := by
  classical
  simp [maskedMass]

theorem maskedMass_nonneg {V : Type*} [DecidableEq V] (S : Finset V) (m : V → ℚ)
    (hm : ∀ i, 0 ≤ m i) (i : V) : 0 ≤ maskedMass S m i := by
  unfold maskedMass; split
  · exact hm i
  · exact le_refl _

/-- The child mass used in transfer is the actual mass of Section 4 with both
the parent's active set and its new pivot's set of strict violators applied. -/
def transitionMass {V : Type*} [DecidableEq V] (h : Bool) (S U : Finset V)
    (m : V → ℚ) : V × Bool → ℚ :=
  maskedMass (States.Mass.childActive h S U) (fun i => States.Mass.factor h i.2 * m i.1)

theorem transitionMass_bounds {V : Type*} [DecidableEq V] (h : Bool) (S U : Finset V)
    (hU : U ⊆ S) (m : V → ℚ) (hm : ∀ i, 0 ≤ m i) (v : V × Bool) :
    0 ≤ transitionMass h S U m v ∧ transitionMass h S U m v ≤ 8 * maskedMass S m v.1 := by
  have hf : 0 ≤ States.Mass.factor h v.2 ∧ States.Mass.factor h v.2 ≤ 8 := by
    unfold States.Mass.factor; split <;> norm_num
  by_cases hv : v ∈ States.Mass.childActive h S U
  · have hi : v.1 ∈ S := by
      rcases Finset.mem_union.mp hv with h1 | h1
      · exact (Finset.mem_product.mp h1).1
      · exact hU (Finset.mem_product.mp h1).1
    simp only [transitionMass, maskedMass, ite_eq_left hv, ite_eq_left hi]
    exact ⟨mul_nonneg hf.1 (hm _), mul_le_mul_of_nonneg_right hf.2 (hm _)⟩
  · simp only [transitionMass, maskedMass, ite_eq_right hv]
    exact ⟨le_refl _, mul_nonneg (by norm_num) (maskedMass_nonneg S m hm v.1)⟩

/-- Section 6 one-step transfer specialized to the actual active vertex
weights of Section 4. Only the upper bound on new pivot probabilities remains
as a hypothesis on the distribution of legal transitions. -/
theorem transition_expertWeight_le {V J : Type*} [DecidableEq V] [Fintype J]
    (p : J → ℚ) (hp : ∀ t, 0 ≤ p t) (hprob : ∑ t, p t = 1)
    (h : Bool) (S : Finset V) (U : J → Finset V) (hU : ∀ t, U t ⊆ S)
    (m : V → ℚ) (hm : ∀ i, 0 ≤ m i) (newPivot : J → Option V)
    (hnew : ∀ i, (∑ t, if newPivot t = some i then p t else 0) ≤ 32 * maskedMass S m i)
    (arity r : ℕ) (x : Fin arity → V × Bool) (ρ : PivotSite V) :
    let w := fun t => transitionMass h S (U t) m
    let a := maskedMass S m
    ∑ t, p t * ((1 / 2 : ℚ) ^ (r + 1) * slots arity (fun i => spread r (w t i)) x *
        childPivot (w t) (newPivot t) ρ) ≤ 8 * 16 ^ (arity + 1) *
      ((1 / 2 : ℚ) ^ (r + 2) * slots arity (fun i : V × Bool => spread (r + 1) (a i.1)) x *
        parentPivot a ρ) :=
  one_step_transfer p hp hprob (maskedMass S m) (maskedMass_nonneg _ _ hm)
    (fun t => transitionMass h S (U t) m)
    (fun t i => (transitionMass_bounds h S (U t) (hU t) m hm i).1)
    (fun t i => (transitionMass_bounds h S (U t) (hU t) m hm i).2)
    newPivot hnew arity r x ρ


/-- Read a descendant from the child level by peeling off its first sign. -/
def splitDescendant {V : Type*} {r : ℕ} (v : Descendant V (r + 1)) :
    Descendant (V × Bool) r :=
  ((v.1, v.2 0), fun i => v.2 i.succ)

private def vertexPivotSite {V : Type*} : (j : ℕ) → Descendant V j → PivotSite V
  | 0, v => .atParent v.1
  | j + 1, v => .later j (splitDescendant v).1

/-- Classify a parent's descriptor by its depth relative to this step. -/
def pivotSite {V : Type*} {r : ℕ} : PivotChoice V (r + 1) → PivotSite V
  | none => .current
  | some ⟨j, v⟩ => vertexPivotSite j.val v

private theorem parentPivot_site {V : Type*} {r : ℕ} (m : V → ℚ) (ρ : PivotChoice V (r+1)) :
    parentPivot m (pivotSite ρ) = pivotMass m ρ := by
  cases ρ with
  | none => rfl
  | some ρ =>
    obtain ⟨⟨j, hj⟩, v⟩ := ρ
    cases j with
    | zero => simp [pivotSite, vertexPivotSite, parentPivot, pivotMass, spread]; ring
    | succ j => rfl

/-- Read the same global descriptor in a child state. The outer option records
whether it became unavailable, and the inner one distinguishes current and future
pivots. -/
def reindexPivot {V : Type*} [DecidableEq V] {r : ℕ} (newPivot : Option V) :
    PivotChoice V (r + 1) → Option (PivotChoice (V × Bool) r)
  | none => if newPivot = none then some none else none
  | some ⟨⟨0, _⟩, v⟩ => if newPivot = some v.1 then some none else none
  | some ⟨⟨j + 1, hj⟩, v⟩ => some (some ⟨⟨j, by omega⟩, splitDescendant v⟩)

private theorem childPivot_site {V : Type*} [DecidableEq V] {r : ℕ} (w : V × Bool → ℚ)
    (newPivot : Option V) (ρ : PivotChoice V (r+1)) :
    (reindexPivot newPivot ρ).elim 0 (pivotMass w) = childPivot w newPivot (pivotSite ρ) := by
  cases ρ with
  | none =>
    by_cases h : newPivot = none <;> simp [reindexPivot, pivotSite, pivotMass, childPivot, h]
  | some ρ =>
    obtain ⟨⟨j, hj⟩, v⟩ := ρ
    cases j with
    | zero =>
      by_cases h : newPivot = some v.1 <;>
        simp [reindexPivot, pivotSite, vertexPivotSite, pivotMass, childPivot, h]
    | succ j => rfl

/-- A child gives weight zero to a parent descriptor that the transition discarded. -/
def reindexedWeight {V : Type*} [DecidableEq V] (w : V × Bool → ℚ)
    (newPivot : Option V) {arity r : ℕ} (x : Fin arity → Descendant V (r+1))
    (ρ : PivotChoice V (r+1)) : ℚ :=
  (reindexPivot newPivot ρ).elim 0 (expertWeight w arity r (fun j => splitDescendant (x j)))

private theorem reindexedWeight_eq {V : Type*} [DecidableEq V] (w : V × Bool → ℚ)
    (newPivot : Option V) {arity r : ℕ} (x : Fin arity → Descendant V (r+1))
    (ρ : PivotChoice V (r+1)) :
    reindexedWeight w newPivot x ρ = (1 / 2 : ℚ) ^ (r+1) *
      slots arity (fun i => spread r (w i)) (fun c => (splitDescendant (x c)).1) *
        childPivot w newPivot (pivotSite ρ) := by
  rw [← childPivot_site, reindexedWeight]
  cases hr : reindexPivot newPivot ρ with
  | none => simp
  | some p => rfl

/-- One-step transfer on the same parent-indexed skeleton, using its actual
expert weight on both sides and the active set in each sampled transition. -/
theorem reindexedWeight_transfer {V J : Type*} [DecidableEq V] [Fintype J]
    (p : J → ℚ) (hp : ∀ t, 0 ≤ p t) (hprob : ∑ t, p t = 1)
    (h : Bool) (S : Finset V) (U : J → Finset V) (hU : ∀ t, U t ⊆ S)
    (m : V → ℚ) (hm : ∀ i, 0 ≤ m i) (newPivot : J → Option V)
    (hnew : ∀ i, (∑ t, if newPivot t = some i then p t else 0) ≤ 32 * maskedMass S m i)
    {arity r : ℕ} (x : Fin arity → Descendant V (r+1)) (ρ : PivotChoice V (r+1)) :
    ∑ t, p t * reindexedWeight (transitionMass h S (U t) m) (newPivot t) x ρ ≤
      8 * 16 ^ (arity + 1) * expertWeight (maskedMass S m) arity (r+1) x ρ := by
  simp_rw [reindexedWeight_eq]
  have hv := transition_expertWeight_le p hp hprob h S U hU m hm newPivot hnew arity r
    (fun c => (splitDescendant (x c)).1) (pivotSite ρ)
  simpa only [parentPivot_site, expertWeight, slots, splitDescendant] using hv


/-- Recover a parent-level descendant by restoring the first sign. -/
def joinDescendant {V : Type*} {r : ℕ} (v : Descendant (V × Bool) r) : Descendant V (r+1) :=
  (v.1.1, Fin.cons v.1.2 v.2)

@[simp] theorem split_joinDescendant {V : Type*} {r : ℕ} (v : Descendant (V × Bool) r) :
    splitDescendant (joinDescendant v) = v := by
  obtain ⟨⟨i, b⟩, bits⟩ := v
  simp [joinDescendant, splitDescendant]

@[simp] theorem join_splitDescendant {V : Type*} {r : ℕ} (v : Descendant V (r+1)) :
    joinDescendant (splitDescendant v) = v := by
  obtain ⟨i, bits⟩ := v
  simp only [joinDescendant, splitDescendant, Prod.mk.injEq, true_and]
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp

/-- Every active child descriptor has one parent descriptor, even when a new
pivot is installed instead of inheriting the old pivot. -/
def joinPivot {V : Type*} (newPivot : Option V) {r : ℕ} :
    PivotChoice (V × Bool) r → PivotChoice V (r+1)
  | none =>
    match newPivot with
    | none => none
    | some i => some ⟨⟨0, Nat.zero_lt_succ _⟩, i, Fin.elim0⟩
  | some ⟨j, v⟩ => some ⟨j.succ, joinDescendant v⟩

@[simp] theorem reindex_joinPivot {V : Type*} [DecidableEq V] (newPivot : Option V)
    {r : ℕ} (ξ : PivotChoice (V × Bool) r) :
    reindexPivot newPivot (joinPivot newPivot ξ) = some ξ := by
  cases ξ with
  | none =>
    cases newPivot with
    | none => rfl
    | some i =>
      change (if some i = some i then some none else none) = (some none : Option (PivotChoice (V × Bool) r))
      simp
  | some ξ =>
    obtain ⟨⟨j,hj⟩,v⟩ := ξ
    simp [joinPivot, reindexPivot]

theorem joinPivot_of_reindex {V : Type*} [DecidableEq V] {newPivot : Option V} {r : ℕ}
    {ρ : PivotChoice V (r+1)} {ξ : PivotChoice (V × Bool) r}
    (hρ : reindexPivot newPivot ρ = some ξ) : joinPivot newPivot ξ = ρ := by
  cases ρ with
  | none =>
    cases newPivot with
    | none =>
      have hc : (none : PivotChoice (V × Bool) r) = ξ := Option.some.inj hρ
      subst ξ; rfl
    | some i => simp [reindexPivot] at hρ
  | some ρ =>
    obtain ⟨⟨j,hj⟩, v⟩ := ρ
    cases j with
    | zero =>
      obtain ⟨i, bits⟩ := v
      cases newPivot with
      | none => simp [reindexPivot] at hρ
      | some i' =>
        by_cases hi : i' = i
        · subst i'; simp only [reindexPivot, ↓reduceIte, Option.some.injEq] at hρ
          subst ξ
          have hbits : (Fin.elim0 : Fin 0 → Bool) = bits := Subsingleton.elim _ _
          simp [joinPivot, hbits]
        · simp [reindexPivot, hi] at hρ
    | succ j =>
      simp only [reindexPivot, Option.some.injEq] at hρ
      subst ξ
      simp [joinPivot]

/-- Sum over the parent's complete list of pivot descriptors after transporting
child weights. Dropped past pivots make no contribution, and every child
descriptor contributes exactly once. The score function may be arbitrary. -/
theorem sum_reindexedWeight_mul {V : Type*} [Fintype V] [DecidableEq V]
    (w : V × Bool → ℚ) (newPivot : Option V) {arity r : ℕ}
    (x : Fin arity → Descendant V (r+1)) (score : PivotChoice V (r+1) → ℚ) :
    ∑ ρ, reindexedWeight w newPivot x ρ * score ρ =
      ∑ ξ, expertWeight w arity r (fun j => splitDescendant (x j)) ξ * score (joinPivot newPivot ξ) := by
  classical
  let v := expertWeight w arity r (fun j => splitDescendant (x j))
  have he (ρ : PivotChoice V (r+1)) : reindexedWeight w newPivot x ρ =
      ∑ ξ : PivotChoice (V × Bool) r, if joinPivot newPivot ξ = ρ then v ξ else 0 := by
    cases hr : reindexPivot newPivot ρ with
    | none =>
      rw [reindexedWeight, hr, Option.elim_none]
      symm; apply Finset.sum_eq_zero
      intro ξ _
      have hne : joinPivot newPivot ξ ≠ ρ := by
        rintro rfl; rw [reindex_joinPivot] at hr; contradiction
      simp [hne]
    | some ψ =>
      have hm (ξ : PivotChoice (V × Bool) r) : joinPivot newPivot ξ = ρ ↔ ξ = ψ := by
        constructor
        · rintro rfl; simpa using hr
        · rintro rfl; exact joinPivot_of_reindex hr
      simp [reindexedWeight, hr, hm, v]
  simp_rw [he, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ _
  simp_rw [ite_mul, zero_mul]
  simp [v]

end Charging
end PriceGame
end LinearProgramming
end Optimization
end OAI
