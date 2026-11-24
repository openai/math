import OAI.Computability.VPVNP.GraphRounding
import Mathlib.Data.Fintype.BigOperators

/-!
# Sparse walks from the Grassmann inequality

In Section 5.2 of *VP and VNP differ over every field*, conditioning on the
restriction of a random linear map to a common hyperplane leaves two independent
vertices in corresponding fibers. Two bijections from `I × E` onto the vertex
set describe the two fiber partitions, with `I` indexing the restrictions and
`E` indexing the possible extensions. We compare the energy of this conditional
coupling with a copy of the previous walk in every fiber and a symmetric
permutation walk joining corresponding extensions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SpectralGeometry

variable {Ω I E J X : Type*} [Fintype Ω] [Fintype I] [Fintype E] [Fintype J]

/-- Place one copy of the preceding walk in each source fiber. -/
noncomputable def fiberWalk (l : I × E ≃ Ω) (P : Matrix E E ℝ) : Matrix Ω Ω ℝ := by
  classical
  exact fun u v ↦ if (l.symm u).1 = (l.symm v).1 then P (l.symm u).2 (l.symm v).2 else 0

/-- Match a vertex to its partner in the target fiber, symmetrizing the direction. -/
noncomputable def matchingWalk (π : Ω ≃ Ω) : Matrix Ω Ω ℝ := by
  classical
  exact fun u v ↦ ((if π u = v then 1 else 0) + (if π v = u then 1 else 0)) / 2

/-- The conditional adjacent-pair energy times the number of vertices. -/
noncomputable def adjacentEnergy [PseudoMetricSpace X] (l r : I × E ≃ Ω) (x : Ω → X) : ℝ :=
  (∑ i, ∑ a, ∑ b, dist (x (l (i,a))) (x (r (i,b))) ^ 2) / Fintype.card E

private theorem sum_chart {M : Type*} [AddCommMonoid M] (l : I × E ≃ Ω) (f : Ω → M) :
    ∑ u, f u = ∑ i, ∑ a, f (l (i,a)) := by
  rw [← l.sum_comp f, Fintype.sum_prod_type]

private theorem sum_divisor {T : Type*} [Fintype T] (f : T → ℝ) (d : ℝ) :
    ∑ a, f a / d = (∑ a, f a) / d := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem fiberWalk_row (l : I × E ≃ Ω) (P : Matrix E E ℝ) (hr : ∀ a, ∑ b, P a b = 1)
    (u : Ω) : ∑ v, fiberWalk l P u v = 1 := by
  classical
  rw [sum_chart l]
  simp [fiberWalk, hr]

theorem matchingWalk_row (π : Ω ≃ Ω) (u : Ω) : ∑ v, matchingWalk π u v = 1 := by
  classical
  simp only [matchingWalk, sum_divisor, Finset.sum_add_distrib,
    show ∀ v, (π v = u) = (v = π.symm u) from fun _ ↦ propext π.eq_symm_apply.symm]
  simp

omit [Fintype Ω] [Fintype I] [Fintype E] in
theorem fiberWalk_symm (l : I × E ≃ Ω) (P : Matrix E E ℝ) (hs : ∀ a b, P a b = P b a)
    (u v : Ω) : fiberWalk l P u v = fiberWalk l P v u := by
  classical
  unfold fiberWalk
  by_cases h : (l.symm u).1 = (l.symm v).1 <;> simp [h, eq_comm, hs]

omit [Fintype Ω] in
theorem matchingWalk_symm (π : Ω ≃ Ω) (u v : Ω) : matchingWalk π u v = matchingWalk π v u := by
  unfold matchingWalk
  rw [add_comm]

omit [Fintype Ω] [Fintype I] [Fintype E] in
theorem fiberWalk_nonneg (l : I × E ≃ Ω) (P : Matrix E E ℝ) (hn : ∀ a b, 0 ≤ P a b)
    (u v : Ω) : 0 ≤ fiberWalk l P u v := by
  classical
  unfold fiberWalk
  split_ifs <;> simp [hn]

omit [Fintype Ω] in
theorem matchingWalk_nonneg (π : Ω ≃ Ω) (u v : Ω) : 0 ≤ matchingWalk π u v := by
  unfold matchingWalk
  split_ifs <;> norm_num

variable [PseudoMetricSpace X]

theorem walkEnergy_fiberWalk (l : I × E ≃ Ω) (P : Matrix E E ℝ) (x : Ω → X) :
    walkEnergy (fiberWalk l P) x = ∑ i, walkEnergy P (fun a ↦ x (l (i,a))) := by
  classical
  unfold walkEnergy
  rw [sum_chart l]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_chart l]
  simp [fiberWalk, ite_mul]

theorem walkEnergy_matchingWalk (π : Ω ≃ Ω) (x : Ω → X) :
    walkEnergy (matchingWalk π) x = ∑ u, dist (x u) (x (π u)) ^ 2 := by
  classical
  unfold walkEnergy matchingWalk
  have hi (u : Ω) : ∑ v, (((if π u = v then 1 else 0) + (if π v = u then 1 else 0)) / 2) *
        dist (x v) (x u) ^ 2 =
      (dist (x (π u)) (x u) ^ 2 + dist (x (π.symm u)) (x u) ^ 2) / 2 := by
    simp only [div_mul_eq_mul_div, add_mul, ite_mul, one_mul, zero_mul,
      show ∀ v, (π v = u) = (v = π.symm u) from fun _ ↦ propext π.eq_symm_apply.symm,
      sum_divisor, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
  simp only [hi, sum_divisor, Finset.sum_add_distrib]
  have h := π.sum_comp (fun u ↦ dist (x (π.symm u)) (x u) ^ 2)
  simp only [Equiv.symm_apply_apply] at h
  rw [← h]
  simp_rw [dist_comm (x (π _)) (x _)]
  ring

private theorem dist_sq_le_split (u v w : X) {ε : ℝ} (hε : 0 < ε) :
    dist u w ^ 2 ≤ (1 + ε) * dist u v ^ 2 + (1 + 1 / ε) * dist v w ^ 2 := by
  have h := pow_le_pow_left₀ dist_nonneg (dist_triangle u v w) 2
  have hcross := sq_nonneg (ε * dist u v - dist v w)
  apply (le_of_mul_le_mul_left (a := ε) _ hε)
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left h hε.le]

/-- Compare independent conditional endpoints through the source partner of the
target endpoint. The factor `γ` is paid only on the part of the energy within
a fiber. This gives the multiplicative coefficient used in the sparse recursion. -/
theorem adjacentEnergy_le [Nonempty E] (l r : I × E ≃ Ω) (P : Matrix E E ℝ) {ε γ : ℝ}
    (hε : 0 < ε) (hP : HasPoincareBound X P γ) (x : Ω → X) :
    adjacentEnergy l r x ≤ ((1 + ε) * γ) * walkEnergy (fiberWalk l P) x +
      (1 + 1 / ε) * walkEnergy (matchingWalk (l.symm.trans r)) x := by
  let L (i : I) (a : E) := x (l (i,a))
  let R (i : I) (a : E) := x (r (i,a))
  have hc : 0 < (Fintype.card E : ℝ) := by exact_mod_cast Fintype.card_pos
  have hlocal (i : I) :
      (∑ a, ∑ b, dist (L i a) (R i b) ^ 2) / Fintype.card E ≤
      (1 + ε) * (γ * walkEnergy P (L i)) + (1 + 1 / ε) * ∑ b, dist (L i b) (R i b) ^ 2 := by
    have h := Finset.sum_le_sum (s := Finset.univ) fun a _ ↦
      Finset.sum_le_sum (s := Finset.univ) fun b _ ↦ dist_sq_le_split (L i a) (L i b) (R i b) hε
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul] at h
    have hp := (div_le_iff₀ hc).mp (hP (L i))
    apply (div_le_iff₀ hc).mpr
    nlinarith only [h, mul_le_mul_of_nonneg_left hp (by linarith only [hε] : 0 ≤ 1 + ε)]
  have h := Finset.sum_le_sum (s := Finset.univ) fun i _ ↦ hlocal i
  simp only [sum_divisor, Finset.sum_add_distrib, ← Finset.mul_sum, ← mul_assoc] at h
  rw [walkEnergy_fiberWalk, walkEnergy_matchingWalk, sum_chart l (fun u ↦
    dist (x u) (x ((l.symm.trans r) u)) ^ 2)]
  simpa only [adjacentEnergy, L, R, Equiv.trans_apply, Equiv.symm_apply_apply] using h

/-- Average the fiber walk and the matching walk over the ordered adjacencies,
using their respective weights from the squared triangle inequality. -/
noncomputable def sparseWalk (l r : J → I × E ≃ Ω) (P : Matrix E E ℝ) (a b : ℝ) :
    Matrix Ω Ω ℝ := fun u v ↦
  (∑ j, (a * fiberWalk (l j) P u v + b * matchingWalk ((l j).symm.trans (r j)) u v)) /
    ((Fintype.card J : ℝ) * (a + b))

theorem sparseWalk_row [Nonempty J] (l r : J → I × E ≃ Ω) (P : Matrix E E ℝ)
    (hr : ∀ e, ∑ f, P e f = 1) {a b : ℝ} (hab : a + b ≠ 0) (u : Ω) :
    ∑ v, sparseWalk l r P a b u v = 1 := by
  unfold sparseWalk
  rw [sum_divisor, Finset.sum_comm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, fiberWalk_row _ _ hr, matchingWalk_row,
    mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : 0 < (Fintype.card J : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  rw [← mul_add, div_self (mul_ne_zero hc.ne' hab)]

omit [Fintype Ω] [Fintype I] [Fintype E] in
theorem sparseWalk_symm (l r : J → I × E ≃ Ω) (P : Matrix E E ℝ)
    (hs : ∀ a b, P a b = P b a) (a b : ℝ) (u v : Ω) :
    sparseWalk l r P a b u v = sparseWalk l r P a b v u := by
  unfold sparseWalk
  congr 1
  exact Finset.sum_congr rfl fun j _ ↦ by
    rw [fiberWalk_symm _ _ hs u v, matchingWalk_symm _ u v]

omit [Fintype Ω] [Fintype I] [Fintype E] in
theorem sparseWalk_nonneg (l r : J → I × E ≃ Ω) (P : Matrix E E ℝ)
    (hn : ∀ e f, 0 ≤ P e f) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (u v : Ω) :
    0 ≤ sparseWalk l r P a b u v :=
  div_nonneg (Finset.sum_nonneg fun _ _ ↦
    add_nonneg (mul_nonneg ha (fiberWalk_nonneg _ _ hn u v))
      (mul_nonneg hb (matchingWalk_nonneg _ u v))) (mul_nonneg (Nat.cast_nonneg _) (add_nonneg ha hb))

omit [Fintype I] [Fintype E] in
theorem walkEnergy_sparseWalk (l r : J → I × E ≃ Ω) (P : Matrix E E ℝ) (a b : ℝ) (x : Ω → X) :
    walkEnergy (sparseWalk l r P a b) x =
      (∑ j, (a * walkEnergy (fiberWalk (l j) P) x +
        b * walkEnergy (matchingWalk ((l j).symm.trans (r j))) x)) /
      ((Fintype.card J : ℝ) * (a + b)) := by
  unfold walkEnergy sparseWalk
  simp only [div_mul_eq_mul_div, sum_divisor, Finset.sum_mul, add_mul, mul_assoc]
  congr 1
  calc
    _ = ∑ u, ∑ j, ∑ v, (a * (fiberWalk (l j) P u v * dist (x v) (x u) ^ 2) +
        b * (matchingWalk ((l j).symm.trans (r j)) u v * dist (x v) (x u) ^ 2)) :=
      Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The sparse recursion of Section 5.2. The sampling inequality is stated in
the same normalization as `HasPoincareBound`. Its coefficient `c` is `m - η`
when applied to the adjacent pairs of the binary Grassmannian. -/
theorem sparseWalk_hasPoincareBound [Nonempty E] [Nonempty J] (l r : J → I × E ≃ Ω)
    (P : Matrix E E ℝ) {ε γ c : ℝ} (hε : 0 < ε) (hγ : 0 ≤ γ) (hc : 0 ≤ c)
    (hP : HasPoincareBound X P γ)
    (hsamp : ∀ x : Ω → X, (∑ u, ∑ v, dist (x u) (x v) ^ 2) / Fintype.card Ω ≤
      c * ((∑ j, adjacentEnergy (l j) (r j) x) / Fintype.card J)) :
    HasPoincareBound X (sparseWalk l r P ((1 + ε) * γ) (1 + 1 / ε))
      (c * ((1 + ε) * γ + (1 + 1 / ε))) := by
  intro x
  let a := (1 + ε) * γ
  let b := 1 + 1 / ε
  have hab : 0 < a + b := by dsimp [a,b]; positivity
  have hj : 0 < (Fintype.card J : ℝ) := by exact_mod_cast Fintype.card_pos
  have h := Finset.sum_le_sum (s := Finset.univ) fun j _ ↦ adjacentEnergy_le (l j) (r j) P hε hP x
  refine (hsamp x).trans ?_
  rw [walkEnergy_sparseWalk]
  change c * (_ / (Fintype.card J : ℝ)) ≤ (c * (a + b)) * (_ / ((Fintype.card J : ℝ) * (a + b)))
  rw [show ∀ s : ℝ, (c * (a + b)) * (s / ((Fintype.card J : ℝ) * (a + b))) =
    c * (s / (Fintype.card J : ℝ)) from fun s ↦ by field_simp]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h hj.le) hc

@[simp] theorem mem_rowSupport {T : Type*} [Fintype T] (P : Matrix T T ℝ) (u v : T) :
    v ∈ rowSupport P u ↔ P u v ≠ 0 := by classical simp [rowSupport]

omit [Fintype I] in
theorem fiberWalk_support (l : I × E ≃ Ω) (P : Matrix E E ℝ) (u : Ω) :
    (rowSupport (fiberWalk l P) u).card ≤ (rowSupport P (l.symm u).2).card := by
  classical
  let S := (rowSupport P (l.symm u).2).image fun e ↦ l ((l.symm u).1, e)
  refine (Finset.card_le_card (t := S) ?_).trans Finset.card_image_le
  intro v hv
  have h := (mem_rowSupport _ _ _).mp hv
  unfold fiberWalk at h
  split_ifs at h with h'
  · refine Finset.mem_image.mpr ⟨(l.symm v).2, (mem_rowSupport _ _ _).mpr h, ?_⟩
    rw [h']
    simp
  · exact False.elim (h rfl)

theorem matchingWalk_support (π : Ω ≃ Ω) (u : Ω) : (rowSupport (matchingWalk π) u).card ≤ 2 := by
  classical
  have hs : rowSupport (matchingWalk π) u ⊆ {π u, π.symm u} := by
    intro v hv
    have h := (mem_rowSupport _ _ _).mp hv
    by_contra hc
    have hv₁ : π u ≠ v := fun he ↦ hc (by simp [← he])
    have hv₂ : π v ≠ u := fun he ↦ hc (by simp [π.eq_symm_apply.mpr he])
    simp [matchingWalk, hv₁, hv₂] at h
  exact (Finset.card_le_card hs).trans (Finset.card_le_two)

omit [Fintype I] in
/-- A row of the new walk uses at most one old row and two matching edges per
ordered Grassmann adjacency. This count is independent of the fiber count. -/
theorem sparseWalk_support (l r : J → I × E ≃ Ω) (P : Matrix E E ℝ) (a b : ℝ)
    {k : ℕ} (hk : ∀ e, (rowSupport P e).card ≤ k) (u : Ω) :
    (rowSupport (sparseWalk l r P a b) u).card ≤ Fintype.card J * (k + 2) := by
  classical
  let S (j : J) := rowSupport (fiberWalk (l j) P) u ∪ rowSupport (matchingWalk ((l j).symm.trans (r j))) u
  have hS : rowSupport (sparseWalk l r P a b) u ⊆ Finset.univ.biUnion S := by
    intro v hv
    by_contra h
    have hzero (j : J) :
        fiberWalk (l j) P u v = 0 ∧ matchingWalk ((l j).symm.trans (r j)) u v = 0 := by
      by_contra! hn
      apply h
      simpa [S] using (show ∃ j, v ∈ S j from ⟨j, by
        simp only [S, Finset.mem_union, mem_rowSupport]; tauto⟩)
    apply (mem_rowSupport _ _ _).mp hv
    simp [sparseWalk, fun j ↦ (hzero j).1, fun j ↦ (hzero j).2]
  calc
    _ ≤ _ := Finset.card_le_card hS
    _ ≤ ∑ j, (S j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : J, (k + 2) := Finset.sum_le_sum fun j _ ↦
      (Finset.card_union_le _ _).trans (Nat.add_le_add ((fiberWalk_support _ _ _).trans (hk _))
        (matchingWalk_support _ _))
    _ = _ := by simp

end SpectralGeometry

end VPVNP
end Computability
end OAI
