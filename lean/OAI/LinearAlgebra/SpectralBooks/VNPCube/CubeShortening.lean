import OAI.Geometry.HyperbolicGroups.CATZero

/-! # Antipodal wires on the binary cube

Averaging the CAT(0) quadrilateral inequality over translations bounds the
sum of the antipodal lengths by the number of antipodal pairs times the
square root of the cube dimension times the maximum edge length.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace VNPCube

open HyperbolicObstruction

abbrev Vertex (a : ℕ) := Fin a → ZMod 2

/-- The displacement of a single cube edge. -/
def unit {a : ℕ} (i : Fin a) : Vertex a := Pi.single i 1

private theorem self_add {a : ℕ} (x : Vertex a) : x + x = 0 :=
  funext fun i => CharTwo.add_self_eq_zero (x i)

variable {a : ℕ} {X : Type*} [MetricSpace X] (y : Vertex a → X)

/-- Sum over both orientations of the squared wire lengths for a displacement. -/
noncomputable def energy (u : Vertex a) : ℝ := ∑ x, dist (y x) (y (x + u)) ^ 2

private lemma sum_translate (g : Vertex a → ℝ) (u : Vertex a) :
    ∑ x, g (x + u) = ∑ x, g x := Equiv.sum_comp (Equiv.addRight u) g

/-- The averaged squared displacement is subadditive on the binary cube. -/
theorem energy_add (h : CATZero X) (u v : Vertex a) :
    energy y (u + v) ≤ energy y u + energy y v := by
  let d (x t : Vertex a) := dist (y x) (y (x+t)) ^ 2
  have point (x : Vertex a) :
      d x (u+v) + d (x+u) (u+v) ≤ d x u + d (x+u) v + d (x+v) u + d x v := by
    have e : (x+u)+(u+v) = x+v := by rw [add_assoc, ← add_assoc u, self_add, zero_add]
    have f : x+v+u=x+u+v := by abel
    simp only [d, ← add_assoc x u v, e, f]
    have q := h.quadrilateral (y x) (y (x+u)) (y (x+u+v)) (y (x+v))
    rw [dist_comm (y (x+u+v)) (y (x+v)), dist_comm (y (x+v)) (y x)] at q
    linarith [sq_nonneg (dist (CATZero.mid h (y x) (y (x+u+v)))
      (CATZero.mid h (y (x+u)) (y (x+v))))]
  have H := Finset.sum_le_sum (s := Finset.univ) fun x _ => point x
  simp only [Finset.sum_add_distrib] at H
  have tr (s t : Vertex a) : ∑ x, d (x+s) t = ∑ x, d x t :=
    sum_translate (fun x => d x t) s
  simp only [tr] at H
  change (∑ x, d x (u+v)) ≤ (∑ x, d x u) + ∑ x, d x v
  linarith

private theorem energy_sum (h : CATZero X) (s : Finset (Fin a)) (f : Fin a → Vertex a) :
    energy y (∑ i ∈ s, f i) ≤ ∑ i ∈ s, energy y (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [energy]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (energy_add y h _ _).trans (add_le_add_right ih _)

private lemma sum_single_coordinate (u : Vertex a) : ∑ i, Pi.single i (u i) = u := by
  ext j
  simp [Finset.sum_apply, Finset.sum_pi_single]

/-- Every displacement has energy at most the sum of the energies of the
coordinate edges, even when some of its coordinates vanish. -/
theorem energy_le_edges (h : CATZero X) (u : Vertex a) :
    energy y u ≤ ∑ i, energy y (unit i) := by
  calc
    _ = energy y (∑ i, Pi.single i (u i)) := congrArg _ (sum_single_coordinate u).symm
    _ ≤ _ := energy_sum y h Finset.univ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      have hbit : u i = 0 ∨ u i = 1 := by
        exact (by decide : ∀ z : ZMod 2, z = 0 ∨ z = 1) (u i)
      rcases hbit with h0 | h1
      · simp only [h0, Pi.single_zero, energy, add_zero, dist_self, zero_pow (by decide : 2 ≠ 0),
          Finset.sum_const_zero]
        positivity
      · rw [h1]; rfl

private theorem card_vertex (a : ℕ) : Fintype.card (Vertex a) = 2^a := by
  rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]

/-- The common bound on the lengths of all oriented edges yields the Enflo
estimate for the sum over all cube vertices. -/
theorem sum_opposite_le (h : CATZero X) {M : ℝ} (hM : 0 ≤ M)
    (he : ∀ x i, dist (y x) (y (x + unit i)) ≤ M) :
    ∑ x, dist (y x) (y (x+1)) ≤ (2:ℝ)^a * Real.sqrt a * M := by
  have hc : (Fintype.card (Vertex a) : ℝ) = (2:ℝ)^a := by exact_mod_cast card_vertex a
  have bound (i : Fin a) : energy y (unit i) ≤ (2:ℝ)^a * M^2 := calc
    _ ≤ ∑ _x : Vertex a, M^2 := Finset.sum_le_sum fun x _ =>
      (sq_le_sq₀ dist_nonneg hM).mpr (he x i)
    _ = _ := by simp
  have E := (energy_le_edges y h 1).trans (Finset.sum_le_sum fun i _ => bound i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at E
  have C := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun x => dist (y x) (y (x+1)))
  change _ ≤ (Finset.univ.card : ℝ) * energy y 1 at C
  rw [Finset.card_univ, hc] at C
  apply (sq_le_sq₀ (Finset.sum_nonneg fun _ _ => dist_nonneg) (by positivity)).mp
  calc
    _ ≤ _ := C
    _ ≤ (2:ℝ)^a * (a * ((2:ℝ)^a * M^2)) := mul_le_mul_of_nonneg_left E (by positivity)
    _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring

/-- One representative of each antipodal pair in dimension `n + 1`. -/
def base {n : ℕ} (r : Vertex n) : Vertex (n+1) := Fin.cons 0 r

private lemma base_add_one {n : ℕ} (r : Vertex n) : base r + 1 = Fin.cons 1 (r+1) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [base]

private lemma one_cons_add_one {n : ℕ} (r : Vertex n) :
    (Fin.cons 1 r : Vertex (n+1)) + 1 = base (r+1) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [base, CharTwo.add_self_eq_zero]

/-- The distance sum over all antipodal pairs in dimension `n + 1`. -/
theorem antipodal_sum_le {n : ℕ} (p : Vertex (n+1) → X) (h : CATZero X) {M : ℝ} (hM : 0 ≤ M)
    (he : ∀ x i, dist (p x) (p (x + unit i)) ≤ M) :
    ∑ r, dist (p (base r)) (p (base r + 1)) ≤ (2:ℝ)^n * Real.sqrt (n+1) * M := by
  let f (x : Vertex (n+1)) := dist (p x) (p (x+1))
  have hpair (r : Vertex n) : f (Fin.cons 1 r) = f (base (r+1)) := by
    change dist _ (p (Fin.cons 1 r + 1)) = dist _ (p (base (r+1) + 1))
    rw [one_cons_add_one, base_add_one, add_assoc, self_add, add_zero, dist_comm]
  have total : ∑ x, f x = 2 * ∑ r, f (base r) := by
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => ZMod 2)).sum_comp f, Fintype.sum_prod_type]
    have two (g : ZMod 2 → ℝ) : ∑ t, g t = g 0 + g 1 := Fin.sum_univ_two g
    change (∑ j : ZMod 2, ∑ r, f (Fin.cons j r)) = _
    rw [two]
    simp_rw [hpair]
    rw [sum_translate (fun r => f (base r))]
    change (∑ r, f (base r)) + _ = _
    ring
  have H := sum_opposite_le p h hM he
  change (∑ x, f x) ≤ _ at H
  rw [total, pow_succ, Nat.cast_add_one] at H
  change (∑ r, f (base r)) ≤ _
  linarith

end VNPCube

end SpectralBooks
end LinearAlgebra
end OAI
