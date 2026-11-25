import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-!
# Concentration of independent pack motions

In §6 a single motion moves a whole pack, so bins inside a pack may be perfectly
correlated. Independence is needed only across packs. Here the distribution of
each motion is any finite distribution, including the finite frame list followed
by a uniform deck translation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Epoch

open scoped BigOperators

variable {I M B : Type*} [Fintype I] [Fintype M] [Fintype B]

/-- The mean count in one bin of one pack. -/
noncomputable def motionMean (p : I → M → ℝ) (x : I → M → B → ℝ) (i : I) (b : B) : ℝ :=
  ∑ m, p i m * x i m b

/-- The squared Euclidean norm of a bin array. -/
noncomputable def binEnergy (x : B → ℝ) : ℝ := ∑ b, (x b) ^ 2

private theorem product_moment [DecidableEq I] (p f : I → M → ℝ) :
    (∑ ω : I → M, (∏ i, p i (ω i)) * ∏ i, f i (ω i)) =
      ∏ i, ∑ m, p i m * f i m := by
  simp only [← Finset.prod_mul_distrib, Fintype.prod_sum]

/-- The expectation of a function of one coordinate in the finite product law is its marginal mean. -/
theorem single_moment [DecidableEq I] (p : I → M → ℝ) (hp : ∀ i, ∑ m, p i m = 1)
    (i : I) (f : M → ℝ) :
    (∑ ω : I → M, (∏ k, p k (ω k)) * f (ω i)) = ∑ m, p i m * f m := by
  have h (j : I) : (∑ m, p j m * (if j = i then f m else 1)) =
      if j = i then ∑ m, p j m * f m else 1 := by
    by_cases he : j = i <;> simp [he, hp]
  simpa only [Fintype.prod_ite_eq', h] using
    product_moment p (fun j m => if j = i then f m else 1)

private theorem mixed_moment [DecidableEq I] (p : I → M → ℝ)
    {i j : I} (hij : i ≠ j) (f g : M → ℝ) (hf : ∑ m, p i m * f m = 0) :
    (∑ ω : I → M, (∏ k, p k (ω k)) * (f (ω i) * g (ω j))) = 0 := by
  have h := product_moment p (fun k m =>
    (if k = i then f m else 1) * (if k = j then g m else 1))
  simp only [Finset.prod_mul_distrib, Fintype.prod_ite_eq'] at h
  rw [h]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa [hij] using hf)

/-- Under the product distribution, the squared deviations of independent
centered pack counts add exactly, even if the bins within each pack are correlated. -/
theorem independent_bin_variance [DecidableEq I] (p : I → M → ℝ)
    (hp : ∀ i, ∑ m, p i m = 1) (z : I → M → B → ℝ)
    (hz : ∀ i b, ∑ m, p i m * z i m b = 0) :
    (∑ ω : I → M, (∏ i, p i (ω i)) * binEnergy (fun b => ∑ i, z i (ω i) b)) =
      ∑ i, ∑ m, p i m * binEnergy (z i m) := by
  have point (b : B) :
      (∑ ω : I → M, (∏ i, p i (ω i)) * (∑ i, z i (ω i) b) ^ 2) =
        ∑ i, ∑ m, p i m * (z i m b) ^ 2 := by
    simp_rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    rw [Finset.sum_eq_single i]
    · exact single_moment p hp i (fun m => z i m b * z i m b)
    · intro j _ hji
      exact mixed_moment p (Ne.symm hji) _ (fun m => z j m b) (hz i b)
    · simp
  simp_rw [binEnergy, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [point]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private theorem weighted_energy_center (p : M → ℝ) (hp : ∑ m, p m = 1)
    (x : M → B → ℝ) :
    (∑ m, p m * binEnergy (fun b => x m b - ∑ a, p a * x a b)) =
      (∑ m, p m * binEnergy (x m)) - binEnergy (fun b => ∑ a, p a * x a b) := by
  simp_rw [binEnergy, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun m b => p m * (x m b)^2), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b _
  let u := ∑ a, p a * x a b
  change (∑ m, p m * (x m b - u)^2) = (∑ m, p m * (x m b)^2) - u^2
  calc
    _ = ∑ m, (p m * (x m b)^2 - (p m * x m b) * (2 * u) + p m * u^2) :=
      Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
                    ← Finset.sum_mul, hp]; change _ - u * (2 * u) + 1 * u^2 = _; ring

/-- A positive-weight sample attains at most the mean of any observable on the finite law. -/
theorem exists_le_weighted (p f : M → ℝ) (hp : ∀ m, 0 ≤ p m)
    (h1 : ∑ m, p m = 1) :
    ∃ m, 0 < p m ∧ f m ≤ ∑ a, p a * f a := by
  have hpos : 0 < ∑ m, p m := by rw [h1]; norm_num
  obtain ⟨k, hk, hkpos⟩ := (Finset.sum_pos_iff_of_nonneg (fun m _ => hp m)).mp hpos
  by_contra! hn
  let v := ∑ a, p a * f a
  have hlt : (∑ a, p a * v) < ∑ a, p a * f a :=
    Finset.sum_lt_sum (fun a _ => by
      by_cases h : p a = 0
      · simp [h]
      · exact mul_le_mul_of_nonneg_left (hn a (lt_of_le_of_ne (hp a) (Ne.symm h))).le (hp a))
      ⟨k, hk, mul_lt_mul_of_pos_left (hn k hkpos) hkpos⟩
  rw [← Finset.sum_mul, h1, one_mul] at hlt
  exact lt_irrefl v hlt

/-- Conditional-expectation step used to find the motions on p. 21. Given the
sum `prior` of previously selected centered arrays, a supported motion for the
next pack incurs at most its unconditional squared-deviation budget. -/
theorem choose_next_motion (p : M → ℝ) (hp : ∀ m, 0 ≤ p m) (hp1 : ∑ m, p m = 1)
    (prior : B → ℝ) (z : M → B → ℝ) (hz : ∀ b, ∑ m, p m * z m b = 0) :
    ∃ m, 0 < p m ∧ binEnergy (fun b => prior b + z m b) ≤
      binEnergy prior + ∑ a, p a * binEnergy (z a) := by
  have h (b : B) : (∑ m, p m * (prior b + z m b)^2) =
      (prior b)^2 + ∑ m, p m * (z m b)^2 := calc
    _ = ∑ m, (p m * (prior b)^2 + (p m * z m b) * (2 * prior b) + p m * (z m b)^2) :=
      Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
                    ← Finset.sum_mul, hp1, hz]; ring
  obtain ⟨m, hm, hv⟩ := exists_le_weighted p (fun m => binEnergy (fun b => prior b + z m b)) hp hp1
  refine ⟨m, hm, hv.trans_eq ?_⟩
  simp_rw [binEnergy, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun b m => p m * (z m b)^2)]

/-- Equation (6.2). A single joint placement controls all bin errors together.
Here `tiles` is the number of output tiles and `radius` is the uniform bound
on the tile-normalized norm of one moved pack (the manuscript's `C Xmax`). -/
theorem exists_concentrated_motions [Nonempty I]
    (p : I → M → ℝ) (hp : ∀ i m, 0 ≤ p i m) (hp1 : ∀ i, ∑ m, p i m = 1)
    (x : I → M → B → ℝ) {tiles radius : ℝ} (ht : 0 ≤ tiles) (hr : 0 ≤ radius)
    (hbound : ∀ i m, tiles * binEnergy (x i m) ≤ radius ^ 2) :
    ∃ ω : I → M, Real.sqrt tiles *
        Real.sqrt (binEnergy (fun b =>
          (∑ i, x i (ω i) b) / Fintype.card I -
          (∑ i, motionMean p x i b) / Fintype.card I)) ≤ radius / Real.sqrt (Fintype.card I) := by
  classical
  let k : ℝ := Fintype.card I
  have hk : 0 < k := by
    dsimp [k]
    exact_mod_cast (Fintype.card_pos (α := I))
  let z := fun i m b => x i m b - motionMean p x i b
  have hz i b : ∑ m, p i m * z i m b = 0 := by
    simp [z, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, motionMean]
  let w := fun ω : I → M => ∏ i, p i (ω i)
  have hw : ∑ ω, w ω = 1 := by simp [w, ← Fintype.prod_sum, hp1]
  obtain ⟨ω, _, hω⟩ := exists_le_weighted w (fun ω => binEnergy (fun b => ∑ i, z i (ω i) b))
    (fun _ => Finset.prod_nonneg fun _ _ => hp _ _) hw
  change binEnergy _ ≤ ∑ ω : I → M, (∏ i, p i (ω i)) * binEnergy _ at hω
  rw [independent_bin_variance p hp1 z hz] at hω
  have hi (i : I) : tiles * (∑ m, p i m * binEnergy (z i m)) ≤ radius^2 := by
    have hc : (∑ m, p i m * binEnergy (z i m)) ≤ ∑ m, p i m * binEnergy (x i m) := by
      rw [show (∑ m, p i m * binEnergy (z i m)) = _ from
        weighted_energy_center (p i) (hp1 i) (x i)]
      exact sub_le_self _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    calc
      _ ≤ tiles * (∑ m, p i m * binEnergy (x i m)) := mul_le_mul_of_nonneg_left hc ht
      _ = ∑ m, p i m * (tiles * binEnergy (x i m)) := by simp only [Finset.mul_sum, mul_left_comm]
      _ ≤ ∑ m, p i m * radius ^ 2 :=
        Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hbound i m) (hp i m)
      _ = radius ^ 2 := by rw [← Finset.sum_mul, hp1, one_mul]
  let e := binEnergy (fun b => ∑ i, z i (ω i) b)
  have he : tiles * e ≤ k * radius ^ 2 := calc
    _ ≤ tiles * (∑ i, ∑ m, p i m * binEnergy (z i m)) := mul_le_mul_of_nonneg_left hω ht
    _ = _ := Finset.mul_sum ..
    _ ≤ ∑ _i : I, radius ^ 2 := Finset.sum_le_sum fun i _ => hi i
    _ = _ := by simp [k]
  refine ⟨ω, ?_⟩
  have hn : binEnergy (fun b => (∑ i, x i (ω i) b) / k - (∑ i, motionMean p x i b) / k) =
      e / k ^ 2 := by
    unfold e binEnergy
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    dsimp [z]
    rw [← sub_div, div_pow, Finset.sum_sub_distrib]
  have he0 : 0 ≤ e := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [hn, Real.sqrt_div he0, Real.sqrt_sq hk.le,
    ← mul_div_assoc, ← Real.sqrt_mul ht, div_le_div_iff₀ hk (Real.sqrt_pos.2 hk)]
  have hroot := Real.sqrt_le_sqrt he
  rw [Real.sqrt_mul hk.le, Real.sqrt_sq hr] at hroot
  calc
    _ ≤ (Real.sqrt k * radius) * Real.sqrt k := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)
    _ = radius * k := by rw [mul_comm (Real.sqrt k) radius, mul_assoc, Real.mul_self_sqrt hk.le]

/-- Distributing tile counts to bins with at most `degree` predecessor tiles
in each bin increases the squared norm by at most that factor. An input tile
may distribute its bits across several output bins. -/
theorem binEnergy_of_local_placement {A : Type*} [Fintype A] (source : A → ℝ)
    (neighbors : B → Finset A) (flow : A → B → ℝ) {degree : ℝ}
    (hdeg : ∀ b, ((neighbors b).card : ℝ) ≤ degree) (hd : 0 ≤ degree)
    (hf : ∀ a b, 0 ≤ flow a b) (hm : ∀ a, ∑ b, flow a b ≤ source a) :
    binEnergy (fun b => ∑ a ∈ neighbors b, flow a b) ≤ degree * binEnergy source := by
  classical
  have hb (b : B) : (∑ a ∈ neighbors b, flow a b)^2 ≤ degree * (∑ a, (flow a b)^2) := calc
    _ ≤ ((neighbors b).card : ℝ) * (∑ a ∈ neighbors b, (flow a b)^2) :=
      sq_sum_le_card_mul_sum_sq
    _ ≤ degree * (∑ a, (flow a b)^2) :=
      mul_le_mul (hdeg b) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => sq_nonneg _)) (Finset.sum_nonneg fun _ _ => sq_nonneg _) hd
  have ha (a : A) : (∑ b, (flow a b)^2) ≤ (source a)^2 :=
    (Finset.sum_sq_le_sq_sum_of_nonneg (fun b _ => hf a b)).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun b _ => hf a b)) (hm a) 2)
  calc
    _ ≤ ∑ b, degree * (∑ a, (flow a b)^2) := Finset.sum_le_sum fun b _ => hb b
    _ = degree * (∑ a, ∑ b, (flow a b)^2) := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ha a) hd

/-- A mean count array with uniformly bounded mass per tile has normalized
Euclidean norm at most its total mass bound. -/
theorem uniform_tile_mean_norm {T : Type*} [Fintype T] [Nonempty T]
    (g : T × B → ℝ) (hg : ∀ t b, 0 ≤ g (t, b)) {mass : ℝ} (hm : 0 ≤ mass)
    (hu : ∀ t, ∑ b, g (t,b) ≤ mass / Fintype.card T) :
    Real.sqrt (Fintype.card T) * Real.sqrt (binEnergy g) ≤ mass := by
  let k : ℝ := Fintype.card T
  have hk : 0 < k := by dsimp [k]; exact_mod_cast (Fintype.card_pos (α := T))
  have hb t : ∑ b, (g (t,b))^2 ≤ (mass / k)^2 :=
    (Finset.sum_sq_le_sq_sum_of_nonneg fun b _ => hg t b).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg fun b _ => hg t b) (hu t) 2)
  have he : binEnergy g ≤ k * (mass / k)^2 := calc
    _ = ∑ t, ∑ b, (g (t,b))^2 := Fintype.sum_prod_type _
    _ ≤ ∑ _ : T, (mass / k)^2 := Finset.sum_le_sum fun t _ => hb t
    _ = _ := by simp [k]
  rw [← Real.sqrt_mul hk.le, Real.sqrt_le_iff]
  refine ⟨hm, (mul_le_mul_of_nonneg_left he hk.le).trans_eq ?_⟩
  field_simp

/-- Cauchy–Schwarz turns the tile-normalized Euclidean estimate into a bound
on the total absolute error, with a constant depending only on the number of
relative addresses per tile. -/
theorem tile_l1_le {T : Type*} [Fintype T] (x : T × B → ℝ) :
    (∑ a, |x a|) ≤ Real.sqrt (Fintype.card B) *
      (Real.sqrt (Fintype.card T) * Real.sqrt (binEnergy x)) := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => |x a|)
  rw [Finset.card_univ, Fintype.card_prod, Nat.cast_mul] at h
  simp only [sq_abs] at h
  have hs := Real.le_sqrt_of_sq_le h
  simpa only [binEnergy, Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
    Real.sqrt_mul (Nat.cast_nonneg _), mul_assoc, mul_left_comm] using hs

end Epoch

end BorderVNP
end Computability
end OAI
