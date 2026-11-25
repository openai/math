import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.Expand
import OAI.LinearAlgebra.MatrixExponent.Sphere.Block
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryJets
import OAI.LinearAlgebra.MatrixExponent.Sphere.Private.Preparation

/-!
# Laurent reconstruction for moving insertions

Use a common denominator. At a point with pole bound `d`, remove
`(X-z)^d` from the denominator. Coefficient `i` of the resulting regular
quotient is Laurent coefficient `i-d`. The reconstruction weights do not
depend on the numerator, so they act simultaneously on every tensor entry.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Motion

open Polynomial
variable {K : Type*} [Field K]

/-- Polynomial denominator for the specified bounds at distinct marks. -/
def poles (s : Finset K) (d : K → ℕ) : K[X] := ∏ z ∈ s, (X - C z) ^ d z

theorem degree_poles (s : Finset K) (d : K → ℕ) :
    (poles s d).natDegree = ∑ z ∈ s, d z := by
  unfold poles
  rw [natDegree_prod_of_monic _ _ (fun z _ => (monic_X_sub_C z).pow _)]
  simp

theorem poles_eval {s : Finset K} {z : K} (d : K → ℕ) (h : z ∉ s) :
    (poles s d).eval z ≠ 0 := by
  rw [poles, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro t ht
  simp only [eval_pow, eval_sub, eval_X, eval_C]
  exact pow_ne_zero _ (sub_ne_zero.mpr (fun he => h (he ▸ ht)))

theorem poles_split [DecidableEq K] {s : Finset K} {z : K} (d : K → ℕ) (h : z ∈ s) :
    poles s d = (X - C z) ^ d z * poles (s.erase z) d :=
  (Finset.mul_prod_erase _ _ h).symm

/-- Coefficient of degree `i` in the regular quotient `p(z + X) / q(z + X)`. -/
def jet (z : K) (q : K[X]) (i : ℕ) : K[X] →ₗ[K] K where
  toFun p := PowerSeries.coeff i ((taylor z p : PowerSeries K) * (taylor z q : PowerSeries K)⁻¹)
  map_add' p p' := by simp only [map_add, Polynomial.coe_add, add_mul]
  map_smul' c p := by simp only [map_smul, Polynomial.coe_smul, smul_mul_assoc, RingHom.id_apply]

theorem jet_zero (z : K) (q p : K[X]) : jet z q 0 p = p.eval z / q.eval z := by
  unfold jet
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, taylor_coeff_zero, div_eq_mul_inv]

/-- Formal expansion of the quotient `p/q` at `z`. -/
def laurent (z : K) (p q : K[X]) : LaurentSeries K :=
  HahnSeries.ofPowerSeries ℤ K (taylor z p) / HahnSeries.ofPowerSeries ℤ K (taylor z q)

private theorem shifted_laurent (z : K) (p q : K[X]) (d : ℕ) (hq : q.eval z ≠ 0) :
    laurent z p ((X - C z) ^ d * q) = HahnSeries.single (-(d : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ K ((taylor z p : PowerSeries K) * (taylor z q : PowerSeries K)⁻¹) := by
  let f := HahnSeries.ofPowerSeries ℤ K
  let a : PowerSeries K := taylor z p
  let b : PowerSeries K := taylor z q
  have hb : PowerSeries.constantCoeff b ≠ 0 := by simpa [b, taylor_coeff_zero] using hq
  have inv : f b⁻¹ = (f b)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, PowerSeries.inv_mul_cancel b hb, map_one])
  have den : (taylor z ((X - C z) ^ d * q) : PowerSeries K) = PowerSeries.X ^ d * b := by
    simp [b]
  change laurent z p _ = _ * f (a * b⁻¹)
  unfold laurent
  rw [den, map_mul, HahnSeries.ofPowerSeries_X_pow, div_eq_mul_inv, mul_inv_rev,
    HahnSeries.inv_single, inv_one, map_mul, inv]
  change f a * ((f b)⁻¹ * _) = _
  ac_rfl

theorem coeff_below (z : K) (p q : K[X]) (d : ℕ) (hq : q.eval z ≠ 0) (j : ℤ) (hj : j < -(d : ℤ)) :
    (laurent z p ((X - C z) ^ d * q)).coeff j = 0 := by
  rw [shifted_laurent _ _ _ _ hq, HahnSeries.coeff_single_mul, one_mul,
    PowerSeries.coeff_coe, ite_eq_left (by omega)]

theorem coeff_laurent (z : K) (p q : K[X]) (d : ℕ) (hq : q.eval z ≠ 0) (i : ℕ) :
    (laurent z p ((X - C z) ^ d * q)).coeff ((i : ℤ) - d) = jet z q i p := by
  rw [shifted_laurent _ _ _ _ hq, sub_eq_add_neg, HahnSeries.coeff_single_mul_add, one_mul,
    HahnSeries.ofPowerSeries_apply_coeff]
  rfl

/-- Multiplying by the invertible regular denominator preserves vanishing
of the first `n` coefficients. -/
theorem dvd_of_jet {z : K} {p q : K[X]} (hq : q.eval z ≠ 0) {n : ℕ}
    (hv : ∀ i < n, jet z q i p = 0) : (X - C z) ^ n ∣ p := by
  let a : PowerSeries K := taylor z p
  let b : PowerSeries K := taylor z q
  have hb : PowerSeries.constantCoeff b ≠ 0 := by simpa [b, taylor_coeff_zero] using hq
  have h : PowerSeries.X ^ n ∣ a * b⁻¹ := PowerSeries.X_pow_dvd_iff.mpr hv
  have ha : PowerSeries.X ^ n ∣ a := by
    simpa only [mul_assoc, PowerSeries.inv_mul_cancel b hb, mul_one] using dvd_mul_of_dvd_left h b
  have hp : X ^ n ∣ taylor z p := by
    simpa only [X_pow_dvd_iff, PowerSeries.X_pow_dvd_iff, a, coeff_coe] using ha
  obtain ⟨w, hw⟩ := hp
  refine ⟨taylor (-z) w, ?_⟩
  simpa [taylor_taylor, sub_eq_add_neg] using congrArg (taylor (-z)) hw

theorem zero_of_jets (s : Finset K) (n : K → ℕ) (q : K → K[X]) (hq : ∀ z ∈ s, (q z).eval z ≠ 0)
    {p : K[X]} (hp : p.natDegree < ∑ z ∈ s, n z)
    (hv : ∀ z ∈ s, ∀ i < n z, jet z (q z) i p = 0) : p = 0 := by
  by_contra h
  have hd : poles s n ∣ p := by
    apply Finset.prod_dvd_of_coprime
    · exact fun _ _ _ _ he => (pairwise_coprime_X_sub_C Function.injective_id he).pow
    · exact fun z hz => dvd_of_jet (hq z hz) (hv z hz)
  exact (hp.not_ge (by simpa only [degree_poles] using natDegree_le_of_dvd hd h))

private theorem reconstruct {ι : Type*} [Fintype ι] (f : ι → K[X] →ₗ[K] K) (D : ℕ)
    (h : ∀ p : K[X], p.natDegree ≤ D → (∀ i, f i p = 0) → p = 0) (l : K[X] →ₗ[K] K) :
    ∃ c : ι → K, ∀ p : K[X], p.natDegree ≤ D → l p = ∑ i, c i * f i p := by
  classical
  let V := degreeLE K (D : WithBot ℕ)
  let e := LinearMap.pi (fun i => (f i).comp V.subtype)
  have hi : e.ker = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    apply Subtype.ext
    exact h x (natDegree_le_iff_degree_le.mpr (mem_degreeLE.mp x.property)) (congrFun hx)
  obtain ⟨g, hg⟩ := e.exists_leftInverse_of_injective hi
  let a := (l.comp V.subtype).comp g
  refine ⟨fun i => a (Pi.single i 1), fun p hp => ?_⟩
  let x : V := ⟨p, mem_degreeLE.mpr (natDegree_le_iff_degree_le.mp hp)⟩
  have hx : g (e x) = x := DFunLike.congr_fun hg x
  calc
    l p = a (e x) := by change l p = l (g (e x)); rw [hx]
    _ = ∑ i, a (Pi.single i (e x i)) := by rw [← map_sum, Finset.univ_sum_single]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have eqn : Pi.single i (e x i) = f i p • (Pi.single i (1 : K) : ι → K) := by
        ext j
        simp [Pi.single_apply, e, x, mul_ite]
      rw [eqn, map_smul, smul_eq_mul, mul_comm]

/-- More regular evaluations than the numerator degree suffice to recover
every linear coefficient, including every Laurent jet. -/
theorem reconstruct_regular (s : Finset K) (q : K[X]) (hq : ∀ z ∈ s, q.eval z ≠ 0)
    (D : ℕ) (hD : D < s.card) (l : K[X] →ₗ[K] K) :
    ∃ c : s → K, ∀ p : K[X], p.natDegree ≤ D →
      l p = ∑ z : s, c z * (p.eval z.val / q.eval z.val) := by
  have h (p : K[X]) (hp : p.natDegree ≤ D) (hv : ∀ z : s, jet z.val q 0 p = 0) : p = 0 := by
    apply zero_of_jets s (fun _ => 1) (fun _ => q) hq (by simpa using hp.trans_lt hD)
    intro z hz i hi
    have : i = 0 := by omega
    subst i
    exact hv ⟨z, hz⟩
  simpa only [jet_zero] using reconstruct (fun z : s => jet z.val q 0) D h l

/-- Regular evaluations recover even a specified coefficient at a pole. -/
theorem recover_coefficient (s : Finset K) (q : K[X]) (hq : ∀ z ∈ s, q.eval z ≠ 0)
    (D : ℕ) (hD : D < s.card) (y : K) (i : ℤ) :
    ∃ c : s → K, ∀ p : K[X], p.natDegree ≤ D →
      (laurent y p q).coeff i = ∑ z : s, c z * (p.eval z.val / q.eval z.val) := by
  let l : K[X] →ₗ[K] K :=
    { toFun := fun p => (laurent y p q).coeff i
      map_add' := by intros; simp [laurent, add_div]
      map_smul' := by
        intro c p
        simp only [laurent, taylor_mul, taylor_C, Polynomial.smul_eq_C_mul, Polynomial.coe_mul,
          Polynomial.coe_C, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, mul_div_assoc,
          HahnSeries.coeff_single_mul, sub_zero, smul_eq_mul, RingHom.id_apply] }
  exact reconstruct_regular s q hq D hD l

/-- The initial jets jointly determine any bounded-degree numerator
when their total length exceeds the degree bound. -/
theorem reconstruct_jets (s : Finset K) (n : K → ℕ) (q : K → K[X])
    (hq : ∀ z ∈ s, (q z).eval z ≠ 0) (D : ℕ) (hD : D < ∑ z ∈ s, n z) (l : K[X] →ₗ[K] K) :
    ∃ c : (Σ z : s, Fin (n z.val)) → K, ∀ p : K[X], p.natDegree ≤ D →
      l p = ∑ i, c i * jet i.1.val (q i.1.val) i.2.val p := by
  apply reconstruct
  intro p hp hv
  exact zero_of_jets s n q hq (hp.trans_lt hD) (fun z hz i hi => hv ⟨⟨z, hz⟩, ⟨i, hi⟩⟩)

/-- At seams keep orders through `-L`, at insertion marks through `-1`,
and at the designated collector through `g*L`. -/
def orders [DecidableEq K] (seams : Finset K) (collector : K) (d : K → ℕ) (g L : ℕ)
    (z : K) : ℕ :=
  if z ∈ seams then d z + 1 - L else d z + if z = collector then g * L + 1 else 0

omit [Field K] in
private theorem enough_orders [DecidableEq K] {s seams : Finset K} (hs : seams ⊆ s)
    {collector : K} (hc : collector ∈ s) (hc' : collector ∉ seams) (d : K → ℕ)
    {g : ℕ} (hg : seams.card ≤ g) (L : ℕ) :
    ∑ z ∈ s, d z < ∑ z ∈ s, orders seams collector d g L z := by
  have step (z : K) : d z + (if z = collector then g * L + 1 else 0) ≤
      orders seams collector d g L z + (if z ∈ seams then L else 0) := by
    unfold orders
    by_cases h : z ∈ seams
    · have hz : z ≠ collector := fun e => hc' (e ▸ h)
      simp only [ite_eq_left h, ite_eq_right hz, add_zero]
      omega
    · simp [h]
  have h := Finset.sum_le_sum (s := s) (fun z _ => step z)
  have he : s.filter (· ∈ seams) = seams := by ext z; simp [and_iff_right_of_imp (hs ·)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', ite_eq_left hc,
    ← Finset.sum_filter, he, Finset.sum_const, nsmul_eq_mul, Nat.cast_id] at h
  have := Nat.mul_le_mul_right L hg
  omega

/-- The same Laurent reconstruction weights work for all numerators bounded
at infinity after division by the common denominator. -/
theorem reconstruct_motion [DecidableEq K] {s seams : Finset K} (hs : seams ⊆ s)
    {collector : K} (hc : collector ∈ s) (hc' : collector ∉ seams) (d : K → ℕ)
    {g : ℕ} (hg : seams.card ≤ g) (L : ℕ) (x : K) :
    ∃ c : (Σ z : s, Fin (orders seams collector d g L z.val)) → K, ∀ p : K[X],
      p.natDegree ≤ (poles s d).natDegree →
      p.eval x / (poles s d).eval x =
        ∑ i, c i * (laurent i.1.val p (poles s d)).coeff ((i.2.val : ℤ) - d i.1.val) := by
  have hD := enough_orders hs hc hc' d hg L
  rw [← degree_poles] at hD
  obtain ⟨c, he⟩ := reconstruct_jets s _ (fun z => poles (s.erase z) d)
    (fun z _ => poles_eval d (Finset.notMem_erase z s)) _ hD (jet x (poles s d) 0)
  refine ⟨c, fun p hp => ?_⟩
  rw [← jet_zero, he p hp]
  apply Finset.sum_congr rfl
  intro i _
  rw [poles_split d i.1.property, coeff_laurent _ _ _ _ (poles_eval d (Finset.notMem_erase _ _))]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Motion
end

/-! # Reading Laurent coefficients in the doubled collision coordinate -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Motion

open Polynomial
variable {K : Type*} [Field K]

theorem expand_taylor (P : ℕ) (hP : P ≠ 0) (z : K) (p : K[X]) :
    PowerSeries.expand P hP (taylor z p : PowerSeries K) =
      (p.comp (X ^ P + C z) : PowerSeries K) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_comp]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial]
    simp [PowerSeries.expand_C]

theorem jet_of_dvd (z : K) (p q w : K[X]) (hq : q.eval z ≠ 0) (N i : ℕ) (hi : 2 * i < N)
    (he : X ^ N ∣ p.comp (X ^ 2 + C z) - q.comp (X ^ 2 + C z) * w) :
    jet z q i p = w.coeff (2 * i) := by
  let f := PowerSeries.expand (R := K) 2 (by decide)
  let a : PowerSeries K := taylor z p
  let b : PowerSeries K := taylor z q
  have hb : PowerSeries.constantCoeff b ≠ 0 := by simpa [b, taylor_coeff_zero] using hq
  have inv : f b * f b⁻¹ = 1 := by rw [← map_mul, PowerSeries.mul_inv_cancel b hb, map_one]
  have dvd : PowerSeries.X ^ N ∣ f a - f b * (w : PowerSeries K) := by
    obtain ⟨v, hv⟩ := he
    refine ⟨v, ?_⟩
    simpa only [a, b, f, expand_taylor, Polynomial.coe_sub, Polynomial.coe_mul,
      Polynomial.coe_pow, Polynomial.coe_X] using congrArg (fun t : K[X] => (t : PowerSeries K)) hv
  have dvd' : PowerSeries.X ^ N ∣ f (a * b⁻¹) - (w : PowerSeries K) := by
    have e := dvd_mul_of_dvd_left dvd (f b⁻¹)
    rwa [sub_mul, mul_right_comm (f b), inv, one_mul, ← map_mul] at e
  have h := PowerSeries.X_pow_dvd_iff.mp dvd' (2 * i) hi
  change PowerSeries.coeff i (a * b⁻¹) = _
  simpa only [map_sub, sub_eq_zero, f, PowerSeries.coeff_expand_mul, coeff_coe] using h

end OAI.LinearAlgebra.MatrixExponent.Sphere.Motion
end

/-!
# Coupled motion in two coordinates

The two parameters are `z^P` and `z`, with `P` a characteristic
power. Pole bounds make the convolution at each order a finite sum.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Motion

open Polynomial
variable {K : Type*} [Field K]

def coupled (P : ℕ) (a b : K[X]) : K[X] := a.comp (X ^ P) * b

def pairs (P d e : ℕ) (j : ℤ) : Finset (ℤ × ℤ) :=
  let n := j + P * d + e
  if n < 0 then ∅ else
    ((Finset.range (n.toNat + 1)).filter (P ∣ ·)).image
      (fun i => (((i / P : ℕ) : ℤ) - d, n - i - e))

theorem mem_pairs {P d e : ℕ} {j : ℤ} {x : ℤ × ℤ} (h : x ∈ pairs P d e j) :
    P * x.1 + x.2 = j ∧ -(d : ℤ) ≤ x.1 ∧ -(e : ℤ) ≤ x.2 := by
  unfold pairs at h
  dsimp only at h
  split_ifs at h with he
  · simp at h
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  have he' : (P : ℤ) * ((i / P : ℕ) : ℤ) = i := by
    exact_mod_cast Nat.mul_div_cancel' hi.2
  simp only [mul_sub, he']
  have : 0 ≤ ((i / P : ℕ) : ℤ) := Int.natCast_nonneg _
  omega

def regular (z : K) (a b : K[X]) : PowerSeries K :=
  (taylor z a : PowerSeries K) * (taylor z b : PowerSeries K)⁻¹

theorem regular_mul (z : K) (a b : K[X]) (h : b.eval z ≠ 0) :
    regular z a b * (taylor z b : PowerSeries K) = taylor z a := by
  rw [regular, mul_assoc, PowerSeries.inv_mul_cancel, mul_one]
  simpa [taylor_coeff_zero] using h

variable (p l : ℕ) [ExpChar K p]

private theorem taylor_coupled (z : K) (a b : K[X]) :
    (taylor z (coupled (p ^ l) a b) : PowerSeries K) =
      PowerSeries.expand (p ^ l) (expChar_pow_pos K p l).ne'
        (taylor (z ^ (p ^ l)) a : PowerSeries K) * (taylor z b : PowerSeries K) := by
  rw [expand_taylor, coupled, taylor_mul, Polynomial.coe_mul, taylor_apply, comp_assoc,
    pow_comp, X_comp, add_pow_expChar_pow, map_pow]

private theorem regular_coupled (z : K) (a b c d : K[X])
    (hb : b.eval (z ^ (p ^ l)) ≠ 0) (hd : d.eval z ≠ 0) :
    regular z (coupled (p ^ l) a c) (coupled (p ^ l) b d) =
      PowerSeries.expand (p ^ l) (expChar_pow_pos K p l).ne' (regular (z ^ (p ^ l)) a b) *
        regular z c d := by
  have he : (coupled (p ^ l) b d).eval z ≠ 0 := by simp [coupled, hb, hd]
  have ht : (taylor z (coupled (p ^ l) b d) : PowerSeries K) ≠ 0 := by
    intro hh
    apply he
    simpa only [constantCoeff_coe, taylor_coeff_zero, map_zero] using congrArg PowerSeries.constantCoeff hh
  apply mul_right_cancel₀ ht
  rw [regular_mul _ _ _ he, taylor_coupled p l, taylor_coupled p l,
    mul_mul_mul_comm, ← map_mul, regular_mul _ _ _ hb, regular_mul _ _ _ hd]

theorem coupled_poles (z : K) (q₁ q₂ : K[X]) (d e : ℕ) :
    coupled (p ^ l) ((X - C (z ^ (p ^ l))) ^ d * q₁) ((X - C z) ^ e * q₂) =
      (X - C z) ^ (p ^ l * d + e) * coupled (p ^ l) q₁ q₂ := by
  unfold coupled
  rw [mul_comp, pow_comp, sub_comp, X_comp, C_comp, map_pow, ← sub_pow_expChar_pow,
    ← pow_mul, mul_mul_mul_comm, ← pow_add]

/-- Convolve the two Laurent expansions. The first coordinate moves at
`p^l` times the order of the second. No choice of numerator enters the
summation range. -/
theorem coupled_coeff (z : K) (a b q₁ q₂ : K[X]) (d e : ℕ)
    (h₁ : q₁.eval (z ^ (p ^ l)) ≠ 0) (h₂ : q₂.eval z ≠ 0) (j : ℤ) :
    let P := p ^ l
    let Q₁ := (X - C (z ^ P)) ^ d * q₁
    let Q₂ := (X - C z) ^ e * q₂
    (laurent z (coupled P a b) (coupled P Q₁ Q₂)).coeff j =
      ∑ v ∈ pairs P d e j, (laurent (z ^ P) a Q₁).coeff v.1 * (laurent z b Q₂).coeff v.2 := by
  intro P Q₁ Q₂
  have hq : (coupled P q₁ q₂).eval z ≠ 0 := by simp [coupled, P, h₁, h₂]
  have eqn : coupled P Q₁ Q₂ = (X - C z) ^ (P * d + e) * coupled P q₁ q₂ :=
    coupled_poles p l z q₁ q₂ d e
  rw [eqn]
  let n : ℤ := j + P * d + e
  by_cases low : n < 0
  · rw [coeff_below _ _ _ _ hq _ (by unfold n at low; push_cast; omega)]
    rw [pairs, ite_eq_left low, Finset.sum_empty]
  have hn : ((n.toNat : ℕ) : ℤ) - (P * d + e : ℕ) = j := by dsimp [n] at *; omega
  have hl := coeff_laurent z (coupled P a b) (coupled P q₁ q₂) (P * d + e) hq n.toNat
  rw [hn] at hl
  rw [hl]
  change PowerSeries.coeff n.toNat (regular z (coupled P a b) (coupled P q₁ q₂)) = _
  rw [regular_coupled p l z a q₁ b q₂ h₁ h₂, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [PowerSeries.coeff_expand, ite_mul, zero_mul, ← Finset.sum_filter]
  have he : Function.Injective (fun i : ℕ => (((i / P : ℕ) : ℤ) - d, n - i - e)) := by
    intro x y h
    have h' := congrArg Prod.snd h
    dsimp only at h'
    omega
  rw [pairs, ite_eq_right low, Finset.sum_image he.injOn]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  change _ = (laurent _ a Q₁).coeff (((i / P : ℕ) : ℤ) - d) * (laurent z b Q₂).coeff (n - i - e)
  have hi' : n - i = ((n.toNat - i : ℕ) : ℤ) := by omega
  rw [hi', coeff_laurent _ _ _ _ h₁, coeff_laurent _ _ _ _ h₂]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Motion
end

/-!
# Two-site fusion

Specialize the cluster expansion to offsets zero and one. Pairing the
translated modes with the reversed output wedge gives the matrix entry
used in transposition at a seam.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

variable {F R : Type*} [Field F] [CommRing R] [Algebra F R] {r : ℕ}

def offsets (F : Type*) [Field F] (a x : List (Mode r)) : List (Site F r) :=
  a.map (0, ·) ++ x.map (1, ·)

private def place (F : Type*) [Field F] : Mark r → Site F r ⊕ Mode r
  | (.origin, x) => .inl (0, x)
  | (.middle, x) => .inl (1, x)
  | (_, x) => .inr x

theorem translate_zero (x y : Mode r) :
    translate ((0 : F), x) y = if x = y then 1 else 0 := by
  unfold translate
  by_cases hs : x.1 = y.1
  · simp only [Prod.ext_iff, hs, true_and, ↓reduceIte]
    rcases lt_trichotomy x.2 y.2 with h | h | h
    · simp [h.ne, zero_pow (Nat.sub_ne_zero_of_lt h)]
    · simp [h]
    · simp [h.ne', Nat.choose_eq_zero_of_lt h]
  · simp [Prod.ext_iff, hs]

private theorem block_place (x y : Mark r) (hx : x.1 ≠ .dual) (hy : y.1 ≠ .dual) :
    blockPair (place F x) (place F y) = pairing F x y := by
  obtain ⟨s, x⟩ := x
  obtain ⟨t, y⟩ := y
  cases s <;> cases t <;> try contradiction
  all_goals
    simp only [place, blockPair, translate_zero]
  case middle.origin =>
    rw [fieldKernel_skew (0, y) (1, x), pairing_skew F (.origin, y) (.middle, x)]
    simp [fieldKernel, coeff, pairing]
    rfl
  all_goals
    by_cases h : x.1 = y.1 <;>
      simp [fieldKernel, coeff, translate, pairing, Prod.ext_iff, h, eq_comm, pow_succ]
  all_goals rfl

theorem blockCoeff_offsets (a x : List (Mode r)) (b : Wedge r) :
    blockCoeff (offsets F a x) b = fusion F a x b.val := by
  let xs := marks .origin a ++ marks .middle x ++ marks .infinity b.val.reverse
  have h : ∀ z ∈ xs, z.1 ≠ .dual := by
    simp only [xs, marks, List.forall_mem_append, List.forall_mem_map]
    simp
  have e : (offsets F a x).map Sum.inl ++ b.val.reverse.map Sum.inr = xs.map (place F) := by
    simp [xs, marks, offsets, List.map_map, Function.comp_def, place]
  unfold blockCoeff fusion
  rw [e, wick_map]
  exact wick_eq_on _ _ _ (fun z hz t ht => block_place z t (h z hz) (h t ht))

/-- Two sites at `c` and `c + u²`, scaled by `u` to their doubled
energies to remove the pole. Spectators stay at fixed positions. -/
def collision (c : F) (u : R) (N : ℕ) (a x : List (Mode r)) (ys : List (Site F r)) : R :=
  wick (Cluster.pair u N) ((offsets F a x).map (.moving c) ++ ys.map .fused)

/-- Exact through degree `N-1`, with no invertibility assumption on two. -/
theorem fusion_expansion (c : F) (u : R) (N : ℕ) (hu : u ^ N = 0)
    (a x : List (Mode r)) (ys : List (Site F r)) :
    collision c u N a x ys =
      ∑ b : LevelLE r N, u ^ energy b.val.val * algebraMap F R (fusion F a x b.val.val) *
        algebraMap F R (wick fieldKernel (b.val.val.map (c, ·) ++ ys)) := by
  have h := Cluster.block u N c hu (offsets F a x) [] (ys.map .fused)
    (by simp) (by simp only [List.forall_mem_map, Cluster.belongs, not_false_eq_true, implies_true])
  simp only [List.nil_append, blockCoeff_offsets] at h
  rw [collision, h]
  apply Finset.sum_congr rfl
  intro b _
  have e := wick_map (Cluster.pair u N) Cluster.Leg.fused (b.val.val.map (c, ·) ++ ys)
  simpa only [List.map_append, List.map_map, Function.comp_def, Cluster.pair, wick_hom]
    using congrArg (fun t => u ^ energy b.val.val * algebraMap F R (fusion F a x b.val.val) * t) e

end OAI.LinearAlgebra.MatrixExponent.Sphere
end

/-!
# Moving one insertion on a sphere

The affine trajectories consist of the identity and the constant maps
to the stationary marks. Clearing the finite collisions gives a numerator
whose degree does not exceed the denominator degree.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Motion

open Polynomial Routing
open scoped Classical
variable {F : Type} {R : Type*} [Field F] [CommRing R] [Algebra F R] {r : ℕ}

def trajectories (s : Finset F) : Option s → Fin 2 → F
  | none => ![1, 0]
  | some z => ![0, z.val]

def direction (z : F) := some (-z)

private theorem injective_direction : Function.Injective (direction (F := F)) :=
  fun _ _ h => neg_injective (Option.some.inj h)

theorem directions_eq (s : Finset F) :
    directions (trajectories s) = insert none (s.image direction) := by
  ext d
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with he | h
    · exact Finset.mem_insert.mpr (.inl he)
    obtain ⟨_, hl, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hl
    cases i <;> cases j <;> simp [trajectories, through, direction, div_neg]
  · intro h
    rcases Finset.mem_insert.mp h with he | h
    · simp [he, directions]
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
    simpa [pole, through, trajectories, direction] using
      pole_mem (trajectories s) none (some ⟨z, hz⟩)

private theorem none_not_mem (s : Finset F) : none ∉ s.image direction := by
  simp [direction]

theorem denominator_eq (s : Finset F) (x : R) :
    denominator (directions (trajectories s)) x 1 =
      ∏ z ∈ s, (x - algebraMap F R z) := by
  rw [directions_eq, denominator, Finset.prod_insert (none_not_mem s),
    Finset.prod_image injective_direction.injOn]
  simp [linearFactor, direction, sub_eq_add_neg]

theorem erase_direction (s : Finset F) (x : F) :
    (directions (trajectories s)).erase (some (-x)) = directions (trajectories (s.erase x)) := by
  rw [directions_eq, directions_eq]
  ext y
  simp [direction]
  grind

def numerator (s : Finset F) (xs : List (Option s × Mode r)) : F[X] :=
  correlatorPoly (trajectories s) X 1 xs

def denominatorPoly (s : Finset F) (xs : List (Option s × Mode r)) : F[X] :=
  poles s (fun _ => weight xs / 2)

theorem degree_numerator (s : Finset F) (xs : List (Option s × Mode r)) :
    (numerator s xs).natDegree ≤ (denominatorPoly s xs).natDegree := by
  have h := (correlator_form (trajectories s) xs).1
  rw [directions_eq, Finset.card_insert_of_notMem (none_not_mem s),
    Finset.card_image_of_injective _ injective_direction] at h
  simpa [numerator, denominatorPoly, degree_poles] using h

theorem aeval_poles (s : Finset F) (e : ℕ) (x : R) :
    aeval x (poles s (fun _ => e)) = denominator (directions (trajectories s)) x 1 ^ e := by
  simp only [poles, map_prod, map_pow, map_sub, aeval_X, aeval_C, denominator_eq, Finset.prod_pow]

/-- Place the moving insertion at an arbitrary extension-field point. -/
def atPoint {E : Type*} [Field E] [Algebra F E] {s : Finset F}
    (x : E) (j : Option s × Mode r) : Site E r :=
  (j.1.elim x (fun z => algebraMap F E z.val), j.2)

/-- This specialization is valid even at a transcendental point over a
finite field. -/
theorem eval_sphere_over {E : Type*} [Field E] [Algebra F E] (s : Finset F)
    (xs : List (Option s × Mode r)) (x : E) (hx : ∀ z ∈ s, x ≠ algebraMap F E z) :
    aeval x (numerator s xs) / aeval x (denominatorPoly s xs) =
      wick fieldKernel (xs.map (atPoint x)) := by
  have hd : denominator (directions (trajectories s)) x 1 ≠ 0 := by
    rw [denominator_eq]
    exact Finset.prod_ne_zero_iff.mpr fun z hz => sub_ne_zero.mpr (hx z hz)
  have hp (z : Option s) : position (trajectories s z) x 1 =
      z.elim x (fun t => algebraMap F E t.val) := by
    cases z <;> simp [position, trajectories]
  rw [wick_map, numerator, denominatorPoly, aeval_poles, correlator_map, aeval_X, map_one,
    correlator_specialize _ _ _ hd, mul_div_cancel_left₀ _ (pow_ne_zero _ hd)]
  simp only [hp, atPoint]

theorem eval_sphere (s : Finset F) (xs : List (Option s × Mode r)) (x : F) (hx : x ∉ s) :
    (numerator s xs).eval x / (denominatorPoly s xs).eval x =
      wick fieldKernel (xs.map (atPoint x)) := by
  have hr : ∀ z ∈ s, x ≠ algebraMap F F z := by
    intro z hz h
    exact hx (h ▸ hz)
  simpa only [coe_aeval_eq_eval] using eval_sphere_over s xs x hr

end OAI.LinearAlgebra.MatrixExponent.Sphere.Motion
end

/-!
# Laurent coefficients of a moving insertion

At a collision with a stationary mark only the two incident blocks are
fused. All other marks are spectators. Remove their weight and the
regular denominator from the truncated polynomial identity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Motion

open Polynomial Routing
open scoped Classical
variable {F R : Type} [Field F] [CommRing R] [Algebra F R] {r : ℕ} {s : Finset F}

/-- Stationary modes, moving modes, then spectators. -/
def triple (c : s) (a x : List (Mode r)) (ys : List (s × Mode r)) :
    List (Option s × Mode r) :=
  a.map (some c, ·) ++ x.map (none, ·) ++ ys.map (fun y => (some y.1, y.2))

def spectators (ys : List (s × Mode r)) : List (Site F r) := ys.map (fun y => (y.1.val, y.2))

private def leg (c : s) : Option s × Mode r → Cluster.Leg F r
  | (none, i) => .moving c.val (1, i)
  | (some d, i) => if d = c then .moving c.val (0, i) else .fused (d.val, i)

private def scale (u : R) (c : s) : Option s × Mode r → R
  | (none, _) => 1
  | (some d, i) => if d = c then 1 else Cluster.weight u i

private theorem moving_fixed (u : R) (N : ℕ) (c d : F) (x : Site F r) (y : Mode r)
    (h : c ≠ d) :
    Cluster.pair u N (.moving c x) (.moving d (0, y)) =
      Cluster.weight u y * Cluster.pair u N (.moving c x) (.fused (d, y)) := by
  simp only [Cluster.pair, h, ↓reduceIte, mul_assoc, mul_left_comm]

private theorem fixed_moving (u : R) (N : ℕ) (c d : F) (x : Site F r) (y : Mode r)
    (h : c ≠ d) :
    Cluster.pair u N (.moving d (0, y)) (.moving c x) =
      Cluster.weight u y * Cluster.pair u N (.fused (d, y)) (.moving c x) := by
  rw [Cluster.pair_skew u N (.moving c x), moving_fixed _ _ _ _ _ _ h,
    Cluster.pair_skew u N (.moving c x), mul_neg]

private theorem both_fixed (u : R) (N : ℕ) (hu : u ^ N = 0) (c d : F) (x y : Mode r) :
    Cluster.pair u N (.moving c (0, x)) (.moving d (0, y)) =
      Cluster.weight u x * Cluster.weight u y * Cluster.pair u N (.fused (c, x)) (.fused (d, y)) := by
  by_cases h : c = d
  · simp [Cluster.pair, h, fieldKernel, Sphere.coeff]
  · have hs (z : R) : shifted u z 0 N = z := by simpa using shifted_mul u z 0 N hu
    simp only [Cluster.pair, h, ↓reduceIte, Cluster.sep, sub_self, map_zero, hs, fieldKernel]
    unfold Sphere.coeff
    split <;> simp only [map_pow, map_mul, map_natCast, map_zero, map_one, map_neg]

private theorem normalized_kernel (u : R) (N : ℕ) (hu : u ^ N = 0) (c : s)
    (x y : Option s × Mode r) :
    clusterKernel u N (fun i => projection (trajectories s i) (some (-c.val)))
      (fun i => collisionOffset (trajectories s i) (some (-c.val))) x y =
        scale u c x * scale u c y * Cluster.pair u N (leg c x) (leg c y) := by
  have eq (x y : Option s × Mode r) :
      clusterKernel u N (fun i => projection (trajectories s i) (some (-c.val)))
        (fun i => collisionOffset (trajectories s i) (some (-c.val))) x y =
      Cluster.pair u N
        (.moving (projection (trajectories s x.1) (some (-c.val)))
          (collisionOffset (trajectories s x.1) (some (-c.val)), x.2))
        (.moving (projection (trajectories s y.1) (some (-c.val)))
          (collisionOffset (trajectories s y.1) (some (-c.val)), y.2)) :=
    by rw [Cluster.pair_moving]; rfl
  rw [eq]
  rcases x with ⟨_|d, x⟩ <;> rcases y with ⟨_|e, y⟩ <;>
    simp [collisionOffset, projection, trajectories, leg, scale]
  · split_ifs with he
    · simp [he]
    · exact moving_fixed u N _ _ _ _ (Subtype.val_injective.ne (Ne.symm he))
  · split_ifs with hd
    · simp [hd]
    · exact fixed_moving u N _ _ _ _ (Subtype.val_injective.ne (Ne.symm hd))
  · by_cases hd : d = c <;> by_cases he : e = c <;> simp [hd, he]
    · exact moving_fixed u N _ _ _ _ (Subtype.val_injective.ne (Ne.symm he))
    · exact fixed_moving u N _ _ _ _ (Subtype.val_injective.ne (Ne.symm hd))
    · exact both_fixed u N hu _ _ _ _

private theorem normalized_wick (u : R) (N : ℕ) (hu : u ^ N = 0) (c : s)
    (a x : List (Mode r)) (ys : List (s × Mode r)) (hy : ∀ y ∈ ys, y.1 ≠ c) :
    wick (clusterKernel u N (fun i => projection (trajectories s i) (some (-c.val)))
      (fun i => collisionOffset (trajectories s i) (some (-c.val)))) (triple c a x ys) =
      u ^ weight ys * collision c.val u N a x (spectators ys) := by
  have fixed :
      (ys.map (fun y => scale u c (some y.1, y.2))).prod = u ^ weight ys ∧
      ys.map (fun y => leg c (some y.1, y.2)) = (spectators ys).map .fused := by
    induction ys with
    | nil => simp [weight, energy, spectators]
    | cons y ys ih =>
      simp only [List.forall_mem_cons] at hy
      obtain ⟨e, t⟩ := ih hy.2
      simp only [List.map_cons, List.prod_cons, weight_cons, pow_add, e, t]
      simp [leg, scale, hy.1, spectators, Cluster.weight, pow_add]
  rw [wick_eq_on _ _ _ (fun z _ t _ => normalized_kernel u N hu c z t), wick_scale_rows,
    ← wick_map]
  simp only [triple, List.map_append, List.map_map, List.prod_append, Function.comp_def, fixed.1, fixed.2]
  simp [leg, scale, collision, offsets, List.map_map, Function.comp_def]

private theorem local_numerator (u : R) (N : ℕ) (hu : u ^ N = 0) (c : s)
    (a x : List (Mode r)) (ys : List (s × Mode r)) (hy : ∀ y ∈ ys, y.1 ≠ c) :
    let xs := triple c a x ys
    let z := u ^ 2 + algebraMap F R c.val
    aeval z (numerator s xs) =
      aeval z (poles (s.erase c.val) (fun _ => weight xs / 2)) *
        (u ^ weight ys * collision c.val u N a x (spectators ys)) := by
  intro xs z
  have hd : some (-c.val) ∈ directions (trajectories s) := by
    rw [directions_eq]
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ c.property)
  have h := local_correlator (trajectories s) _ hd u N hu (triple c a x ys)
  simp only [localX, localY, map_neg, sub_neg_eq_add, erase_direction,
    normalized_wick u N hu c a x ys hy] at h
  rw [numerator, correlator_map, aeval_X, map_one, aeval_poles]
  exact h

def outcome (c : F) (a x : List (Mode r)) (ys : List (Site F r)) (b : Wedge r) : F :=
  fusion F a x b.val * wick fieldKernel (b.val.map (c, ·) ++ ys)

private def series (c : s) (a x : List (Mode r)) (ys : List (s × Mode r)) (N : ℕ) : F[X] :=
  ∑ b : LevelLE r N, X ^ (weight ys + energy b.val.val) * C (outcome c.val a x (spectators ys) b.val)

private theorem local_dvd (c : s) (a x : List (Mode r)) (ys : List (s × Mode r))
    (hy : ∀ y ∈ ys, y.1 ≠ c) (N : ℕ) :
    let xs := triple c a x ys
    let z := X ^ 2 + C c.val
    X ^ N ∣ (numerator s xs).comp z -
      (poles (s.erase c.val) (fun _ => weight xs / 2)).comp z * series c a x ys N := by
  intro xs z
  let u := jetVar F N
  have hu : u ^ N = 0 := jetVar_pow F N
  have em : AdjoinRoot.mkₐ (X ^ N : F[X]) = aeval u := by ext; simp [u, jetVar]
  apply AdjoinRoot.mk_eq_mk.mp
  change AdjoinRoot.mkₐ (X ^ N) _ = AdjoinRoot.mkₐ (X ^ N) _
  rw [em, map_mul, aeval_comp, aeval_comp]
  simp only [z, map_add, map_pow, aeval_X, aeval_C]
  rw [local_numerator u N hu c a x ys hy, fusion_expansion _ _ _ hu]
  congr 1
  simp only [series, map_sum, map_mul, map_pow, aeval_X, aeval_C, outcome, Finset.mul_sum, pow_add,
    mul_assoc]

/-- Laurent coefficient at order `i - H`, with common pole bound `H`.
The degree `2*i` includes the fixed weight of the spectators. -/
private theorem coeff_fusion_truncated (c : s) (a x : List (Mode r)) (ys : List (s × Mode r))
    (hy : ∀ y ∈ ys, y.1 ≠ c) (i N : ℕ) (hi : 2 * i < N) :
    let xs := triple c a x ys
    (laurent c.val (numerator s xs) (denominatorPoly s xs)).coeff
        ((i : ℤ) - (weight xs / 2 : ℕ)) =
      ∑ b : LevelLE r N, if weight ys + energy b.val.val = 2 * i
        then outcome c.val a x (spectators ys) b.val else 0 := by
  intro xs
  let d : F → ℕ := fun _ => weight xs / 2
  have hq : (poles (s.erase c.val) d).eval c.val ≠ 0 :=
    poles_eval d (Finset.notMem_erase _ _)
  rw [denominatorPoly, poles_split d c.property, coeff_laurent _ _ _ _ hq,
    jet_of_dvd _ _ _ _ hq N i hi (local_dvd c a x ys hy N)]
  simp [series, Polynomial.finsetSum_coeff, eq_comm]

omit [Field F] in
theorem weight_triple (c : s) (a x : List (Mode r)) (ys : List (s × Mode r)) :
    weight (triple c a x ys) = energy a + energy x + weight ys := by
  simp [triple, weight, energy, List.map_map, Function.comp_def, add_assoc]

private theorem outcome_odd (c : s) (a x : List (Mode r)) (ys : List (s × Mode r))
    (h : weight (triple c a x ys) % 2 = 1) (b : Wedge r) :
    outcome c.val a x (spectators ys) b = 0 := by
  have e := energy_mod_two ((triple c a x ys).map Prod.snd)
  change weight (triple c a x ys) % 2 = _ at e
  rw [h] at e
  simp only [triple, List.length_append, List.length_map] at e
  unfold outcome
  by_cases hb : (a.length + x.length + b.val.length) % 2 = 1
  · have : fusion F a x b.val = 0 := by
      apply wick_odd
      simpa only [marks, List.length_append, List.length_map, List.length_reverse] using hb
    rw [this, zero_mul]
  · have : wick fieldKernel (b.val.map (c.val, ·) ++ spectators ys) = 0 := by
      apply wick_odd
      simp only [spectators, List.length_append, List.length_map]
      omega
    rw [this, mul_zero]

private theorem sum_level (e N : ℕ) (he : e ≤ N) (f : Wedge r → F) :
    (∑ b : LevelLE r N, if energy b.val.val = e then f b.val else 0) =
      ∑ b : Level r e, f b.val := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun b hb => ⟨b.val, (Finset.mem_filter.mp hb).2⟩)
    (fun _ _ => Finset.mem_univ _) ?_ ?_ (fun _ _ => rfl)
  · intro b _ d _ h
    exact Subtype.ext (congrArg (fun b : Level r e => b.val) h)
  · intro b _
    exact ⟨⟨b.val, b.property.le.trans he⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.property⟩, rfl⟩

/-- At Laurent order `j` the two colliding states fuse through precisely
doubled energy `energy a + energy x + 2*j`, independently of the spectators. -/
theorem coeff_fusion (c : s) (a x : List (Mode r)) (ys : List (s × Mode r))
    (hy : ∀ y ∈ ys, y.1 ≠ c) (j : ℤ) :
    let xs := triple c a x ys
    let e := (energy a : ℤ) + energy x + 2 * j
    (laurent c.val (numerator s xs) (denominatorPoly s xs)).coeff j =
      if e < 0 then 0 else ∑ b : Level r e.toNat, outcome c.val a x (spectators ys) b.val := by
  intro xs e
  have hw : weight xs = energy a + energy x + weight ys := weight_triple c a x ys
  let d := weight xs / 2
  by_cases low : j < -(d : ℤ)
  · have he : e < 0 := by dsimp [e, d] at *; omega
    rw [ite_eq_left he, denominatorPoly, poles_split _ c.property]
    exact coeff_below _ _ _ _ (poles_eval _ (Finset.notMem_erase _ _)) _ low
  let i := (j + d).toNat
  let N := 2 * i + 1
  have hj : j = (i : ℤ) - (weight xs / 2 : ℕ) := by unfold i d at *; omega
  rw [hj, coeff_fusion_truncated c a x ys hy i N (by omega)]
  by_cases odd : weight xs % 2 = 1
  · simp only [outcome_odd c a x ys odd, ite_self, Finset.sum_const_zero]
  have hE : e + weight ys = 2 * i := by unfold e; omega
  by_cases neg : e < 0
  · rw [ite_eq_left neg]
    exact Finset.sum_eq_zero (fun b _ => ite_eq_right (by omega))
  rw [ite_eq_right neg, ← sum_level _ N (by omega)]
  apply Finset.sum_congr rfl
  intro b _
  simp only [show weight ys + energy b.val.val = 2 * i ↔ energy b.val.val = e.toNat by omega]

/-- Reconstruct the fusion coefficient from regular evaluations. The
weights depend only on the marks, pole bound, and coefficient index. -/
theorem recover_fusion (c : s) (T : Finset F) (hT : Disjoint T s) (H : ℕ)
    (hH : s.card * H < T.card) (j : ℤ) :
    ∃ f : T → F, ∀ (a x : List (Mode r)) (ys : List (s × Mode r)),
      (∀ y ∈ ys, y.1 ≠ c) → weight (triple c a x ys) / 2 = H →
      let e := (energy a : ℤ) + energy x + 2 * j
      (if e < 0 then 0 else ∑ b : Level r e.toNat, outcome c.val a x (spectators ys) b.val) =
        ∑ z : T, f z * wick fieldKernel ((triple c a x ys).map (atPoint z.val)) := by
  let q := poles s (fun _ => H)
  have hq (z : F) (hz : z ∈ T) : q.eval z ≠ 0 :=
    poles_eval _ (Finset.disjoint_left.mp hT hz)
  obtain ⟨f, hf⟩ := recover_coefficient T q hq q.natDegree (by simpa [q, degree_poles] using hH)
    c.val j
  refine ⟨f, fun a x ys hy he => ?_⟩
  let xs := triple c a x ys
  have e : denominatorPoly s xs = q := by unfold denominatorPoly; rw [he]
  rw [← e] at hf
  dsimp only
  rw [← coeff_fusion c a x ys hy j, hf _ (degree_numerator s xs)]
  exact Finset.sum_congr rfl fun z _ =>
    congrArg (f z * ·) (eval_sphere s xs z.val (Finset.disjoint_left.mp hT z.property))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Motion
end
