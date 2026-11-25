import OAI.LinearAlgebra.MatrixExponent.Spectrum.Comparison
import OAI.LinearAlgebra.MatrixExponent.Integral.Nodes
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.FreeModule.PID
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Dual
import OAI.LinearAlgebra.MatrixExponent.Integral.WeightedGrowth
import OAI.LinearAlgebra.MatrixExponent.Integral.Upper.Character.Rank
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Support
import OAI.LinearAlgebra.MatrixExponent.Growth

section
/-! Strict comparison for two elements that dominate the unit. -/

namespace OAI.LinearAlgebra.MatrixExponent.Integral
open scoped NNReal
variable {S : Type*} [CommSemiring S] [PartialOrder S]

/-- On the subsemiring of zero and the elements dominating one, every
nonzero element dominates one. Characters extend by translating by one. -/
theorem strictComparison [Nontrivial S]
    (hadd : ∀ a b c : S, a ≤ b → a + c ≤ b + c)
    (hmul : ∀ a b c : S, a ≤ b → c * a ≤ c * b)
    {x y : S} (hzero : ∀ a : S, 0 ≤ a) (hbound : ∀ a : S, ∃ n : ℕ, a ≤ (n : S))
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (h : ∀ f : S →+* ℝ≥0, Monotone f → f x < f y) :
    ∃ C : ℕ, ∀ r : ℕ, x ^ r ≤ (C : S) * y ^ r := by
  have grow (a b : S) : b ≤ a + b := by simpa using hadd 0 a b (hzero a)
  let T : Subsemiring S :=
    { carrier := {a | a = 0 ∨ 1 ≤ a}
      zero_mem' := .inl rfl
      one_mem' := .inr le_rfl
      add_mem' := by
        rintro a b ha (rfl | hb)
        · simpa using ha
        · exact .inr (hb.trans (grow a b))
      mul_mem' := by
        rintro a b (rfl | ha) hb
        · exact .inl (zero_mul _)
        rcases hb with rfl | hb
        · exact .inl (mul_zero _)
        · exact .inr (ha.trans (by simpa using hmul 1 b a hb)) }
  let X : T := ⟨x, .inr hx⟩
  let Y : T := ⟨y, .inr hy⟩
  have hn : Y ≠ 0 := by
    intro he
    have : y = 0 := congrArg Subtype.val he
    exact one_ne_zero (le_antisymm (this ▸ hy) (hzero 1))
  have cmp (f : T →+* ℝ≥0) (hf : Monotone f) : f X < f Y := by
    let up (a : S) : T := ⟨a + 1, .inr (grow a 1)⟩
    let g (a : S) := f (up a) - 1
    have plus (a : S) : g a + 1 = f (up a) :=
      tsub_add_cancel_of_le (by simpa using hf (show 1 ≤ up a from grow a 1))
    have ext (a : T) : g a = f a := by simp [g, show up a = a + 1 from rfl]
    have add (a b : S) : g (a + b) = g a + g b := by
      have e : up (a + b) + 1 = up a + up b := Subtype.ext (by change a + b + 1 + 1 = (a + 1) + (b + 1); ring)
      have e' := congrArg f e
      simp only [map_add, map_one, ← plus] at e'
      exact add_right_cancel (add_right_cancel (e'.trans (by ring)))
    have mul (a b : S) : g (a * b) = g a * g b := by
      have e : up (a * b + a + b) = up a * up b :=
        Subtype.ext (by change a * b + a + b + 1 = (a + 1) * (b + 1); ring)
      have e' := congrArg f e
      simp only [map_mul, ← plus, add] at e'
      exact add_right_cancel (add_right_cancel (add_right_cancel (e'.trans (by ring))))
    let G : S →+* ℝ≥0 :=
      { toFun := g
        map_add' := add
        map_mul' := mul
        map_one' := (ext 1).trans (map_one f)
        map_zero' := (ext 0).trans (map_zero f) }
    have hm : Monotone G :=
      fun _ _ hab => tsub_le_tsub_right (hf (hadd _ _ 1 hab)) _
    rw [← ext X, ← ext Y]
    exact h G hm
  obtain ⟨C, hC⟩ := Spectrum.strictComparison (S := T) (fun a b c => hadd a b c)
    (fun a b c => hmul a b c) (fun a => hzero a)
    (fun a ha => a.property.resolve_left (fun e => ha (Subtype.ext e)))
    (fun a => hbound a) hn cmp
  exact ⟨C, hC⟩

end OAI.LinearAlgebra.MatrixExponent.Integral
end

section
/-! A rank decomposition over the algebraic integers uses a finite order.
Descending from that order costs the same constant for every tensor power. -/

namespace OAI.LinearAlgebra.MatrixExponent.Integral
variable {i j k r : ℕ}

private theorem Rank.pow {A : Type*} [CommRing A] (h : Rank A i j k r) (n : ℕ) :
    Rank A (i ^ n) (j ^ n) (k ^ n) (r ^ n) := by
  classical
  let T (x : Pos i k) (y : Pos k j) (z : Pos i j) :=
    if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then (1 : A) else 0
  have ht : OAI.MatrixMultiplication.Foundation.Tensor.RankAtMost T r := by
    obtain ⟨a, b, c, he⟩ := h
    exact ⟨a, b, c, funext fun x => funext fun y => funext fun z => (he x y z).symm⟩
  let digit {a b : ℕ} (x : Pos (a ^ n) (b ^ n)) (l : Fin n) : Pos a b :=
    (finFunctionFinEquiv.symm x.1 l, finFunctionFinEquiv.symm x.2 l)
  obtain ⟨a, b, c, he⟩ := ht.power n
  refine ⟨fun l x => a l (digit x), fun l y => b l (digit y), fun l z => c l (digit z), ?_⟩
  intro x y z
  have hh := congrFun (congrFun (congrFun he (digit x)) (digit y)) (digit z)
  refine hh.symm.trans ?_
  simp only [OAI.MatrixMultiplication.Foundation.Tensor.power, T, digit, Fintype.prod_ite_zero,
    forall_and, ← funext_iff, Equiv.symm_apply_eq, Equiv.apply_symm_apply, Finset.prod_const_one]

/-- Put every coefficient in a single finite torsion-free ℤ-algebra. -/
private theorem in_order (h : Rank O i j k r) :
    ∃ A : Subalgebra ℤ O, Module.Finite ℤ A ∧ Rank A i j k r := by
  obtain ⟨a, b, c, h⟩ := h
  let S := Set.range (Function.uncurry a) ∪ Set.range (Function.uncurry b) ∪
    Set.range (Function.uncurry c)
  let A := Algebra.adjoin ℤ S
  have hf : S.Finite := ((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)
  refine ⟨A, Algebra.finite_adjoin_of_finite_of_isIntegral hf
    (fun x _ => Algebra.IsIntegral.isIntegral x), ?_⟩
  refine ⟨fun t x => ⟨a t x, Algebra.subset_adjoin (.inl (.inl ⟨(t, x), rfl⟩))⟩,
    fun t y => ⟨b t y, Algebra.subset_adjoin (.inl (.inr ⟨(t, y), rfl⟩))⟩,
    fun t z => ⟨c t z, Algebra.subset_adjoin (.inr ⟨(t, z), rfl⟩)⟩, ?_⟩
  intro x y z
  apply Subtype.val_injective
  change A.val _ = A.val _
  rw [map_sum, apply_ite A.val, map_one, map_zero]
  exact h x y z

/-- A diagonal entry of the regular representation sends one to one. -/
private theorem descend {L : Type*} [CommRing L] [Nontrivial L]
    [Module.IsTorsionFree ℤ L] [Module.Finite ℤ L]
    (h : Rank L i j k r) : Rank ℤ i j k (r * Module.finrank ℤ L ^ 2) := by
  classical
  obtain ⟨a, b, c, habc⟩ := h
  let d := Module.finrank ℤ L
  let B := Module.finBasis ℤ L
  let t : Fin d := ⟨0, Module.finrank_pos⟩
  let π := (B.coord t).comp (LinearMap.mulRight ℤ (B t))
  have hπ : π 1 = 1 := by simp [π]
  have expand (u v w : L) :
      ∑ l : Fin d, ∑ m : Fin d, B.repr u l * B.repr v m * π (B l * B m * w) =
        π (u * v * w) := by
    conv_rhs =>
      rw [← B.sum_repr u, Finset.sum_mul, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro l _
    conv_rhs =>
      rw [← B.sum_repr v, Finset.mul_sum, Finset.sum_mul, map_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, map_smul, map_smul,
      smul_eq_mul, smul_eq_mul, mul_assoc]
  rw [pow_two]
  let e : Fin r × Fin d × Fin d ≃ Fin (r * (d * d)) :=
    ((Equiv.refl (Fin r)).prodCongr finProdFinEquiv).trans finProdFinEquiv
  refine ⟨fun l x => B.repr (a (e.symm l).1 x) (e.symm l).2.1,
    fun l y => B.repr (b (e.symm l).1 y) (e.symm l).2.2,
    fun l z => π (B (e.symm l).2.1 * B (e.symm l).2.2 * c (e.symm l).1 z), ?_⟩
  intro x y z
  rw [← e.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, expand, ← map_sum, habc]
  split_ifs <;> simp [hπ]

/-- Expand the two input legs only after taking powers in the fixed order. -/
theorem Rank.integer_powers (h : Rank O i j k r) :
    ∃ C : ℕ, ∀ n : ℕ, Rank ℤ (i ^ n) (j ^ n) (k ^ n) (C * r ^ n) := by
  obtain ⟨A, hf, hh⟩ := in_order h
  refine ⟨Module.finrank ℤ A ^ 2, fun n => ?_⟩
  rw [mul_comm]
  exact descend (hh.pow n)

end OAI.LinearAlgebra.MatrixExponent.Integral
end

section
/-! # From three nonnegative wire exponents to the rectangular upper bound -/

namespace OAI.LinearAlgebra.MatrixExponent.Integral
open Filter Rectangle

variable {x y z a b c : ℝ}

private theorem real_weights
    (h : ∀ A B C : ℕ, 0 < A → 0 < B → 0 < C →
      4 * (x * B * C + y * A * C + z * A * B) ≤ ((A : ℝ) + B + C) ^ 2)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    4 * (x * b * c + y * a * c + z * a * b) ≤ (a + b + c) ^ 2 := by
  have h₁ := tendsto_nat_ceil_mul_div_atTop ha.le
  have h₂ := tendsto_nat_ceil_mul_div_atTop hb.le
  have h₃ := tendsto_nat_ceil_mul_div_atTop hc.le
  apply le_of_tendsto_of_tendsto
    (((((h₂.const_mul x).mul h₃).add ((h₁.const_mul y).mul h₃)).add ((h₁.const_mul z).mul h₂)).const_mul 4)
    (((h₁.add h₂).add h₃).pow 2)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have he := h ⌈a * t⌉₊ ⌈b * t⌉₊ ⌈c * t⌉₊ (by positivity) (by positivity) (by positivity)
  generalize ⌈a * t⌉₊ = A, ⌈b * t⌉₊ = B, ⌈c * t⌉₊ = C at he ⊢
  field_simp
  linarith only [he]

private theorem ordered (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hz : 0 ≤ z)
    (h : ∀ s : ℝ, 0 < s → 4 * (a * x + b * y + s * z) * (a * b * s) ≤ ((a + b) * s + a * b) ^ 2) :
    a * x + b * y + c * z ≤ benchmark a b c := by
  have hq (s : ℝ) (hs : 0 < s) : a * x + b * y + s * z ≤
      a + b + ((a + b) * s - a * b) ^ 2 / (4 * a * b * s) := by
    rw [← sub_le_iff_le_add', le_div_iff₀ (by positivity)]
    linarith only [h s hs]
  unfold benchmark
  by_cases he : 0 ≤ (a + b) * c - a * b
  · rw [max_eq_left he]
    exact hq c hc
  · rw [max_eq_right (le_of_not_ge he), zero_pow (by decide : 2 ≠ 0), zero_div, add_zero]
    have h' := hq (a * b / (a + b)) (by positivity)
    rw [mul_div_cancel₀ _ (by positivity : a + b ≠ 0), sub_self, zero_pow (by decide : 2 ≠ 0), zero_div, add_zero] at h'
    refine le_trans ?_ h'
    gcongr
    exact (le_div_iff₀ (by positivity)).mpr (by linarith)

theorem shape_bound (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hx' : x ≤ 1) (hy' : y ≤ 1) (hz' : z ≤ 1)
    (h : ∀ A B C : ℕ, 0 < A → 0 < B → 0 < C →
      4 * (x * B * C + y * A * C + z * A * B) ≤ ((A : ℝ) + B + C) ^ 2) :
    a * x + b * y + c * z ≤ U a b c := by
  by_cases he : a = 0 ∨ b = 0 ∨ c = 0
  · rw [U_plane ha hb hc he]
    exact add_le_add (add_le_add (mul_le_of_le_one_right ha hx') (mul_le_of_le_one_right hb hy'))
      (mul_le_of_le_one_right hc hz')
  push Not at he
  have ha' := ha.lt_of_ne' he.1
  have hb' := hb.lt_of_ne' he.2.1
  have hc' := hc.lt_of_ne' he.2.2
  have aux (i j k : ℝ) (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
      4 * (i * x + j * y + k * z) * (i * j * k) ≤ ((i + j) * k + i * j) ^ 2 := by
    linarith only [real_weights h (mul_pos hj hk) (mul_pos hi hk) (mul_pos hi hj)]
  unfold U
  split_ifs
  · exact ordered ha' hb' hc' hz (fun s hs => aux a b s ha' hb' hs)
  · rw [show a * x + b * y + c * z = b * y + c * z + a * x by ring]
    apply ordered hb' hc' ha' hx
    intro s hs
    linarith only [aux s b c hs hb' hc']
  · rw [show a * x + b * y + c * z = c * z + a * x + b * y by ring]
    apply ordered hc' ha' hb' hy
    intro s hs
    linarith only [aux a s c ha' hs hc']

end OAI.LinearAlgebra.MatrixExponent.Integral
end

/-! # Near-optimal integral rank witnesses -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Integral
open Rectangle Integral.Upper Integral.Upper.TensorClass

variable {A B : Type*} [CommRing A] [CommRing B] {i j k r : ℕ}

theorem Rank.map (h : Rank A i j k r) (f : A →+* B) : Rank B i j k r := by
  obtain ⟨a, b, c, he⟩ := h
  refine ⟨fun l x => f (a l x), fun l y => f (b l y), fun l z => f (c l z), fun x y z => ?_⟩
  simpa only [map_sum, map_mul, apply_ite f, map_one, map_zero] using congrArg f (he x y z)

theorem Rank.areas {F : Type*} [Field F] (f : A →+* F) (h : Rank A i j k r)
    (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) : max (i * j) (max (i * k) (j * k)) ≤ r := by
  have hr : Rectangle.RankLE F i j k r := h.map f
  exact max_le (hr.area hk) (max_le (hr.transpose.cycle.area hj) (hr.cycle.area hi))

private instance : Nontrivial TensorClass := by
  refine ⟨⟨dots 1 1 1, 0, fun he => ?_⟩⟩
  obtain ⟨a, b, c, he⟩ := rank_of_dots (r := 0) (by simpa using he.le)
  simpa using he (0, 0) (0, 0) (0, 0)

variable {a b c s : ℝ}

private theorem comparison (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    {n r : ℕ} (hn : 2 ≤ n) (hlo : 8 * (n : ℝ) ^ U a b c < r) :
    ∃ C : ℕ, ∀ p : ℕ, Rank O ((side n a) ^ p) ((side n b) ^ p) ((side n c) ^ p) (r ^ p * C) := by
  let M := dots (side n a) (side n b) (side n c)
  have hn' : 0 < n := by omega
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn'
  have hr : 0 < (r : ℝ) := lt_trans (by positivity) hlo
  have hx : 1 ≤ M := by
    simpa only [M, dots, one_mul] using mul_mono (mul_mono (one_le_dotX (side_pos hn' b))
      (one_le_dotY (side_pos hn' a))) (one_le_dotZ (side_pos hn' c))
  have hy : 1 ≤ (r : TensorClass) := by
    rw [← Nat.cast_one (R := TensorClass), natCast_eq_ofTensor_natTensor, natCast_eq_ofTensor_natTensor]
    exact ofTensor_le (CoefficientTensor.natTensor_restricts_of_le (by exact_mod_cast hr))
  have hp (g : TensorClass →+* NNReal) (hg : Monotone g) : g M < g (r : TensorClass) := by
    let f : Character := ⟨g, hg⟩
    have h := shape_bound ha hb hc f.pY_nonneg f.pX_nonneg f.pZ_nonneg
      f.pY_le_one f.pX_le_one f.pZ_le_one (fun A B C hA hB hC => by
        linarith only [character_bound f B A C hB hA hC])
    rw [map_natCast]
    apply NNReal.coe_lt_coe.mp
    calc
      (g M : ℝ) ≤ 8 * (n : ℝ) ^ (b * f.pX + a * f.pY + c * f.pZ) := price_dots f hn' ha hb hc
      _ ≤ 8 * (n : ℝ) ^ U a b c := by gcongr; linarith
      _ < r := hlo
  obtain ⟨C, hC⟩ := strictComparison
    (fun _ _ _ h => add_mono h le_rfl) (fun _ _ _ h => mul_mono le_rfl h)
    TensorClass.zero_le (fun A => ⟨rank A, le_rank_natCast A⟩) hx hy hp
  refine ⟨C, fun p => rank_of_dots ?_⟩
  rw [dots_power, Nat.cast_mul, Nat.cast_pow, mul_comm]
  exact hC p

/-- Take powers twice. The first removes spectral overhead and the
second removes the cost of descending a fixed finite algebra. -/
theorem witness (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hs : U a b c < s) :
    ∃ n i j k r : ℕ, 2 ≤ n ∧ side n a ≤ i ∧ side n b ≤ j ∧ side n c ≤ k ∧
      Rank ℤ i j k r ∧ (r : ℝ) < (n : ℝ) ^ s := by
  have hu : 0 ≤ U a b c := by unfold U benchmark; split_ifs <;> positivity
  obtain ⟨n, r, hn, hlo, hhi⟩ := price_gap hu hs
  obtain ⟨C, hC⟩ := comparison ha hb hc hn hlo
  obtain ⟨p, hp, hsize⟩ := absorb_overhead (D := C) hn (lt_trans (by positivity) hlo) hhi
  have hr := hC p
  have hpos (x : ℝ) : 0 < side n x ^ p := pow_pos (side_pos (by omega) _) _
  have hi := hr.areas (algebraMap O (AlgebraicClosure ℚ)) (hpos a) (hpos b) (hpos c)
  have hs' : 0 < ((r ^ p * C : ℕ) : ℝ) := Nat.cast_pos.mpr
    ((Nat.mul_pos (hpos a) (hpos b)).trans_le ((le_max_left _ _).trans hi))
  obtain ⟨D, hD⟩ := hr.integer_powers
  obtain ⟨q, hq, hbound⟩ := absorb_overhead (D := D) hp hs' hsize
  refine ⟨_, _, _, _, _, hq, side_pow (side_pow le_rfl p) q, side_pow (side_pow le_rfl p) q,
    side_pow (side_pow le_rfl p) q, hD q, ?_⟩
  rwa [mul_comm]

end OAI.LinearAlgebra.MatrixExponent.Integral
end

section
/-!
# Division-free matrix multiplication over commutative rings

Integral rank witnesses supply the upper bound over every ring.
For the opposite inequality, map a division-free circuit into
a residue field before applying the rectangular field formula.
-/

universe u
namespace OAI.LinearAlgebra.MatrixExponent.Integral
open Rectangle (U)
variable {a b c : ℝ}

theorem arithmetic_upper (A : Type*) [CommRing A] (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Admissible A a b c (U a b c) := by
  intro ε hε
  obtain ⟨n, i, j, k, r, hn, hi, hj, hk, hr, hs⟩ := witness ha hb hc (lt_add_of_pos_right _ (half_pos hε))
  have hpos (x : ℝ) := Rectangle.side_pos (show 0 < n by omega) x
  have harea := hr.areas (Int.castRingHom ℚ)
    ((hpos a).trans_le hi) ((hpos b).trans_le hj) ((hpos c).trans_le hk)
  have h := Rectangle.integral_of_rank hn ha hb hc hi hj hk (hr.map (Int.castRingHom A)) harea hs.le
  simpa only [add_assoc, add_halves] using h (ε / 2) (half_pos hε)

theorem field_lower {A F : Type*} [CommRing A] [Field F] (f : A →+* F)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Rectangle.exponent F a b c ≤ exponent A a b c ∧ exponent A a b c ≤ U a b c := by
  have hl (s : ℝ) (h : Admissible A a b c s) : Rectangle.exponent F a b c ≤ s :=
    csInf_le ⟨_, fun _ hs => Rectangle.areas_le_admissible hs⟩ (h.field f)
  have hu := arithmetic_upper A ha hb hc
  exact ⟨le_csInf ⟨_, hu⟩ hl, csInf_le ⟨_, hl⟩ hu⟩

/-- Over a field the two models have identical exponents, independently
of the square and rectangular equality theorems. -/
theorem agreement (F : Type*) [Field F] (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    exponent F a b c = Rectangle.exponent F a b c := by
  apply le_antisymm _ (field_lower (RingHom.id F) ha hb hc).1
  by_contra! hlt
  obtain ⟨s, hlo, hhi⟩ := exists_between hlt
  obtain ⟨n, r, hn, hr, hs⟩ := (Rectangle.exponent_lt_iff_rank ha hb hc).mp hlo
  have hpos (x : ℝ) := Rectangle.side_pos (show 0 < n by omega) x
  have harea := Rank.areas (RingHom.id F) hr (hpos a) (hpos b) (hpos c)
  have hu := Rectangle.integral_of_rank hn ha hb hc le_rfl le_rfl le_rfl hr harea hs.le
  exact hhi.not_ge (csInf_le ⟨_, fun _ h => Rectangle.areas_le_admissible (Admissible.field h (RingHom.id F))⟩ hu)

theorem of_fields (A : Type u) [CommRing A] [Nontrivial A] (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : ∀ (F : Type u) [Field F], Rectangle.exponent F a b c = U a b c) :
    exponent A a b c = U a b c := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal A
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  obtain ⟨hl, hu⟩ := field_lower (Ideal.Quotient.mk I) ha hb hc
  exact le_antisymm hu ((h _).ge.trans hl)

end OAI.LinearAlgebra.MatrixExponent.Integral
end
