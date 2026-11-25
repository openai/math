import OAI.LinearAlgebra.MatrixExponent.Sphere.Plant.Decoded
import OAI.LinearAlgebra.MatrixExponent.Sphere.Seam
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.Chebyshev
import OAI.LinearAlgebra.MatrixExponent.Prices.Fields
import OAI.LinearAlgebra.MatrixExponent.Prices.MovingForms
import OAI.LinearAlgebra.MatrixExponent.Sphere.Private.Preparation
import OAI.LinearAlgebra.MatrixExponent.Spectrum.Comparison
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Seating
import OAI.LinearAlgebra.MatrixExponent.Prices.WireRecovery
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Splitting a homogeneous state into consecutive groups of species -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Chunk

open Finset Plant
variable {M d e : ℕ}

abbrev Shape (M e : ℕ) := {b : Fin M → Fin (e + 1) // ∑ i, (b i).val = e}

abbrev Cells (d : ℕ) (b : Shape M e) := ∀ i, Level d (b.val i).val

def join (u : Fin M → Wedge d) : Wedge (M * d) :=
  pack (fun i => slice (u (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2)

def split (u : Wedge (M * d)) (i : Fin M) : Wedge d :=
  pack (fun j => slice u (finProdFinEquiv (i, j)))

@[simp] theorem split_join (u : Fin M → Wedge d) (i : Fin M) : split (join u) i = u i := by
  simp only [split, join, slice_pack, Equiv.symm_apply_apply, pack_slice]

@[simp] theorem join_split (u : Wedge (M * d)) : join (split u) = u := by
  simp only [join, split, slice_pack, Prod.mk.eta, Equiv.apply_symm_apply, pack_slice]

theorem energy_join (u : Fin M → Wedge d) : energy (join u).val = ∑ i, energy (u i).val := by
  rw [join, energy_pack, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply, ← energy_pack, pack_slice]

def put (v : Σ b : Shape M e, Cells d b) : Level (M * d) e :=
  ⟨join (fun i => (v.2 i).val), by
    rw [energy_join]
    exact (sum_congr rfl fun i _ => (v.2 i).property).trans v.1.property⟩

def states (M d e : ℕ) : (Σ b : Shape M e, Cells d b) ≃ Level (M * d) e := by
  refine Equiv.ofBijective put ⟨?_, ?_⟩
  · rintro ⟨b, x⟩ ⟨c, y⟩ h
    have he (i) : (x i).val = (y i).val := by
      simpa only [put, split_join] using congrArg (fun u => split u.val i) h
    have : b = c := Subtype.ext (funext fun i => Fin.ext <|
      (x i).property.symm.trans ((congrArg (fun t => energy t.val) (he i)).trans (y i).property))
    subst c
    rw [show x = y from funext fun i => Subtype.ext (he i)]
  · intro u
    have he : ∑ i, energy (split u.val i).val = e := by rw [← energy_join, join_split, u.property]
    let b : Shape M e := ⟨fun i => ⟨energy (split u.val i).val, Nat.lt_succ_of_le (by
      exact (single_le_sum (fun i _ => Nat.zero_le (energy (split u.val i).val)) (mem_univ i)).trans_eq he)⟩, he⟩
    exact ⟨⟨b, fun i => ⟨split u.val i, rfl⟩⟩, Subtype.ext (join_split _)⟩

theorem states_val (b : Shape M e) (x : Cells d b) :
    (states M d e ⟨b, x⟩).val = join (fun i => (x i).val) := rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Chunk
end

section
/-! # Splitting a sphere into smaller spheres at prescribed chunk energies -/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Chunk

open Finset Plant
variable {A F : Type*} [Field F] {M d : ℕ}

private theorem expand (z : A → F) (xs : A → Wedge d) (l : List A) :
    wick fieldKernel (bundle z xs l) =
      (-1 : F) ^ shuffle (fun i j => energy (slice (xs i) j).val) (List.finRange d) l *
        ∏ j, wick fieldKernel (bundle z (fun i => slice (xs i) j) l) := by
  have h := wick_species z (fun i j => slice (xs i) j) (fun i j => energy (slice (xs i) j).val)
    (fun i j => (energy_mod_two _).symm) l
  simp only [pack_slice] at h
  exact h

private theorem energy_slices (x : Wedge d) : ∑ j, energy (slice x j).val = energy x.val := by
  rw [← energy_pack, pack_slice]

/-- The sign is determined by the outer index of chunk energies. -/
theorem wick_chunks (z : A → F) (e : A → ℕ) (b : ∀ i, Shape M (e i))
    (u : ∀ i, Cells d (b i)) (l : List A) :
    wick fieldKernel (bundle z (fun i => (states M d (e i) ⟨b i, u i⟩).val) l) =
      (-1 : F) ^ shuffle (fun i j => ((b i).val j).val) (List.finRange M) l *
        ∏ j, wick fieldKernel (bundle z (fun i => (u i j).val) l) := by
  let xs (i : A) := join (fun j => (u i j).val)
  have he (i j k) : slice (xs i) (finProdFinEquiv (j, k)) = slice (u i j).val k := by
    simp only [xs, join, slice_pack, Equiv.symm_apply_apply]
    exact congrArg (fun j => slice (u i j).val k) (congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (j, k)))
  simp only [states_val]
  change wick fieldKernel (bundle z xs l) = _
  rw [expand, shuffle_blocks, ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]
  simp only [he, energy_slices, show ∀ i j, energy (u i j).val.val = ((b i).val j).val
    from fun i j => (u i j).property, pow_add, ← prod_pow_eq_pow_sum, mul_assoc, ← prod_mul_distrib]
  congr 1
  exact prod_congr rfl fun j _ => (expand z (fun i => (u i j).val) l).symm

end OAI.LinearAlgebra.MatrixExponent.Sphere.Chunk
end

/-! # Binary widths of a homogeneous leg and its chunks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Chunk

open Finset Real

def width (d e : ℕ) := ⌈4 * sqrt ((d : ℝ) * e)⌉₊

theorem width_le (d e : ℕ) : (width d e : ℝ) ≤ 4 * sqrt ((d : ℝ) * e) + 1 :=
  (Nat.ceil_lt_add_one (by positivity)).le

theorem card_le (d e : ℕ) : Fintype.card (Level d e) ≤ 2 ^ width d e := by
  have hlog : (1 / 2 : ℝ) ≤ log 2 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2⁻¹)
    rw [log_inv] at h
    linarith
  have hcost : 2 * sqrt ((d : ℝ) * e) ≤ width d e * log 2 := by
    have h := mul_le_mul (Nat.le_ceil (4 * sqrt ((d : ℝ) * e))) hlog (by norm_num) (by positivity)
    unfold width
    linarith
  have h := (card_level d e).trans (exp_le_exp.mpr hcost)
  rw [exp_nat_mul, exp_log (by norm_num)] at h
  exact_mod_cast h

theorem total_width {M e : ℕ} (d : ℕ) (b : Shape M e) :
    (∑ i, (width d (b.val i).val : ℝ)) ≤ 4 * sqrt ((M : ℝ) * d * e) + M := by
  let f i := sqrt ((d : ℝ) * (b.val i).val)
  have hs : ∑ i, f i ≤ sqrt ((M : ℝ) * d * e) := by
    apply (le_sqrt (by unfold f; positivity) (by positivity)).mpr
    refine sq_sum_le_card_mul_sum_sq.trans_eq ?_
    have h (i) : f i ^ 2 = (d : ℝ) * (b.val i).val := sq_sqrt (by positivity)
    rw [card_univ, Fintype.card_fin]
    simp only [h, ← mul_sum, ← Nat.cast_sum, b.2, mul_assoc]
  calc
    _ ≤ ∑ i, (4 * f i + 1) := sum_le_sum fun i _ => width_le d _
    _ = 4 * (∑ i, f i) + M := by simp [sum_add_distrib, mul_sum]
    _ ≤ _ := by linarith

end OAI.LinearAlgebra.MatrixExponent.Sphere.Chunk
end

/-!
# Private spheres as universal tensors

Give each leg twice the target width. A spectral point can transmit
the target from the same auxiliary position used in the sphere lower
bound. The cost of transmitting a binary common label shows that the
extra width supplies a strict margin, uniform in the spectral point.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Private

open Sphere Spectral Finset Filter

variable {F K A : Type} [Field F] [Field K] [Algebra F K]
  [Fintype A] [DecidableEq A] [Nonempty A]

theorem map_kernel {r : ℕ} (x y : Site F r) :
    algebraMap F K (fieldKernel x y) =
      fieldKernel (algebraMap F K x.1, x.2) (algebraMap F K y.1, y.2) := by
  simp [fieldKernel, Sphere.coeff, apply_ite (algebraMap F K)]

omit [DecidableEq A] in
theorem map_sphere (z : A → F) (e : A → ℕ) :
    Tensor.map (algebraMap F K) (sphereTensor z e) =
      sphereTensor (algebraMap F K ∘ z) e := by
  apply Tensor.ofRaw_eq
  refine Raw.equiv_coeff (fun _ => Equiv.refl _) fun x => ?_
  erw [Raw.coeff_map, Raw.coeff_ofTable, Raw.coeff_ofTable]
  change algebraMap F K (sphereForm z e x) = sphereForm (algebraMap F K ∘ z) e x
  change States 1 e at x
  unfold sphereForm
  rw [wick_hom]
  simp only [map_kernel, Function.comp_apply]

/-- The largest doubled energy of a leg at the given width cap. -/
def cap (t : ℝ) : ℕ := ⌊(t / entropy) ^ 2⌋₊

theorem cap_iff {t : ℝ} (ht : 0 ≤ t) (e : ℕ) : e ≤ cap t ↔ width e ≤ t := by
  unfold cap width
  rw [Nat.le_floor_iff (sq_nonneg _), mul_comm, ← le_div_iff₀ entropy_pos,
    Real.sqrt_le_iff, and_iff_right (div_nonneg ht entropy_pos.le)]

abbrev Bounds (a : A → ℝ) := (i : A) → Fin (cap (a i) + 1)

/-- The direct sum over the allowed energy profiles. -/
def universalSphere (z : A → F) (a : A → ℝ) : Tensor F A :=
  ∑ e : Bounds a, sphereTensor z (fun i => (e i).val)

private theorem universal_contains (z : A → F) (a : A → ℝ) (e : A → ℕ)
    (h : ∀ i, e i ≤ cap (a i)) : sphereTensor z e ≤ universalSphere z a := by
  classical
  let j : Bounds a := fun i => ⟨e i, Nat.lt_succ_of_le (h i)⟩
  unfold universalSphere
  rw [← sum_erase_add _ _ (mem_univ j)]
  have he := Tensor.add_le_add_right 0
    (∑ t ∈ univ.erase j, sphereTensor z (fun i => (t i).val)) (sphereTensor z e) (Tensor.zero_le _)
  rwa [zero_add] at he

private theorem universal_nonzero (z : A → F) (a : A → ℝ) : universalSphere z a ≠ 0 := by
  intro hz
  have he := universal_contains z a (fun _ => 0) (fun _ => Nat.zero_le _)
  rw [hz] at he
  have hv := le_antisymm he (Tensor.zero_le _)
  apply sphereForm_vacuum z
  funext x
  exact (Raw.coeff_ofTable _ _ x).symm.trans ((Tensor.ofRaw_eq_zero _).mp hv x)

theorem of_prices (z : A → F) (n : ℕ) (hn : 0 < n) (a : A → ℝ) (ε : ℝ)
    (hε : 0 < ε) (ha : ∀ i, 2 * ε ≤ a i)
    (price : ∀ f : Tensor K A →+* ℝ, Monotone f →
      ∃ g : Tensor K (A ⊕ Unit) →+* ℝ, Monotone g ∧ (∀ T, g (Tensor.pad Unit T) = f T) ∧
        ∃ e : A → ℕ, (∀ i, width (e i) ≤ n * (2 * a i)) ∧
          n * ((∑ i, 2 * a i * Tensor.dist g (.inl i) (.inr ())) - ε) ≤
            Real.log (f (sphereTensor (algebraMap F K ∘ z) e)))
    (U : Raw F A) (hU : ∀ i, Real.log (Fintype.card (U.leg i)) ≤ n * a i) :
    ∃ C : ℕ, ∀ d : ℕ, (Tensor.ofRaw U) ^ d ≤
      (C : Tensor F A) * (universalSphere z (fun i => n * (2 * a i))) ^ d := by
  classical
  let V := universalSphere z (fun i => n * (2 * a i))
  have hv : V ≠ 0 := universal_nonzero _ _
  apply Spectrum.strictComparison Tensor.add_le_add_right Tensor.mul_le_mul_left
    Tensor.zero_le Tensor.one_le Tensor.exists_bound hv
  intro f hf
  let p := NNReal.toRealHom.comp f
  have hp : Monotone p := fun _ _ h => hf h
  change p (Tensor.ofRaw U) < p V
  have hv' : 0 < p V := zero_lt_one.trans_le (Tensor.value_one_le hp hv)
  by_cases hz : Tensor.ofRaw U = 0
  · simpa [hz] using hv'
  have hu' : 0 < p (Tensor.ofRaw U) := zero_lt_one.trans_le (Tensor.value_one_le hp hz)
  obtain ⟨p', hp', he⟩ := Tensor.extend_field_real (L := K) p hp
  obtain ⟨g, hg, he', e, hw, hl⟩ := price p' hp'
  let v i := Tensor.dist g (.inl i) (.inr ())
  have hb (i) : 0 ≤ v i := Tensor.dist_nonneg g hg _ _
  let E := ∑ i, a i * v i
  have energy_low : 2 * ε ≤ E := calc
    _ ≤ 2 * ε * ∑ i, v i :=
      le_mul_of_one_le_right (by positivity) (Tensor.preparation_lower hg he')
    _ = ∑ i, 2 * ε * v i := mul_sum _ _ _
    _ ≤ E := sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (ha i) (hb i)
  have hprep := Tensor.preparation hg (U.map (algebraMap F K))
  rw [he', ← Tensor.map_ofRaw, he] at hprep
  have upper : Real.log (p (Tensor.ofRaw U)) ≤ n * E := hprep.trans (by
    unfold E
    rw [mul_sum]
    refine sum_le_sum fun i _ => ?_
    change v i * Real.log (Fintype.card (U.leg i)) ≤ _
    calc
      _ ≤ v i * (n * a i) := mul_le_mul_of_nonneg_left (hU i) (hb i)
      _ = _ := by ring)
  have hmul : (∑ i, 2 * a i * v i) = 2 * E := by simp only [E, mul_sum, mul_assoc]
  change (n : ℝ) * ((∑ i, 2 * a i * v i) - ε) ≤ _ at hl
  rw [hmul, ← map_sphere, he] at hl
  have hgap : (n : ℝ) * E < Real.log (p (sphereTensor z e)) :=
    (mul_lt_mul_of_pos_left (by linarith) (Nat.cast_pos.mpr hn)).trans_le hl
  have hcap : sphereTensor z e ≤ V := universal_contains _ _ e fun i =>
    (cap_iff ((width_nonneg (e i)).trans (hw i)) _).mpr (hw i)
  have hpos : 0 < p (sphereTensor z e) := by
    by_cases h : sphereTensor z e = 0
    · simp only [h, map_zero, Real.log_zero] at hgap
      exact (not_lt_of_ge (mul_nonneg (Nat.cast_nonneg n) (by linarith)) hgap).elim
    · exact zero_lt_one.trans_le (Tensor.value_one_le hp h)
  exact (Real.log_lt_log_iff hu' hv').mp
    ((upper.trans_lt hgap).trans_le (Real.log_le_log hpos (hp hcap)))

end OAI.LinearAlgebra.MatrixExponent.Routing.Private
end

/-! # Local matrices implementing a private state on each chosen profile -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Private

open Finset Spectral Sphere

variable {F A : Type} [Field F] [Fintype A] [DecidableEq A] [Nonempty A]

abbrev Selector (widths : A → ℝ) (C d : ℕ) := Fin C × (Fin d → Bounds widths)

abbrev leg {widths : A → ℝ} {C d : ℕ} (v : Selector widths C d) (i : A) :=
  ∀ j, Level 1 (v.2 j i).val

def sources (z : A → F) {widths : A → ℝ} {C d : ℕ} (v : Selector widths C d)
    (x : ∀ i, leg v i) : F :=
  ∏ j, sphereForm z (fun i => (v.2 j i).val) (fun i => x i j)

private theorem expand_source (z : A → F) (widths : A → ℝ) (C d : ℕ) :
    (C : Tensor F A) * universalSphere z widths ^ d =
      ∑ v : Selector widths C d, Tensor.ofRaw (Raw.ofTable (leg v) (sources z v)) := by
  classical
  let T (e : Bounds widths) := sphereTensor z (fun i => (e i).val)
  have hd : universalSphere z widths ^ d = ∑ w : Fin d → Bounds widths, ∏ j, T (w j) := by
    rw [← Fintype.prod_sum (fun (_ : Fin d) (w : Bounds widths) => T w)]
    simp [T, universalSphere]
  rw [hd, Fintype.sum_prod_type]
  have he (i : Fin C) (v : Fin d → Bounds widths) :
      Tensor.ofRaw (Raw.ofTable (leg (i, v)) (sources z (i, v))) = ∏ j, T (v j) :=
    (Tensor.product_tables (fun j a => Level 1 (v j a).val)
      (fun j => sphereForm z (fun a => (v j a).val))).symm
  simp only [he, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The common selector is internal. Once it is fixed, each map can
read only the state at its own site across the selected blocks. -/
theorem local_matrices (z : A → F) (widths : A → ℝ) (C d : ℕ)
    (X : A → Type) [∀ i, Fintype (X i)] (J : (∀ i, X i) → F)
    (h : (Tensor.ofRaw (Raw.ofTable X J)) ^ d ≤ (C : Tensor F A) * universalSphere z widths ^ d) :
    ∃ L : (v : Selector widths C d) → (i : A) → (Fin d → X i) → leg v i → F,
      ∀ x : (i : A) → Fin d → X i, (∏ j, J (fun i => x i j)) =
        ∑ v, ∑ y : ∀ i, leg v i, (∏ i, L v i (x i) (y i)) * sources z v y := by
  classical
  have target := Tensor.product_tables (fun _ : Fin d => X) (fun _ => J)
  simp only [prod_const, card_univ, Fintype.card_fin] at target
  rw [target, expand_source] at h
  obtain ⟨L, hL⟩ := (Raw.restriction_sum_iff _ _ _).mp h
  refine ⟨L, fun x => ?_⟩
  have e := hL x
  erw [Raw.coeff_ofTable] at e
  rw [e]
  refine sum_congr rfl fun v _ => ?_
  unfold Raw.applyLocal
  rw [Raw.expand]
  refine sum_congr rfl fun y _ => ?_
  erw [Raw.coeff_ofTable]

end OAI.LinearAlgebra.MatrixExponent.Routing.Private
end

/-! # Uniform comparison with the direct sum of bounded sphere levels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Private

open Sphere Spectral Filter

variable {F K A : Type} [Field F] [Field K] [Algebra F K] [Infinite K]
  [Fintype A] [DecidableEq A] [Nonempty A]

/-- Under shared-parameter pricing over an infinite extension, all the
restrictions are over the original field. Their multiplicative overhead
can depend on the target, but not on the tensor power. -/
theorem universal (sync : Prices.SharedPrice K) (z : A → F) (hz : Function.Injective z)
    (a : A → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ᶠ n : ℕ in atTop, ∀ U : Raw F A, (∀ i, Real.log (Fintype.card (U.leg i)) ≤ n * a i) →
      ∃ C : ℕ, ∀ d : ℕ, (Tensor.ofRaw U) ^ d ≤
        (C : Tensor F A) * (universalSphere z (fun i => n * (2 * a i))) ^ d := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_min_image a Finset.univ_nonempty
  have he := (bounded_forms K).weighted sync
  have hz' : Function.Injective (algebraMap F K ∘ z) := (algebraMap F K).injective.comp hz
  have hw := prescribed_widths he (wireProbe K) _ hz' (fun j => 2 * a j)
    (fun j => mul_pos (by norm_num) (ha j)) (half_pos (ha i))
  filter_upwards [hw, eventually_gt_atTop 0] with n hn hpos
  exact of_prices z n hpos a _ (half_pos (ha i))
    (fun j => by linarith [hi j (Finset.mem_univ j)]) hn

/-- The same width at every mark suffices for a block of binary rows. -/
theorem binary_matrices (sync : Prices.SharedPrice K) (z : A → F) (hz : Function.Injective z) :
    ∀ᶠ b : ℕ in atTop, ∀ J : (A → Fin b → Bool) → F,
      ∃ C : ℕ, ∀ d : ℕ, ∃ L : (v : Selector (fun _ : A => 2 * (b : ℝ)) C d) →
          (i : A) → (Fin d → Fin b → Bool) → leg v i → F,
        ∀ x : A → Fin d → Fin b → Bool, (∏ j, J (fun i => x i j)) =
          ∑ v, ∑ y : ∀ i, leg v i, (∏ i, L v i (x i) (y i)) * sources z v y := by
  filter_upwards [universal sync z hz (fun _ => 1) (by simp)] with b h
  intro J
  obtain ⟨C, hC⟩ := h (Raw.ofTable (fun _ => Fin b → Bool) J) (by
    intro i
    change Real.log (Fintype.card (Fin b → Bool)) ≤ (b : ℝ) * 1
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Real.log_pow]
    have hl : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg _))
  refine ⟨C, fun d => local_matrices z _ C d _ J ?_⟩
  simpa only [mul_one, mul_comm (b : ℝ)] using hC d

end OAI.LinearAlgebra.MatrixExponent.Routing.Private
end

/-! # A private sphere on the packed species -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Private

open Finset Sphere Plant
open scoped Classical
variable {A F : Type} [Fintype A] [DecidableEq A] [Field F]

/-- Push independent finite sums forward along site maps. Different
preimages of one local label contribute additively. -/
theorem local_push {X Y : A → Type} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)]
    (f : ∀ i, X i → Y i) (w : ∀ i, X i → F) (T : (∀ i, Y i) → F) :
    (∑ y : ∀ i, Y i, (∏ i, ∑ x, if f i x = y i then w i x else 0) * T y) =
      ∑ x : ∀ i, X i, (∏ i, w i (x i)) * T (fun i => f i (x i)) := by
  simp_rw [Fintype.prod_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  rw [Fintype.sum_eq_single (fun i => f i (x i))]
  · simp
  · intro y hy
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    rw [prod_eq_zero (mem_univ i) (ite_eq_right (Ne.symm hi)), zero_mul]

variable {a : A → ℝ} {C d : ℕ}

def profile (v : Selector a C d) (i : A) : ℕ := ∑ j, (v.2 j i).val

def packed (v : Selector a C d) (i : A) (x : leg v i) : Level d (profile v i) :=
  ⟨pack (fun j => (x j).val), by rw [energy_pack]; exact sum_congr rfl (fun j _ => (x j).2)⟩

def value {r : ℕ} (z : A → F) {e : A → ℕ} (x : States r e) : F :=
  wick fieldKernel (bundle z (fun i => (x i).val) univ.toList)

omit [DecidableEq A] in
private theorem one_species (z : A → F) (e : A → ℕ) (x : States 1 e) :
    value z x = sphereForm z e x := by
  unfold sphereForm
  rw [← wick_map fieldKernel (fun i : A × Mode 1 => (z i.1, i.2))]
  simp [value, bundle, inputs, marksAt, List.map_flatMap, Function.comp_def]

def parity (v : Selector a C d) : ℕ :=
  shuffle (fun i j => (v.2 j i).val) (List.finRange d) univ.toList

omit [DecidableEq A] in
theorem packed_value (z : A → F) (v : Selector a C d) (x : ∀ i, leg v i) :
    sources z v x = (-1 : F) ^ parity v * value z (fun i => packed v i (x i)) := by
  have hp (i j) : (x i j).val.val.length % 2 = (v.2 j i).val % 2 :=
    (energy_mod_two _).symm.trans (congrArg (· % 2) (x i j).2)
  have h := wick_species z (fun i j => (x i j).val) (fun i j => (v.2 j i).val) hp univ.toList
  change value z (fun i => packed v i (x i)) = (-1 : F) ^ parity v *
    ∏ j, value z (fun i => x i j) at h
  rw [h, ← mul_assoc, ← mul_pow]
  simp only [neg_mul_neg, one_mul, one_pow, sources, one_species]

/-- Pack the product of selected one-species spaces into prescribed
levels of a single private sphere. The order sign is fixed by the selector. -/
theorem local_packed (z : A → F) (v : Selector a C d) (L : ∀ i, leg v i → F) :
    (∑ y : ∀ i, leg v i, (∏ i, L i (y i)) * sources z v y) =
      (-1 : F) ^ parity v * ∑ y : States d (profile v),
        (∏ i, ∑ x, if packed v i x = y i then L i x else 0) * value z y := by
  refine Eq.trans ?_ (congrArg ((-1 : F) ^ parity v * ·) (local_push (packed v) L (value z)).symm)
  rw [mul_sum]
  apply sum_congr rfl
  intro y _
  rw [packed_value, mul_left_comm]

end OAI.LinearAlgebra.MatrixExponent.Routing.Private
end

/-!
# Realizing the signed joint state

The signature exchanging blocks depends only on their occupancy counts
at each mark. Include these counts in the common selector and check
them locally. The signature within a block is part of its input table.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Private

open Finset Sphere Plant Filter
open scoped Classical
variable {F K A : Type} [Field F] [Fintype A] [DecidableEq A] {n d b C : ℕ}

/-- The coefficient across all species after ordering by marks. -/
def signed (rows : List A) (J : (A → Bool) → F) (x : A → Fin n → Bool) :=
  (-1 : F) ^ shuffle (fun i j => (x i j).toNat) (List.finRange n) rows *
    ∏ j, J (fun i => x i j)

def blocks (x : Fin (d * b) → Bool) (j : Fin d) (k : Fin b) := x (finProdFinEquiv (j, k))

def counts (x : Fin (d * b) → Bool) (j : Fin d) : Fin (b + 1) :=
  ⟨∑ k, (blocks x j k).toNat, Nat.lt_succ_of_le (calc
    _ ≤ ∑ _ : Fin b, 1 := sum_le_sum fun k _ => by cases blocks x j k <;> decide
    _ = b := by simp)⟩

theorem sum_counts (x : Fin (d * b) → Bool) :
    ∑ j, (counts x j).val = energy (occupancy x).val := by
  rw [energy_occupancy, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  rfl

abbrev Counts (A : Type) (b d : ℕ) := A → Fin d → Fin (b + 1)

def inter (rows : List A) (m : Counts A b d) :=
  shuffle (fun i j => (m i j).val) (List.finRange d) rows

omit [Fintype A] [DecidableEq A] in
theorem signed_blocks (rows : List A) (J : (A → Bool) → F) (x : A → Fin (d * b) → Bool) :
    signed rows J x = (-1 : F) ^ inter rows (fun i => counts (x i)) *
      ∏ j, signed rows J (fun i => blocks (x i) j) := by
  rw [signed, shuffle_blocks, pow_add, ← finProdFinEquiv.prod_comp, Fintype.prod_prod_type]
  simp only [signed, prod_mul_distrib, prod_pow_eq_pow_sum, mul_assoc, inter, counts, blocks]

abbrev Selection (A : Type) (b C d : ℕ) :=
  Counts A b d × Selector (fun _ : A => 2 * (b : ℝ)) C d

def energyA (v : Selection A b C d) (i : A) := ∑ j, (v.1 i j).val

abbrev energyB (v : Selection A b C d) := profile v.2

def sign (rows : List A) (v : Selection A b C d) := inter rows v.1 + parity v.2

/-- The only coupling between distinct marks, beyond the private sphere
itself, is the common selection. Both energies are known from it. -/
theorem private_joint [Field K] [Infinite K] [Algebra F K] [Nonempty A]
    (sync : Prices.SharedPrice K) (z : A → F) (hz : Function.Injective z) :
    ∀ᶠ b : ℕ in atTop, ∀ (rows : List A) (J : (A → Bool) → F),
      ∃ C : ℕ, ∀ d : ℕ,
        ∃ L : (v : Selection A b C d) → (i : A) → (Fin (d * b) → Bool) → Level d (energyB v i) → F,
          (∀ v i x y, L v i x y ≠ 0 → energy (occupancy x).val = energyA v i) ∧
          ∀ x : A → Fin (d * b) → Bool, signed rows J x =
            ∑ v, (-1 : F) ^ sign rows v *
              ∑ y : States d (energyB v), (∏ i, L v i (x i) (y i)) * value z y := by
  filter_upwards [binary_matrices sync z hz] with b hb
  intro rows J
  obtain ⟨C, hC⟩ := hb (signed rows J)
  refine ⟨C, fun d => ?_⟩
  obtain ⟨L, hL⟩ := hC d
  let W (v : Selection A b C d) (i : A) (x : Fin (d * b) → Bool) (y : Level d (energyB v i)) : F :=
    if v.1 i = counts x then ∑ k, if packed v.2 i k = y then L v.2 i (blocks x) k else 0 else 0
  refine ⟨W, ?_, ?_⟩
  · intro v i x y h
    have e : v.1 i = counts x := by by_contra! h'; simp [W, h'] at h
    rw [energyA, e, sum_counts]
  intro x
  let m i := counts (x i)
  rw [signed_blocks, hL, mul_sum, Fintype.sum_prod_type (α₁ := Counts A b d), Fintype.sum_eq_single m]
  · refine sum_congr rfl fun v _ => ?_
    rw [local_packed z v (fun i => L v i (blocks (x i)))]
    simp only [sign, m, W, ↓reduceIte, pow_add, mul_assoc]
  · intro k hk
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
    apply sum_eq_zero
    intro v _
    apply mul_eq_zero_of_right
    apply sum_eq_zero
    intro y _
    rw [prod_eq_zero (mem_univ i) (by simp [W, m] at hi ⊢; exact fun he => (hi he).elim), zero_mul]

end OAI.LinearAlgebra.MatrixExponent.Routing.Private
end

/-! # Energy and selector costs of the private sphere -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Private

open Finset Sphere Filter
variable {A : Type} {b C d : ℕ}

/-- Absolute constant for the private energy bound. -/
def energyConstant := ⌈(2 / entropy) ^ 2⌉₊

theorem cap_le (b : ℕ) : cap (2 * (b : ℝ)) ≤ energyConstant * b ^ 2 := by
  have ht := Nat.floor_le (sq_nonneg (2 * (b : ℝ) / entropy))
  change (cap (2 * (b : ℝ)) : ℝ) ≤ _ at ht
  apply (Nat.cast_le (α := ℝ)).mp
  rw [Nat.cast_mul, Nat.cast_pow]
  refine ht.trans ?_
  rw [mul_div_right_comm, mul_pow]
  exact mul_le_mul_of_nonneg_right (Nat.le_ceil _) (sq_nonneg _)

theorem energyA_le (v : Selection A b C d) (i : A) : energyA v i ≤ d * b := by
  unfold energyA
  calc
    _ ≤ ∑ _ : Fin d, b := sum_le_sum fun j _ => Nat.le_of_lt_succ (v.1 i j).isLt
    _ = _ := by simp

theorem energyB_le (v : Selection A b C d) (i : A) :
    energyB v i ≤ d * (energyConstant * b ^ 2) := by
  unfold energyB profile
  calc
    _ ≤ ∑ _ : Fin d, energyConstant * b ^ 2 := sum_le_sum fun j _ =>
      (Nat.le_of_lt_succ (v.2.2 j i).isLt).trans (cap_le b)
    _ = _ := by simp

variable (A) [Fintype A] [DecidableEq A]

private theorem card_selection (b C d : ℕ) :
    Fintype.card (Selection A b C d) =
      C * (((b + 1) * (cap (2 * (b : ℝ)) + 1)) ^ Fintype.card A) ^ d := by
  simp only [Selection, Selector, Counts, Bounds, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin, mul_pow, ← pow_mul]
  ac_rfl

omit [DecidableEq A] in
private theorem selector_rate {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ b : ℕ in atTop,
      (((b + 1) * (cap (2 * (b : ℝ)) + 1) : ℕ) : ℝ) ^ Fintype.card A ≤ Real.exp (ε * b) := by
  let m := Fintype.card A
  let t := 2 * ((energyConstant : ℝ) + 1)
  have ht : 0 ≤ t := by unfold t; positivity
  have h := (isLittleO_pow_exp_pos_mul_atTop (3 * m) hε).const_mul_left (t ^ m)
  filter_upwards [eventually_ge_atTop 1, tendsto_natCast_atTop_atTop.eventually (h.bound zero_lt_one)]
    with b hb h
  have hb' : 1 ≤ (b : ℝ) := Nat.one_le_cast.mpr hb
  have hcap : (cap (2 * (b : ℝ)) : ℝ) ≤ energyConstant * (b : ℝ) ^ 2 := by exact_mod_cast cap_le b
  have h' : t ^ m * (b : ℝ) ^ (3 * m) ≤ Real.exp (ε * b) := by
    simpa [Real.norm_eq_abs, abs_of_nonneg ht] using h
  push_cast
  calc
    _ ≤ ((2 * (b : ℝ)) * (((energyConstant : ℝ) + 1) * b ^ 2)) ^ m := by
      gcongr
      · linarith
      · nlinarith
    _ = t ^ m * (b : ℝ) ^ (3 * m) := by rw [pow_mul, ← mul_pow]; congr 1; unfold t; ring
    _ ≤ _ := h'

/-- Any prescribed selector rate is available by choosing the block
size first and then the number of blocks. -/
theorem selector_small {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ b : ℕ in atTop, ∀ C : ℕ, ∀ᶠ d : ℕ in atTop,
      (Fintype.card (Selection A b C d) : ℝ) ≤ Real.exp (ε * d * b) := by
  filter_upwards [selector_rate A (half_pos hε), eventually_gt_atTop 0] with b h hb
  intro C
  let v := ε / 2 * (b : ℝ)
  have hv : 0 < v := mul_pos (half_pos hε) (Nat.cast_pos.mpr hb)
  have hd := Real.tendsto_exp_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hv)
  filter_upwards [hd.eventually_ge_atTop (C : ℝ)] with d hd
  rw [card_selection, Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  calc
    _ ≤ Real.exp (v * d) * (Real.exp v) ^ d :=
      mul_le_mul hd (pow_le_pow_left₀ (by positivity) h _) (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; unfold v; ring

end OAI.LinearAlgebra.MatrixExponent.Routing.Private
end

/-! # Both spheres have prescribed total energies at every auxiliary mark -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Private

open Finset Sphere Plant Filter
open scoped Classical

variable {F K A : Type} [Field F] [Fintype A] [DecidableEq A] {r b C d : ℕ}

/-- Push the supported occupancy assignments onto the prescribed energy
level. The equality check is on the full ordered wedge. -/
private theorem push_level (e : A → ℕ) (c : A → (Fin r → Bool) → F)
    (hc : ∀ i x, c i x ≠ 0 → energy (occupancy x).val = e i) (T : (A → Wedge r) → F) :
    (∑ y : States r e, (∏ i, ∑ x, if occupancy x = (y i).val then c i x else 0) *
      T (fun i => (y i).val)) =
      ∑ x : A → Fin r → Bool, (∏ i, c i (x i)) * T (fun i => occupancy (x i)) := by
  simp_rw [Fintype.prod_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  by_cases h : ∀ i, c i (x i) ≠ 0
  · let y : States r e := fun i => ⟨occupancy (x i), hc i _ (h i)⟩
    rw [Fintype.sum_eq_single y]
    · simp [y]
    · intro z hz
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hz
      have ne : occupancy (x i) ≠ (z i).val := fun eq => hi (Subtype.ext eq.symm)
      rw [prod_eq_zero (mem_univ i) (ite_eq_right ne), zero_mul]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [prod_eq_zero (mem_univ i) hi, zero_mul]
    apply sum_eq_zero
    intro y _
    rw [prod_eq_zero (mem_univ i) (by simp [hi]), zero_mul]

/-- One local coupling matrix per auxiliary mark. -/
abbrev Coupling (F : Type) (v : Selection A b C d) :=
  ∀ i, Level (d * b) (energyA v i) → Level d (energyB v i) → F

def couple (z : A → F) (v : Selection A b C d) (L : Coupling F v)
    (T : (A → Wedge (d * b)) → F) :=
  ∑ y : States d (energyB v), ∑ x : States (d * b) (energyA v),
    (∏ i, L i (x i) (y i)) * T (fun i => (x i).val) * value z y

theorem private_levels [Field K] [Infinite K] [Algebra F K] [Nonempty A]
    (sync : Prices.SharedPrice K) (z : A → F) (hz : Function.Injective z) :
    ∀ᶠ b : ℕ in atTop, ∀ (rows : List A) (J : (A → Bool) → F),
      ∃ C : ℕ, ∀ d : ℕ,
        ∃ L : (v : Selection A b C d) → Coupling F v,
          ∀ T : (A → Wedge (d * b)) → F,
            (∑ x : A → Fin (d * b) → Bool, signed rows J x * T (fun i => occupancy (x i))) =
              ∑ v, (-1 : F) ^ sign rows v * couple z v (L v) T := by
  filter_upwards [private_joint sync z hz] with b hb
  intro rows J
  obtain ⟨C, hC⟩ := hb rows J
  refine ⟨C, fun d => ?_⟩
  obtain ⟨L, hL, he⟩ := hC d
  let W (v : Selection A b C d) : Coupling F v :=
    fun i a b => ∑ x, if occupancy x = a.val then L v i x b else 0
  refine ⟨W, fun T => ?_⟩
  simp_rw [he, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  simp only [mul_assoc, ← mul_sum]
  congr 1
  simp_rw [sum_mul]
  rw [sum_comm]
  unfold couple
  apply sum_congr rfl
  intro y _
  have h := push_level (energyA v) (fun i x => L v i x (y i)) (fun i x => hL v i x _) T
  rw [← sum_mul]
  rw [show (∑ x : States (d * b) (energyA v), (∏ i, W v i (x i) (y i)) *
    T (fun i => (x i).val)) = _ from h, sum_mul]
  exact sum_congr rfl (fun _ _ => mul_right_comm _ _ _)

end OAI.LinearAlgebra.MatrixExponent.Routing.Private
end

/-!
# Public energies and a private selector

The outer index records just the total energy at each auxiliary mark
of each sphere. Its size is polynomial in the number of species.
The short private selector is summed internally.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Private

open Finset Sphere Plant Filter
open scoped Classical

variable {F K : Type} [Field F] {n b d : ℕ}

/-- The two total doubled energies at each auxiliary mark. -/
abbrev Shape (n b d : ℕ) :=
  (Fin n → Fin (d * b + 1)) × (Fin n → Fin (d * (energyConstant * b ^ 2) + 1))

def shape {C : ℕ} (v : Selection (Fin n) b C d) : Shape n b d :=
  (fun i => ⟨energyA v i, Nat.lt_succ_of_le (energyA_le v i)⟩,
    fun i => ⟨energyB v i, Nat.lt_succ_of_le (energyB_le v i)⟩)

theorem card_shape (n b d : ℕ) : Fintype.card (Shape n b d) =
    ((d * b + 1) * (d * (energyConstant * b ^ 2) + 1)) ^ n := by
  simp only [Shape, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, mul_pow]

abbrev Tables (F : Type) (p : Shape n b d) :=
  ∀ i : Fin n, Level (d * b) (p.1 i).val → Level d (p.2 i).val → F

def term (z : Fin n → F) (p : Shape n b d) (U : Tables F p)
    (T : (Fin n → Wedge (d * b)) → F) :=
  ∑ y : States d (fun i => (p.2 i).val), ∑ x : States (d * b) (fun i => (p.1 i).val),
    (∏ i, U i (x i) (y i)) * T (fun i => (x i).val) *
      wick fieldKernel (bundle z (fun i => (y i).val) (List.finRange n))

private theorem ordered (z : Fin n → F) (e : Fin n → ℕ) :
    ∃ k : F, ∀ y : States d e,
      value z y = k * wick fieldKernel (bundle z (fun i => (y i).val) (List.finRange n)) := by
  have perm : (univ : Finset (Fin n)).toList.Perm (List.finRange n) :=
    (List.perm_ext_iff_of_nodup (nodup_toList _) (List.nodup_finRange _)).mpr (by simp)
  obtain ⟨q, hq⟩ := wick_perm_sites (R := F) (r := d) e perm
  let f (i : Fin n × Mode d) := (z i.1, i.2)
  refine ⟨(-1) ^ q, fun y => ?_⟩
  have h := hq (fun i j => fieldKernel (f i) (f j)) (fun i j => fieldKernel_skew _ _) y []
  simp only [List.nil_append, ← wick_map] at h
  simpa [value, bundle, List.map_flatMap, marksAt, Function.comp_def, f] using h

private theorem move_sign {C : ℕ} (z : Fin n → F) (v : Selection (Fin n) b C d) (L : Coupling F v) :
    ∃ k : F, ∀ T, couple z v L T = k * term z (shape v) L T := by
  obtain ⟨k, hk⟩ := ordered (d := d) z (energyB v)
  refine ⟨k, fun T => ?_⟩
  unfold couple term
  simp only [shape, hk, mul_sum, mul_left_comm _ k, mul_assoc]
  rfl

/-- One selector and one family of local tables per public shape.
The scalar weight can enforce consistency of the private choice. -/
structure Program (F : Type) (n b d : ℕ) where
  labels : ℕ
  scalar : Shape n b d → Fin labels → F
  table : (p : Shape n b d) → Fin labels → Tables F p

def Program.eval (p : Program F n b d) (z : Fin n → F) (T : (Fin n → Wedge (d * b)) → F) : F :=
  ∑ e, ∑ i, p.scalar e i * term z e (p.table e i) T

private theorem compile (z : Fin n → F) {C : ℕ} (L : (v : Selection (Fin n) b C d) → Coupling F v) :
    ∃ p : Program F n b d, p.labels = Fintype.card (Selection (Fin n) b C d) ∧ ∀ T,
      p.eval z T = ∑ v, (-1 : F) ^ sign (List.finRange n) v * couple z v (L v) T := by
  choose k hk using fun v => move_sign z v (L v)
  let e := (Fintype.equivFin (Selection (Fin n) b C d)).symm
  let W (v : Selection (Fin n) b C d) (s : Shape n b d) : Tables F s :=
    if h : shape v = s then h ▸ (show Tables F (shape v) from L v) else fun _ _ _ => 0
  let g (v : Selection (Fin n) b C d) (s : Shape n b d) : F :=
    if s = shape v then (-1 : F) ^ sign (List.finRange n) v * k v else 0
  refine ⟨⟨_, fun s j => g (e j) s, fun s j => W (e j) s⟩, rfl, fun T => ?_⟩
  rw [Program.eval, sum_comm, ← e.sum_comp]
  refine sum_congr rfl fun j _ => ?_
  simp only [g, W, ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true, ↓reduceDIte, hk, mul_assoc]

theorem private_program [Field K] [Algebra F K] [Infinite K] [NeZero n]
    (sync : Prices.SharedPrice K) (z : Fin n ↪ F) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ b : ℕ in atTop, ∀ J : (Fin n → Bool) → F, ∀ᶠ d : ℕ in atTop,
      ∃ p : Program F n b d, (p.labels : ℝ) ≤ Real.exp (ε * d * b) ∧
        ∀ T, p.eval z T = ∑ x, signed (List.finRange n) J x * T (fun i => occupancy (x i)) := by
  filter_upwards [private_levels sync z z.injective, selector_small (Fin n) hε] with b hb hs
  intro J
  obtain ⟨C, hC⟩ := hb (List.finRange n) J
  filter_upwards [hs C] with d hd
  obtain ⟨L, h⟩ := hC d
  obtain ⟨p, he, hp⟩ := compile z L
  exact ⟨p, he ▸ hd, fun T => (hp T).trans (h T).symm⟩

end OAI.LinearAlgebra.MatrixExponent.Routing.Private
end

/-!
# Implanting a wiring table using two spheres

The original marks carry fixed-energy codes, independently for each
species. This includes seam labels. Only the total energy is checked
there, so the rule applies to an arbitrary summation over seam states.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Private

open Finset Sphere Plant Filter
open scoped Classical
variable {F K : Type} [Field F] {m n r b d : ℕ}

abbrev Marks (w : Fin m → ℕ) (r : ℕ) := ∀ i, Level r (r * (8 * w i ^ 2))

def demand (w : Fin m → ℕ) (L : Bits w → F) (X : Marks w r) : F :=
  ∑ σ : (i : Fin m) → bitsAt (w i) r,
    if ∀ i, markCode (w i) r (σ i) = X i then ∏ j, L (fun i => σ i j) else 0

def marked (z : Fin m → F) (y : Fin n → F) {w : Fin m → ℕ}
    (X : Marks w r) (Y : Fin n → Wedge r) : F :=
  wick fieldKernel (bundle y Y (List.finRange n) ++ bundle z (fun i => (X i).val) (List.finRange m))

/-- The thresholds for the block size and number of blocks are uniform
in all three sets of positions, the individual widths and the wiring table. -/
theorem install [Finite F] [Field K] [Algebra F K] [Infinite K] [NeZero n]
    (sync : Prices.SharedPrice K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ b : ℕ in atTop, ∀ᶠ d : ℕ in atTop,
      ∀ (m : ℕ) (z : Fin m ↪ F) (y q : Fin n ↪ F), (∀ i j, y j ≠ z i) →
        ∀ w : Fin m → ℕ, (∑ i, 4 * w i) ≤ n → ∀ L : Bits w → F,
          ∃ p : Program F n b d, (p.labels : ℝ) ≤ Real.exp (ε * d * b) ∧
            ∀ X : Marks w (d * b), p.eval q (marked z y X) = demand w L X := by
  have hm := Filter.eventually_all.mpr (fun q : Fin n ↪ F => private_program sync q hε)
  filter_upwards [hm] with b hb
  have hd := Filter.eventually_all.mpr fun q => Filter.eventually_all.mpr (hb q)
  filter_upwards [hd] with d hp
  intro m z y q he w hn L
  obtain ⟨J, _, hJ⟩ := joint_decoded z y he w hn L
  obtain ⟨p, hy, h⟩ := hp q J
  exact ⟨p, hy, fun X => (h (marked z y X)).trans (hJ _ X)⟩

end OAI.LinearAlgebra.MatrixExponent.Routing.Private
end
