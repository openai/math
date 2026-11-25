import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Rows
import OAI.LinearAlgebra.MatrixExponent.Spectrum.Comparison
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Model
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Algebra.MvPolynomial.Monad
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Mask
import Mathlib.Algebra.Polynomial.Roots
import OAI.LinearAlgebra.MatrixExponent.Spectral.Span
import Mathlib.Algebra.BigOperators.Fin
import OAI.LinearAlgebra.TensorSpectrum.TagGrowth
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.WeightedModel
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup.Dense
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law

universe u

section
/-!
# Specialization by a valuation

If every polynomial identity of a tuple holds at another tuple, one
valuation subring contains the first tuple and specializes it to the
second. The coefficients are fixed under specialization.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open MvPolynomial IsLocalRing

variable {K E : Type*} [Field K] [Field E] {ι : Type}

theorem valuation_place (φ : K →+* E) (v : ι → E) (x : ι → K)
    (h : ∀ p : MvPolynomial ι K, eval₂ φ v p = 0 → eval x p = 0) :
    ∃ (V : ValuationSubring E) (f : K →+* V) (u : ι → V),
      (∀ a, (f a : E) = φ a) ∧ (∀ i, (u i : E) = v i) ∧
      (∀ i, residue V (u i) = residue V (f (x i))) := by
  let e := eval₂Hom φ v
  let I := Ideal.map e.rangeRestrict (RingHom.ker (eval x))
  have hI : I ≠ ⊤ := by
    intro he
    have h₁ : (1 : e.range) ∈ I := by rw [he]; exact Submodule.mem_top
    obtain ⟨p, hp, hp'⟩ := (Ideal.mem_map_iff_of_surjective _ e.rangeRestrict_surjective).mp h₁
    change eval x p = 0 at hp
    have he' : e p = 1 := congrArg Subtype.val hp'
    have hz := h (p - 1) (by change e (p - 1) = 0; rw [map_sub, map_one, he', sub_self])
    simp [hp] at hz
  obtain ⟨V, hV, hnon⟩ := I.image_subset_nonunits_valuationSubring hI
  let ev : MvPolynomial ι K →+* V := (Subring.inclusion hV).comp e.rangeRestrict
  refine ⟨V, ev.comp C, fun i => ev (X i), ?_, ?_, ?_⟩
  · intro a
    change eval₂ φ v (C a) = _
    simp
  · intro i
    change eval₂ φ v (X i) = _
    simp
  · intro i
    let p := X i - C (x i)
    have hp : p ∈ RingHom.ker (eval x) := by simp [p]
    have hz : (ev p : E) ∈ (V.nonunits : Set E) := hnon ⟨e.rangeRestrict p, Ideal.mem_map_of_mem _ hp, rfl⟩
    rw [← V.image_maximalIdeal] at hz
    obtain ⟨z, hz, he⟩ := hz
    have hz' : residue V (ev p) = 0 := by
      rw [← Subtype.ext he]
      exact (residue_eq_zero_iff _).mpr hz
    simpa only [p, map_sub, sub_eq_zero, RingHom.comp_apply] using hz'

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

section
/-!
# A simultaneous spectral maximizer

Testing the weighted tensor tensored with many ordinary copies
finds a point attaining the ordinary maximum while retaining
the weighted lower bound. Only two observables of the compact
spectrum are needed.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Spectral Set
open scoped NNReal

variable {F : Type} [Field F] {A B : Tensor F (Fin 3)} {a b : ℝ}

private theorem large_power {u v : ℝ} (hu : 0 < u) (hv : u < v) (C : ℝ) :
    ∃ n : ℕ, C * u ^ n < v ^ n := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C ((one_lt_div hu).mpr hv)
  rw [div_pow, lt_div_iff₀ (pow_pos hu _)] at hn
  exact ⟨n, hn⟩

private theorem compact_max {P : Set (Tensor F (Fin 3) → ℝ≥0)}
    (hc : IsCompact P) (hn : P.Nonempty) (hs : P ⊆ Spectrum.points (Tensor F (Fin 3)))
    (A : Tensor F (Fin 3)) :
    ∃ f : Point F, Monotone f ∧ ⇑f ∈ P ∧ ∀ g : Point F, ⇑g ∈ P → (g A : ℝ) ≤ f A := by
  obtain ⟨u, hu, hh⟩ := hc.exists_isMaxOn hn (continuous_apply A).continuousOn
  obtain ⟨f, hf, rfl⟩ := hs hu
  exact ⟨f, hf, hu, fun g hg => NNReal.coe_le_coe.mpr (hh hg)⟩

/-- Exact lower bounds at all powers are detected by a single spectral point. -/
theorem detector (ha : 0 < a) (hl : ∀ n r : ℕ, A ^ n ≤ (r : Tensor F (Fin 3)) → a ^ n ≤ r) :
    ∃ f : Point F, Monotone f ∧ a ≤ (f A : ℝ) := by
  obtain ⟨g, hg, _⟩ := maximum_score F 0 0 0
  obtain ⟨f, hf, _, hmax⟩ := compact_max (Spectrum.compact_points Tensor.exists_bound)
    ⟨g, g, hg, rfl⟩ Set.Subset.rfl A
  have hA : A ≠ 0 := by
    intro he
    have := hl 1 0 (by simp [he])
    simp at this
    linarith
  have hf₁ : 1 ≤ (f A : ℝ) := by
    have he := hf (Tensor.one_le A hA)
    rw [map_one] at he
    exact_mod_cast he
  refine ⟨f, hf, ?_⟩
  by_contra! hlt
  obtain ⟨n, hn⟩ := large_power (zero_lt_one.trans_le hf₁) hlt 3
  let r := ⌈2 * (f A : ℝ) ^ n⌉₊
  have hrr := one_le_pow₀ (n := n) hf₁
  have hlo : (f A : ℝ) ^ n < r := lt_of_lt_of_le (by linarith) (Nat.le_ceil _)
  have hhi : (r : ℝ) < a ^ n := lt_trans (Nat.ceil_lt_add_one (by positivity)) (by linarith)
  have hr : 0 < (r : ℝ) := (by positivity : 0 ≤ (f A : ℝ) ^ n).trans_lt hlo
  have hne : (r : Tensor F (Fin 3)) ≠ 0 := by
    intro he
    have hh : r ≤ 0 := (Tensor.natCast_le_iff (K := F) (S := Fin 3) r 0).mp (by simp [he])
    exact hr.not_ge (by exact_mod_cast hh)
  have hp (g : Point F) (hg : Monotone g) : g (A ^ n) < g (r : Tensor F (Fin 3)) := by
    rw [map_pow, map_natCast]
    exact_mod_cast (pow_le_pow_left₀ (NNReal.coe_nonneg _) (hmax g ⟨g, hg, rfl⟩) n).trans_lt hlo
  obtain ⟨C, hC⟩ := Spectrum.strictComparison Tensor.add_le_add_right Tensor.mul_le_mul_left
    Tensor.zero_le Tensor.one_le Tensor.exists_bound hne hp
  obtain ⟨m, hm⟩ := large_power hr hhi C
  have he := hl (n * m) (C * r ^ m) (by rw [pow_mul, Nat.cast_mul, Nat.cast_pow]; exact hC m)
  rw [pow_mul, Nat.cast_mul, Nat.cast_pow] at he
  exact hm.not_ge he

theorem simultaneous (ha : 0 < a) (hb : 0 < b)
    (hmax : ∀ f : Point F, Monotone f → (f B : ℝ) ≤ b)
    (hl : ∀ m n r : ℕ, (A * B ^ m) ^ n ≤ (r : Tensor F (Fin 3)) → (a * b ^ m) ^ n ≤ r) :
    ∃ f : Point F, Monotone f ∧ a ≤ (f A : ℝ) ∧ (f B : ℝ) = b := by
  have hpoint (m : ℕ) : ∃ f : Point F, Monotone f ∧ a ≤ (f A : ℝ) ∧
      a * b ^ m ≤ (f A : ℝ) * (f B : ℝ) ^ m := by
    obtain ⟨f, hf, he⟩ := detector (by positivity) (hl m)
    simp only [f.map_mul, map_pow, NNReal.coe_mul, NNReal.coe_pow] at he
    refine ⟨f, hf, ?_, he⟩
    apply le_of_mul_le_mul_right _ (pow_pos hb m)
    exact he.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (hmax f hf) _) (by positivity))
  let P := Spectrum.points (Tensor F (Fin 3)) ∩ {g | a ≤ (g A : ℝ)}
  have hc : IsCompact P := (Spectrum.compact_points Tensor.exists_bound).inter_right
    (isClosed_le continuous_const (by fun_prop))
  obtain ⟨g, hg, hg', he⟩ := hpoint 1
  obtain ⟨f, hf, hf', hm⟩ := compact_max hc ⟨g, ⟨g, hg, rfl⟩, hg'⟩ inter_subset_left B
  refine ⟨f, hf, hf'.2, le_antisymm (hmax _ hf) ?_⟩
  by_contra! hlt
  have hpos : 0 < (f B : ℝ) := by
    have hh : 0 < (g A : ℝ) * (g B : ℝ) := by rw [pow_one, pow_one] at he; exact (mul_pos ha hb).trans_le he
    exact (pos_of_mul_pos_right hh (by positivity)).trans_le (hm g ⟨⟨g, hg, rfl⟩, hg'⟩)
  obtain ⟨R, hR⟩ := Tensor.exists_bound A
  obtain ⟨m, hh⟩ := large_power hpos hlt (R / a)
  obtain ⟨g, hg, hg', he⟩ := hpoint m
  have hg₁ : (g A : ℝ) ≤ R := by exact_mod_cast (show g A ≤ R by simpa using hg hR)
  have hg₂ := hm g ⟨⟨g, hg, rfl⟩, hg'⟩
  rw [div_mul_eq_mul_div, div_lt_iff₀ ha, mul_comm (b ^ m)] at hh
  exact hh.not_ge (he.trans (mul_le_mul hg₁ (pow_le_pow_left₀ (by positivity) hg₂ _) (by positivity)
    (by positivity)))

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-!
# Generic rank decompositions

Over an infinite field the identities of rank-bounded tensors are
exactly the polynomial identities of the generic decomposition.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Border
open MvPolynomial IsLocalRing

variable {K : Type u} {E : Type*} [Field K] [Field E] {i j k r : ℕ}

private abbrev Param (i j k r : ℕ) := Fin r × (Pos i k ⊕ Pos k j ⊕ Pos i j)

private def generic (K : Type*) [Field K] (i j k r : ℕ) :
    Coordinates i j k → MvPolynomial (Param i j k r) K := fun t =>
  ∑ l, X (l, .inl t.1) * X (l, .inr (.inl t.2.1)) * X (l, .inr (.inr t.2.2))

private theorem generic_mem (g : MvPolynomial (Param i j k r) K →+* E) :
    (fun t => g (generic K i j k r t)) ∈ rankSet E i j k r := by
  refine ⟨fun l x => g (X (l, .inl x)), fun l y => g (X (l, .inr (.inl y))),
    fun l z => g (X (l, .inr (.inr z))), fun x y z => ?_⟩
  simp only [generic, map_sum, map_mul]

private theorem generic_identity {p : MvPolynomial (Coordinates i j k) K}
    (hp : eval₂ C (generic K i j k r) p = 0)
    (φ : K →+* E) {v : Coordinates i j k → E} (hv : v ∈ rankSet E i j k r) :
    eval₂ φ v p = 0 := by
  obtain ⟨a, b, c, h⟩ := hv
  let g := eval₂Hom φ (fun t : Param i j k r => Sum.elim (a t.1) (Sum.elim (b t.1) (c t.1)) t.2)
  have hg : (fun t => g (generic K i j k r t)) = v := by
    funext t
    simpa [generic, g] using h t.1 t.2.1 t.2.2
  have he := congrArg g hp
  rwa [hom_eval₂, hg, show g.comp C = φ from eval₂Hom_comp_C _ _, map_zero] at he

/-- Base-field equations of a rank locus apply also to extension-field witnesses. -/
theorem identity_of_rank [Infinite K] {p : MvPolynomial (Coordinates i j k) K}
    (hp : ∀ v ∈ rankSet K i j k r, eval v p = 0)
    (φ : K →+* E) {v : Coordinates i j k → E} (hv : v ∈ rankSet E i j k r) :
    eval₂ φ v p = 0 := by
  apply generic_identity _ φ hv
  apply MvPolynomial.funext
  intro x
  rw [map_zero, hom_eval₂, show (eval x).comp C = RingHom.id K from eval₂Hom_comp_C _ _]
  exact hp _ (generic_mem (eval x))

/-- Only the tensor entries have to be integral at the place.
The summands of the generic decomposition may have poles. -/
theorem integral_model {x : Coordinates i j k → K} (hx : ZClosure (rankSet K i j k r) x) :
    ∃ (L : Type u) (_ : Field L) (V : ValuationSubring L) (f : K →+* V)
      (v : Coordinates i j k → V),
      (fun t => (v t : L)) ∈ rankSet L i j k r ∧ ∀ t, residue V (v t) = residue V (f (x t)) := by
  let S := MvPolynomial (Param i j k r) K
  let L := FractionRing S
  let g := algebraMap S L
  let y t := g (generic K i j k r t)
  have he (p) (hp : eval₂ (g.comp C) y p = 0) : eval x p = 0 := by
    apply hx
    have hg : eval₂ C (generic K i j k r) p = 0 := by
      apply IsFractionRing.injective S L
      rw [map_zero, hom_eval₂]
      exact hp
    exact fun _ hv => generic_identity hg (RingHom.id K) hv
  obtain ⟨V, f, v, _, hv, hv'⟩ := valuation_place (g.comp C) y x he
  exact ⟨L, inferInstance, V, f, v, by simpa only [hv] using generic_mem g, hv'⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Border
end

/-!
# One pivot for a border-rank decomposition

Choose a live output of maximal valuation in the first summand. Its
multiples cancel that summand on every live output, with the multipliers
integral at the chosen place. All other outputs are projected to zero.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Border
open IsLocalRing MvPolynomial

variable {i j k r : ℕ}

def shear {R : Type*} [CommRing R] (u : Finset (Pos i j)) (o : Pos i j)
    (d : Pos i j → R) (v : Coordinates i j k → R)
    (a : Fin i → R) (b : Fin j → R) (c : Pos i j → R) : Coordinates i j k → R :=
  fun (x, y, z) => if z ∈ u then a x.1 * b y.2 * c z * (v (x, y, z) - d z * v (x, y, o)) else 0

private theorem map_shear {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (u : Finset (Pos i j)) (o : Pos i j) (d : Pos i j → R) (v : Coordinates i j k → R)
    (a : Fin i → R) (b : Fin j → R) (c : Pos i j → R) :
    φ ∘ shear u o d v a b c = shear u o (φ ∘ d) (φ ∘ v) (φ ∘ a) (φ ∘ b) (φ ∘ c) := by
  funext t
  simp only [shear, Function.comp_apply, apply_ite φ, map_mul, map_sub, map_zero]

variable {K : Type u} [Field K] {L : Type*} [Field L] {u : Finset (Pos i j)}

private theorem pivot (V : ValuationSubring L) (hu : u.Nonempty)
    {v : Coordinates i j k → L} (hv : v ∈ rankSet L i j k (r + 1)) :
    ∃ o ∈ u, ∃ d : Pos i j → V, d o = 1 ∧ ∀ a b c,
      shear u o (fun z => (d z : L)) v a b c ∈ rankSet L i j k r := by
  classical
  obtain ⟨A, B, C, h⟩ := hv
  obtain ⟨o, ho, hmax⟩ := u.exists_max_image (fun z => V.valuation (C 0 z)) hu
  have hd (z : Pos i j) : ∃ e : V, (z = o → e = 1) ∧ (z ∈ u → (e : L) * C 0 o = C 0 z) := by
    by_cases he : z = o
    · exact ⟨1, fun _ => rfl, fun _ => by simp [he]⟩
    by_cases hz : z ∈ u
    · obtain ⟨e, h'⟩ := (V.valuation_le_iff _ _).mp (hmax z hz)
      exact ⟨e, fun h => (he h).elim, fun _ => h'⟩
    · exact ⟨0, fun h => (he h).elim, fun h => (hz h).elim⟩
  choose d h₁ h₂ using hd
  refine ⟨o, ho, d, h₁ o rfl, fun a b c => ?_⟩
  let C' l z := if z ∈ u then c z * (C l z - (d z : L) * C l o) else 0
  refine ⟨fun l x => a x.1 * A l.succ x, fun l y => b y.2 * B l.succ y,
    fun l z => C' l.succ z, fun x y z => ?_⟩
  by_cases hz : z ∈ u
  swap; · simp [C', shear, hz]
  let f l := a x.1 * A l x * (b y.2 * B l y) * C' l z
  have hf : f 0 = 0 := by simp [f, C', hz, h₂ z hz]
  change ∑ l : Fin r, f l.succ = _
  rw [← zero_add (∑ l : Fin r, f l.succ), ← hf, ← Fin.sum_univ_succ]
  simp only [shear, hz, ↓reduceIte, ← h, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l _
  simp only [f, C', hz, ↓reduceIte]
  ring

/-- A residue-field pivot works simultaneously for every diagonal rescaling
over the ground field and every polynomial identity of rank at most `r`. -/
theorem shear_identity [Infinite K] {v : Coordinates i j k → K}
    (hv : ZClosure (rankSet K i j k (r + 1)) v) (hu : u.Nonempty) :
    ∃ o ∈ u, ∃ (E : Type u) (_ : Field E) (φ : K →+* E) (d : Pos i j → E), d o = 1 ∧
      ∀ (a : Fin i → K) (b : Fin j → K) (c : Pos i j → K) (p : MvPolynomial (Coordinates i j k) K),
        (∀ x ∈ rankSet K i j k r, eval x p = 0) →
        eval₂ φ (shear u o d (φ ∘ v) (φ ∘ a) (φ ∘ b) (φ ∘ c)) p = 0 := by
  obtain ⟨L, _, V, g, w, hw, he⟩ := integral_model hv
  obtain ⟨o, ho, d, hd, h⟩ := pivot V hu hw
  let π := residue V
  let e : V →+* L := V.toSubring.subtype
  refine ⟨o, ho, ResidueField V, inferInstance, π.comp g, π ∘ d, by simp [hd], ?_⟩
  intro a b c p hp
  let y := shear u o d w (g ∘ a) (g ∘ b) (g ∘ c)
  have hy : eval₂ g y p = 0 := by
    apply Subtype.ext
    change e (eval₂ g y p) = e 0
    rw [map_zero, eval₂_comp_left]
    apply identity_of_rank hp
    unfold y
    rw [map_shear]
    exact h _ _ _
  have hπ := congrArg π hy
  rw [map_zero, eval₂_comp_left] at hπ
  unfold y at hπ
  rw [map_shear, show π ∘ w = (π.comp g) ∘ v from funext he] at hπ
  exact hπ

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Border
end

/-!
# Isolating an output cell

Independent scalings of rows and columns preserve the weighted product.
Scale every row and column other than the pivot's by a parameter. On the
sheared tensor this gives a polynomial path whose value at zero simply
erases the pivot. Polynomial identities persist at zero.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Border
open MvPolynomial

variable {i j k r : ℕ} {K E : Type*} [Field K] [Field E]

private def scale {R : Type*} [One R] {n : ℕ} (o : Fin n) (t : R) (x : Fin n) : R :=
  if x = o then 1 else t

private def factor {R : Type*} [Monoid R] (o : Pos i j) (t : R) (x : Pos i j) : R :=
  scale o.1 t x.1 * scale o.2 t x.2

private def path {R : Type*} [CommRing R] (u : Finset (Pos i j)) (o : Pos i j)
    (d : Pos i j → R) (v : Coordinates i j k → R) (t : R) : Coordinates i j k → R :=
  fun (x, y, z) => if z ∈ u then v (x, y, z) - factor o t z * d z * v (x, y, o) else 0

private theorem shear_path (φ : K →+* E) (w : Fin i → Fin j → Fin k → K)
    (u : Finset (Pos i j)) (o : Pos i j) (d : Pos i j → E) {t : K} (ht : t ≠ 0) :
    shear u o d (φ ∘ coefficients w) (φ ∘ scale o.1 t⁻¹) (φ ∘ scale o.2 t⁻¹)
        (φ ∘ factor o t) = path u o d (φ ∘ coefficients w) (φ t) := by
  funext ⟨x, y, z⟩
  have hmap (p : Pos i j) : factor o (φ t) p = φ (factor o t p) := by
    simp only [factor, scale, map_mul, apply_ite φ, map_one]
  have he (p : Pos i j) :
      scale o.1 t⁻¹ x.1 * scale o.2 t⁻¹ y.2 * factor o t p * coefficients w (x, y, p) =
        coefficients w (x, y, p) := by
    by_cases h : x.1 = p.1 ∧ x.2 = y.1 ∧ y.2 = p.2
    · rw [h.1, h.2.2, factor, mul_mul_mul_comm]
      have hcancel {n : ℕ} (a b : Fin n) : scale a t⁻¹ b * scale a t b = 1 := by
        unfold scale
        split <;> simp [ht]
      rw [hcancel, hcancel, one_mul, one_mul]
    · simp [coefficients, h]
  have hz := congrArg φ (he z)
  have ho := congrArg φ (he o)
  simp only [show factor o t o = 1 by simp [factor, scale], mul_one, map_mul] at ho
  simp only [map_mul] at hz
  by_cases h : z ∈ u
  · simp only [shear, path, h, ↓reduceIte, Function.comp_apply, hmap]
    linear_combination hz - φ (factor o t z) * d z * ho
  · simp [shear, path, h]

private theorem path_zero (φ : K →+* E) (w : Fin i → Fin j → Fin k → K)
    (u : Finset (Pos i j)) (o : Pos i j) (d : Pos i j → E) (hd : d o = 1) :
    path u o d (φ ∘ coefficients w) 0 = φ ∘ coefficients (mask w (u.erase o)) := by
  funext ⟨x, y, z⟩
  have hscale : factor o (0 : E) z = if z = o then 1 else 0 := by
    simp only [factor, scale, Prod.ext_iff, ite_and, ite_mul, one_mul, zero_mul]
  have hmask : coefficients (mask w (u.erase o)) (x, y, z) =
      if z ∈ u.erase o then coefficients w (x, y, z) else 0 := by
    by_cases h : x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2
    · simp [coefficients, mask, h.1, h.2.1, h.2.2]
    · simp [coefficients, h]
  simp only [path, Function.comp_apply, hscale, hmask, Finset.mem_erase]
  by_cases he : z = o
  · simp [he, hd]
  · simp [he, apply_ite φ]

private theorem path_identity [Infinite K] (φ : K →+* E) (v : Coordinates i j k → E)
    (u : Finset (Pos i j)) (o : Pos i j) (d : Pos i j → E) (p : MvPolynomial (Coordinates i j k) K)
    (h : ∀ t : K, t ≠ 0 → eval₂ φ (path u o d v (φ t)) p = 0) :
    eval₂ φ (path u o d v 0) p = 0 := by
  let Q := eval₂ (Polynomial.C.comp φ) (path u o (Polynomial.C ∘ d) (Polynomial.C ∘ v)
    Polynomial.X) p
  have he (t : E) : Q.eval t = eval₂ φ (path u o d v t) p := by
    let ev := Polynomial.evalRingHom t
    change ev Q = _
    unfold Q
    rw [eval₂_comp_left]
    have hc : ev.comp (Polynomial.C.comp φ) = φ := by ext a; simp [ev]
    rw [hc]
    congr 1
    funext a
    simp only [Function.comp_apply, path, factor, scale, apply_ite ev, map_mul, map_one, map_sub, map_zero]
    simp [ev]
  have hz : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply ((Set.infinite_range_of_injective φ.injective).sdiff (Set.finite_singleton 0)).mono
    rintro _ ⟨⟨t, rfl⟩, ht⟩
    change Q.eval (φ t) = 0
    rw [he]
    exact h t (fun he => ht (by simp [he]))
  rw [← he, hz, Polynomial.eval_zero]

/-- Erase one cell of a nonempty set, dropping the border rank budget by one. -/
theorem erase [Infinite K] (w : Fin i → Fin j → Fin k → K) (u : Finset (Pos i j))
    (hu : u.Nonempty) (h : ZClosure (rankSet K i j k (r + 1)) (coefficients w)) :
    ∃ o ∈ u, ZClosure (rankSet K i j k r) (coefficients (mask w (u.erase o))) := by
  obtain ⟨o, ho, E, _, φ, d, hd, he⟩ := shear_identity h hu
  refine ⟨o, ho, fun p hp => ?_⟩
  apply φ.injective
  rw [map_zero, eval₂_comp, ← path_zero φ w u o d hd]
  apply path_identity
  intro t ht
  rw [← shear_path φ w u o d ht]
  exact he _ _ _ p hp

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Border
end

section
/-! # Coordinate deletion in geometric border rank -/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open MvPolynomial

variable {F : Type*} [Field F] {i j k r : ℕ} {w : Fin i → Fin j → Fin k → F}

private theorem BorderRankLE.zero (h : BorderRankLE w 0) (a : Fin i) (b : Fin j) (c : Fin k) :
    w a b c = 0 := by
  let t : Coordinates i j k := ((a, c), (c, b), (a, b))
  have he := h (X t) (by
    rintro v ⟨A, B, C, hv⟩
    rw [eval_X]
    simpa [t] using (hv (a, c) (c, b) (a, b)).symm)
  simpa [t, coefficients] using he

private theorem BorderRankLE.erase {u : Finset (Pos i j)} (hu : u.Nonempty)
    (h : BorderRankLE (mask w u) (r + 1)) :
    ∃ o ∈ u, BorderRankLE (mask w (u.erase o)) r := by
  let φ := algebraMap F (AlgebraicClosure F)
  obtain ⟨o, ho, hr⟩ := Border.erase (fun x y z => φ (mask w u x y z)) u hu h
  refine ⟨o, ho, ?_⟩
  have he : (fun x y z => φ (mask w (u.erase o) x y z)) =
      mask (fun x y z => φ (mask w u x y z)) (u.erase o) := by
    funext x y z
    by_cases h' : (x, y) ∈ u.erase o
    · simp only [mask, h', Finset.mem_of_mem_erase h', ↓reduceIte]
    · simp only [mask, h', ↓reduceIte, map_zero]
  rwa [← he] at hr

private theorem delete_mask (hw : ∀ x y z, w x y z ≠ 0) (hk : 0 < k)
    (u : Finset (Pos i j)) (hr : BorderRankLE (mask w u) r) :
    u.card ≤ r ∧ ∀ q ≤ u.card, ∃ v : Finset (Pos i j),
      v.card = q ∧ BorderRankLE (mask w v) (r - (u.card - q)) := by
  induction r generalizing u with
  | zero =>
    have he : u.card = 0 := by
      by_contra hne
      obtain ⟨⟨a, b⟩, hab⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
      have h' := hr.zero a b ⟨0, hk⟩
      simp [mask, hab, hw] at h'
    exact ⟨he.le, fun q hq => ⟨u, by omega, by simpa using hr⟩⟩
  | succ r ih =>
    by_cases he : u.Nonempty
    · obtain ⟨o, ho, he'⟩ := BorderRankLE.erase he hr
      obtain ⟨hle, hd⟩ := ih (u.erase o) he'
      have hcard := Finset.card_erase_add_one ho
      refine ⟨by omega, fun q hq => ?_⟩
      rcases eq_or_lt_of_le hq with rfl | hlt
      · exact ⟨u, rfl, by simpa using hr⟩
      · rw [show r + 1 - (u.card - q) = r - ((u.erase o).card - q) by omega]
        exact hd q (by omega)
    · have he' := Finset.not_nonempty_iff_eq_empty.mp he
      subst u
      simp only [Finset.card_empty, zero_le, true_and, Nat.le_zero, Nat.zero_sub, Nat.sub_zero]
      exact fun q hq => ⟨∅, by simp [hq], hr⟩

/-- Retaining some set of exactly `q` output cells lowers the geometric
border-rank budget by the number deleted. No hypothesis on the field or
on the rank of the retained set is required. -/
theorem BorderRankLE.delete (h : BorderRankLE w r) (hw : ∀ x y z, w x y z ≠ 0)
    (hk : 0 < k) {q : ℕ} (hq : q ≤ i * j) :
    i * j ≤ r ∧ ∃ u : Finset (Pos i j), u.card = q ∧ BorderRankLE (mask w u) (r - (i * j - q)) := by
  have he : mask w Finset.univ = w := by funext a b c; simp [mask]
  have h' := delete_mask hw hk Finset.univ (he.symm ▸ h)
  simp only [Finset.card_univ, Pos, Fintype.card_prod, Fintype.card_fin] at h'
  exact ⟨h'.1, h'.2 q hq⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-!
# Spectral sublevels are Zariski closed

The rank interpolation argument works for any spectral point because
a linear combination costs at most the sum of its constituent prices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Spectral
open scoped NNReal

variable {K S : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
  {X : S → Type} [∀ s, Fintype (X s)] {A : Set ((∀ s, X s) → K)} {T : (∀ s, X s) → K}

def copyTable (T : (∀ s, X s) → K) (n : ℕ) (x : ∀ s, Fin n → X s) : K :=
  ∏ l, T (fun s => x s l)

omit [DecidableEq S] in
theorem table_pow (T : (∀ s, X s) → K) (n : ℕ) :
    Tensor.ofRaw (Raw.ofTable (fun s => Fin n → X s) (copyTable T n)) =
      (Tensor.ofRaw (Raw.ofTable X T)) ^ n := by
  classical
  induction n with
  | zero =>
    rw [pow_zero]
    apply Tensor.ofRaw_eq
    refine Raw.equiv_coeff (fun s => Equiv.ofUnique (Fin 0 → X s) Unit) fun x => ?_
    change (∀ s, Fin 0 → X s) at x
    change _ = (1 : Raw K S).coeff (fun _ => ())
    rw [Raw.coeff_ofTable]
    change copyTable T 0 x = ∑ _ : Unit, ∏ _ : S, (1 : K)
    simp [copyTable]
  | succ n ih =>
    rw [pow_succ', ← ih, ← Tensor.ofRaw_mul]
    apply Tensor.ofRaw_eq
    refine Raw.equiv_coeff (fun s => (Fin.consEquiv (fun _ => X s)).symm) fun x => ?_
    change (∀ s, Fin (n + 1) → X s) at x
    change _ = (Raw.ofTable X T * Raw.ofTable (fun s => Fin n → X s)
      (copyTable T n)).coeff (fun s => (x s 0, fun l => x s l.succ))
    rw [Raw.coeff_ofTable, Raw.coeff_mul]
    change _ = (Raw.ofTable X T).coeff (fun s => x s 0) *
      (Raw.ofTable (fun s => Fin n → X s) (copyTable T n)).coeff (fun s l => x s l.succ)
    rw [Raw.coeff_ofTable X T (fun s => x s 0),
      Raw.coeff_ofTable _ (copyTable T n) (fun s l => x s l.succ)]
    unfold copyTable
    rw [Fin.prod_univ_succ]

theorem ZClosure.price (h : ZClosure A T) (f : Tensor K S →+* ℝ≥0) (hf : Monotone f)
    {B : ℝ} (hB : 0 ≤ B) (hprice : ∀ t ∈ A, (f (Tensor.ofRaw (Raw.ofTable X t)) : ℝ) ≤ B) :
    (f (Tensor.ofRaw (Raw.ofTable X T)) : ℝ) ≤ B := by
  classical
  apply TensorSpectrum.le_of_pow_le_polynomial_mul_pow _ _ 1 (Fintype.card (∀ s, X s))
    hB (by positivity) (by norm_num) (by positivity)
  intro n _
  obtain ⟨d, hd, y, c, hy, he⟩ := h.power n
  have hs := hf (Tensor.span_le (fun s => Fin n → X s) (copyTable T n)
    (fun i => copyTable (y i) n) c (fun t => he (fun l s => t s l)))
  simp only [table_pow, map_pow, map_sum] at hs
  rw [one_mul, Real.rpow_natCast]
  calc
    _ ≤ ∑ t : Fin d, (f (Tensor.ofRaw (Raw.ofTable X (y t))) : ℝ) ^ n := by exact_mod_cast hs
    _ ≤ ∑ _ : Fin d, B ^ n := Finset.sum_le_sum fun t _ =>
      pow_le_pow_left₀ (by positivity) (hprice _ (hy t)) _
    _ = d * B ^ n := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hd) (by positivity)

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-! # Weighted products as three-site spectral tensors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle
open Spectral

variable {F : Type} [Field F] {i j k r : ℕ}

theorem legs_card (i j k : ℕ) (s : Fin 3) :
    Fintype.card (legs i j k s) ≤ max (i * j) (max (i * k) (j * k)) := by
  fin_cases s
  · change Fintype.card (Pos i j) ≤ _
    simp only [Pos, Fintype.card_prod, Fintype.card_fin]
    exact le_max_left _ _
  · change Fintype.card (Pos i k) ≤ _
    simp only [Pos, Fintype.card_prod, Fintype.card_fin]
    exact (le_max_left _ _).trans (le_max_right _ _)
  · change Fintype.card (Pos k j) ≤ _
    simp only [Pos, Fintype.card_prod, Fintype.card_fin, mul_comm k j]
    exact (le_max_right _ _).trans (le_max_right _ _)

theorem wtensor_le_iff (T : Coordinates i j k → F) :
    wtensor T ≤ (r : Tensor F (Fin 3)) ↔ T ∈ rankSet F i j k r := by
  constructor
  · intro h
    obtain ⟨A, he⟩ := Speedup.exists_form h
    refine ⟨fun l => A l 1, fun l => A l 2, fun l => A l 0, fun x y z => ?_⟩
    have hh := congrFun he (tripleLeg (α := legs i j k) z x y)
    simp only [Speedup.form, Fin.prod_univ_three] at hh
    change T (x, y, z) = ∑ l, A l 0 z * A l 1 x * A l 2 y at hh
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hh.symm
  · rintro ⟨a, b, c, h⟩
    let A : Speedup.Family F (legs i j k) r := fun l => tripleLeg (c l) (a l) (b l)
    have he : T ∘ ungroup = Speedup.form A := by
      funext x
      simp only [Speedup.form, Fin.prod_univ_three]
      change T (x 1, x 2, x 0) = ∑ l, c l (x 0) * a l (x 1) * b l (x 2)
      simpa only [mul_comm, mul_left_comm, mul_assoc] using (h (x 1) (x 2) (x 0)).symm
    rw [wtensor, he]
    exact Speedup.form_le A

theorem ordinary_le_tensor (F : Type) [Field F] (hi : 0 < i) (hj : 0 < j) (hk : 0 < k) :
    weightedTensor (fun (_ : Fin i) (_ : Fin j) (_ : Fin k) => (1 : F)) ≤ tensor F i j k := by
  let proj : (s : Fin 3) → legs i j k s → (Fin i × Fin j) × Fin k :=
    tripleLeg (fun z => (z, ⟨0, hk⟩)) (fun x => ((x.1, ⟨0, hj⟩), x.2))
      (fun y => ((⟨0, hi⟩, y.2), y.1))
  refine Raw.Restricts.pullback proj fun x => ?_
  change (∀ s, legs i j k s) at x
  rw [Raw.coeff_ofTable, coeff_wires (fun s => proj s (x s))]
  rfl


variable {i' j' k' I J K : ℕ}

private def split {n m N p q P : ℕ} (f : Fin N ≃ Pos n m) (g : Fin P ≃ Pos p q) (v : Pos N P) :=
    (((f v.1).1, (g v.2).1), ((f v.1).2, (g v.2).2))

private theorem product_le {w : Fin i → Fin j → Fin k → F} {v : Fin i' → Fin j' → Fin k' → F}
    {u : Fin I → Fin J → Fin K → F} (x : Fin I ≃ Pos i i') (y : Fin J ≃ Pos j j')
    (z : Fin K ≃ Pos k k')
    (h : ∀ (X : Pos I K) (Y : Pos K J) (Z : Pos I J),
      coefficients u (X, Y, Z) =
      coefficients w ((split x z X).1, (split z y Y).1, (split x y Z).1) *
      coefficients v ((split x z X).2, (split z y Y).2, (split x y Z).2)) :
    weightedTensor u ≤ weightedTensor w * weightedTensor v := by
  let proj : (s : Fin 3) → legs I J K s → legs i j k s × legs i' j' k' s :=
    tripleLeg (split x y) (split x z) (split z y)
  refine Raw.Restricts.pullback proj fun t => ?_
  change (∀ s, legs I J K s) at t
  rw [Raw.coeff_ofTable]
  let A := Raw.ofTable (legs i j k) (coefficients w ∘ ungroup)
  let B := Raw.ofTable (legs i' j' k') (coefficients v ∘ ungroup)
  change _ = (A * B).coeff (fun s => proj s (t s))
  rw [Raw.coeff_mul A B (fun s => proj s (t s))]
  unfold A B
  rw [Raw.coeff_ofTable _ _ (fun s => (proj s (t s)).1),
    Raw.coeff_ofTable _ _ (fun s => (proj s (t s)).2)]
  exact h (t 1) (t 2) (t 0)

private theorem product_full {w : Fin i → Fin j → Fin k → F} {v : Fin i' → Fin j' → Fin k' → F}
    (hw : ∀ a b c, w a b c ≠ 0) (hv : ∀ a b c, v a b c ≠ 0)
    (x : Fin I ≃ Pos i i') (y : Fin J ≃ Pos j j') (z : Fin K ≃ Pos k k') :
    ∃ u : Fin I → Fin J → Fin K → F, (∀ a b c, u a b c ≠ 0) ∧
      weightedTensor u ≤ weightedTensor w * weightedTensor v := by
  let u a b c := w (x a).1 (y b).1 (z c).1 * v (x a).2 (y b).2 (z c).2
  refine ⟨u, fun _ _ _ => mul_ne_zero (hw _ _ _) (hv _ _ _), ?_⟩
  apply product_le x y z
  have he {n m N : ℕ} (f : Fin N ≃ Pos n m) (a b : Fin N) :
      a = b ↔ (f a).1 = (f b).1 ∧ (f a).2 = (f b).2 :=
    f.injective.eq_iff.symm.trans Prod.ext_iff
  intro X Y Z
  simp only [coefficients, split, u, ite_mul, mul_ite, zero_mul, mul_zero, ← ite_and,
    he x X.1 Z.1, he z X.2 Y.1, he y Y.2 Z.2, and_comm, and_left_comm, and_assoc]

/-- Tensor products retain a full-support weighting after pairing the
indices on each side. -/
theorem tensor_full {w : Fin i → Fin j → Fin k → F} {v : Fin i' → Fin j' → Fin k' → F}
    (hw : ∀ a b c, w a b c ≠ 0) (hv : ∀ a b c, v a b c ≠ 0)
    (hi : I = i * i') (hj : J = j * j') (hk : K = k * k') :
    ∃ u : Fin I → Fin J → Fin K → F, (∀ a b c, u a b c ≠ 0) ∧
      weightedTensor u ≤ weightedTensor w * weightedTensor v := by
  let x := (finCongr hi).trans finProdFinEquiv.symm
  let y := (finCongr hj).trans finProdFinEquiv.symm
  let z := (finCongr hk).trans finProdFinEquiv.symm
  exact product_full hw hv x y z

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end

/-!
# Powers and field transfer for geometric border rank

Powering is a polynomial map of coefficient spaces, so exact
decompositions suffice to verify its action on the closure.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k r : ℕ} {w : Fin i → Fin j → Fin k → F}

namespace Border

def digit {i j n : ℕ} (x : Pos (i ^ n) (j ^ n)) (l : Fin n) : Pos i j :=
  (finFunctionFinEquiv.symm x.1 l, finFunctionFinEquiv.symm x.2 l)

theorem coefficients_pow (w : Fin i → Fin j → Fin k → F) (n : ℕ)
    (x : Pos (i ^ n) (k ^ n)) (y : Pos (k ^ n) (j ^ n)) (z : Pos (i ^ n) (j ^ n)) :
    (∏ l, coefficients w (digit x l, digit y l, digit z l)) =
      coefficients (WPower w n) (x, y, z) := by
  classical
  unfold coefficients digit WPower
  simp only [Fintype.prod_ite_zero, forall_and, ← funext_iff, Equiv.symm_apply_eq,
    Equiv.apply_symm_apply]

def powerTable {R : Type*} [CommMonoid R] (v : Coordinates i j k → R) (n : ℕ) :
    Coordinates (i ^ n) (j ^ n) (k ^ n) → R :=
  fun (x, y, z) => ∏ l, v (digit x l, digit y l, digit z l)

theorem rankSet_power {v : Coordinates i j k → F} (hv : v ∈ rankSet F i j k r) (n : ℕ) :
    powerTable v n ∈ rankSet F (i ^ n) (j ^ n) (k ^ n) (r ^ n) := by
  obtain ⟨A, B, C, h⟩ := hv
  refine ⟨fun t x => ∏ l, A (finFunctionFinEquiv.symm t l) (digit x l),
    fun t y => ∏ l, B (finFunctionFinEquiv.symm t l) (digit y l),
    fun t z => ∏ l, C (finFunctionFinEquiv.symm t l) (digit z l), fun x y z => ?_⟩
  rw [← finFunctionFinEquiv.sum_comp]
  simp only [powerTable, ← h, Equiv.symm_apply_apply, Fintype.prod_sum,
    Finset.prod_mul_distrib]

end Border

open Border MvPolynomial

theorem BorderRankLE.pow (h : BorderRankLE w r) (n : ℕ) : BorderRankLE (WPower w n) (r ^ n) := by
  let K := AlgebraicClosure F
  let v x y z := algebraMap F K (w x y z)
  have hv : (fun x y z => algebraMap F K (WPower w n x y z)) = WPower v n := by
    funext x y z
    simp only [WPower, map_prod, v]
  unfold BorderRankLE
  rw [hv, show coefficients (WPower v n) = powerTable (coefficients v) n from
    funext fun ⟨x, y, z⟩ => (coefficients_pow v n x y z).symm]
  intro p hp
  let q := eval₂ C (powerTable X n) p
  have he (z : Coordinates i j k → K) : eval z q = eval (powerTable z n) p := by
    unfold q
    rw [hom_eval₂, show (eval z).comp C = RingHom.id K from eval₂Hom_comp_C _ _]
    have hh : (fun t => eval z (powerTable X n t)) = powerTable z n := by
      funext t
      simp only [powerTable, map_prod, eval_X]
    rw [hh]
    rfl
  rw [← he]
  exact h q (fun z hz => (he z).trans (hp _ (rankSet_power hz n)))

/-- Adjoin the weights together with countably many distinct elements
of the algebraic closure. Infinitude ensures rank-locus identities
over this smaller field apply over the entire closure. -/
theorem BorderRankLE.small (h : BorderRankLE w r) :
    ∃ (K : Type) (_ : Field K) (_ : Infinite K) (_ : Algebra K (AlgebraicClosure F))
      (u : Fin i → Fin j → Fin k → K),
      (∀ x y z, u x y z = 0 ↔ w x y z = 0) ∧ ZClosure (rankSet K i j k r) (coefficients u) := by
  let L := AlgebraicClosure F
  let a := algebraMap F L
  let e := Infinite.natEmbedding L
  let data : (Fin i × Fin j × Fin k) ⊕ ℕ → L :=
    Sum.elim (fun p => a (w p.1 p.2.1 p.2.2)) e
  obtain ⟨K, _, φ, v, hv⟩ := small_coefficients data
  have : Infinite K := Infinite.of_injective (fun n : ℕ => v (.inr n)) (by
    intro n m he
    apply e.injective
    exact (hv (.inr n)).symm.trans ((congrArg φ he).trans (hv (.inr m))))
  let u x y z := v (.inl (x, y, z))
  have hu x y z : φ (u x y z) = a (w x y z) := hv (.inl (x, y, z))
  refine ⟨K, inferInstance, inferInstance, φ.toAlgebra, u, ?_, fun p hp => ?_⟩
  · intro x y z
    rw [← φ.injective.eq_iff, hu, map_zero, ← map_zero a, a.injective.eq_iff]
  have he : φ ∘ coefficients u = coefficients (fun x y z => a (w x y z)) := by
    funext t
    simp only [Function.comp_apply, coefficients, apply_ite φ, map_zero, hu]
  apply φ.injective
  rw [map_zero, eval₂_comp, he, ← eval_map]
  exact h _ fun z hz => by rw [eval_map]; exact identity_of_rank hp φ hz

end OAI.LinearAlgebra.MatrixExponent.Rectangle
end
