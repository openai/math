import OAI.LinearAlgebra.MatrixExponent.Valued.Uniform
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.TreePrice
import Mathlib.Analysis.Real.Cardinality
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Basic
import OAI.LinearAlgebra.MatrixExponent.Valued.Continuity
import OAI.LinearAlgebra.MatrixExponent.Prices.Chord
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.Rigidity
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.Tripod
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Dual
import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Existence of a valued lift

From a price over an infinite field, construct a price on every
rationally valued field extension trivial on the base. The discount
fixes scalar values, and power interpolation gives integral monotonicity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued
open Spectral

variable {E K S : Type} [Field E] [Field K] [Algebra E K] [Infinite E]
  [Fintype S] [Nonempty S] {O : Subring K} (v : AddValuation K (WithTop ℚ))

theorem ITensor.scalar_pow (x : K) (n : ℕ) :
    ITensor.scalar O S (x ^ n) = ITensor.scalar O S x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, ITensor.scalar_one]
  | succ n ih => rw [pow_succ, ITensor.scalar_mul, ih, pow_succ]

private theorem scalar_values (g : ITensor O S →+* ℝ) (hg : Monotone g) (b : ℝ)
    (h : ∀ (c : K) (m : ℤ), (↑(m : ℚ) : WithTop ℚ) ≤ v c →
      g (ITensor.scalar _ _ c) ≤ Real.exp (-(m : ℝ) * b)) (c : K) (q : ℚ) (hq : v c = ↑q) :
    g (ITensor.scalar _ _ c) = Real.exp (-(q : ℝ) * b) := by
  have integer (x : K) (m : ℤ) (hm : v x = ↑(m : ℚ)) :
      g (ITensor.scalar _ _ x) = Real.exp (-(m : ℝ) * b) := by
    have hx : x ≠ 0 := by rintro rfl; simp at hm
    have hi : v x⁻¹ = ↑((-m : ℤ) : ℚ) := by rw [v.map_inv, hm, Int.cast_neg]; rfl
    apply le_antisymm (h _ _ hm.ge)
    have he := h _ _ hi.ge
    have e : g (ITensor.scalar O S x) * g (ITensor.scalar O S x⁻¹) = 1 := by
      rw [← g.map_mul, ← ITensor.scalar_mul, mul_inv_cancel₀ hx, ITensor.scalar_one, map_one]
    have H := mul_le_mul_of_nonneg_left he (ITensor.positive_scalar g hg x hx).le
    rw [e, Int.cast_neg, neg_neg] at H
    rw [neg_mul, Real.exp_neg, ← one_div, div_le_iff₀ (Real.exp_pos _)]
    exact H
  have hn : v (c ^ q.den) = ↑(q.num : ℚ) := by
    rw [v.map_pow, hq, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_comm, Rat.mul_den_eq_num]
  have eq := integer _ _ hn
  rw [ITensor.scalar_pow, map_pow] at eq
  have hz : 0 ≤ g (ITensor.scalar O S c) := by simpa using hg (ITensor.zero_le (ITensor.scalar O S c))
  apply (pow_left_inj₀ hz (Real.exp_pos _).le q.den_pos.ne').mp
  rw [eq, ← Real.exp_nat_mul]
  have he : (q : ℝ) * q.den = q.num := by exact_mod_cast q.mul_den_eq_num
  rw [← he]
  congr 1
  ring

theorem exists_lift (hv : constants E K ≤ integralRing v) (f : Tensor E S →+* ℝ)
    (hf : Monotone f) (b : ℝ) (hb : 0 < b) :
    ∃ g : ITensor (integralRing v) S →+* ℝ, Monotone g ∧
      (∀ A, g (ITensor.fromBase hv A) = f A) ∧
      ∀ (c : K) (q : ℚ), v c = ↑q → g (ITensor.scalar _ _ c) = Real.exp (-(q : ℝ) * b) := by
  obtain ⟨g, hg, he, hb⟩ := weighted_character v hv f hf b hb
  have hp (c : K) (hc : c ∈ integralRing v) : g (ITensor.scalar _ _ c) ≤ 1 := by
    simpa using hb c 0 hc
  let φ (A : Raw K S) := g (ITensor.ofRaw A)
  have hm {A B : Raw K S} (h : Restricts (integralRing v) A B) : φ B ≤ φ A :=
    ITensor.integral_mono g hg hv hp h
  let p : ITensor (integralRing v) S →+* ℝ :=
    { toFun := Quotient.lift φ (fun _ _ h => le_antisymm (hm h.2) (hm h.1))
      map_zero' := map_zero g
      map_one' := map_one g
      map_add' := fun x y => Quotient.inductionOn₂ x y fun a b => g.map_add (ITensor.ofRaw a) (ITensor.ofRaw b)
      map_mul' := fun x y => Quotient.inductionOn₂ x y fun a b => g.map_mul (ITensor.ofRaw a) (ITensor.ofRaw b) }
  refine ⟨p, fun x y => Quotient.inductionOn₂ x y fun _ _ h => hm h, ?_, ?_⟩
  · intro A
    exact Quotient.inductionOn A fun a => he (Tensor.ofRaw a)
  · exact fun c q hq => scalar_values v g hg b hb c q hq

end OAI.LinearAlgebra.MatrixExponent.Valued
end

section
/-! # Simultaneous bounds over the open valuation disk -/

namespace OAI.LinearAlgebra.MatrixExponent.Valued
open Prices Motion K0

variable {E S : Type} [Field E] [Fintype S] [Nonempty S]
local notation "O" => integralRing (val E)

/-- Uniform strict slack in finitely many price bounds suffices. -/
def DiskSync (f : ITensor O S →+* ℝ) : Prop :=
  ∀ (I : Type) [Fintype I] (A : I → K0 E → ITensor O (S ⊕ Unit)),
    (∀ i, ∃ d, ITensor.Family (A i) d) →
    ∀ (p q : I → ℝ), (∀ i, p i < q i) →
    (∀ z ∈ O, ∃ g : ITensor O (S ⊕ Unit) →+* ℝ,
      Monotone g ∧ (∀ T, g (ITensor.pad Unit T) = f T) ∧ (∀ i, g (A i z) ≤ p i)) →
    ∃ g : ITensor O (S ⊕ Unit) →+* ℝ, Monotone g ∧ (∀ T, g (ITensor.pad Unit T) = f T) ∧
      ∀ i z, 0 < val E z → g (A i z) ≤ q i

end OAI.LinearAlgebra.MatrixExponent.Valued
end

/-!
# From the open valuation disk to its boundary

At degree k use nodes of valuation at least 1/(k+1), with pairwise
differences of exactly that valuation. One factor t clears every
interpolation denominator. Its cost is independent of the power.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
open Prices Motion K0

variable {E S : Type} [Field E] [Infinite E] [Fintype S] [Nonempty S]
local notation "O" => integralRing (val E)

omit [Infinite E] in
private theorem scale_basis {K : Type} [Field K] (V : Subring K) (φ : E →+* K)
    (hc : ∀ a, φ a ∈ V) {s : K} (hs : s ∈ V) (hn : s ≠ 0) {k : ℕ} (u : Fin (k + 1) → E)
    (x : K) (hx : x ∈ V) (i : Fin (k + 1)) :
    s ^ (k + 1) * (Lagrange.basis Finset.univ (fun j => s * φ (u j)) i).eval x ∈ V := by
  let v (i : Fin (k + 1)) := s * φ (u i)
  have hv (j) : v j ∈ V := V.mul_mem hs (hc _)
  have h (j : Fin (k + 1)) : s * (Lagrange.basisDivisor (v i) (v j)).eval x ∈ V := by
    simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_sub, Polynomial.eval_X]
    rw [← mul_assoc]
    apply V.mul_mem _ (V.sub_mem hx (hv j))
    unfold v
    rw [← mul_sub, mul_inv_rev, mul_left_comm, mul_inv_cancel₀ hn, mul_one, ← map_sub, ← map_inv₀]
    exact hc _
  have hp := V.prod_mem (t := Finset.univ.erase i) (fun j _ => h j)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel] at hp
  rw [pow_succ', mul_assoc, Lagrange.basis, Polynomial.eval_prod]
  exact V.mul_mem hs hp

private theorem small_nodes (k : ℕ) (x : K0 E) (hx : x ∈ O) :
    ∃ v : Fin (k + 1) → K0 E, Function.Injective v ∧ (∀ i, 0 < val E (v i)) ∧
      ∀ i, t (E := E) 1 * (Lagrange.basis Finset.univ v i).eval x ∈ O := by
  let s := t (E := E) (((k + 1 : ℕ) : ℚ)⁻¹)
  have hs : 0 < val E s := by rw [show val E s = _ from val_t _]; exact WithTop.coe_pos.mpr (by positivity)
  have hn : s ≠ 0 := t_ne_zero _
  have he : s ^ (k + 1) = t (E := E) 1 := by
    unfold s
    rw [t_pow, mul_inv_cancel₀ (by positivity)]
  let u : Fin (k + 1) ↪ E := Fin.valEmbedding.trans (Infinite.natEmbedding E)
  let v i := s * C (u i)
  have hi : Function.Injective v := by
    intro i j h
    change s * C (u i) = s * C (u j) at h
    have hh : C (u i) = C (u j) := mul_left_cancel₀ hn h
    have hh' : u i = u j := (C (E := E)).injective hh
    exact u.injective hh'
  have hc (a : E) : C a ∈ O := by
    change 0 ≤ val E (C a)
    by_cases e : a = 0 <;> simp [e]
  have hv (i) : 0 < val E (v i) := by
    change 0 < val E (s * C (u i))
    rw [AddValuation.map_mul]
    exact hs.trans_le (le_add_of_nonneg_right (show 0 ≤ val E (C (u i)) from hc (u i)))
  refine ⟨v, hi, hv, fun i => ?_⟩
  rw [← he]
  exact scale_basis O C hc (show s ∈ O from hs.le) hn u x hx i

/-- Any monotone valued character bounded on the open disk is bounded by
the same constant on the closed valuation disk. -/
theorem Family.bound_disk {A : K0 E → ITensor O S} {d : ℕ} (h : Family A d)
    (f : ITensor O S →+* ℝ) (hf : Monotone f) {r : ℝ}
    (hr : ∀ x, 0 < val E x → f (A x) ≤ r) (x : K0 E) (hx : x ∈ O) : f (A x) ≤ r := by
  have pos := positive_scalar f hf (t 1) (t_ne_zero _)
  let H := 1 / f (scalar O S (t 1))
  have hH : 0 < H := one_div_pos.mpr pos
  have hb (a : K0 E) (ha : t (E := E) 1 * a ∈ O) : f (scalar O S a) ≤ H := by
    have he := hf (scalar_le_one O _ ha)
    rw [scalar_mul, map_mul, map_one, mul_comm] at he
    exact (le_div_iff₀ pos).mpr he
  have hz (A : ITensor O S) : 0 ≤ f A := by simpa using hf (zero_le A)
  have hr0 := (hz _).trans (hr 0 (by simp))
  refine TensorSpectrum.le_of_pow_le_polynomial_mul_pow r (f (A x)) (H * (d + 1)) 1 hr0 (hz _)
    (by positivity) zero_le_one fun n _ => ?_
  obtain ⟨v, hi, hv, hw⟩ := small_nodes (n * d) x hx
  have he := hf ((h.pow n).weighted (by simp) v hi x)
  rw [map_sum, map_pow] at he
  refine he.trans ?_
  rw [Real.rpow_one]
  calc
    _ ≤ ∑ _i : Fin (n * d + 1), H * r ^ n := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [map_mul, map_pow]
      exact mul_le_mul (hb _ (hw i)) (pow_le_pow_left₀ (hz _) (hr _ (hv i)) _)
        (pow_nonneg (hz _) _) hH.le
    _ ≤ _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ← mul_assoc, mul_comm _ H, mul_assoc H (↑d + 1)]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 n)
      apply mul_le_mul_of_nonneg_left _ hH.le
      push_cast
      linarith

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end

/-!
# Recovering an ordinary simultaneous price

A valued extension controls all positive-valuation shifts at once.
Power interpolation recovers the bound at each constant. It suffices
to have strict slack and finitely many families because each ordinary
closure test uses only a finite list of indices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued
open Spectral Prices Motion K0 Filter Topology

variable {E F : Type} [Field E] [Field F] [Infinite E] [Infinite F]
local notation "O" => integralRing (val E)

omit [Infinite F] in
/-- Passing all finite tests with arbitrarily small slack suffices. -/
private theorem finite_slack {S I J : Type} [Fintype S] [Nonempty S]
    (f : Tensor F S →+* ℝ) (hf : Monotone f)
    (A : I → J → Tensor F (S ⊕ Unit)) (p : I → ℝ)
    (h : ∀ (L : Finset I) (ε : ℝ), 0 < ε →
      ∃ g : Tensor F (S ⊕ Unit) →+* ℝ, Monotone g ∧ (∀ T, g (Tensor.pad Unit T) = f T) ∧
        ∀ i ∈ L, ∀ j, g (A i j) ≤ p i + ε) :
    ∃ g : Tensor F (S ⊕ Unit) →+* ℝ, Monotone g ∧ (∀ T, g (Tensor.pad Unit T) = f T) ∧
      ∀ i j, g (A i j) ≤ p i := by
  classical
  let X (i : I × J) := A i.1 i.2
  let P (i : I × J) := p i.1
  have test (w : List (I × J)) (T : Tensor F S) (ht : Tensor.pad Unit T ≤ (w.map X).prod) :
      f T ≤ (w.map P).prod := by
    let L := (w.map Prod.fst).toFinset
    let q (ε : ℝ) := (w.map (fun i => P i + ε)).prod
    have hm (ε : ℝ) (hε : 0 < ε) : f T ≤ q ε := by
      obtain ⟨g, hg, he, hb⟩ := h L ε hε
      have hw (u : List (I × J)) (hu : ∀ i ∈ u, i.1 ∈ L) :
          g (u.map X).prod ≤ (u.map (fun i => P i + ε)).prod := by
        induction u with
        | nil => simp
        | cons i u ih =>
          simp only [List.map_cons, List.prod_cons]
          rw [g.map_mul]
          have hn (B : Tensor F (S ⊕ Unit)) : 0 ≤ g B := by simpa using hg (Tensor.zero_le B)
          have hl := hb i.1 (hu i (by simp)) i.2
          exact mul_le_mul hl (ih (fun a ha => hu a (by simp [ha]))) (hn _) ((hn _).trans hl)
      exact ((he _).symm.trans_le (hg ht)).trans
        (hw w fun i hi => List.mem_toFinset.mpr (List.mem_map.mpr ⟨i, hi, rfl⟩))
    have hc : Continuous q := by
      unfold q
      fun_prop
    have hh : f T ≤ q 0 := ge_of_tendsto (hc.continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)) (eventually_mem_nhdsWithin.mono hm)
    simpa only [q, add_zero] using hh
  obtain ⟨g, hg, he, hb⟩ := (Tensor.extension_iff f hf X P).mpr test
  exact ⟨g, hg, he, fun i j => hb (i, j)⟩

theorem sharedPrice_of_disk [Algebra F (K0 E)] (hv : constants F (K0 E) ≤ O)
    (hs : ∀ (S : Type) [Fintype S] [DecidableEq S] [Nonempty S] (f : ITensor O S →+* ℝ),
      Monotone f →
      (∀ (c : K0 E) (q : ℚ), val E c = ↑q → f (ITensor.scalar O S c) = Real.exp (-(q : ℝ))) →
      DiskSync f) : SharedPrice F := by
  intro S I _ _ _ f hf B X _ P p h
  obtain ⟨g, hg, he, hval⟩ := exists_lift (val E) hv f hf 1 zero_lt_one
  simp only [mul_one] at hval
  let A i : K0 E → ITensor O (S ⊕ Unit) := ITensor.liftFamily (X i) (P i)
  have hA i : ∃ d, ITensor.Family (A i) d := ITensor.of_polynomial _ _
  have hb (L : Finset I) (ε : ℝ) (hε : 0 < ε) :
      ∃ k : Tensor F (S ⊕ Unit) →+* ℝ, Monotone k ∧ (∀ T, k (Tensor.pad Unit T) = f T) ∧
        ∀ i ∈ L, ∀ j, k (evalFamily (X i) (P i) j) ≤ p i + ε := by
    obtain ⟨k, hk, hp, hl⟩ := hs S g hg hval L (fun i => A i.val) (fun i => hA i.val)
      (fun i => p i.val) (fun i => p i.val + ε) (fun _ => lt_add_of_pos_right _ hε)
      (fun z hz => by
        obtain ⟨k, hk, hp, hl⟩ := ITensor.lift_shared hv f hf g hg he B X P p h z hz
        exact ⟨k, hk, hp, fun i => hl i.val⟩)
    refine ⟨k.comp (ITensor.fromBase hv), hk.comp (ITensor.fromBase_mono hv), ?_, ?_⟩
    · intro T
      rw [RingHom.comp_apply, ITensor.fromBase_pad, hp, he]
    · intro i hi z
      rw [RingHom.comp_apply, ← ITensor.liftFamily_constant]
      exact (hA i).choose_spec.bound_disk k hk (hl ⟨i, hi⟩) _ (hv ⟨z, rfl⟩)
  obtain ⟨k, hk, hp, hl⟩ := finite_slack f hf (fun i => evalFamily (X i) (P i)) p hb
  exact ⟨k, hk, hp, fun i z _ => hl i z⟩

/-- An uncountable field of constant parameters over any base. -/
theorem uncountable_extension (F : Type) [Field F] :
    ∃ (E : Type) (_ : Field E) (_ : Uncountable E) (_ : Algebra F (K0 E)),
      constants F (K0 E) ≤ integralRing (val E) := by
  let R := MvPolynomial ℝ F
  let E := FractionRing R
  have hu : Uncountable E := ((IsFractionRing.injective R E).comp MvPolynomial.X_injective).uncountable
  let _ : Algebra F (K0 E) := (C.comp (algebraMap F E)).toAlgebra
  refine ⟨E, inferInstance, hu, inferInstance, ?_⟩
  rintro _ ⟨x, rfl⟩
  change 0 ≤ val E (C (algebraMap F E x))
  by_cases h : algebraMap F E x = 0 <;> simp [h]

end OAI.LinearAlgebra.MatrixExponent.Valued
end

/-! # The spectral pseudometric on the additive group of disk shifts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.Problem
open Spectral Prices Motion K0 Filter

variable {F E S I U V : Type} [Field F] [Field E] [Algebra F (K0 E)]
    [Fintype S] [Nonempty S] [DecidableEq S] [Fintype I] [Countable F] [Uncountable E]
    (H : Problem F E S I) [Fintype U] [DecidableEq U]

def spectral (p : U → G E) := H.price (idx ∘ p)

omit [Fintype I] [Countable F] [Uncountable E] in
theorem spectral_mono (p : U → G E) : Monotone (H.spectral p) :=
  (H.model _).point_mono H.inc

theorem spectral_pull [Fintype V] [DecidableEq V] (p : U → G E) (x : V → U)
    (B : Tensor F (S ⊕ V)) : H.spectral (p ∘ x) B = H.spectral p (Tensor.place (Sum.map id x) B) :=
  H.price_pull (idx ∘ p) (fun i => (idx_pos (p i)).le) x B

theorem spectral_shift (p : U → G E) (g : G E) :
    H.spectral (fun i => g * p i) = H.spectral p := by
  unfold spectral
  rw [show idx ∘ (fun i => g * p i) = translate (idx ∘ p) (idx g) by
    funext i; exact (idx_mul _ _).trans (add_comm _ _)]
  exact H.price_shift _ (fun i => (idx_pos (p i)).le) (idx_pos g).le

def gap (x y : G E) : ℝ :=
  Tensor.dist (H.spectral (fun i : Bool => if i then x else y)) (.inr true) (.inr false)

theorem gap_eq (p : U → G E) (i j : U) :
    H.gap (p i) (p j) = Tensor.dist (H.spectral p) (.inr i) (.inr j) := by
  let x (t : Bool) := if t then i else j
  unfold gap Tensor.dist
  rw [show (fun t : Bool => if t then p i else p j) = p ∘ x by funext t; cases t <;> rfl,
    spectral_pull, Tensor.place_wire]
  rfl

abbrev metric : PseudoMetricSpace (G E) where
  dist := H.gap
  dist_self x := (H.gap_eq (fun _ : Unit => x) () ()).trans (Tensor.dist_self _ _)
  dist_comm x y := by
    let p := ![x, y]
    change H.gap (p 0) (p 1) = H.gap (p 1) (p 0)
    rw [gap_eq, gap_eq, Tensor.dist_comm]
  dist_triangle x y z := by
    let p := ![x, y, z]
    change H.gap (p 0) (p 2) ≤ H.gap (p 0) (p 1) + H.gap (p 1) (p 2)
    rw [gap_eq, gap_eq, gap_eq]
    exact Tensor.dist_triangle _ (H.spectral_mono p) _ _ _

omit [Fintype I] [Countable F] [Uncountable E] in
theorem gap_bound (x y : G E) : H.gap x y ≤ 1 := Tensor.dist_le_one _ (H.spectral_mono _) _ _

def values (p : U → G E) : Tensor F U → ℝ :=
  Tensor.values 1 (H.spectral p) ∘ Tensor.place Sum.inr

theorem value_wire (p : U → G E) (i j) : H.values p (Tensor.wire F i j 2) = H.gap (p i) (p j) := by
  rw [values, Function.comp_apply, Tensor.place_wire, gap_eq]
  exact one_mul _

theorem value_shift (p : U → G E) (g : G E) : H.values (fun i => g * p i) = H.values p := by
  unfold values
  rw [spectral_shift]

def atlas : @Atlas F (G E) _ H.metric := by
  let _ := H.metric
  refine ⟨fun p => H.values p, ?_, fun p => H.value_wire p, ?_⟩
  · intro B _ _ _ p
    have h : Tensor.values 1 (H.spectral p) ∈ Tensor.ordinary F (S ⊕ B) 1 :=
      ⟨1, ⟨zero_le_one, le_rfl⟩, _, H.spectral_mono p, rfl⟩
    refine ⟨1 * Fintype.card B, Tensor.ordinary_restrict h Sum.inr fun i j => ?_⟩
    exact (one_mul _).le.trans (Tensor.dist_le_one _ (H.spectral_mono p) _ _)
  · intro B C _ _ _ _ _ _ p x
    funext A
    simp only [values, Function.comp_apply, Tensor.values, spectral_pull, ← Tensor.place_comp]
    rfl

theorem value_star (a b : U → K0 E) (x : K0 E) (hx : 0 ≤ val E x) {n : ℕ}
    (c : Fin n → K0 E) (r : Option (Fin n) → ℚ)
    (hc : ∀ j, 0 ≤ val E (c j)) (hd : ∀ i j, i ≠ j → val E (c i - c j) = 0)
    (hr : ∀ j, 0 < r j) (ha : ∀ i, 0 < val E (a i)) (hb : ∀ i, 0 < val E (b i))
    (ho : ∀ i, 0 < val E (t (-r none) * b i)) :
    ∀ᶠ u : E in cocountable, ∀ A : Tensor F U,
      H.values (fun i => shift (aff a b x i)) A ≤ ∑ j, weight r j *
        H.values (fun i => shift (aff a b (armEnd c r (C u) j) i)) A := by
  have prod {v y : K0 E} (hv : 0 < val E v) (hy : 0 ≤ val E y) : 0 < val E (v * y) := by
    rw [(val E).map_mul]
    exact hv.trans_le (le_add_of_nonneg_right hy)
  have hm (i) := (val E).map_lt_add (ha i) (prod (hb i) hx)
  have he (j y) (hy : 0 ≤ val E y) (i) : 0 < val E (aff a b (armEnd c r y j) i) := by
    apply (val E).map_lt_add (ha i)
    cases j with
    | none =>
      rw [armEnd, ← mul_assoc, mul_comm (b i)]
      exact prod (ho i) hy
    | some j =>
      apply prod (hb i) ((val E).map_le_add (hc j) ?_)
      rw [(val E).map_mul, val_t]
      exact add_nonneg (WithTop.coe_nonneg.mpr (hr _).le) hy
  have h := H.star a b x hx c r hc hd hr (fun i => (hm i).le) (fun j y hy i => (he j y hy i).le)
  refine h.mono fun u hu A => ?_
  have eq (p : U → K0 E) (hp : ∀ i, 0 < val E (p i)) :
      H.values (fun i => shift (p i)) A = Real.log (H.price p (Tensor.place Sum.inr A)) / Real.log 2 := by
    have e : idx ∘ (fun i => shift (p i)) = p := funext fun i => idx_shift (hp i)
    simp only [values, spectral, e, Function.comp_apply, Tensor.values, one_mul]
  have h' j := eq _ (he j _ (integral_C u))
  rw [eq (aff a b x) hm]
  simp only [h', ← mul_div_assoc, ← Finset.sum_div]
  exact div_le_div_of_nonneg_right (hu _) (Real.log_nonneg (by norm_num))

end OAI.LinearAlgebra.MatrixExponent.Valued.Problem
end

/-!
# Synchronization from collapse of the pinned sites

Every finite tuple of shifts is realized by an assignment dominated
by its generic profile on ordinary tensors. If all its wire distances
vanish, integral transport identifies the sites even on valued inputs.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued
open Spectral ITensor Prices Motion K0 Assignment

variable {F E S I : Type} [Field F] [Field E] [Algebra F (K0 E)]
    [Fintype S] [Nonempty S] [DecidableEq S] [Fintype I] [Countable F] [Uncountable E]

namespace Problem
variable (H : Problem F E S I)

private theorem joint_collapse {U : Type} [Fintype U] [DecidableEq U] [Nonempty U]
    (h : ∀ x y, H.gap x y = 0) (x : U → G E) :
    ∃ g : Assignment H.f Unit, ∀ i u, g.val (H.A i (idx (x u))) ≤ H.q i := by
  obtain ⟨g, hg, hb⟩ := H.price_controls (idx ∘ x) (fun i => (idx_pos _).le) (RingOf E).zero_mem
  have hv (i j : U) : Assignment.dist H.inc g (.inr i) (.inr j) = 0 := by
    have hw := hb (Tensor.wire F (.inr i) (.inr j) 2)
    change g.point H.inc _ ≤ H.spectral x _ at hw
    rw [Tensor.price_wire _ (g.point_mono H.inc) _ _ (by decide),
      Tensor.price_wire _ (H.spectral_mono x) _ _ (by decide), ← H.gap_eq x, h] at hw
    exact le_antisymm ((Real.rpow_le_rpow_left_iff (by norm_num)).mp hw)
      (Assignment.dist_nonneg _ _ _ _)
  let j := Classical.arbitrary U
  refine ⟨g.atSite j, fun i u => ?_⟩
  rw [show g.atSite j = g.atSite u from pull_eq H.inc g _ _ (fun _ => hv j u)]
  have e := hg u (some i)
  change (g.atSite u).val (H.A i (idx (x u) + 0)) ≤ H.q i at e
  simpa only [add_zero] using e

theorem collapse (h : ∀ x y, H.gap x y = 0) :
    ∃ g : Assignment H.f Unit, ∀ i z, 0 < val E z → g.val (H.A i z) ≤ H.q i := by
  classical
  let A (j : I × G E) := H.A j.1 (idx j.2)
  let p (j : I × G E) := H.q j.1
  have ht (w : List (I × G E)) : assisted (pad Unit) H.f (w.map A).prod ≤ (w.map p).prod := by
    let L := insert 1 (w.map Prod.snd).toFinset
    let _ : Nonempty ↥L := ⟨⟨1, Finset.mem_insert_self _ _⟩⟩
    obtain ⟨g, hg⟩ := H.joint_collapse h (fun x : L => x.val)
    refine ((assisted_minimum H.f H.mono _).2 ⟨g.val, g.mono, g.old, rfl⟩).trans ?_
    have aux (v : List (I × G E)) (hv : ∀ j ∈ v, j.2 ∈ L) :
        g.val (v.map A).prod ≤ (v.map p).prod := by
      induction v with
      | nil => simp
      | cons j v ih =>
        simp only [List.map_cons, List.prod_cons]
        rw [g.val.map_mul]
        have hj := hg j.1 ⟨j.2, hv j (by simp)⟩
        exact mul_le_mul hj (ih (fun j h => hv _ (by simp [h]))) (g.nonneg _) ((g.nonneg _).trans hj)
    exact aux w fun j hj => Finset.mem_insert_of_mem (List.mem_toFinset.mpr (List.mem_map.mpr ⟨j, hj, rfl⟩))
  obtain ⟨g, hg⟩ := (Assignment.exists_iff H.mono A p).mpr ht
  exact ⟨g, fun i z hz => by simpa only [A, p, idx_shift hz] using hg (i, shift z)⟩

end Problem

theorem diskSync_of_collapse (inc : constants F (K0 E) ≤ RingOf E)
    (f : ITensor (RingOf E) S →+* ℝ) (hf : Monotone f)
    (hs : ∀ c (q : ℚ), val E c = ↑q → f (scalar _ _ c) = Real.exp (-(q : ℝ)))
    (h : ∀ (I : Type) [Fintype I] (H : Problem F E S I), ∀ x y, H.gap x y = 0) :
    DiskSync f := by
  intro I _ A ha p q hp feas
  have hh x (hx : x ∈ RingOf E) : ∃ g : Assignment f Unit, g.Supports (fun i => A i x) p := by
    obtain ⟨g, hg, he, hp⟩ := feas x hx
    exact ⟨⟨g, hg, he⟩, hp⟩
  let o := Classical.arbitrary S
  obtain ⟨r, hr, hmin⟩ := pin_exists inc o hf (fun (x : RingOf E) i => A i x.val) q (fun x => by
    obtain ⟨g, hg⟩ := hh x.val x.property
    exact ⟨g, fun i => (hg i).trans (hp i).le⟩)
  let H : Problem F E S I :=
    { inc := inc, f := f, mono := hf, scal := hs, o := o, A := A, poly := ha, p := p, q := q
      slack := hp, feasible := hh, r := r, bound := hr
      least := ⟨fun x hx => hmin.1 ⟨x, hx⟩, fun _ hv => hmin.2 (fun x => hv x.val x.property)⟩ }
  obtain ⟨g, hg⟩ := H.collapse (h I H)
  exact ⟨g.val, g.mono, g.old, hg⟩

end OAI.LinearAlgebra.MatrixExponent.Valued
end

/-!
# Rigidity of the pinned disk

Compatibility gives an isometric action on the closed hull.
The submean comparison extends from orbit tests to the hull,
and continuity at the marked orbit point forces it to be fixed.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.Problem
open Spectral Prices Motion K0 Filter

variable {F E S I : Type} [Field F] [Field E] [Algebra F (K0 E)]
    [Fintype S] [Nonempty S] [DecidableEq S] [Fintype I] [Countable F] [Uncountable E]
    (H : Problem F E S I)

private theorem gap_small (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℚ, 0 < N ∧ ∀ g : G E, ↑N ≤ val E (idx g) → H.gap g 1 ≤ ε := by
  obtain ⟨N, hN, h⟩ := H.continuity ε hε
  refine ⟨N, hN, fun g hg => ?_⟩
  let z := idx ∘ (fun i : Bool => if i then g else 1)
  have hz (i : Bool) : z i ∈ RingOf E := (idx_pos _).le
  obtain ⟨x, hx, hp, hj⟩ := H.model_peak z hz
  exact h (translate z x) (H.model z) (fun i => (RingOf E).add_mem (hz i) hx)
    (by simpa [translate, z] using hg) hp.1 hj

theorem gap_eq_zero (hF : ∀ (Y : Type) [PseudoMetricSpace Y], Leaves F E Y → False) (x y : G E) : H.gap x y = 0 := by
  let _ := H.metric
  obtain ⟨Y, _, _, _, _, C, B, o, hd, hp, hm⟩ :=
    H.atlas.action_hull H.gap_bound (fun _ _ _ _ p g => H.value_shift p g)
  have he (p q : G E) : Dist.dist (p • o) (q • o) = H.gap p q := by
    have h := congrFun (hp _ ![p, q]) (Tensor.wire F 0 1 2)
    rw [B.wire, H.atlas.wire] at h
    exact h
  have mov : MovingAt E B o := by
    intro S _ _ _ a b v hv n c r hc he hr ha hb ho
    filter_upwards [H.value_star a b v hv c r hc he hr ha hb ho] with u hu T
    simp only [hp]
    exact hu T
  have hs (ε : ℝ) (hε : 0 < ε) : ∃ b, 0 < b ∧ profile E o b < ε := by
    obtain ⟨N, hN, h⟩ := H.gap_small _ (half_pos hε)
    refine ⟨N, Rat.cast_pos.mpr hN, lt_of_le_of_lt ?_ (half_lt_self hε)⟩
    apply displacement_le
    intro g hg
    rw [_root_.dist_comm]
    simpa using (he g 1).le.trans (h g ((mem_level _ _).mp hg))
  have hf := (Moving.of_dense mov C hd).constant C hm o hs hF
  rw [← he, hf, hf, _root_.dist_self]

end OAI.LinearAlgebra.MatrixExponent.Valued.Problem
end

section
/-!
# Synchronization or contact

Nonconstant motion supplies three fixed branches on the disk tree.
One-sided private products give contact on their homogeneous tangent,
and the tripod comparison propagates contact to every shape.
Otherwise all pinned profiles collapse, giving simultaneous pricing.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Valued

theorem contact_of_not_shared {F : Type} [Field F] [Infinite F] [Countable F]
    (h : ¬ Prices.SharedPrice F) : omega F = 9 / 4 ∧ Rectangle.Rigidity F := by
  by_contra bad
  apply h
  obtain ⟨E, _, _, _, he⟩ := uncountable_extension F
  refine sharedPrice_of_disk he fun S _ _ _ f hf hs => diskSync_of_collapse he f hf hs ?_
  exact fun I _ H => H.gap_eq_zero (fun _ _ t => bad t.contact)

theorem shared_of_dual {F : Type} [Field F] [Infinite F] [Countable F]
    (h : 1 / 2 < Rectangle.dual F 1 1) : Prices.SharedPrice F := by
  by_contra bad
  obtain ⟨hs, hr⟩ := contact_of_not_shared bad
  exact h.ne' (Rectangle.dual_square hr hs)

end OAI.LinearAlgebra.MatrixExponent.Valued

namespace OAI.LinearAlgebra.MatrixExponent

/-- Descend the square and rectangular conclusions from the countable
algebraic closure. The network estimates can stay over the finite field. -/
theorem contact_of_not_shared {F : Type} [Field F] [Finite F]
    (h : ¬ Prices.SharedPrice (AlgebraicClosure F)) : omega F = 9 / 4 ∧ Rectangle.Rigidity F := by
  let K := AlgebraicClosure F
  have : Countable K := Cardinal.mk_le_aleph0_iff.mp
    ((Algebra.IsAlgebraic.cardinalMk_le_max F K).trans (max_le Cardinal.mk_le_aleph0 le_rfl))
  obtain ⟨hs, hr⟩ := Valued.contact_of_not_shared h
  refine ⟨(omega_extension F K).symm.trans hs, Or.inl fun a b c ha hb hc => ?_⟩
  exact (Rectangle.exponent_extension F K ha.le hb.le hc.le).symm.trans
    (Rectangle.positive_shapes hr hs ha hb hc)

theorem shared_of_saving {F : Type} [Field F] [Finite F] (h : omega F < 9 / 4) :
    Prices.SharedPrice (AlgebraicClosure F) := by
  by_contra bad
  exact h.ne (contact_of_not_shared bad).1

end OAI.LinearAlgebra.MatrixExponent
end
