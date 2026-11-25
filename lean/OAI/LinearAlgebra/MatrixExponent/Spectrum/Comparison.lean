import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.Compact
import OAI.LinearAlgebra.TensorSpectrum.Additive.Catalyst
import OAI.LinearAlgebra.TensorSpectrum.AdditiveCone.Encoding
import OAI.LinearAlgebra.TensorSpectrum.Multiplicative.Character
import Mathlib.RingTheory.Congruence.Defs

section
/-! # Pointwise compactness of the spectrum -/

open scoped NNReal
open Set

namespace OAI.LinearAlgebra.MatrixExponent.Spectrum

/-- Semiring homomorphisms preserving the order, in the topology of pointwise convergence. -/
def points (T : Type*) [CommSemiring T] [PartialOrder T] : Set (T → ℝ≥0) :=
  {v | ∃ g : T →+* ℝ≥0, Monotone g ∧ ⇑g = v}

variable {S T : Type*} [CommSemiring T] [PartialOrder T]

private theorem closed_points : IsClosed (points T) := by
  have heq : points T =
      {v | v 0 = 0 ∧ v 1 = 1 ∧ (∀ x y, v (x + y) = v x + v y) ∧
        (∀ x y, v (x * y) = v x * v y) ∧ Monotone v} := by
    ext v
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨map_zero g, map_one g, map_add g, map_mul g, hg⟩
    · rintro ⟨hz, ho, ha, hm, hv⟩
      exact ⟨{toFun := v, map_zero' := hz, map_one' := ho, map_add' := ha, map_mul' := hm},
        hv, rfl⟩
  rw [heq]
  simp only [ofPred_and, ofPred_forall]
  refine (isClosed_eq (continuous_apply 0) continuous_const).inter <|
    (isClosed_eq (continuous_apply 1) continuous_const).inter <|
    IsClosed.inter ?_ (IsClosed.inter ?_ isClosed_monotone)
  · exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply _) ((continuous_apply x).add (continuous_apply y))
  · exact isClosed_iInter fun x => isClosed_iInter fun y =>
      isClosed_eq (continuous_apply _) ((continuous_apply x).mul (continuous_apply y))

theorem compact_points (hbound : ∀ a : T, ∃ n : ℕ, a ≤ (n : T)) :
    IsCompact (points T) := by
  choose R hR using hbound
  have box : IsCompact {v : T → ℝ≥0 | ∀ a, v a ∈ Icc 0 (R a : ℝ≥0)} :=
    isCompact_pi_infinite fun _ => isCompact_Icc
  refine box.of_isClosed_subset closed_points ?_
  rintro _ ⟨g, hg, rfl⟩ a
  exact ⟨zero_le, by simpa only [map_natCast] using hg (hR a)⟩

/-- If no spectral point realizes the observations, finitely many already
separate them from every point by a positive squared distance. -/
theorem separated (hbound : ∀ a : T, ∃ n : ℕ, a ≤ (n : T)) (i : S → T) (f : S → ℝ≥0)
    (h : ¬ ∃ g : T →+* ℝ≥0, Monotone g ∧ ∀ a, g (i a) = f a) :
    ∃ (U : Finset S) (ε : ℝ), 0 < ε ∧ ∀ g : T →+* ℝ≥0, Monotone g →
      ε ≤ ∑ a ∈ U, ((g (i a) : ℝ) - f a) ^ 2 := by
  classical
  by_cases hn : (points T).Nonempty
  swap
  · exact ⟨∅, 1, zero_lt_one, fun g hg => (hn ⟨g, g, hg, rfl⟩).elim⟩
  have hc := compact_points hbound
  let V (a : S) := {v : T → ℝ≥0 | v (i a) ≠ f a}
  have hopen (a : S) : IsOpen (V a) := isOpen_ne_fun (continuous_apply _) continuous_const
  have hcover : points T ⊆ ⋃ a, V a := by
    rintro _ ⟨g, hg, rfl⟩
    apply mem_iUnion.mpr
    exact not_forall.mp (fun heq => h ⟨g, hg, heq⟩)
  obtain ⟨U, hU⟩ := hc.elim_finite_subcover V hopen hcover
  let d (v : T → ℝ≥0) := ∑ a ∈ U, ((v (i a) : ℝ) - f a) ^ 2
  have hd : Continuous d := by unfold d; fun_prop
  obtain ⟨v, hv, hmin⟩ := hc.exists_isMinOn hn hd.continuousOn
  refine ⟨U, d v, ?_, fun g hg => hmin ⟨g, hg, rfl⟩⟩
  obtain ⟨a, ha, hne⟩ := mem_iUnion₂.mp (hU hv)
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨a, ha,
    sq_pos_of_ne_zero (sub_ne_zero.mpr (fun heq => hne (Subtype.ext heq)))⟩

end OAI.LinearAlgebra.MatrixExponent.Spectrum
end

section
/-! # Absorbing an additive catalyst without order cancellation -/

namespace OAI.LinearAlgebra.MatrixExponent.Spectrum

variable {S : Type*} [CommSemiring S] [PartialOrder S]

/-- Repeating the strict gain pays for an extra factor `D + 1`.
The resulting multiplicative catalyst dominates the unit and works
unchanged for every power. -/
theorem absorb
    (hadd : ∀ a b c : S, a ≤ b → a + c ≤ b + c)
    (hmul : ∀ a b c : S, a ≤ b → c * a ≤ c * b)
    (hzero : ∀ a : S, 0 ≤ a)
    (hbound : ∀ a : S, ∃ n : ℕ, a ≤ (n : S))
    {x y D s : S} (hy : 1 ≤ y) (h : D + 1 + x * s ≤ D + y * s) :
    ∃ C : ℕ, ∀ r : ℕ, x ^ r ≤ (C : S) * y ^ r := by
  have iterate (n : ℕ) : D + (n : S) + x * ((n : S) * s) ≤ D + y * ((n : S) * s) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ]
      calc
        _ = (D + (n : S) + x * ((n : S) * s)) + (1 + x * s) := by ring
        _ ≤ (D + y * ((n : S) * s)) + (1 + x * s) := hadd _ _ _ ih
        _ = (D + 1 + x * s) + y * ((n : S) * s) := by ring
        _ ≤ (D + y * s) + y * ((n : S) * s) := hadd _ _ _ h
        _ = _ := by ring
  have le_sum (a b : S) : a ≤ b + a := by
    simpa only [zero_add] using hadd _ _ a (hzero b)
  obtain ⟨n, hn⟩ := hbound (x * (D + 1))
  let t := (n : S) * s + (D + 1)
  have ht : 1 ≤ t := (le_sum 1 D).trans (le_sum _ _)
  have hD : D ≤ y * (D + 1) := calc
    D ≤ 1 + D := le_sum D 1
    _ = (D + 1) * 1 := by ring
    _ ≤ (D + 1) * y := hmul _ _ _ hy
    _ = y * (D + 1) := mul_comm _ _
  have hcat : x * t ≤ y * t := calc
    x * t = x * (D + 1) + x * ((n : S) * s) := by unfold t; ring
    _ ≤ D + (n : S) + x * ((n : S) * s) := hadd _ _ _ (hn.trans (le_sum _ _))
    _ ≤ D + y * ((n : S) * s) := iterate n
    _ ≤ y * (D + 1) + y * ((n : S) * s) := hadd _ _ _ hD
    _ = y * t := by unfold t; ring
  obtain ⟨C, hC⟩ := hbound t
  refine ⟨C, fun r => ?_⟩
  calc
    x ^ r = x ^ r * 1 := (mul_one _).symm
    _ ≤ x ^ r * t := hmul _ _ _ ht
    _ ≤ y ^ r * t := TensorSpectrum.catalytic_power_iteration hmul hcat r
    _ ≤ y ^ r * (C : S) := hmul _ _ _ hC
    _ = (C : S) * y ^ r := mul_comm _ _

end OAI.LinearAlgebra.MatrixExponent.Spectrum
end

section
/-!
# Strict spectral comparison

Adjoin the reversed comparison `y ≤ x` to the order, then identify
mutually comparable elements. Any character of the resulting semiring
would contradict the assumed strict inequality. The additive-state
obstruction gives a strict gain in the quotient. Lifting that comparison
provides the catalyst needed for all powers, with one constant overhead.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Spectrum

open scoped NNReal

variable {S : Type*} [CommSemiring S] [PartialOrder S]
variable (hadd : ∀ a b c : S, a ≤ b → a + c ≤ b + c)
variable (hmul : ∀ a b c : S, a ≤ b → c * a ≤ c * b)
variable {x y : S}

private def extended (x y a b : S) : Prop :=
  ∃ t : S, a + x * t ≤ b + y * t

private theorem extend {a b : S} (h : a ≤ b) : extended x y a b :=
  ⟨0, by simpa using h⟩

include hadd in
private theorem chain {a b c : S} (h : extended x y a b) (k : extended x y b c) :
    extended x y a c := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨t, ht⟩ := k
  refine ⟨s + t, ?_⟩
  calc
    a + x * (s + t) = (a + x * s) + x * t := by ring
    _ ≤ (b + y * s) + x * t := hadd _ _ _ hs
    _ = (b + x * t) + y * s := by ring
    _ ≤ (c + y * t) + y * s := hadd _ _ _ ht
    _ = c + y * (s + t) := by ring

include hadd in
private theorem extAdd {a b : S} (c : S) (h : extended x y a b) :
    extended x y (a + c) (b + c) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨s, by simpa only [add_right_comm _ c] using hadd _ _ c hs⟩

include hmul in
private theorem extMul {a b : S} (c : S) (h : extended x y a b) :
    extended x y (c * a) (c * b) := by
  obtain ⟨s, hs⟩ := h
  exact ⟨c * s, by simpa only [mul_add, mul_left_comm c] using hmul _ _ c hs⟩

private def con (x y : S) : RingCon S where
  r a b := extended x y a b ∧ extended x y b a
  iseqv := ⟨fun _ => ⟨extend le_rfl, extend le_rfl⟩, fun h => h.symm,
    fun h k => ⟨chain hadd h.1 k.1, chain hadd k.2 h.2⟩⟩
  add' := by
    have f {a b c d : S} (h : extended x y a b) (k : extended x y c d) :
        extended x y (a + c) (b + d) :=
      chain hadd (extAdd hadd c h) (by simpa only [add_comm _ b] using extAdd hadd b k)
    exact fun _ _ _ _ h k => ⟨f h.1 k.1, f h.2 k.2⟩
  mul' := by
    have f {a b c d : S} (h : extended x y a b) (k : extended x y c d) :
        extended x y (a * c) (b * d) :=
      chain hadd (extMul hmul a k) (by simpa only [mul_comm d] using extMul hmul d h)
    exact fun _ _ _ _ h k => ⟨f h.1 k.1, f h.2 k.2⟩

@[instance_reducible]
private def quotientOrder (x y : S) : PartialOrder (con hadd hmul x y).Quotient where
  le := Quotient.lift₂ (extended x y) fun _ _ _ _ h k => propext
    ⟨fun t => chain hadd h.2 (chain hadd t k.1),
     fun t => chain hadd h.1 (chain hadd t k.2)⟩
  le_refl a := Quotient.inductionOn a fun _ => extend le_rfl
  le_trans a b c := Quotient.inductionOn₃ a b c fun _ _ _ => chain hadd
  le_antisymm a b := Quotient.inductionOn₂ a b fun _ _ h k => Quotient.sound ⟨h, k⟩

include hadd hmul in
/-- A strict inequality at all spectral points allows a single overhead
independent of the power. -/
theorem strictComparison
    (hzero : ∀ a : S, 0 ≤ a) (hunit : ∀ a : S, a ≠ 0 → 1 ≤ a)
    (hbound : ∀ a : S, ∃ n : ℕ, a ≤ (n : S)) (hy : y ≠ 0)
    (h : ∀ f : S →+* ℝ≥0, Monotone f → f x < f y) :
    ∃ C : ℕ, ∀ r : ℕ, x ^ r ≤ (C : S) * y ^ r := by
  let q := con hadd hmul x y
  let : PartialOrder q.Quotient := quotientOrder hadd hmul x y
  have mono : Monotone q.mk' := fun _ _ h => extend h
  have rev : q.mk' y ≤ q.mk' x := ⟨1, by simp [add_comm]⟩
  have add' : ∀ a b c : q.Quotient, a ≤ b → a + c ≤ b + c :=
    fun a b c => Quotient.inductionOn₃ a b c fun _ _ c => extAdd hadd c
  have mul' : ∀ c : q.Quotient, Monotone (fun a => c * a) :=
    fun c a b => Quotient.inductionOn₃ a b c fun _ _ c => extMul hmul c
  have zero' : ∀ a : q.Quotient, 0 ≤ a :=
    fun a => Quotient.inductionOn a fun a => mono (hzero a)
  have unit' : ∀ a : q.Quotient, a ≠ 0 → 1 ≤ a := by
    rintro a ha
    obtain ⟨a, rfl⟩ := q.mk'_surjective a
    exact mono (hunit a (fun e => ha (by simp [e])))
  have bound' : ∀ a : q.Quotient, ∃ n : ℕ, a ≤ (n : q.Quotient) := by
    intro a
    obtain ⟨a, rfl⟩ := q.mk'_surjective a
    obtain ⟨n, hn⟩ := hbound a
    exact ⟨n, by simpa using mono hn⟩
  choose R hR using bound'
  have hempty : TensorSpectrum.stateSet (0 : q.Quotient) 0 = ∅ := by
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hne
    obtain ⟨f, hf, _⟩ := TensorSpectrum.exists_nnreal_character_of_nonempty_stateSet
      0 0 R zero' unit' hR mul' hne
    exact (h (f.comp q.mk') (hf.comp mono)).not_ge (hf rev)
  obtain ⟨m, hm, D, _, hg⟩ := TensorSpectrum.catalyst_of_no_state
    0 0 R add' zero' hR hempty
  simp only [Nat.cast_zero, zero_mul, add_zero] at hg
  obtain ⟨d, rfl⟩ := q.mk'_surjective D
  have h1 : (1 : S) ≤ (m : S) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simpa [Nat.cast_succ] using hadd _ _ 1 (hzero (n : S))
  have step : q.mk' (d + 1) ≤ q.mk' d := by
    refine le_trans ?_ hg
    simpa [add_comm] using mono (hadd _ _ d h1)
  obtain ⟨s, hs⟩ := step
  exact absorb hadd hmul hzero hbound (hunit y hy) hs

end OAI.LinearAlgebra.MatrixExponent.Spectrum
end
