import OAI.LinearAlgebra.TensorSpectrum.Multiplicative.Character
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Multiplicative states with linear inequalities

The inequalities hold after multiplication by every element. This
ensures invariance under normalized multiplication. In a valued
restriction semiring, nonzero elements can have price below one;
an additive multiple suffices for the fixed-point argument.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Spectrum

open OAI.LinearAlgebra.TensorSpectrum Set

variable {S I : Type*} [CommSemiring S] [PartialOrder S]

theorem constrained_character
    (hmul : ∀ a b c : S, a ≤ b → c * a ≤ c * b) (hzero : ∀ a : S, 0 ≤ a)
    (A B : I → S) (c : I → ℝ) (fixed : Set I)
    (lower : ∀ x ≠ 0, ∃ i ∈ fixed, A i = 1 ∧ B i = x)
    (upper : ∀ x, ∃ i ∈ fixed, A i = x ∧ B i = 1)
    (hs : ∀ J : Finset I, ∃ f : S →+ ℝ, f 1 = 1 ∧ Monotone f ∧
      ∀ i, i ∈ fixed ∨ i ∈ J → ∀ U, f (A i * U) ≤ c i * f (B i * U)) :
    ∃ g : S →+* ℝ, Monotone g ∧ ∀ i, g (A i) ≤ c i * g (B i) := by
  choose R hR eR h1 using upper
  let C (i : I) : Set (S → ℝ) := {f | ∀ U, f (A i * U) ≤ c i * f (B i * U)}
  let K := stateSet (0 : S) 0 ∩ ⋂ i, C i
  let V := stateSet (0 : S) 0 ∩ ⋂ i ∈ fixed, C i
  have incl : K ⊆ V := fun _ hf => ⟨hf.1, mem_iInter₂.mpr fun i _ => mem_iInter.mp hf.2 i⟩
  have closed (i : I) : IsClosed (C i) := by
    unfold C
    rw [ofPred_forall]
    exact isClosed_iInter fun U =>
      isClosed_le (continuous_apply _) (continuous_const.mul (continuous_apply _))
  have bound (f : S → ℝ) (hf : f ∈ V) (x : S) : 0 ≤ f x ∧ f x ≤ c (R x) := by
    refine ⟨by rw [← hf.1.1]; exact hf.1.2.2.2.1 (hzero x), ?_⟩
    simpa only [eR, h1, mul_one, hf.1.2.1] using mem_iInter₂.mp hf.2 (R x) (hR x) 1
  have hc : IsCompact V := by
    have hb : IsCompact {f : S → ℝ | ∀ x, f x ∈ Icc 0 (c (R x))} :=
      isCompact_pi_infinite fun _ => isCompact_Icc
    exact hb.of_isClosed_subset
      ((stateSet_isClosed 0 0).inter (isClosed_iInter fun i => isClosed_iInter fun _ => closed i))
      bound
  have compact : IsCompact K :=
    hc.of_isClosed_subset ((stateSet_isClosed 0 0).inter (isClosed_iInter closed)) incl
  have ne : K.Nonempty := by
    have hh : (V ∩ ⋂ i, C i).Nonempty := by
      apply hc.inter_iInter_nonempty C closed
      intro J
      obtain ⟨f, h1, hf, hj⟩ := hs J
      exact ⟨f, ⟨⟨f.map_zero, h1, f.map_add, hf, by simp⟩,
        mem_iInter₂.mpr fun i hi => hj i (.inl hi)⟩, mem_iInter₂.mpr fun i hi => hj i (.inr hi)⟩
    exact hh.mono fun _ h => ⟨h.1.1, h.2⟩
  have convex : Convex ℝ K := by
    apply (stateSet_convex (0 : S) 0).inter
    apply convex_iInter
    intro i f hf g hg a b ha hb _ U
    change a * f (A i * U) + b * g (A i * U) ≤ c i * (a * f (B i * U) + b * g (B i * U))
    calc
      _ ≤ a * (c i * f (B i * U)) + b * (c i * g (B i * U)) :=
        add_le_add (mul_le_mul_of_nonneg_left (hf U) ha) (mul_le_mul_of_nonneg_left (hg U) hb)
      _ = _ := by ring
  have nat (f : S → ℝ) (hf : f ∈ K) (n : ℕ) (z : S) : f (n * z) = n * f z := by
    let F : S →+ ℝ := { toFun := f, map_zero' := hf.1.1, map_add' := hf.1.2.2.1 }
    change F _ = _ * F _
    rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  have lo (z : S) (hz : z ≠ 0) : ∃ n : ℕ, 0 < n ∧ ∀ f ∈ K, 1 ≤ f (n * z) := by
    obtain ⟨i, _, ha, hb⟩ := lower z hz
    obtain ⟨n, hn⟩ := exists_nat_gt (max 0 (c i))
    refine ⟨n, Nat.cast_pos.mp ((le_max_left _ _).trans_lt hn), fun f hf => ?_⟩
    rw [nat f hf]
    have hl := mem_iInter.mp hf.2 i 1
    simp only [mul_one, ha, hb, hf.1.2.1] at hl
    exact hl.trans (mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hn.le) (bound f (incl hf) z).1)
  have pos (f : S → ℝ) (hf : f ∈ K) (z : S) (hz : z ≠ 0) : 0 < f z := by
    obtain ⟨n, _, hn⟩ := lo z hz
    have h := zero_lt_one.trans_le (hn f hf)
    rw [nat f hf] at h
    exact pos_of_mul_pos_right h (Nat.cast_nonneg _)
  have invariant (z : S) (hz : z ≠ 0) : MapsTo (projective z) K K := by
    intro f hf
    have hp := pos f hf z hz
    refine ⟨⟨projective_zero z f hf.1.1, projective_one z f hp.ne', ?_, ?_, ?_⟩, ?_⟩
    · intro x y
      unfold projective
      rw [mul_add, hf.1.2.2.1, add_div]
    · exact fun x y h => div_le_div_of_nonneg_right (hf.1.2.2.2.1 (hmul _ _ _ h)) hp.le
    · simp [projective, hf.1.1]
    · refine mem_iInter.mpr fun i U => ?_
      change f (z * (A i * U)) / f z ≤ c i * (f (z * (B i * U)) / f z)
      rw [mul_left_comm z, mul_left_comm z, ← mul_div_assoc]
      exact div_le_div_of_nonneg_right (mem_iInter.mp hf.2 i (z * U)) hp.le
  have point : ∃ f ∈ K, ∀ z x, f (z * x) = f z * f x := by
    apply multiplicative_of_finite_common_points K compact fun _ hf => hf.1.1
    apply finite_common_points_of_slice_fixedPoints K ne compact convex (fun _ hf => hf.1.2.1)
      (fun f hf z hz => (pos f hf z hz).ne') invariant
    intro L hL hn hc hv hi z hz
    obtain ⟨n, hn', hl⟩ := lo z hz
    have eq (f : S → ℝ) (hf : f ∈ L) : projective ((n : S) * z) f = projective z f := by
      funext x
      unfold projective
      rw [mul_assoc, nat f (hL hf), nat f (hL hf)]
      exact mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hn'.ne')
    obtain ⟨f, hf, he⟩ := projective_fixedPoint_of_compact_convex L ((n : S) * z) (c ∘ R)
      hn hc hv (fun f hf => (hL hf).1.2.1) (fun f hf => bound f (incl (hL hf)))
      (fun f hf => hl f (hL hf)) (fun f hf => by rw [eq f hf]; exact hi z hz hf)
    exact ⟨f, hf, (eq f hf).symm.trans he⟩
  obtain ⟨f, hf, hfmul⟩ := point
  let g : S →+* ℝ :=
    { toFun := f, map_zero' := hf.1.1, map_one' := hf.1.2.1,
      map_add' := hf.1.2.2.1, map_mul' := hfmul }
  refine ⟨g, hf.1.2.2.2.1, fun i => ?_⟩
  change f (A i) ≤ c i * f (B i)
  simpa only [mul_one] using mem_iInter.mp hf.2 i 1

end OAI.LinearAlgebra.MatrixExponent.Spectrum
