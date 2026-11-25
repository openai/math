import OAI.LinearAlgebra.MatrixExponent.Rectangle.Face.Contact
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Threshold.Square
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Dual
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup.Strict
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior.Convert
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Entropy
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Lower

/-!
# Rectangular matrix multiplication over arbitrary fields

The upper bound and the entire region below the harmonic threshold
are unconditional. Propagation of positive contact is the remaining
spectral input for the rigidity dichotomy.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle

variable {a b c : ℝ}

theorem upper (F : Type*) [Field F] (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    exponent F a b c ≤ U a b c := by
  by_cases h : a = 0 ∨ b = 0 ∨ c = 0
  · rw [coordinate_plane F ha hb hc h, U_plane ha hb hc h]
  push Not at h
  obtain ⟨K, _, ⟨alg⟩⟩ := small_field F
  rw [exponent_extension K F ha hb hc]
  exact upper_of_diagonal (support K) (diagonal K)
    (ha.lt_of_ne' h.1) (hb.lt_of_ne' h.2.1) (hc.lt_of_ne' h.2.2)

/-- The full benchmark upper bound includes arbitrary positive slack
in the cost of the formal arithmetic circuits. -/
theorem arithmetic_upper (F : Type*) [Field F] (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    Admissible F a b c (U a b c) := by
  intro ε hε
  have h := lt_add_of_le_of_pos (upper F ha hb hc) hε
  obtain ⟨s, hs, hlt⟩ := exists_lt_of_csInf_lt ⟨_, volume_admissible F ha hb hc⟩ h
  obtain ⟨C, hC, hprog⟩ := hs (U a b c + ε - s) (sub_pos.mpr hlt)
  refine ⟨C, hC, ?_⟩
  simpa only [show s + (U a b c + ε - s) = U a b c + ε by ring] using hprog

theorem flat (F : Type*) [Field F] (ha : 0 < a) (hb : 0 < b) (hc : 0 ≤ c)
    (hc' : c ≤ a * b / (a + b)) : exponent F a b c = a + b := by
  have h : (a + b) * c ≤ a * b := by
    rw [mul_comm]; exact (le_div_iff₀ (add_pos ha hb)).mp hc'
  have hmin : c ≤ min a b := by apply le_min <;> nlinarith
  have hu := upper F ha.le hb.le hc
  simp only [U, ite_eq_left hmin, benchmark, max_eq_right (sub_nonpos.mpr h), zero_pow
    (by decide : 2 ≠ 0), zero_div, add_zero] at hu
  exact le_antisymm hu ((le_max_left _ _).trans (bounds F ha.le hb.le hc).1)

theorem dual_lower (F : Type*) [Field F] (ha : 0 < a) (hb : 0 < b) :
    a * b / (a + b) ≤ dual F a b := by
  have h : 0 ≤ a * b / (a + b) := by positivity
  have h' : a * b / (a + b) ≤ min a b := by
    apply le_min <;> rw [div_le_iff₀ (add_pos ha hb)] <;> nlinarith
  exact le_csSup ⟨min a b, fun _ hc => hc.1.2⟩ ⟨⟨h, h'⟩, flat F ha hb h le_rfl⟩

theorem rigidity (h : ∀ (K : Type) [Field K], Propagation (Prices K))
    (F : Type*) [Field F] : Rigidity F := by
  obtain ⟨K, _, ⟨alg⟩⟩ := small_field F
  rcases rigidity_of_contact (support K) (diagonal K) (h K) with hK | hK
  · left
    intro a b c ha hb hc
    rw [exponent_extension K F ha.le hb.le hc.le]
    exact hK a b c ha hb hc
  · right
    intro a b c ha hb hc hactive
    rw [exponent_extension K F ha.le hb.le hc.le]
    exact hK a b c ha hb hc hactive

/-- A strict saving at any fixed shape is witnessed in some prime field. -/
theorem prime_specialization {F : Type*} [Field F] {s : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : exponent F a b c < s) :
    ∃ (p : ℕ) (_ : Fact p.Prime), exponent (ZMod p) a b c < s := by
  obtain ⟨n, r, hn, hr, hs⟩ := (exponent_lt_iff_rank ha hb hc).mp h
  obtain ⟨K, _, _, hK⟩ := specializeRank hr
  let p := ringChar K
  have : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  let _ : Algebra (ZMod p) K := ZMod.algebra K p
  refine ⟨p, inferInstance, ?_⟩
  rw [← exponent_extension (ZMod p) K ha hb hc]
  exact exponent_lt_of_rank ha hb hc hn hK hs

theorem of_prime_fields
    (h : ∀ (p : ℕ) [Fact p.Prime], MatrixExponent.omega (ZMod p) = 9 / 4 ∧ Rigidity (ZMod p))
    (F : Type*) [Field F] : MatrixExponent.omega F = 9 / 4 ∧ Rigidity F := by
  have he (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
      exponent F a b c = U a b c := by
    refine le_antisymm (upper F ha.le hb.le hc.le) ?_
    by_contra! hlt
    obtain ⟨p, _, hp⟩ := prime_specialization ha.le hb.le hc.le hlt
    exact hp.ne (positive_shapes (h p).2 (h p).1 ha hb hc)
  have hs := he 1 1 1 zero_lt_one zero_lt_one zero_lt_one
  norm_num [square, U, benchmark] at hs
  exact ⟨hs, Or.inl he⟩

theorem of_finite_fields
    (h : ∀ (K : Type) [Field K] [Finite K], MatrixExponent.omega K = 9 / 4 ∧ Rigidity K)
    (F : Type*) [Field F] : MatrixExponent.omega F = 9 / 4 ∧ Rigidity F :=
  of_prime_fields (fun p _ => h (ZMod p)) F

end OAI.LinearAlgebra.MatrixExponent.Rectangle
