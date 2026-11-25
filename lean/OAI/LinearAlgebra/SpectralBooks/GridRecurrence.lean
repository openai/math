import OAI.LinearAlgebra.SpectralBooks.FormalBlockFamily
import OAI.LinearAlgebra.SpectralBooks.PlaneGridContradiction

/-! # Composing planar map table circuits

The cost at `(N,w)` is the minimum size of a straight-line program for the
universal map polynomial in independent width-`w` table entries. Substitution
places a previously computed table entry in one register, shared by every
subsequent occurrence. This gives addition of costs when the map identity is
iterated.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

section

open Arithmetic Arithmetic.RecursiveBlock MvPolynomial
open scoped Classical

variable {F I J : Type*} [Field F]

/-- The actual least (division-free) straight-line program cost of a polynomial. -/
def polynomialProgramCost (f : MvPolynomial I F) : ℕ :=
  Nat.find (show ∃ s, ∃ (r : ℕ) (p : Program F I r) (o : Fin r),
      registerPolynomial p o = f ∧ p.cost = s from by
    obtain ⟨r,p,o,h⟩ := exists_registerPolynomial f
    exact ⟨p.cost,r,p,o,h,rfl⟩)

theorem exists_program_of_cost (f : MvPolynomial I F) :
    ∃ (r : ℕ) (p : Program F I r) (o : Fin r),
      registerPolynomial p o = f ∧ p.cost = polynomialProgramCost f := by
  unfold polynomialProgramCost
  exact Nat.find_spec (p := fun s => ∃ (r : ℕ) (p : Program F I r) (o : Fin r),
    registerPolynomial p o = f ∧ p.cost = s) _

theorem polynomialProgramCost_le {r : ℕ} (p : Program F I r) (o : Fin r) :
    polynomialProgramCost (registerPolynomial p o) ≤ p.cost :=
  Nat.find_min' (p := fun s => ∃ (r : ℕ) (q : Program F I r) (j : Fin r),
    registerPolynomial q j = registerPolynomial p o ∧ q.cost = s) _ ⟨_, p, o, rfl, rfl⟩

/-- Compute the table entries once and feed their registers into the circuit
for the smaller universal map polynomial. -/
theorem polynomialProgramCost_bind_le (p : Family F I J) (f : MvPolynomial J F) :
    polynomialProgramCost (bind₁ (familyPolynomial p) f) ≤ p.cost + polynomialProgramCost f := by
  obtain ⟨r, q, o, hq, hc⟩ := exists_program_of_cost f
  let Q : Family F J Unit := ⟨r, q, fun _ => o⟩
  have he := familyPolynomial_compose p Q ()
  change familyPolynomial (p.compose Q) () = bind₁ (familyPolynomial p) (registerPolynomial q o) at he
  rw [hq] at he
  rw [← he]
  exact (polynomialProgramCost_le (p.compose Q).program _).trans_eq
    ((Family.cost_compose p Q).trans (congrArg (p.cost + ·) hc))

/-- A fixed multiple of `log(2N)` bounds the number of bits needed for `2N` symbols. -/
theorem clog_two_mul_le {n : ℕ} (hn : 0 < n) :
    (Nat.clog 2 (2*n) : ℝ) ≤ (2 / Real.log 2) * Real.log (2*n) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hle : Real.log 2 ≤ Real.log (2 * n) :=
    Real.log_le_log (by norm_num) (by linarith)
  have htwo : (1:ℝ) ≤ (2 * n : ℕ) := by simp only [Nat.cast_mul, Nat.cast_ofNat]; linarith
  have h := Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num : (1:ℝ) < 2) htwo)
  rw [← Real.natCeil_logb_natCast 2 (2*n)]
  simp only [Nat.cast_ofNat, Nat.cast_mul] at h ⊢
  unfold Real.logb at h
  have ht := (lt_div_iff₀ hl).mp (show (⌈Real.log (2 * n) / Real.log 2⌉₊ : ℝ) - 1 <
    Real.log (2*n) / Real.log 2 by linarith)
  unfold Real.logb
  rw [div_mul_eq_mul_div, le_div_iff₀ hl]
  linarith

/-- Concrete polynomial programs and exact formal map identities give the
one-round cost recurrence used in the independent-set contradiction. The
integer `C` is uniform over the vertex bound and the old table width. -/
def gridTableCompressionOfCircuits
    {Addr : ℕ → Type*} (Z : (n w : ℕ) → MvPolynomial (Addr w) F)
    (a C : ℕ)
    (base : ∀ w : ℕ, 0 < w → polynomialProgramCost (Z 1 w) ≤ 2^(C*(w+1)))
    (round : ∀ n w : ℕ, 1 < n → 0 < w → ∃ w' : ℕ, 0 < w' ∧
      w' ≤ 10*w + C*Nat.clog 2 (2*n) ∧ ∃ p : Family F (Addr w) (Addr w'),
      p.cost ≤ 2^(C*(w + Nat.clog 2 (2*n))) ∧
      Z n w = bind₁ (familyPolynomial p) (Z (max 1 (n/a)) w')) :
    GridTableCompression a where
  cost n w := polynomialProgramCost (Z n w)
  pinConstant := C * max 1 (2 / Real.log 2)
  gateConstant := C * max 1 (2 / Real.log 2)
  widthConstant := C * max 1 (2 / Real.log 2)
  pin_nonneg := by positivity
  gate_nonneg := by positivity
  width_nonneg := by positivity
  finalCost w hw := by
    have h : 1 ≤ (2 / Real.log 2) * Real.log 2 := by
      rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1:ℝ)<2)))]; norm_num
    have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hbit := le_trans h (mul_le_mul_of_nonneg_right (le_max_right 1 _) hl)
    have hb := (Nat.cast_le (α := ℝ)).mpr (base w hw)
    rw [Nat.cast_pow, ← Real.rpow_natCast] at hb
    push_cast at hb
    apply hb.trans
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [mul_add]
    exact add_le_add (le_mul_of_one_le_left (Nat.cast_nonneg _) (le_max_left _ _)) hbit
  step n w hn hw := by
    obtain ⟨w', hw', hsize, p, hcost, he⟩ := round n w hn hw
    let m := max 1 (n/a)
    let L := Real.log (2*n)
    let k : ℝ := max 1 (2 / Real.log 2)
    have hL : 0 ≤ L := Real.log_nonneg (by
      have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn.le
      linarith)
    have hbits : (Nat.clog 2 (2*n) : ℝ) ≤ k*L :=
      (clog_two_mul_le (by omega)).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hL)
    refine ⟨w', hw', ?_, ?_⟩
    · have h := (Nat.cast_le (α := ℝ)).mpr hsize
      push_cast at h
      apply h.trans
      rw [mul_assoc]
      gcongr
    · have hc : (p.cost : ℝ) ≤ (2:ℝ)^((C:ℝ)*k*(w+L)) := calc
        (p.cost : ℝ) ≤ ((2^(C*(w + Nat.clog 2 (2*n))) : ℕ) : ℝ) := by exact_mod_cast hcost
        _ = (2:ℝ)^((C:ℝ)*((w:ℝ)+Nat.clog 2 (2*n))) := by
          rw [Nat.cast_pow, ← Real.rpow_natCast]; push_cast; rfl
        _ ≤ _ := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          rw [mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          rw [mul_add]
          exact add_le_add (le_mul_of_one_le_left (Nat.cast_nonneg _) (le_max_left _ _)) hbits
      rw [he]
      have h := (Nat.cast_le (α := ℝ)).mpr (polynomialProgramCost_bind_le p (Z m w'))
      rw [Nat.cast_add] at h
      exact h.trans (add_le_add_left hc _)

end

end

end SpectralBooks
end LinearAlgebra
end OAI
