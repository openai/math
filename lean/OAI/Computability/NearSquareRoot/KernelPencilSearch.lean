import OAI.Computability.NearSquareRoot.KernelRepairSearch
import OAI.LinearAlgebra.FiniteFourier.PrimeCyclotomicPencil

/-! # Effective finite binary repair pencils

The certificate checks the clock power on the complete finite sign cube.
It reads its predicted scalar on the first diagonal entry and counts every
shift at which this scalar differs from the target. No symbolic polynomial,
basis-choice algorithm, or numerical estimate is needed by the search. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PencilSearch

open OAI.LinearAlgebra.FiniteFourier CyclotomicCode Matrix

abbrev Signature (m : ℕ) := Fin m → ZMod 2
abbrev Clock (h b : ℕ) := Fin h → Fin b

/-- A constant matrix and one query matrix per axis at each shifted batch. -/
abbrev Coefficients (a m h b : ℕ) :=
  Signature m → Option (Fin m) → Clock h b → Clock h b → Number a

variable {a m h b : ℕ}

def sign (a : ℕ) (e : ZMod 2) : Number a := (-1) ^ e.val

def target (a : ℕ) (k : Signature m) : Number a := ∏ j, sign a (k j)

def stage (A : Coefficients a m h b) (k β : Signature m) :
    Matrix (Clock h b) (Clock h b) (Number a) :=
  Matrix.of (A β none) + ∑ j, sign a (k j) • Matrix.of (A β (some j))

/-- One scalar per shift, independent of the clock input row. -/
def prediction [NeZero b] (A : Coefficients a m h b) (k β : Signature m) : Number a :=
  (stage A k β ^ b) 0 0

def failures [NeZero b] (A : Coefficients a m h b) (k : Signature m) : Finset (Signature m) :=
  Finset.univ.filter fun β => prediction A k β ≠ target a k

def Good [NeZero b] (A : Coefficients a m h b) : Prop :=
  (∀ k β, stage A k β ^ b = prediction A k β • 1) ∧
  ∀ k, (failures A k).card ≤ 2 ^ m / (2 * m ^ 3)

instance [NeZero b] : DecidablePred (Good (a := a) (m := m) (h := h) (b := b)) :=
  fun _ => inferInstanceAs <| Decidable ((_ ∧ _) : Prop)

private theorem two_unit : IsUnit (2 : Number a) :=
  isUnit_iff_exists_inv'.mpr ⟨_, Number.half_two⟩

private theorem clock_root {d : ℕ} (hd : d ≤ a+1) :
    ∃ ξ : Number a, IsPrimitiveRoot ξ (2^d) ∧
      ∀ k, 0 < k → k < 2^d → IsUnit (ξ^k - 1) := by
  have hu : IsUnit (2 : Dyadic) :=
    isUnit_iff_exists_inv'.mpr ⟨Dyadic.ofIntWithPrec 1 1, by decide⟩
  have hs : ∑ i ∈ Finset.range 2, (-1 : Dyadic)^i = 0 := by simp
  obtain ⟨hp, h⟩ := primeCyclotomicRoot_power_data (ζ := (-1 : Dyadic)) (p := 2) a d hd hu (by simp) hs
  let f := (Number.ringEquiv a).symm
  exact ⟨_, hp.map_of_injective (f := f) f.injective, fun k hk hk' => by
    simpa only [map_sub, map_pow, map_one] using (h k hk hk').map f⟩

private theorem sign_root : IsPrimitiveRoot (-1 : Number a) 2 := by
  obtain ⟨hp, hh⟩ := primeCyclotomicRoot_power_data (ζ := (-1 : Dyadic)) (p := 2) a 1 (by omega)
    (isUnit_iff_exists_inv'.mpr ⟨Dyadic.ofIntWithPrec 1 1, by decide⟩) (by simp) (by simp)
  have h : IsPrimitiveRoot (-1 : Extension a) 2 := by
    simpa only [Nat.add_one_sub_one, primeCyclotomicRoot_pow, map_neg, map_one, pow_one] using hp
  apply IsPrimitiveRoot.of_map_of_injective (f := Number.ringEquiv a) _ (Number.ringEquiv a).injective
  simpa only [map_neg, map_one] using h

private instance : PrimeSpectrumOrthogonal (sign_root (a := a)) :=
  PrimeSpectrumOrthogonal.of_unit_sub _ (by
    intro k hk hk'
    have : k = 1 := by omega
    subst k
    simpa [show (-1 : Number a) - 1 = -2 by ring] using (two_unit (a := a)).neg)

private theorem good_of_symbolic [NeZero b] (hm : 2 ≤ m)
    (p : PrimeRepairPencil 2 m b (sign_root (a := a))) :
    ∃ A : Coefficients a m (primeClockDigits 2 m b) b, Good A := by
  let A : Coefficients a m (primeClockDigits 2 m b) b :=
    fun β j => match j with
      | none => p.A₀ β
      | some i => p.A β i 1
  let val (k β : Signature m) : Number a :=
    MvPolynomial.eval (queryPowerValues sign_root k)
      (countPredictor sign_root β (repairWindowLower 2 m) (repairWindowDegree 2 m))
  have hstage (k β : Signature m) :
      stage A k β = (p.L β).map (MvPolynomial.eval (queryPowerValues sign_root k)) := by
    rw [p.stage]
    have hsum : Finset.univ.erase (0 : ZMod 2) = {1} := by decide
    simp [A, stage, hsum, queryPowerValues, sign, digitPhase_apply, Matrix.of]
    rfl
  have hp (k β : Signature m) : stage A k β ^ b = val k β • 1 := by
    rw [hstage]
    exact specialize_matrix_root _ (p.power β)
  have hv (k β : Signature m) : prediction A k β = val k β := by
    simp only [prediction, hp, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
  refine ⟨A, (fun k β => (hp k β).trans (congrArg (· • 1) (hv k β).symm)), fun k => ?_⟩
  apply (Finset.card_le_card ?_).trans (exceptionalShifts_card_le (by decide : 2 ≤ 2) hm k)
  intro β hβ
  by_contra hn
  have hwin : (shiftedCount k β : ℤ) ∈ Set.Icc (repairWindowLower 2 m) (repairWindowUpper 2 m) := by
    simpa [exceptionalShifts] using hn
  have hcount : val k β = target a k := by
    apply eval_countPredictor_of_orthogonal sign_root two_unit
    · exact hwin.1
    · simpa only [repairWindowLower_add_degree] using hwin.2
  exact (Finset.mem_filter.mp hβ).2 ((hv k β).trans hcount)

/-- A concrete search terminates for any power-of-two clock that is long
enough for the count window and available in the chosen coefficient ring. -/
theorem exists_good {d : ℕ} (hd : d ≤ a+1) (hdegree : repairWindowDegree 2 m ≤ 2^d)
    (hm : 2 ≤ m) :
    ∃ A : Coefficients a m (primeClockDigits 2 m (2^d)) (2^d), Good A := by
  obtain ⟨ξ, hξ, hu⟩ := clock_root hd
  obtain ⟨p⟩ := exists_primeRepairPencil (ζ := (-1 : Number a)) sign_root hξ.pow_eq_one hu hdegree
  exact good_of_symbolic hm p

private instance : Encodable (ZMod 2) := inferInstanceAs (Encodable (Fin 2))

/-- Run the finite signature tests on successive coefficient arrays. The
matrices can be generated before the first call at any column length. -/
def generate {d : ℕ} (hd : d ≤ a+1) (hdegree : repairWindowDegree 2 m ≤ 2^d)
    (hm : 2 ≤ m) : Coefficients a m ((2^d+1)^(m*2)) (2^d) :=
  Encodable.choose (p := Good (a := a) (m := m) (h := (2^d+1)^(m*2)) (b := 2^d)) (exists_good hd hdegree hm)

theorem generate_good {d : ℕ} (hd : d ≤ a+1) (hdegree : repairWindowDegree 2 m ≤ 2^d)
    (hm : 2 ≤ m) : Good (generate hd hdegree hm) :=
  Encodable.choose_spec (p := Good (a := a) (m := m) (h := (2^d+1)^(m*2)) (b := 2^d)) (exists_good hd hdegree hm)

end PencilSearch

end NearSquareRoot
end Computability
end OAI
