import OAI.Optimization.LinearProgramming.PriceGame.Moment

/-! Rational replay of the weights and the market-to-moment interface. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Moment

open Finset

def etaQ : ℚ := sigmaQ / 8

@[simp] theorem etaQ_cast : (etaQ : ℝ) = eta := by simp [etaQ, eta]

def gainQ {E I : Type*} [Fintype I] (f : E → I → ℚ) (u : E → ℚ) (z : I → ℚ) (e : E) : ℚ :=
  ∑ i, f e i * u e * z i

@[simp] theorem gainQ_cast {E I : Type*} [Fintype I] (f : E → I → ℚ)
    (u : E → ℚ) (z : I → ℚ) (e : E) :
    ((gainQ f u z e : ℚ) : ℝ) =
      allocationGain (fun e i => (f e i : ℝ)) (fun e => (u e : ℝ)) (fun i => (z i : ℝ)) e := by
  simp only [gainQ, allocationGain, Rat.cast_sum, Rat.cast_mul]

def localWeightQ {E : Type*} (η : ℚ) (initial : E → ℚ) (g : ℕ → E → ℚ) (t : ℕ) (e : E) : ℚ :=
  initial e * ∏ j ∈ range t, (1 + η * g j e)

@[simp] theorem localWeightQ_cast {E : Type*} (η : ℚ) (initial : E → ℚ)
    (g : ℕ → E → ℚ) (t : ℕ) (e : E) :
    ((localWeightQ η initial g t e : ℚ) : ℝ) =
      localWeight η (fun e => (initial e : ℝ)) (fun j e => (g j e : ℝ)) t e := by
  simp only [localWeightQ, localWeight, Rat.cast_mul, Rat.cast_prod, Rat.cast_add, Rat.cast_one]

def deepWeightQ {E : Type*} (initial : E → ℚ) (s : ℕ → E → ℕ) (t : ℕ) (e : E) : ℚ :=
  initial e * 2 ^ ∑ j ∈ range t, s j e

@[simp] theorem deepWeightQ_cast {E : Type*} (initial : E → ℚ) (s : ℕ → E → ℕ) (t : ℕ) (e : E) :
    ((deepWeightQ initial s t e : ℚ) : ℝ) = deepWeight (fun e => (initial e : ℝ)) s t e := by
  simp only [deepWeightQ, deepWeight, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]

def localPartQ {E : Type*} (mask : E → Bool) (w : E → ℚ) (e : E) : ℚ :=
  if mask e then w e else 0

def deepPartQ {E : Type*} (mask : E → Bool) (w : E → ℚ) (e : E) : ℚ :=
  if mask e then 0 else w e

@[simp] theorem localPartQ_cast {E : Type*} (mask : E → Bool) (w : E → ℚ) (e : E) :
    ((localPartQ mask w e : ℚ) : ℝ) = localPart mask (fun e => (w e : ℝ)) e := by
  cases he : mask e <;> simp [localPartQ, localPart, he]

@[simp] theorem deepPartQ_cast {E : Type*} (mask : E → Bool) (w : E → ℚ) (e : E) :
    ((deepPartQ mask w e : ℚ) : ℝ) = deepPart mask (fun e => (w e : ℝ)) e := by
  cases he : mask e <;> simp [deepPartQ, deepPart, he]

/-- A rational allocation at each probe supplies exactly the admissibility conditions of
the moment proof. All premises about allocations, gains and updates are checked over ℚ. -/
theorem Trial.node_admissible_of_rational_market {E I : Type*} [Fintype E] [Fintype I] {r : ℕ}
    (C σ η : ℚ) (mask : E → Bool) (w : E → ℚ)
    (gain : Fin r → E → ℚ) (children : Fin (2 * r) → Trial E r)
    (allocation : Fin r → E → I → ℚ) (sign : E → ℚ) (label : Fin r → I → ℚ)
    (hsign : ∀ e, |sign e| = 1) (hlabel : ∀ t i, |label t i| = 1)
    (hnn : ∀ t e i, 0 ≤ allocation t e i)
    (hmass : ∀ t e, ∑ i, allocation t e i ≤ 1)
    (hgain : ∀ t e, gain t e = gainQ (allocation t) sign (label t) e)
    (hbal : ∀ t : Fin r, ∀ i, ∑ e, localWeightQ η (localPartQ mask w) (probeAt gain) t e *
      sign e * allocation t e i = 0)
    (hc : ∀ t : Fin (2 * r), (children t).Admissible C σ η
      (fun e => (deepWeightQ (deepPartQ mask w) (childScoreAt C σ children) t e : ℝ))) :
    (Trial.node mask gain children).Admissible C σ η (fun e => (w e : ℝ)) := by
  apply Trial.node_admissible_of_allocation C σ η mask _ gain children
    (fun t e i => (allocation t e i : ℝ)) (fun e => (sign e : ℝ)) (fun t i => (label t i : ℝ))
  · intro e; exact_mod_cast hsign e
  · intro t i; exact_mod_cast hlabel t i
  · intro t e i; exact_mod_cast hnn t e i
  · intro t e; exact_mod_cast hmass t e
  · intro t e
    simpa only [gainQ_cast] using congrArg (fun x : ℚ => (x : ℝ)) (hgain t e)
  · intro t i
    have h := congrArg (fun x : ℚ => (x : ℝ)) (hbal t i)
    have hg : (fun j e => ((probeAt gain j e : ℚ) : ℝ)) = gainAt gain := rfl
    have hw : (fun e => ((localPartQ mask w e : ℚ) : ℝ)) =
        localPart mask (fun e => (w e : ℝ)) := by funext e; exact localPartQ_cast mask w e
    simpa only [Rat.cast_sum, Rat.cast_mul, Rat.cast_zero, localWeightQ_cast, hw, hg] using h
  · intro t
    simpa only [deepWeightQ_cast, deepPartQ_cast] using hc t

end Moment
end PriceGame
end LinearProgramming
end Optimization
end OAI
