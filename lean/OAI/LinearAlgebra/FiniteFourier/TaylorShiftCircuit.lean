import OAI.LinearAlgebra.FiniteFourier.TaylorShiftPolynomial
import OAI.LinearAlgebra.FiniteFourier.RingFixedConvolution
import OAI.LinearAlgebra.FiniteFourier.CircuitRingCombine
import OAI.LinearAlgebra.FiniteFourier.ConvolutionEnvelope

/-! # Denominator-free Taylor shifts with a recursive convolution budget

For a block of length `2m` the two halves can be translated independently.
A single convolution with the fixed coefficient vector of `(X+C a)^m`
recovers the shifted high half before the two contributions are added.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {R : Type*} [CommRing R]

private def padCircuit (n m : ℕ) : Circuit R (Fin n) (Fin m) 0 where
  program := .nil
  output i := if h : i.val < n then .scaled 1 (.inl ⟨i.val, h⟩) else .zero

private theorem padCircuit_eval {n m : ℕ} (x : Fin n → R) :
    (padCircuit n m).eval x = taylorPad x := by
  funext i
  by_cases h : i.val < n <;> simp [taylorPad, padCircuit, Circuit.eval, Readout.eval, h]

private def restrictOutputs {I O O' : Type*} {s : ℕ} (p : Circuit R I O s) (f : O' → O) :
    Circuit R I O' s := ⟨p.program, fun j => p.output (f j)⟩

private abbrev ShiftAtCost (a : R) (n : ℕ) (bound : ℝ) : Prop :=
  ∃ (s : ℕ) (p : Circuit R (Fin n) (Fin n) s), (s : ℝ) ≤ bound ∧
    ∀ x k, p.eval x k = shiftedCoefficient a x k.val

private theorem shift_double {n : ℕ} {a : R} {C : ℝ} (h : ShiftAtCost a n C) :
    ShiftAtCost a (n+n) (2*C + integralConvolutionCost (n+1) + 2*n) := by
  obtain ⟨s, p, hs, hp⟩ := h
  let lo := p.rewire (fun i => (1, Fin.castAdd n i)) (fun k => (1, k))
  let hi := p.rewire (fun i => (1, Fin.natAdd n i)) (fun k => (1, k))
  have hlo (x : Fin (n+n) → R) :
      lo.eval x = fun k => shiftedCoefficient a (fun i => x (Fin.castAdd n i)) k.val := by
    funext k
    simp [lo, Circuit.eval_rewire, hp]
  have hhi (x : Fin (n+n) → R) :
      hi.eval x = fun k => shiftedCoefficient a (fun i => x (Fin.natAdd n i)) k.val := by
    funext k
    simp [hi, Circuit.eval_rewire, hp]
  obtain ⟨t, ht, low, hlow⟩ := circuit_comp lo (padCircuit n (n+n))
  obtain ⟨u, hu, high, hhigh⟩ := circuit_comp hi (padCircuit n (n+1))
  let y (i : Fin (n+1)) := ((Polynomial.X + Polynomial.C a)^n).coeff i.val
  obtain ⟨v, hv, mul, hmul⟩ := exists_fixed_convolution_circuit (n+1) y
  let coefficient (k : Fin (n+n)) : Fin (2*(n+1)-1) := ⟨k.val, by have := k.isLt; omega⟩
  obtain ⟨w, hw, product, hprod⟩ := circuit_comp high (restrictOutputs mul coefficient)
  obtain ⟨b, hb, out, hout⟩ := circuit_sumPair (Fin (n+n)) (Fin (n+n)) (1 : R) 1 low product
  refine ⟨b, out, ?_, ?_⟩
  · simp only [Fintype.card_fin] at hb
    have H : b ≤ 2*s + integralConvolutionCost (n+1) + 2*n := by omega
    have := (Nat.cast_le (α := ℝ)).2 H
    push_cast at this
    linarith
  · intro x k
    rw [shiftedCoefficient_split a x k, hout, hlow, hprod, padCircuit_eval, hlo]
    change 1 * _ + 1 * mul.eval (high.eval x) (coefficient k) = _
    rw [hmul, hhigh, padCircuit_eval, hhi]
    simp [y, coefficient]

private theorem shift_power_two (a : R) (k : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (hD : ∀ j : ℕ, 0 < j → j ≤ 2^k → (integralConvolutionCost j : ℝ) ≤ A*j) :
    ShiftAtCost a (2^k) ((k : ℝ) * (2:ℝ)^k * (A+1)) := by
  induction k with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, pow_zero]
    exact ⟨0, padCircuit 1 1, by simp, fun x k => by
      rw [padCircuit_eval, shiftedCoefficient_one a x k]
      fin_cases k
      simp [taylorPad]⟩
  | succ k ih =>
    let m := 2^k
    have hm : 0 < m := pow_pos (by decide) _
    have he : 2^(k+1) = m+m := by simp [m, pow_succ, mul_two]
    have hhalf := ih fun j hj hj' => hD j hj (hj'.trans (by rw [he]; omega))
    obtain ⟨s, p, hs, hp⟩ := shift_double hhalf
    rw [he]
    refine ⟨s, p, hs.trans ?_, hp⟩
    have hc := hD (m+1) (by omega) (by rw [he]; omega)
    have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    have hAm : A ≤ A*(m:ℝ) := le_mul_of_one_le_right hA hm'
    change 2 * ((k:ℝ) * (2:ℝ)^k * (A+1)) + integralConvolutionCost (m+1) + 2*(m:ℝ) ≤ _
    push_cast at hc ⊢
    have hcast : (m:ℝ) = (2:ℝ)^k := by simp [m]
    rw [← hcast, pow_succ, ← hcast]
    nlinarith

/-- Over every commutative ring, the full Taylor shift uses at most
`2 n ⌈log₂ n⌉ (A+1)` gates when all integral convolution costs up to
length `2n` are bounded by `A` per coefficient. -/
theorem exists_taylor_shift_circuit (n : ℕ) (hn : 0 < n) (a : R) {A : ℝ} (hA : 0 ≤ A)
    (hD : ∀ j : ℕ, 0 < j → j ≤ 2*n → (integralConvolutionCost j : ℝ) ≤ A*j) :
    ∃ (s : ℕ) (p : Circuit R (Fin n) (Fin n) s),
      (s : ℝ) ≤ (Nat.clog 2 n : ℝ)*(2*n)*(A+1) ∧
      ∀ x k, p.eval x k = shiftedCoefficient a x k.val := by
  let k := Nat.clog 2 n
  let m := 2^k
  have hnm : n ≤ m := Nat.le_pow_clog (by decide) n
  have hmn : m ≤ 2*n := by
    by_cases h : n ≤ 1
    · simp [m, k, Nat.clog_of_right_le_one h, show n = 1 by omega]
    · have H := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) (by omega : 1 < n)
      have hk : 0 < k := Nat.clog_pos (by decide) (by omega)
      change 2^k ≤ 2*n
      calc
        2^k = 2^((k-1)+1) := by rw [Nat.sub_add_cancel hk]
        _ = 2^(k-1)*2 := pow_succ _ _
        _ ≤ 2*n := by change 2^(k-1) < n at H; omega
  obtain ⟨s, p, hs, hp⟩ := shift_power_two a k A hA (fun j hj hjm => hD j hj (hjm.trans hmn))
  obtain ⟨t, ht, out, hout⟩ := circuit_comp (padCircuit n m) (restrictOutputs p (Fin.castLE hnm))
  refine ⟨t, out, ?_, ?_⟩
  · have hm : (2:ℝ)^k ≤ 2*(n:ℝ) := by exact_mod_cast hmn
    have ht' : (t:ℝ) ≤ (s:ℝ) := by exact_mod_cast (show t ≤ s by simpa using ht)
    exact ht'.trans (hs.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm
      (Nat.cast_nonneg k)) (by linarith)))
  · intro x j
    rw [hout, padCircuit_eval]
    change p.eval (taylorPad x) _ = _
    rw [hp, shiftedCoefficient_pad a hnm]
    rfl

/-- Shift all coefficient coordinates of a length-`h` jet. The circuit
performs one denominator-free shift on each of the `e` coordinates. -/
theorem exists_coordinate_taylor_shift_circuit (e h : ℕ) (hh : 0 < h) (a : R) {A : ℝ}
    (hA : 0 ≤ A)
    (hD : ∀ j : ℕ, 0 < j → j ≤ 2*h → (integralConvolutionCost j : ℝ) ≤ A*j) :
    ∃ (t : ℕ) (q : Circuit R (Fin h × Fin e) (Fin h × Fin e) t),
      (t : ℝ) ≤ 2*e*h*(1+Real.logb 2 h)*(1+A) ∧ ∀ x i k,
        q.eval x (k, i) = shiftedCoefficient a (fun j => x (j, i)) k.val := by
  obtain ⟨s, p, hs, hp⟩ := exists_taylor_shift_circuit h hh a hA hD
  obtain ⟨t, ht, z, hz⟩ := circuit_family (fun _ : Fin e => p)
  let q := z.rewire (fun j => (1, (j.2, j.1)))
    (fun j : Fin h × Fin e => (1, ⟨j.2, j.1⟩))
  refine ⟨t, q, ?_, ?_⟩
  · have hcost : t ≤ e*s := by simpa using ht
    have hlog : 0 ≤ Real.logb 2 h :=
      Real.logb_nonneg (by norm_num) (by exact_mod_cast hh)
    have hceil : (Nat.clog 2 h : ℝ) ≤ 1 + Real.logb 2 h := by
      rw [← Real.natCeil_logb_natCast]
      simpa only [Nat.cast_ofNat, add_comm] using (Nat.ceil_lt_add_one hlog).le
    calc
      (t : ℝ) ≤ (e : ℝ)*s := by exact_mod_cast hcost
      _ ≤ e*((Nat.clog 2 h : ℝ)*(2*h)*(A+1)) := by gcongr
      _ ≤ e*((1+Real.logb 2 h)*(2*h)*(A+1)) := by gcongr
      _ = _ := by ring
  · intro x i k
    simp [q, Circuit.eval_rewire, hz, hp, Function.comp_def]

/-- The denominator-free Taylor shift estimate used on each list of the
integral descent, with the recursive envelope at any cutoff at least `2h`. -/
theorem exists_taylor_shift_envelope {e h cutoff : ℕ} (hh : 0 < h) (hc : 2*h ≤ cutoff) (a : R) :
    ∃ (t : ℕ) (q : Circuit R (Fin h × Fin e) (Fin h × Fin e) t),
      (t : ℝ) ≤ 4*e*h*(1+Real.logb 2 h)*convolutionEnvelope cutoff ∧ ∀ x i k,
        q.eval x (k, i) = shiftedCoefficient a (fun j => x (j, i)) k.val := by
  have he := convolutionEnvelope_one_le (show 0 < cutoff by omega)
  have hD (j : ℕ) (hj : 0 < j) (hjs : j ≤ 2*h) :
      (integralConvolutionCost j : ℝ) ≤ convolutionEnvelope cutoff * j :=
    (div_le_iff₀ (show 0 < (j : ℝ) by exact_mod_cast hj)).mp
      (convolutionRate_le_envelope hj (hjs.trans hc))
  obtain ⟨t, q, ht, hq⟩ := exists_coordinate_taylor_shift_circuit e h hh a
    (zero_le_one.trans he) hD
  refine ⟨t, q, ht.trans ?_, hq⟩
  have hl : 0 ≤ Real.logb 2 h := Real.logb_nonneg (by norm_num) (by exact_mod_cast hh)
  calc
    _ ≤ 2*e*h*(1+Real.logb 2 h)*(2*convolutionEnvelope cutoff) := by
      gcongr
      linarith
    _ = _ := by ring

end FiniteFourier
end LinearAlgebra
end OAI
