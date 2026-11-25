import OAI.Hierarchy.FactorSchedule
import OAI.Hierarchy.GridBandwidth

namespace OAI
/-! # Work and pin capacity of the actual lists allocated to the universal ticks -/

namespace Hierarchy.GridScale

open FactorAllocation Filter

private theorem cast_cost {α : Type*} (f : α → ℕ) (xs : List α) :
    (xs.map (fun x => (f x : ℝ))).sum = ((xs.map f).sum : ℝ) := by
  simp [List.map_map, Function.comp_def]

/-- Pay the mean and the one-item-per-class rounding error for the actual list,
including any fixed multiplicative charge applied to its resource. -/
theorem resource_fits {α : Type*} {T d w cap m C : ℕ} (cost : α → Fin d → ℕ)
    (items : List α) (j : Fin d) (t : Fin T)
    (width : ∀ a∈items, ∀ h, cost a h ≤ 2^w) (bounded : ∀ a∈items, ∀ h, cost a h ≤ cap)
    (avg : 4*C*(items.map (fun a => cost a j)).sum ≤ T*m)
    (err : 4*C*((20*(w+1)+2)^d)*cap ≤ m) :
    C * ((factors w cost items t).map (fun a => cost a j)).sum ≤ m := by
  have h := (tickLoad_bounds cost items cap width bounded j t).2
  rw [←sum_factors_eq_tickLoad, cast_cost] at h
  have hR : (4:ℝ)*C*((items.map (fun a => cost a j)).sum:ℝ) ≤ (T:ℝ)*m := by exact_mod_cast avg
  have eR : (4:ℝ)*C*(20*((w:ℝ)+1)+2)^d*cap ≤ (m:ℝ) := by exact_mod_cast err
  have positive : (0:ℝ)<T := by exact_mod_cast (Nat.zero_lt_of_lt t.isLt)
  have rate : (4:ℝ)*C*(((items.map (fun a => cost a j)).sum:ℝ)/T) ≤ m := by
    rw [←mul_div_assoc, div_le_iff₀ positive]
    simpa [mul_comm (m:ℝ)] using hR
  have paid := mul_le_mul_of_nonneg_left h (show (0:ℝ)≤C by positivity)
  exact_mod_cast (show (C:ℝ)*(((factors w cost items t).map (fun a => cost a j)).sum:ℝ) ≤ m by
    linarith only [paid, rate, eR, show (0:ℝ)≤m by positivity])

private theorem classes_le (k w : ℕ) : classes k w ≤ 22^(k+2)*(w+1)^(k+2) := by
  rw [← Nat.mul_pow]
  exact Nat.pow_le_pow_left (by omega : 20*(w+1)+2 ≤ 22*(w+1)) _

/-- One common additive-error estimate provides room even after any fixed
polynomial per-word overhead. Both the pin budget and the clock can pay it. -/
theorem rounding_room {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D) (k A C d c₀ : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q ≤ Q w → ∀ cap : ℕ,
      (cap:ℝ) ≤ ((2:ℝ)^w)^(3/5:ℝ) →
      4*(C*(w+1)^d)*classes k w*cap ≤ pins w (overhead Q D w) ∧
      4*(C*(w+1)^d)*classes k w*cap ≤ 2^(w-((w^c₀).log2+1)) := by
  filter_upwards [budgets H k A (4*C*22^(k+2)) (d+(k+2)),
    polynomial H 1 c₀, (grows H).eventually_ge_atTop 1] with w b limit growth
  intro q hq top cap capBound
  let a := overhead Q D w
  let coeff := 4*C*22^(k+2)*(w+1)^(d+(k+2))
  have paid := ((b q hq top).descriptor).1
  have cls : 4*(C*(w+1)^d)*classes k w ≤ coeff := by
    calc
      _ ≤ 4*(C*(w+1)^d)*(22^(k+2)*(w+1)^(k+2)) := Nat.mul_le_mul_left _ (classes_le k w)
      _ = coeff := by simp only [coeff, pow_add]; ring
  have cc : (cap:ℝ) ≤ ((2:ℝ)^w)^(4/5:ℝ) := capBound.trans (Real.rpow_le_rpow_of_exponent_le
    (one_le_pow₀ (by norm_num)) (by norm_num))
  have capPaid : 4*(C*(w+1)^d)*classes k w*cap ≤ pins w a := by
    have rat : (coeff:ℝ)*(cap:ℝ) ≤ (pins w a:ℝ) :=
      (mul_le_mul_of_nonneg_left cc (by positivity)).trans paid
    exact (Nat.mul_le_mul_right cap cls).trans (by exact_mod_cast rat)
  have logBound : w^c₀ ≤ 2^a :=
    (Nat.pow_le_pow_left (Nat.le_succ w) _).trans (by simpa using limit)
  have logle : (w^c₀).log2 ≤ a := by
    by_cases empty : w^c₀ = 0
    · simp [empty]
    · exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp ((Nat.log2_self_le empty).trans logBound)
  exact ⟨capPaid, capPaid.trans (Nat.pow_le_pow_right (by decide)
    (show w-4*a ≤ w-((w^c₀).log2+1) by change 1 ≤ a at growth; omega))⟩

/-- Descriptor reconstruction and reading a polynomial number of words per pin
both fit in the actual rounded tick clock, with any fixed multiplicative margin. -/
theorem receiver_setup_room {Q : ℕ → ℕ} {D : ℕ → ℝ} (H : Envelopes Q D) (k A C d c₀ : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q ≤ Q w → let a := overhead Q D w
      ((C*(w+1)^d:ℕ):ℝ) * (((2:ℝ)^w)^(4/5:ℝ) + pins w a) ≤ (2^(w-((w^c₀).log2+1)):ℕ) := by
  filter_upwards [budgets H k A 1 0, polynomial H (2*C) d, polynomial H 1 c₀,
    sublinear H 4, (grows H).eventually_ge_atTop 1] with w b poly room small high
  intro q hq top
  dsimp only
  let a := overhead Q D w
  have large : ((2:ℝ)^w)^(4/5:ℝ) ≤ (pins w a:ℝ) := by
    simpa using ((b q hq top).descriptor).1
  have logBound : w^c₀ ≤ 2^a := (Nat.pow_le_pow_left (Nat.le_succ w) _).trans (by simpa using room)
  have l : (w^c₀).log2 ≤ a := by
    by_cases empty : w^c₀=0
    · simp [empty]
    · exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp ((Nat.log2_self_le empty).trans logBound)
  have paid : 2*(C*(w+1)^d)*pins w a ≤ 2^(w-((w^c₀).log2+1)) := by
    have c : 2*(C*(w+1)^d) ≤ 2^a := by simpa only [Nat.mul_assoc] using poly
    apply (Nat.mul_le_mul_right _ c).trans
    rw [pins, ←pow_add]
    apply Nat.pow_le_pow_right (by decide)
    change 4*a ≤ w at small
    change 1 ≤ a at high
    omega
  have est := mul_le_mul_of_nonneg_left (add_le_add_left large (pins w a : ℝ))
    (show 0 ≤ ((C*(w+1)^d:ℕ):ℝ) by positivity)
  have cash : (2:ℝ)*((C*(w+1)^d:ℕ):ℝ)*(pins w a:ℝ) ≤ (2^(w-((w^c₀).log2+1)):ℕ) := by
    exact_mod_cast paid
  linarith only [est,cash]

end Hierarchy.GridScale

end OAI
