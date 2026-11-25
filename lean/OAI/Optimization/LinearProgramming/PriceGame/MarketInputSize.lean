import OAI.Optimization.LinearProgramming.PriceGame.MarketSolverBounds
import OAI.Optimization.LinearProgramming.PriceGame.MarketPotentialsCost

/-! # Polynomial-size intermediates for the finite market solver

The input measure counts capacities, both reduced components of every arc bid,
and the dimensions. The same bound applies at each prefix of the executed
bit-scaling schedule, including after doublings. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace NumberBounds

open OAI.Optimization.LinearProgramming.PriceGame.Market.Augment
variable {m g : ℕ}

def arcInput (I : Input m g) (p : Fin m × Fin g) : ℚ := I.intercept p.1 p.2

def inputWidth (I : Input m g) (qty : Fin m → ℕ) : ℕ :=
  1 + m + g + (∑ e, (qty e).size) +
    (∑ p : Fin m × Fin g, ((arcInput I p).num.natAbs.size + (arcInput I p).den.size))

theorem dim_le_width (I : Input m g) (qty : Fin m → ℕ) : m + g + 1 ≤ inputWidth I qty := by
  unfold inputWidth
  omega

theorem qtyBits_le_width (I : Input m g) (qty : Fin m → ℕ) :
    Input.bits qty ≤ inputWidth I qty := by
  apply Finset.sup_le
  intro e _
  have h : (qty e).size ≤ ∑ j, (qty j).size :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (qty j).size) (Finset.mem_univ e)
  unfold inputWidth
  omega

theorem bidSize_le_width (I : Input m g) (qty : Fin m → ℕ) (e : Fin m) (i : Fin g) :
    (I.intercept e i).num.natAbs.size ≤ inputWidth I qty := by
  have h := Finset.single_le_sum
    (f := fun p : Fin m × Fin g => (arcInput I p).num.natAbs.size + (arcInput I p).den.size)
    (fun p _ => Nat.zero_le _) (Finset.mem_univ (e, i))
  change (I.intercept e i).num.natAbs.size + _ ≤ _ at h
  unfold inputWidth
  omega

theorem commonDenSize_le_width (I : Input m g) (qty : Fin m → ℕ) :
    (Denominator.denominator (arcInput I)).size ≤ inputWidth I qty + 1 := by
  have h := Denominator.denominator_size_le (arcInput I)
  have hb := Finset.sum_le_sum
    (s := Finset.univ) (fun (p : Fin m × Fin g) _ =>
      Nat.le_add_left (arcInput I p).den.size (arcInput I p).num.natAbs.size)
  unfold inputWidth
  omega

theorem abs_le_num (x : ℚ) : |x| ≤ (x.num.natAbs : ℚ) := by
  have h : (x.num : ℚ) = x * (x.den : ℚ) :=
    (div_eq_iff (by exact_mod_cast x.den_ne_zero)).mp x.num_div_den
  have habs : (x.num.natAbs : ℚ) = |(x.num : ℚ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hp : (1 : ℚ) ≤ (x.den : ℚ) := by exact_mod_cast x.den_pos
  rw [habs, h, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℚ) x.den)]
  exact le_mul_of_one_le_right (abs_nonneg _) hp

theorem bound_cost_by_width (I : Input m g) (qty : Fin m → ℕ) :
    OptimumDual.costBound I.intercept ≤ ((2 ^ inputWidth I qty : ℕ) : ℚ) := by
  apply Finset.max'_le
  intro q hq
  rcases Finset.mem_insert.mp hq with rfl | ha
  · positivity
  · obtain ⟨⟨e, i⟩, _, rfl⟩ := Finset.mem_image.mp ha
    apply (abs_le_num (I.intercept e i)).trans
    exact_mod_cast (Nat.lt_size_self _).le.trans
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (bidSize_le_width I qty e i))

/-- An upper magnitude for carried potentials. Its *encoding* grows polynomially
even when the numerical scale of the rewards is exponential. -/
def amplitude (s : ℕ) := 2 ^ s * (1 + s * s * (1 + s))

theorem amplitude_size (s : ℕ) : (amplitude s).size ≤ s + 2 + s * s * (1 + s) := by
  have h := Nat.size_le.mpr (Nat.lt_two_pow_self (n := 1 + s * s * (1 + s)))
  calc
    _ ≤ (2 ^ s).size + (1 + s * s * (1 + s)).size :=
      by
        apply Nat.size_le.mpr
        rw [pow_add]
        exact (Nat.mul_le_mul_right _ (Nat.lt_size_self _).le).trans_lt
          (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self _) (Nat.two_pow_pos _))
    _ ≤ _ := by rw [Nat.size_pow]; omega

theorem prefix_events (I : Input m g) (qty : Fin m → ℕ) (l : List (Option (Fin m)))
    (hl : l <+: schedule (Input.bits qty) qty) : (l.filterMap id).length ≤ inputWidth I qty ^ 2 := by
  obtain ⟨tail, ht⟩ := hl
  have hn := schedule_cost (Input.bits qty) qty
  rw [← ht, List.filterMap_append, List.length_append] at hn
  have he : m ≤ inputWidth I qty := by have := dim_le_width I qty; omega
  exact (show (l.filterMap id).length ≤ m * Input.bits qty by omega).trans
    (by simpa [pow_two] using Nat.mul_le_mul he (qtyBits_le_width I qty))

theorem prefix_amplitude (I : Input m g) (qty : Fin m → ℕ) (l : List (Option (Fin m)))
    (hl : l <+: schedule (Input.bits qty) qty) :
    let C := OptimumDual.costBound I.intercept
    C + ((l.filterMap id).length : ℚ) * (1 + ((m + g : ℕ) : ℚ) * C) ≤ (amplitude (inputWidth I qty) : ℚ) := by
  let s := inputWidth I qty
  let A : ℚ := ((2 ^ s : ℕ) : ℚ)
  let C := OptimumDual.costBound I.intercept
  let k := (l.filterMap id).length
  have hC : C ≤ A := bound_cost_by_width I qty
  have h0 : 0 ≤ C := OptimumDual.costBound_nonneg _
  have h1 : (1 : ℚ) ≤ A := by unfold A; exact_mod_cast (Nat.one_le_two_pow : 1 ≤ 2 ^ s)
  have hA : 0 ≤ A := h1.trans' zero_le_one
  have hdim : ((m + g : ℕ) : ℚ) ≤ (s : ℚ) := by
    exact_mod_cast (by have := dim_le_width I qty; dsimp [s]; omega : m + g ≤ s)
  have hkNat : k ≤ s * s := by simpa only [k, s, pow_two] using prefix_events I qty l hl
  have hk : (k : ℚ) ≤ (s : ℚ) * s := by exact_mod_cast hkNat
  have hinner : 1 + ((m + g : ℕ) : ℚ) * C ≤ (1 + (s : ℚ)) * A := by
    have hmul := mul_le_mul hdim hC h0 (Nat.cast_nonneg s)
    nlinarith only [hmul, h1]
  change C + (k : ℚ) * (1 + ((m + g : ℕ) : ℚ) * C) ≤ _
  calc
    _ ≤ A + ((s : ℚ) * s) * ((1 + (s : ℚ)) * A) :=
      add_le_add hC (mul_le_mul hk hinner (by positivity) (by positivity))
    _ = _ := by simp [amplitude, A, s]; ring

/-- One polynomial in encoded data bounds every stored dual register at every
actual prefix. The bound includes reduced numerators and denominators. -/
theorem prefix_dual_bits (I : Input m g) (qty : Fin m → ℕ) (l : List (Option (Fin m)))
    (hl : l <+: schedule (Input.bits qty) qty) :
    let s := inputWidth I qty
    let cap := 7 + 3 * s + s * s * (1 + s)
    let st := l.foldl (operation Input.double I.unit) I.initial
    (∀ e, RAM.ratBits (st.pe e) ≤ cap) ∧ (∀ o, RAM.ratBits (st.po o) ≤ cap) := by
  let S := inputWidth I qty
  let D := Denominator.denominator (arcInput I)
  have hD : 0 < D := Denominator.denominator_pos _
  have hd (e i) : OnGrid D (I.intercept e i) :=
    (grid_iff_den_dvd hD _).mpr (Denominator.den_dvd_denominator (arcInput I) (e, i))
  have hb := run_bound I hd l (initial_bound I D hd)
  have ha := prefix_amplitude I qty l hl
  have bs := amplitude_size S
  have ds := commonDenSize_le_width I qty
  change D.size ≤ S + 1 at ds
  have bound (x : ℚ) (grid : OnGrid D x) (h : |x| ≤ (amplitude S : ℚ)) :
      RAM.ratBits x ≤ 7 + 3 * S + S * S * (1 + S) := by
    have hh := ratBits_grid hD grid h
    omega
  exact ⟨fun e => bound _ (hb.expert_grid e) ((hb.expert_abs e).trans ha),
    fun o => bound _ (hb.option_grid o) ((hb.option_abs o).trans ha)⟩

/-- Width of the original rational market, before clearing supplies. -/
def rationalInputWidth (I : Input m g) (L : Fin m → ℚ) : ℕ :=
  1 + m + g + (∑ e, ((L e).num.natAbs.size + (L e).den.size)) +
    (∑ p : Fin m × Fin g, ((arcInput I p).num.natAbs.size + (arcInput I p).den.size))

theorem cleared_width (I : Input m g) (L : Fin m → ℚ) (Q : ℕ) :
    inputWidth I (fun e => Denominator.qty Q (L e)) ≤ rationalInputWidth I L + m * Q.size := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun (e : Fin m) _ => Denominator.qty_size_le Q (L e))
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun (e : Fin m) _ =>
    Nat.le_add_right (L e).num.natAbs.size (L e).den.size)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hs
  have sumBound : (∑ e, (Denominator.qty Q (L e)).size) ≤
      (∑ e, ((L e).num.natAbs.size + (L e).den.size)) + m * Q.size :=
    hs.trans (Nat.add_le_add_right hl _)
  unfold inputWidth rationalInputWidth
  calc
    _ ≤ (1 + m + g) + ((∑ e, ((L e).num.natAbs.size + (L e).den.size)) + m * Q.size) +
        (∑ p : Fin m × Fin g, ((arcInput I p).num.natAbs.size + (arcInput I p).den.size)) :=
      Nat.add_le_add_right (Nat.add_le_add_left sumBound _) _
    _ = _ := by ac_rfl

theorem standard_den_width (I : Input m g) (L : Fin m → ℚ) :
    (Denominator.denominator L).size ≤ rationalInputWidth I L + 1 := by
  have hh := Denominator.denominator_size_le L
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun (e : Fin m) _ =>
    Nat.le_add_left (L e).den.size (L e).num.natAbs.size)
  unfold rationalInputWidth
  omega

theorem cleared_width_default (I : Input m g) (L : Fin m → ℚ) :
    inputWidth I (fun e => Denominator.qty (Denominator.denominator L) (L e)) ≤
      rationalInputWidth I L + m * (rationalInputWidth I L + 1) :=
  (cleared_width I L _).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (standard_den_width I L)) _)

end NumberBounds
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
