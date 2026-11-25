import OAI.Computability.BorderVNP.PackedDeckEnergy

/-! # Telescoping the chosen motions over the actual sequence of count banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckEnergy

open CoverDeck PackedDeckCandidate Epoch Finset

variable {B G J : Type*} [Fintype B] [Fintype G] [Group G] [Fintype J] {K : ℕ}

/-- Successive updated banks contain the chosen translated raw counts and exact accumulated
means. The final squared deviation is bounded by the sum of the one-pack raw budgets. -/
theorem run_energy (prob : Fin K → J → ℚ) (hp : ∀ i, ∑ j, prob i j = 1)
    (C : Fin K → J → B → G → ℕ) (bank : ℕ → B → G → ℕ) (base : ℕ → B → ℚ)
    (choice : Fin K → J) (deck : Fin K → G)
    (start : ∀ b g, (bank 0 b g : ℚ) = base 0 b)
    (update : ∀ (i : Fin K) b g, bank (i.val+1) b g = bank i.val b g + C i (choice i) b (deck i*g))
    (means : ∀ (i : Fin K) b, base (i.val+1) b = base i.val b + PackedDeckMean.mean (prob i) (C i) b 1)
    (picked : ∀ (i : Fin K), increment (fun b g => (bank i.val b g : ℚ)-base i.val b)
        (fun b g => (C i (choice i) b g : ℚ)) (fun b => PackedDeckMean.mean (prob i) (C i) b 1) (deck i) ≤
      ∑ j, prob i j * uniformScore (bank i.val) (C i j) (base i.val)
        (fun b => PackedDeckMean.mean (prob i) (C i) b 1)) :
    bankEnergy (bank K) (base K) ≤ ∑ i, rawBudget (prob i) (C i) := by
  let budget (j : ℕ) := if h : j < K then rawBudget (prob ⟨j,h⟩) (C ⟨j,h⟩) else 0
  have cumulative (t : ℕ) (ht : t ≤ K) : bankEnergy (bank t) (base t) ≤ ∑ j ∈ range t, budget j := by
    induction t with
    | zero => simp [bankEnergy, energy, start]
    | succ t ih =>
      let i : Fin K := ⟨t,ht⟩
      have hb : bank (t+1) = fun b g => bank t b g + C i (choice i) b (deck i*g) :=
        funext fun b => funext (update i b)
      have hμ : base (t+1) = fun b => base t b + PackedDeckMean.mean (prob i) (C i) b 1 :=
        funext (means i)
      rw [hb,hμ,sum_range_succ]
      have hc : budget t = rawBudget (prob i) (C i) := by simp [budget, i, show t < K from ht]
      rw [hc]
      exact (bank_step_le (prob i) (hp i) (bank t) (C i) (base t) (choice i) (deck i) (picked i)).trans
        (add_le_add (ih (Nat.le_of_lt ht)) le_rfl)
  have full : (∑ i : Fin K, rawBudget (prob i) (C i)) = ∑ j ∈ range K, budget j := by
    rw [← Fin.sum_univ_eq_sum_range budget]
    exact sum_congr rfl fun i _ => by simp [budget, i.isLt]
  rw [full]
  exact cumulative K le_rfl

omit [Group G] in
/-- A one-pack uniform bound on translated raw energies controls its full probability-weighted
budget. Multiplying by the tile count is exactly the normalization of §6. -/
theorem rawBudget_le {tiles radius : ℝ} (prob : J → ℚ)
    (hpos : ∀ j, 0 ≤ prob j) (hp : ∑ j, prob j = 1) (C : J → B → G → ℕ)
    (bound : ∀ j, tiles * ((energy (fun b g => (C j b g : ℚ)) : ℚ) : ℝ) ≤ radius^2) :
    tiles * (rawBudget prob C : ℝ) ≤ radius^2 := by
  have mass : ∑ j, ((prob j : ℚ) : ℝ) = 1 := by exact_mod_cast hp
  simp only [rawBudget, Rat.cast_sum, Rat.cast_mul, mul_sum]
  calc
    _ = ∑ j, (prob j : ℝ) * (tiles * (energy (fun b g => (C j b g : ℚ)) : ℝ)) :=
      sum_congr rfl fun _ _ => by ring
    _ ≤ ∑ j, (prob j : ℝ) * radius^2 := sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (bound j) (by exact_mod_cast hpos j)
    _ = _ := by rw [← sum_mul, mass, one_mul]

omit [Group G] in
/-- Equation (6.2) for the chosen final bank, rather than merely for some outcome of independent
pack sampling. The bank and mean are divided by the number of original packs. -/
theorem normalized_bound (hK : 0 < K) {tiles radius : ℝ} (ht : 0 ≤ tiles) (hr : 0 ≤ radius)
    (A : B → G → ℕ) (base : B → ℚ) (cost : Fin K → ℚ)
    (hbank : bankEnergy A base ≤ ∑ i, cost i) (hcost : ∀ i, tiles * (cost i : ℝ) ≤ radius^2) :
    Real.sqrt tiles * Real.sqrt (binEnergy (fun z : G × B =>
      (A z.2 z.1 : ℝ)/K - (base z.2 : ℝ)/K)) ≤ radius / Real.sqrt K := by
  let k : ℝ := K
  let E : ℝ := bankEnergy A base
  have hk : 0 < k := by dsimp [k]; exact_mod_cast hK
  have hE : 0 ≤ E := by
    change 0 ≤ ((∑ b, ∑ g, ((A b g : ℚ)-base b)^2 : ℚ) : ℝ)
    exact_mod_cast (sum_nonneg (s := univ) fun (b : B) _ => sum_nonneg (s := univ) fun (g : G) _ => sq_nonneg ((A b g : ℚ)-base b))
  have hcast : E ≤ ∑ i, (cost i : ℝ) := by dsimp [E]; exact_mod_cast hbank
  have hnorm : tiles * E ≤ k * radius^2 := calc
    _ ≤ tiles * ∑ i, (cost i : ℝ) := mul_le_mul_of_nonneg_left hcast ht
    _ = ∑ i, tiles*(cost i : ℝ) := mul_sum ..
    _ ≤ ∑ _ : Fin K, radius^2 := sum_le_sum fun i _ => hcost i
    _ = _ := by simp [k]
  have hscale : binEnergy (fun z : G × B => (A z.2 z.1 : ℝ)/k - (base z.2 : ℝ)/k) = E/k^2 := by
    simp only [binEnergy, Fintype.sum_prod_type, ← sub_div, div_pow, ← sum_div, E, bankEnergy, energy, Rat.cast_sum,
      Rat.cast_pow, Rat.cast_sub, Rat.cast_natCast]
    rw [sum_comm]
  change Real.sqrt tiles * Real.sqrt (binEnergy (fun z : G × B => (A z.2 z.1 : ℝ)/k - (base z.2 : ℝ)/k)) ≤ radius / Real.sqrt k
  rw [hscale, Real.sqrt_div hE, Real.sqrt_sq hk.le, ← mul_div_assoc, ← Real.sqrt_mul ht,
    div_le_div_iff₀ hk (Real.sqrt_pos.2 hk)]
  have hroot := Real.sqrt_le_sqrt hnorm
  rw [Real.sqrt_mul hk.le, Real.sqrt_sq hr] at hroot
  calc
    _ ≤ (Real.sqrt k * radius)*Real.sqrt k := mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)
    _ = _ := by rw [mul_comm (Real.sqrt k) radius, mul_assoc, Real.mul_self_sqrt hk.le]

/-- The complete (6.2) estimate for the actual sequentially updated count bank on the
product deck group. The raw one-pack bound is the geometric concentration bound applied
to the fixed candidate before its final translation. -/
theorem run_concentrated (hK : 0 < K) {radius : ℝ} (hr : 0 ≤ radius)
    (prob : Fin K → J → ℚ) (hn : ∀ i j, 0 ≤ prob i j) (hp : ∀ i, ∑ j, prob i j = 1)
    (C : Fin K → J → B → G → ℕ) (bank : ℕ → B → G → ℕ) (base : ℕ → B → ℚ)
    (choice : Fin K → J) (deck : Fin K → G)
    (start : ∀ b g, (bank 0 b g : ℚ) = base 0 b)
    (update : ∀ (i : Fin K) b g, bank (i.val+1) b g = bank i.val b g + C i (choice i) b (deck i*g))
    (means : ∀ (i : Fin K) b, base (i.val+1) b = base i.val b + PackedDeckMean.mean (prob i) (C i) b 1)
    (picked : ∀ (i : Fin K), increment (fun b g => (bank i.val b g : ℚ)-base i.val b)
        (fun b g => (C i (choice i) b g : ℚ)) (fun b => PackedDeckMean.mean (prob i) (C i) b 1) (deck i) ≤
      ∑ j, prob i j * uniformScore (bank i.val) (C i j) (base i.val)
        (fun b => PackedDeckMean.mean (prob i) (C i) b 1))
    (bound : ∀ i j, (Fintype.card G : ℝ) * ((energy (fun b g => (C i j b g : ℚ)) : ℚ) : ℝ) ≤ radius^2) :
    Real.sqrt (Fintype.card G) * Real.sqrt (binEnergy (fun z : G × B =>
      (bank K z.2 z.1 : ℝ)/K - (base K z.2 : ℝ)/K)) ≤ radius / Real.sqrt K :=
  normalized_bound hK (Nat.cast_nonneg _) hr (bank K) (base K) _
    (run_energy prob hp C bank base choice deck start update means picked)
    (fun i => rawBudget_le (prob i) (hn i) (hp i) (C i) (bound i))

end PackedDeckEnergy

end BorderVNP
end Computability
end OAI
