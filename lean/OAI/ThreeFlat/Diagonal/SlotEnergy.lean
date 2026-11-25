import OAI.Computability.VPVNP.Compression
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

namespace OAI
/-! # Integer slot widths and the compression energy

A payload is split into consecutive strings. The first `b % m` strings
have one more bit than the others. The additive energy cost is the
variance of these two lengths. -/

namespace ThreeFlat.Diagonal.SlotEnergy

open scoped BigOperators

/-- Number of bits assigned to a particular slot in a balanced split. -/
def piece (b m : ℕ) (i : Fin m) : ℕ := b / m + if i.val < b % m then 1 else 0

private theorem sum_long (b m : ℕ) (hm : 0 < m) :
    (∑ i : Fin m, if i.val < b % m then 1 else 0 : ℕ) = b % m := by
  let r : Fin m := ⟨b % m, Nat.mod_lt _ hm⟩
  have h : Finset.univ.filter (fun i : Fin m => i.val < b % m) = Finset.Iio r := by
    ext i
    simp [r, Fin.lt_def]
  rw [Finset.sum_boole, h, Fin.card_Iio]
  rfl

/-- Concatenating the pieces reconstructs the entire payload length. -/
theorem sum_piece (b m : ℕ) (hm : 0 < m) : ∑ i, piece b m i = b := by
  simp only [piece, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Nat.nsmul_eq_mul, sum_long b m hm]
  exact Nat.div_add_mod b m

/-- The sum of squares differs from that of the uniform real allocation by
exactly the variance contribution of the remainder. -/
theorem sum_piece_sq (b m : ℕ) (hm : 0 < m) :
    (∑ i : Fin m, (piece b m i : ℝ) ^ 2) =
      (m : ℝ) * (b / m : ℕ) ^ 2 + (2 * (b / m : ℕ) + 1) * (b % m : ℕ) := by
  let q : ℝ := (b / m : ℕ)
  have entry (i : Fin m) : (piece b m i : ℝ)^2 =
      q ^ 2 + (2*q + 1) * ((if i.val < b % m then 1 else 0 : ℕ) : ℝ) := by
    by_cases h : i.val < b % m <;> simp [piece, q, h]; ring
  rw [Finset.sum_congr rfl (fun i _ => entry i), Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Nat.cast_sum, sum_long b m hm]
  simp [q]

/-- Splitting one wire into `m` integer pieces incurs at most `m/4` in
squared length above the Cauchy–Schwarz lower bound. -/
theorem sum_piece_sq_le (b m : ℕ) (hm : 0 < m) :
    (∑ i : Fin m, (piece b m i : ℝ)^2) ≤ (b : ℝ)^2 / m + m / 4 := by
  rw [sum_piece_sq b m hm]
  have hpos : (0 : ℝ) < m := by exact_mod_cast hm
  have decomp : (b : ℝ) = (m : ℝ) * (b / m : ℕ) + (b % m : ℕ) := by
    exact_mod_cast (Nat.div_add_mod b m).symm
  rw [show (b : ℝ)^2 = ((m : ℝ) * (b / m : ℕ) + (b % m : ℕ))^2 from congrArg (·^2) decomp]
  field_simp [hpos.ne']
  nlinarith [sq_nonneg ((m : ℝ) - 2*(b % m : ℕ))]

/-- The integer count of parallel slots supplies the required fraction of
ideal mass once one slot lies within the allowed relative loss. -/
theorem floor_mass {mass p δ : ℝ} (hp : 0 < p) (hm : 0 < mass) (hδ : δ < 1)
    (hsmall : p ≤ δ * mass) :
    let m := ⌊mass / p⌋₊
    0 < m ∧ (1-δ)*mass ≤ m*p ∧ m*p ≤ mass := by
  dsimp only
  have hlt := Nat.lt_floor_add_one (mass / p)
  have hslot : mass < ((⌊mass/p⌋₊ : ℝ)+1)*p := (div_lt_iff₀ hp).mp hlt
  have hlo : (1-δ)*mass ≤ ⌊mass/p⌋₊*p := by nlinarith
  have hpos : (0:ℝ) < (1-δ)*mass := mul_pos (by linarith) hm
  refine ⟨?_, hlo, (le_div_iff₀ hp).mp (Nat.floor_le (div_nonneg hm.le hp.le))⟩
  by_contra! he
  have heq : ⌊mass/p⌋₊ = 0 := by omega
  rw [heq, Nat.cast_zero, zero_mul] at hlo
  linarith

/-- Energy of the actual integer pieces after the relative mass loss in
parallel slot allocation. -/
theorem piece_energy_le (b m : ℕ) (hm : 0 < m) {p mass δ : ℝ}
    (hp : 0 < p) (hδ : δ < 1) (hmass : 0 < mass) (henough : (1-δ)*mass ≤ m*p) :
    (∑ i : Fin m, (piece b m i : ℝ)^2 / p) ≤ (b : ℝ)^2 / mass / (1-δ) + m/(4*p) := by
  rw [← Finset.sum_div]
  calc
    _ ≤ ((b : ℝ)^2 / m + m / 4) / p := div_le_div_of_nonneg_right (sum_piece_sq_le b m hm) hp.le
    _ = (b : ℝ)^2 / (m*p) + m/(4*p) := by ring
    _ ≤ (b : ℝ)^2 / ((1-δ)*mass) + m/(4*p) := by
      exact add_le_add (div_le_div_of_nonneg_left (sq_nonneg _)
        (mul_pos (sub_pos.mpr hδ) hmass) henough) le_rfl
    _ = _ := by rw [div_div, mul_comm (1-δ) mass]

/-- Summing over all surviving wires charges only their total number of
parallel arcs. The arc mass is `1/Z` and at most `Z` arcs are allocated. -/
theorem regularized_energy_le {E : Type*} [Fintype E] (b m : E → ℕ) (mass : E → ℝ)
    {Z δ : ℝ} (hZ : 0 < Z) (hδ : δ < 1) (hm : ∀ e, 0 < m e)
    (hpos : ∀ e, 0 < mass e) (enough : ∀ e, (1-δ)*mass e ≤ m e * (1/Z))
    (capacity : ∑ e, (m e : ℝ) ≤ Z) :
    (∑ e, ∑ i : Fin (m e), (piece (b e) (m e) i : ℝ)^2 / (1/Z)) ≤
      (∑ e, (b e : ℝ)^2 / mass e) / (1-δ) + Z^2/4 := by
  calc
    _ ≤ ∑ e, ((b e : ℝ)^2 / mass e / (1-δ) + m e/(4*(1/Z))) :=
      Finset.sum_le_sum fun e _ => piece_energy_le _ _ (hm e) (by positivity) hδ (hpos e) (enough e)
    _ = (∑ e, (b e : ℝ)^2 / mass e) / (1-δ) + (∑ e, (m e : ℝ))/(4*(1/Z)) := by
      rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
    _ ≤ _ := by
      apply add_le_add le_rfl
      calc
        _ ≤ Z/(4*(1/Z)) := div_le_div_of_nonneg_right capacity (by positivity)
        _ = _ := by field_simp [hZ.ne']

/-- At refresh, concatenating a whole port fiber costs at most `d₀` times
the energy of its old strings when the new mass is `D*p/d₀`. -/
theorem refresh_bundle_le {D : ℕ} (b : Fin D → ℕ) {p d₀ : ℝ} (hp : 0 < p) (hd : 0 < d₀) :
    (∑ j, (b j : ℝ))^2 / ((D : ℝ)*p/d₀) ≤ d₀ * ∑ j, (b j : ℝ)^2 / p := by
  have h := Finset.sq_sum_div_le_sum_sq_div Finset.univ (fun j => (b j : ℝ)) (fun _ _ => hp)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  calc
    _ = d₀ * ((∑ j, (b j : ℝ))^2 / ((D : ℝ)*p)) := by rw [div_div_eq_mul_div]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h hd.le

/-- Pack `K` old widths into one payload and give its `Q` pieces equal
mass `r*p`. Equality `Q*r = K` makes the ideal demand cost at most the
old energy of the bundle. The only additive cost is rounding. -/
theorem packed_demand_le {K Q : ℕ} (b : Fin K → ℕ) {p r : ℝ}
    (hQ : 0 < Q) (hp : 0 < p) (hr : 0 < r) (hmatch : Q*r = K) :
    (∑ i : Fin Q, (piece (∑ j, b j) Q i : ℝ)^2 / (r*p)) ≤
      (∑ j, (b j : ℝ)^2 / p) + Q/(4*r*p) := by
  have h := Finset.sq_sum_div_le_sum_sq_div Finset.univ (fun j => (b j : ℝ)) (fun _ _ => hp)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  rw [← Finset.sum_div]
  calc
    _ ≤ (((∑ j, b j : ℕ) : ℝ)^2 / Q + Q/4)/(r*p) :=
      div_le_div_of_nonneg_right (sum_piece_sq_le _ _ hQ) (mul_pos hr hp).le
    _ = (∑ j, (b j : ℝ))^2 / ((Q*r)*p) + Q/(4*r*p) := by push_cast; ring
    _ ≤ _ := by rw [hmatch]; exact add_le_add h le_rfl

/-- All thick demand bundles together inherit the original energy up to an
explicit error per bundle. Thin demands keep their old mass and width. -/
theorem packed_demands_le {B : Type*} [Fintype B] {K Q : ℕ} (b : B → Fin K → ℕ) {p r : ℝ}
    (hQ : 0 < Q) (hp : 0 < p) (hr : 0 < r) (hmatch : Q*r = K) :
    (∑ t, ∑ i : Fin Q, (piece (∑ j, b t j) Q i : ℝ)^2 / (r*p)) ≤
      (∑ t, ∑ j, (b t j : ℝ)^2 / p) + Fintype.card B * (Q/(4*r*p)) := by
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    (Finset.sum_le_sum (s := Finset.univ) (fun t _ => packed_demand_le (b t) hQ hp hr hmatch))

/-- Choosing the cheaper of two layouts and regularizing the surviving
wires gives a strict shrink with the explicit ratio `126/127`. The two
errors are the pre-regularization additive loss and the new slot count. -/
theorem shrink_step {L left right extra Z final : ℝ}
    (supply : left + right ≤ (63/32 : ℝ)*L + extra)
    (slots : final ≤ min left right / (1-1/128) + Z^2/4) :
    final ≤ (126/127 : ℝ)*L + (64/127 : ℝ)*extra + Z^2/4 := by
  have choice : 2 * min left right ≤ left + right := by
    exact (by linarith [min_le_left left right, min_le_right left right])
  norm_num at slots ⊢
  linarith

end ThreeFlat.Diagonal.SlotEnergy

end OAI
