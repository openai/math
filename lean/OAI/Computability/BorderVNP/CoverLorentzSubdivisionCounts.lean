import OAI.Computability.BorderVNP.CoverLorentzSubdivision
import OAI.Computability.BorderVNP.ShortenEpochLocality

/-!
# Site loads during geodesic subdivision

The table for each hop sends records to one fixed offset of the initial
tile. Consequently the fan-in and fan-out are bounded independently of
the congruence level, for both public records and expanded bit slots.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Set Finset

section Arrays

variable {G S J : Type*} [Group G] [Fintype S] [Fintype J]

/-- Charge each wire at its initial tile and separate the charges by move type. -/
def sourceMass (rows : G → S → ℝ) (g : G) : ℝ := ∑ s, rows g s

/-- Reassign one copy of each record to each prescribed segment slot, preserving its mass. -/
def slotMass (rows : G → S → ℝ) (offset : S × J → G) (b : G) : ℝ :=
  ∑ t : S × J, rows (b * (offset t)⁻¹) t.1

/-- Bounded initial load per tile implies bounded load at every fixed slot type. -/
theorem slotMass_le_max (rows : G → S → ℝ) (offset : S × J → G) {M : ℝ}
    (hpos : ∀ g s, 0 ≤ rows g s) (hM : ∀ g, sourceMass rows g ≤ M) (b : G) :
    slotMass rows offset b ≤ Fintype.card (S × J) * M := by
  calc
    _ ≤ ∑ _t : S × J, M := by
      apply sum_le_sum
      intro t _
      exact (single_le_sum (fun s _ => hpos _ s) (mem_univ t.1)).trans (hM _)
    _ = _ := by simp

/-- Squared midpoint loads are bounded using Cauchy–Schwarz and the fact that every
fixed carry acts as a permutation of the tile names. -/
theorem slotMass_energy [Fintype G] (rows : G → S → ℝ) (offset : S × J → G)
    (hpos : ∀ g s, 0 ≤ rows g s) :
    ∑ b, (slotMass rows offset b)^2 ≤
      (Fintype.card (S × J) : ℝ)^2 * ∑ a, (sourceMass rows a)^2 := by
  let T := Fintype.card (S × J)
  have term (b : G) (t : S × J) : rows (b*(offset t)⁻¹) t.1 ^ 2 ≤ sourceMass rows (b*(offset t)⁻¹)^2 :=
    pow_le_pow_left₀ (hpos _ _) (single_le_sum (fun s _ => hpos _ s) (mem_univ t.1)) 2
  calc
    _ ≤ ∑ b, (T:ℝ) * ∑ t : S × J, sourceMass rows (b*(offset t)⁻¹)^2 := by
      apply sum_le_sum
      intro b _
      calc
        _ ≤ (T:ℝ) * ∑ t : S × J, rows (b*(offset t)⁻¹) t.1 ^ 2 := by
          simpa only [T,slotMass,card_univ] using (sq_sum_le_card_mul_sum_sq
            (s := (univ : Finset (S × J))) (f := fun t => rows (b*(offset t)⁻¹) t.1))
        _ ≤ _ := mul_le_mul_of_nonneg_left (sum_le_sum (fun t _ => term b t)) (Nat.cast_nonneg _)
    _ = (T:ℝ) * ∑ t : S × J, ∑ b : G, sourceMass rows (b*(offset t)⁻¹)^2 := by
      rw [← mul_sum, sum_comm]
    _ = _ := by
      have he (t : S × J) : (∑ b : G, sourceMass rows (b*(offset t)⁻¹)^2) =
          ∑ b : G, sourceMass rows b^2 :=
        Equiv.sum_comp (Equiv.mulRight ((offset t)⁻¹)) (fun b => sourceMass rows b ^ 2)
      simp_rw [he]
      simp [T,pow_two,mul_assoc]

variable {E : Type*} [Fintype E]

/-- Populate the public rows by grouping the actual wires by source tile and chosen move. -/
noncomputable def sourceRows (atTile : E → G) (move : E → S) (charge : E → ℝ) (a : G) (s : S) : ℝ := by
  classical
  exact ∑ e, if atTile e = a ∧ move e = s then charge e else 0

omit [Group G] [Fintype S] [Fintype J] in
/-- Nonnegative wire charges give nonnegative public rows. -/
theorem sourceRows_nonneg (atTile : E → G) (move : E → S) {charge : E → ℝ} (hc : ∀ e, 0 ≤ charge e) :
    ∀ a s, 0 ≤ sourceRows atTile move charge a s := by
  classical
  exact fun _ _ => sum_nonneg fun e _ => by split_ifs <;> simp_all

omit [Group G] [Fintype J] in
/-- Grouping by move preserves the source count. -/
theorem sourceMass_rows [DecidableEq G] (atTile : E → G) (move : E → S) (charge : E → ℝ) (a : G) :
    sourceMass (sourceRows atTile move charge) a = ∑ e, if atTile e = a then charge e else 0 := by
  classical
  simp only [sourceMass,sourceRows]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  by_cases h : atTile e = a <;> simp [h]

/-- The histogram with carries counts exactly the wires whose actual slot lands at the
specified tile. -/
theorem slotMass_rows [DecidableEq G] (atTile : E → G) (move : E → S) (charge : E → ℝ)
    (offset : S × J → G) (b : G) :
    slotMass (sourceRows atTile move charge) offset b =
      ∑ e, ∑ j : J, if atTile e * offset (move e,j) = b then charge e else 0 := by
  classical
  simp only [slotMass,sourceRows]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  rw [Fintype.sum_prod_type,sum_comm]
  apply sum_congr rfl
  intro j _
  rw [sum_eq_single (move e)]
  · simp [eq_mul_inv_iff_mul_eq]
  · intro s _ hs
    simp [Ne.symm hs]
  · simp

end Arrays

open BorderVNP.Epoch
open scoped Classical

variable {I : Type*} [Fintype I] {L h : ℝ}

/-- Exact histogram of physical midpoints, with wires indexed by their actual start and move. -/
theorem midpoint_histogram {E : Type*} [Fintype E] (d : ℕ) (a : E → I → gamma 1)
    (s : E → allowedMoves I L) (charge : E → ℝ) (b : I → Deck (d+1)) :
    slotMass (sourceRows (fun e => reduceMove d (a e)) s charge)
      (fun t : Hop I L h => reduceMove d (hopCarry t (1/2))) b =
    ∑ e, ∑ j : Fin (hopCount L h), if productAddress d (productProjection (d+1)
      (translatePoint (a e) (hopPosition (s e,j) (1/2)))) = b then charge e else 0 := by
  classical
  simp_rw [hopAddress]
  exact slotMass_rows _ _ _ _ _

/-- Midpoint concentration after subdivision is bounded by the site-incidence concentration
times the fixed catalog size. Incoming endpoint incidences may also be charged in `ends`. -/
theorem initial_concentration_le (d : ℕ) (rows : (I → Deck (d+1)) → allowedMoves I L → ℝ)
    (ends : (I → Deck (d+1)) → ℝ) (hpos : ∀ a s, 0 ≤ rows a s)
    (he : ∀ a, sourceMass rows a ≤ ends a) :
    Real.sqrt (Fintype.card (I → Deck (d+1))) *
      Real.sqrt (∑ b, (slotMass rows (fun t : Hop I L h => reduceMove d (hopCarry t (1/2))) b)^2) ≤
    Fintype.card (Hop I L h) * (Real.sqrt (Fintype.card (I → Deck (d+1))) *
      Real.sqrt (∑ a, (ends a)^2)) := by
  have hsum : (∑ a, (sourceMass rows a)^2) ≤ ∑ a, (ends a)^2 :=
    sum_le_sum (fun a _ => pow_le_pow_left₀ (sum_nonneg (fun s _ => hpos a s)) (he a) 2)
  have hz := (slotMass_energy rows (fun t : Hop I L h => reduceMove d (hopCarry t (1/2))) hpos).trans
    (mul_le_mul_of_nonneg_left hsum (sq_nonneg _))
  have hroot := Real.sqrt_le_sqrt hz
  rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg _)] at hroot
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)

/-- Retaining the old tile records and adding the new first-end, equality-site and last-end
records costs a level-independent multiple of the input per-tile bound. The same proof
applies with expanded records charged by their slot widths. -/
theorem subdivision_tile_load_le (d : ℕ) (rows : (I → Deck (d+1)) → allowedMoves I L → ℝ)
    (retained : (I → Deck (d+1)) → ℝ) {M : ℝ} (hpos : ∀ a s, 0 ≤ rows a s)
    (he : ∀ a, sourceMass rows a ≤ M) (hr : ∀ a, retained a ≤ M) (b : I → Deck (d+1)) :
    retained b + slotMass rows (fun t : Hop I L h => reduceMove d (hopCarry t 0)) b +
      slotMass rows (fun t : Hop I L h => reduceMove d (hopCarry t 0)) b +
      slotMass rows (fun t : Hop I L h => reduceMove d (hopCarry t 1)) b ≤
      (1 + 3*(Fintype.card (Hop I L h) : ℝ))*M := by
  have hs (f : ℝ) := slotMass_le_max rows (fun t : Hop I L h => reduceMove d (hopCarry t f)) hpos he b
  linarith only [hr b,hs 0,hs 1]

end Cover

end BorderVNP
end Computability
end OAI
