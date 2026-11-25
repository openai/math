import OAI.Computability.NearSquareRoot.PhysicalWalshPositionInverse

/-! # Accounting for arbitrary position routing before and after a selected Walsh pass

The positional permutation compiler can spend a fixed polynomial in the
address width on its small tables, in addition to the record passes.
These estimates absorb both charges, including the singleton row.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.GatherProgram

open IntegerMultiplication Code Space FixedPoint Controlled.Reflections

theorem position_setup_bound (e : ℕ) : ∃ C : ℕ, ∀ k, (k+1)^e ≤ C*(Pieces.sparseSpace k+1) := by
  obtain ⟨D,b⟩ := polynomial_le_multiple_array_length e
  refine ⟨D,fun k => (b k).trans (Nat.mul_le_mul_left _ ?_)⟩
  cases k with
  | zero => decide
  | succ n => exact (Nat.le_mul_of_pos_right (2^(n+1)) (Nat.succ_pos _)).trans (Nat.le_succ _)

theorem position_time_bound {ρ : ℝ} (hr : 0 ≤ ρ) (e : ℕ) :
    ∃ B : ℕ, ∀ k : ℕ, (Odd.time k:ℝ)*(1+(k:ℝ))^ρ + ((k+1:ℕ):ℝ)^e ≤ B*(Pieces.sparseTime ρ k+1:ℕ) := by
  obtain ⟨D,d⟩ := Pieces.odd_time_le (ρ:=0) le_rfl
  obtain ⟨E,hE⟩ := position_setup_bound e
  refine ⟨3*D+E+2,fun k => ?_⟩
  have extra : (((k+1:ℕ):ℝ)^e) ≤ (E:ℝ)*(Pieces.sparseTime ρ k+1:ℕ) := by
    exact_mod_cast (hE k).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Pieces.space_le_clock hr k) 1))
  have time : (Odd.time k:ℝ)*(1+(k:ℝ))^ρ ≤ (3*D+1:ℕ)*(Pieces.sparseTime ρ k+1:ℕ) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Odd.time,GridTask.recordCost,Pieces.sparseTime]
    let V := (2:ℝ)^k*k
    let Z := 1+Real.log (2+(k:ℝ))
    let R := (1+(k:ℝ))^ρ
    have hz : 1 ≤ Z := by unfold Z; linarith [Real.log_nonneg (show 1 ≤ 2+(k:ℝ) by linarith [Nat.cast_nonneg (α:=ℝ) k])]
    have hv : 1 ≤ V := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (by exact_mod_cast hk)
    have vz := one_le_mul_of_one_le_of_one_le hv hz
    have clk : Pieces.sparseTime 0 k = ⌈V*Z⌉₊ := by simp [Pieces.sparseTime,V,Z]
    have cceil := (Nat.ceil_lt_add_one (zero_le_one.trans vz)).le
    have base : (Odd.time k:ℝ) ≤ 3*D*(V*Z) := by
      have given := d k
      rw [clk] at given
      have c : (Odd.time k:ℝ) ≤ (D:ℝ)*((⌈V*Z⌉₊:ℕ)+1) := by exact_mod_cast given
      apply c.trans
      calc
        _ ≤ (D:ℝ)*(3*(V*Z)) := mul_le_mul_of_nonneg_left (by linarith only [vz,cceil]) (Nat.cast_nonneg D)
        _ = _ := by ring
    have hc : V*Z*R ≤ (Pieces.sparseTime ρ k:ℝ) := by
      simpa only [Pieces.sparseTime,V,Z,R,mul_right_comm] using Nat.le_ceil (V*R*Z)
    have mult := mul_le_mul_of_nonneg_right base (show 0 ≤ R by unfold R; positivity)
    change (Odd.time k:ℝ)*R ≤ _
    apply mult.trans
    rw [mul_assoc (3*(D:ℝ))]
    have b := mul_le_mul_of_nonneg_left hc (show 0 ≤ (3:ℝ)*D by positivity)
    push_cast
    apply b.trans
    nlinarith only [Nat.cast_nonneg (α:=ℝ) (Pieces.sparseTime ρ k),Nat.cast_nonneg (α:=ℝ) D]
  push_cast at time extra ⊢
  nlinarith only [time,extra,Nat.cast_nonneg (α:=ℝ) (Pieces.sparseTime ρ k)]

/-- A physically executed record router with a polynomial setup term gives the
original-order, sparse-width position-routing primitive. -/
theorem positionRuns_of_native_rate {ρ : ℝ} {K : ℕ} (hr : 0 ≤ ρ)
    {t r : {v : PositionInput // K ≤ v.k} → ℕ}
    (route : BoundedTask t r (fun q => send (table q.val.positions,Odd.words q.val.row))
      (fun q => send (Odd.words (q.val.row ∘ BoxFin.bitAddress q.val.positions))))
    (C e : ℕ) (ht : ∀ q,(t q:ℝ) ≤ C*((Odd.time q.val.k:ℝ)*(1+(q.val.k:ℝ))^ρ + ((q.val.k+1:ℕ):ℝ)^e))
    (hs : ∀ q,r q ≤ C*(Odd.volume q.val.k + (q.val.k+1)^e)) : PositionRuns ρ K := by
  apply positionRuns_of_push hr
  obtain ⟨B,bd⟩ := position_time_bound hr e
  obtain ⟨D,dd⟩ := position_setup_bound e
  apply route.bound (C*B+1) (C*(2+D)+1)
  · intro q
    have le := (ht q).trans (mul_le_mul_of_nonneg_left (bd q.val.k) (Nat.cast_nonneg (α:=ℝ) C))
    rw [←mul_assoc] at le
    have b : t q ≤ C*B*(Pieces.sparseTime ρ q.val.k+1) := by exact_mod_cast le
    rw [Nat.succ_mul]
    omega
  · intro q
    have le := (hs q).trans (Nat.mul_le_mul_left C (Nat.add_le_add (Pieces.odd_volume_le q.val.k) (dd q.val.k)))
    rw [←Nat.add_mul,←Nat.mul_assoc] at le
    rw [Nat.succ_mul]
    omega

end PhysicalWalsh.GatherProgram

end NearSquareRoot
end Computability
end OAI
