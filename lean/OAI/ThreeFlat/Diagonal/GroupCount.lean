import Lean.Elab.Tactic.Omega

namespace OAI
/-! # Group counts in the diagonal schedule

The factor `V/a` costs exactly `2^(w^4)`. The team count, polynomial
block length and fixed factor 2048 together cost at most another
`2^(w^4)`. The resulting groups fit in a quarter of the transition count.
-/

namespace ThreeFlat.Diagonal

/-- The external pairs are split into at most `2^(2*w^4)` groups.
This estimate also holds with rounded-down integer sizes. -/
theorem group_count_budget {w d A L : Nat} (hw : d + 16 ≤ w) (hL : L ≤ w ^ d) :
    let q := 2 ^ (w ^ 3)
    let V := 2 ^ (w ^ 10)
    let a := 2 ^ (w ^ 10 - w ^ 4)
    let B := 2 * (q * V * L / w ^ (A + 2))
    1024 * B / a ≤ 2 ^ (2 * w ^ 4) := by
  dsimp only
  have hwpos : 0 < w := by omega
  have hpoly : L ≤ 2 ^ (w ^ 2) := by
    calc
      L ≤ w ^ d := hL
      _ ≤ (2 ^ w) ^ d := Nat.pow_le_pow_left (Nat.le_of_lt Nat.lt_two_pow_self) _
      _ = 2 ^ (w * d) := (Nat.pow_mul ..).symm
      _ ≤ 2 ^ (w ^ 2) := Nat.pow_le_pow_right (by decide) (by
        simpa [Nat.pow_succ] using Nat.mul_le_mul_left w (by omega : d ≤ w))
  have hsmall : 11 + w ^ 3 + w ^ 2 ≤ w ^ 4 := by
    have htwo := Nat.pow_le_pow_right hwpos (by decide : 2 ≤ 3)
    have hthree := Nat.le_trans (by omega : 11 ≤ w) (Nat.le_self_pow (by decide : 3 ≠ 0) w)
    have hscale := Nat.mul_le_mul_left (w ^ 3) (by omega : 3 ≤ w)
    rw [Nat.pow_succ w 3]
    omega
  have hspine := Nat.pow_le_pow_right hwpos (by decide : 4 ≤ 10)
  apply Nat.div_le_of_le_mul
  calc
    1024 * (2 * (2 ^ (w ^ 3) * 2 ^ (w ^ 10) * L / w ^ (A + 2))) ≤
        1024 * (2 * (2 ^ (w ^ 3) * 2 ^ (w ^ 10) * 2 ^ (w ^ 2))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
        (Nat.le_trans (Nat.div_le_self ..) (Nat.mul_le_mul_left _ hpoly)))
    _ = 2 ^ 11 * (2 ^ (w ^ 3) * 2 ^ (w ^ 10) * 2 ^ (w ^ 2)) := by
      rw [← Nat.mul_assoc]
    _ = 2 ^ (11 + w ^ 3 + w ^ 10 + w ^ 2) := by
      simp only [Nat.pow_add, Nat.mul_assoc]
    _ ≤ 2 ^ ((w ^ 10 - w ^ 4) + 2 * w ^ 4) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    _ = _ := Nat.pow_add ..

/-- Four transitions per group fit in the total `T = 2^(w^6)`. -/
theorem group_count_fits_transitions {w J : Nat} (hw : 3 ≤ w)
    (hJ : J ≤ 2 ^ (2 * w ^ 4)) : 4 * J ≤ 2 ^ (w ^ 6) := by
  have hwpos : 0 < w := by omega
  have hfour := Nat.le_trans hw (Nat.le_self_pow (by decide : 4 ≠ 0) w)
  have hscale := Nat.mul_le_mul_left (w ^ 4) hw
  have h56 := Nat.pow_le_pow_right hwpos (by decide : 5 ≤ 6)
  rw [Nat.pow_succ w 4] at h56
  calc
    4 * J ≤ 4 * 2 ^ (2 * w ^ 4) := Nat.mul_le_mul_left _ hJ
    _ = 2 ^ (2 + 2 * w ^ 4) := (Nat.pow_add 2 2 _).symm
    _ ≤ 2 ^ (w ^ 6) := Nat.pow_le_pow_right (by decide) (by omega)

/-- At dyadic widths and block lengths a quarter of the transitions per group
consists of whole scans of the external register. -/
theorem dyadic_scan_alignment {w d A L : Nat} (hw : d + 16 ≤ w)
    (wdyad : ∃ u : Nat, w = 2 ^ u) (Ldyad : ∃ l : Nat, L = 2 ^ l)
    (hmin : w ^ (A + 2) ≤ L) (hmax : L ≤ w ^ d) :
    let q := 2 ^ (w ^ 3)
    let V := 2 ^ (w ^ 10)
    let a := 2 ^ (w ^ 10 - w ^ 4)
    let B := 2 * (q * V * L / w ^ (A + 2))
    let J := 1024 * B / a
    let T := 2 ^ (w ^ 6)
    (∃ k : Nat, J = 2 ^ k) ∧ (4 * J ∣ T) ∧ B / a ∣ T / (4 * J) := by
  intro q V a B J T
  obtain ⟨u, hu⟩ := wdyad
  obtain ⟨l, hl⟩ := Ldyad
  let denExp := u * (A + 2)
  have hden : w ^ (A + 2) = 2 ^ denExp := by rw [hu]; exact (Nat.pow_mul ..).symm
  rw [hden, hl] at hmin
  have hd := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hmin
  let bExp := 1 + (w ^ 3 + w ^ 10 + l - denExp)
  have hb : B = 2 ^ bExp := by
    change 2 * (2 ^ (w ^ 3) * 2 ^ (w ^ 10) * L / w ^ (A + 2)) = _
    rw [hden, hl, ← Nat.pow_add, ← Nat.pow_add, Nat.pow_div (by omega) (by decide)]
    exact (Nat.pow_add 2 1 _).symm
  have ha : w ^ 10 - w ^ 4 ≤ bExp := by dsimp only [bExp]; omega
  let scanExp := bExp - (w ^ 10 - w ^ 4)
  have haB : a ∣ B := by rw [hb]; exact Nat.pow_dvd_pow 2 ha
  have hscan : B / a = 2 ^ scanExp := by rw [hb]; exact Nat.pow_div ha (by decide)
  have hj : J = 2 ^ (10 + scanExp) := by
    change 1024 * B / a = _
    rw [Nat.mul_div_assoc _ haB, hscan]
    exact (Nat.pow_add 2 10 _).symm
  have hjBound : J ≤ 2 ^ (2 * w ^ 4) := group_count_budget hw hmax
  rw [hj] at hjBound
  have hjExp := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hjBound
  have hfour := Nat.le_trans (by omega : 2 ≤ w) (Nat.le_self_pow (by decide : 4 ≠ 0) w)
  have hscale := Nat.mul_le_mul_left (w ^ 4) (by omega : 5 ≤ w)
  have h56 := Nat.pow_le_pow_right (by omega : 0 < w) (by decide : 5 ≤ 6)
  rw [Nat.pow_succ w 4] at h56
  refine ⟨⟨_, hj⟩, ?_, Nat.dvd_div_of_mul_dvd ?_⟩
  · rw [hj]
    change 2 ^ 2 * 2 ^ (10 + scanExp) ∣ 2 ^ (w ^ 6)
    rw [← Nat.pow_add]
    exact Nat.pow_dvd_pow 2 (by omega)
  · rw [hj, hscan]
    change 2 ^ 2 * 2 ^ (10 + scanExp) * 2 ^ scanExp ∣ 2 ^ (w ^ 6)
    rw [← Nat.pow_add, ← Nat.pow_add]
    exact Nat.pow_dvd_pow 2 (by omega)

end ThreeFlat.Diagonal

end OAI
