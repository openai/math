import OAI.Computability.BorderVNP.TeamContractionWires

/-! # Sublinear interior width of the actual successor and paired-record topology

Each logical input-memory word or instruction probe uses two slots. A height
`clog 2 (2H)` therefore accommodates three blocks of header plus one of instructions in
`4·2^e` slots. The physical sorter width has one extra bit for the read/write ordinal.
Both effects and both possible virtual blocks fit a single uniform little-o estimate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.Wires

open TeamScales TeamTapeInputRoute Filter

/-- Physical bucket exponent for doubled read/write slots. -/
abbrev sortExponent (H : ℕ) := Nat.clog 2 (2*H)

/-- Room for the two slots of every initialization and execution probe at a processor. -/
theorem paired_slots_fit (H : ℕ) : 2*(3*H+H) ≤ 4*2^sortExponent H := by
  calc
    _ = 4*(2*H) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) _)

private theorem index_width {r n : ℕ} (hr : 0 < r) (hn : 0 < n) :
    Nat.clog 2 r+1 ≤ logWidth r n := by
  have hd : Nat.clog 2 (2*r) = Nat.clog 2 r+1 := by
    rw [Nat.clog_of_two_le (by decide) (by omega),show (2*r+2-1)/2 = r by omega]
  rw [← hd]
  have he : logWidth r n = Nat.clog 2 (2*n*r) := by
    unfold logWidth
    rw [← Real.natCeil_logb_natCast]
    norm_cast
  rw [he]
  exact Nat.clog_mono_right _ (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hn))

/-- All register-frame, comparator and boundary bits counted at their true physical
width, including the actual global zero clamps. -/
theorem innerWidth_bound {r n H : ℕ} (hr : 0 < r) (hn : 0 < n) (hH : 0 < H) (k D : ℕ) :
    let B := logWidth r n ^ D
    innerWidth r k B (sortExponent H) (B+1) ≤ (2*k+686)*H*logWidth r n^(D+2) := by
  intro B
  let L := logWidth r n
  let V := H*B*L^2
  have hd := index_width hr hn
  have hL : 1 ≤ L := by dsimp [L]; omega
  have hB : 1 ≤ B := Nat.one_le_pow _ _ hL
  have hsq : 1 ≤ L^2 := Nat.one_le_pow _ _ hL
  have hb : B ≤ V := (Nat.le_mul_of_pos_left _ hH).trans (Nat.le_mul_of_pos_right _ hsq)
  have hp : 2^sortExponent H ≤ 4*H := (TeamSorting.padding_lt_twice (show 0 < 2*H by omega)).le.trans_eq (by ring)
  have choose : (Nat.clog 2 r+1).choose 2 ≤ L^2 := by
    rw [Nat.choose_two_right,pow_two]
    exact (Nat.div_le_self ..).trans (Nat.mul_le_mul hd (by dsimp [L]; omega))
  have hs : comparisonSize (Nat.clog 2 r) (sortExponent H) (B+1) ≤ 320*V := by
    calc
      _ ≤ 40*(4*H)*(2*B)*L^2 := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ hp) (by omega)) choose
      _ = _ := by unfold V; ring
  have hf : frameWidth k B ≤ (k+3)*V := by
    change 1+(k+2)*B ≤ (k+3)*V
    rw [show (k+3)*V = (k+2)*V+V by ring]
    have hmul := Nat.mul_le_mul_left (k+2) hb
    omega
  have he : (2*k+686)*H*logWidth r n^(D+2) = (2*k+686)*V := by
    unfold V B L; rw [pow_add]; ring
  rw [he]
  unfold innerWidth
  rw [show (2*k+686)*V = 2*((k+3)*V)+680*V by ring]
  omega

/-- The actual interior-slot count is `o(n)`: one positive team-size exponent works for
every constant multiple of this precise layout, uniformly over all positive teams of
size at most `2^(n^ω)`. -/
theorem eventually_innerWidth (k D : ℕ) {ξ : ℝ} (hξ : 0 < ξ) (hξ' : ξ < 3) :
    ∃ ω : ℝ, 0 < ω ∧ ∀ c : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 0 < r →
      (r : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) ^ ω) →
      c*innerWidth r k (logWidth r n^D) (sortExponent (block ξ n)) (logWidth r n^D+1) ≤ n := by
  obtain ⟨ω,hω,hpoly⟩ := eventually_sorting_links (D+2) hξ
  refine ⟨ω,hω,fun c => ?_⟩
  filter_upwards [hpoly (c*(2*k+686)), eventually_ge_atTop 1] with n hcap hn
  intro r hr hrmax
  have hH : 0 < block ξ n := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using
      Real.one_le_rpow (by exact_mod_cast hn : 1 ≤ (n : ℝ)) (show 0 ≤ 1-ξ/3 by linarith)
  refine (Nat.mul_le_mul_left c (innerWidth_bound hr hn hH k D)).trans ?_
  simpa only [Nat.mul_assoc] using hcap r hr hrmax

end TeamContraction.Wires

end BorderVNP
end Computability
end OAI
