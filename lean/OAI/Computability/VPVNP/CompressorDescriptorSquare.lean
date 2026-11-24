import OAI.Computability.VPVNP.CompressorDescriptorSpace
import OAI.Computability.VPVNP.PairWorkspace

/-!
# Relative square arena for the complete descriptor and evaluation workspaces

The directory reserves old-site capacity at every level, independently of
the selected placements. Its level count contributes another logarithm.
This arena, the selected depth-first rows and the final wire bits fit
together inside the square of the live processor count, relative to any
starting address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.DescriptorSpace

open Compression CursorNetwork CursorBounds Filter

private theorem cursor_positions_le {b n : ℕ} (hn : 2 ≤ n) :
    initialPositions b n ≤ (2*(b+2))*processorCount b n*n*(n.log2+1)^2 := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hpow : (n : ℝ) ^ (3/4 : ℝ) ≤ n := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn₁ (by norm_num : (3/4 : ℝ) ≤ 1)
  have h := (initialPositions_bound b n hn).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (by positivity)) (sq_nonneg _))
  exact_mod_cast h

private theorem cursor_level_count_le (F : Shape) {b n : ℕ} (hn : 2 ≤ n) (steps start : ℕ)
    {θ : ℝ} (hθ : θ ≤ 1) : (cursorLayout F b steps θ start n).levels ≤ (steps+2)*n := by
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hT : blockCount θ n ≤ Nat.clog 2 n := by
    rw [blockCount, ← Real.natCeil_logb_natCast 2 n]
    exact (Nat.floor_le_floor (mul_le_of_le_one_left (Real.logb_nonneg (by norm_num) hn₁) hθ)).trans
      (Nat.floor_le_ceil _)
  have ht := hT.trans (Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le)
  change 1+(steps+1)*blockCount θ n ≤ (steps+2)*n
  exact (Nat.add_le_add (show 1 ≤ n by omega) (Nat.mul_le_mul_left _ ht)).trans_eq (by ring)

/-- The length threshold precedes every memory start, coordinate split,
coefficient specialization and compressor term. The final summand accommodates
fixed-stride traversal rows, final bits, and processor-local work cells. -/
theorem eventually_selected_square {k : Type*} [_root_.Field k] {S : BlockSchedule k} (F : Shape)
    (B : S.Templates) (u : PairExponents B.growthConstant) (b : ℕ) (hb : max S.laneBits 5 ≤ b)
    (K : ℕ) : ∀ᶠ n : ℕ in atTop,
      ∀ (start : ℕ) {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
        (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
        (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
        let X := pairInput S labels hD
        let T := blockCount (u.θ : ℝ) n
        let E := B.execute f hf T hT X
        let L := cursorLayout F b S.steps (u.θ : ℝ) start n
        ∀ z : E.Choices, let Y := E.finalState z
          endAddress L + K * (X.positions + processorCount b n +
            Y.positions * B.growthConstant ^ T + Y.totalWidth) + 1 < start + (processorCount b n)^2 := by
  let C := F.fixedWords + F.levelFixed + F.siteWords
  let p := 2*(b+2)
  filter_upwards [eventually_pairWorkspace_lt_square b ((le_max_right _ _).trans hb)
    (2*C*p*(S.steps+2)), eventually_pairArenaFitBoth B u b hb (2*K+2), eventually_ge_atTop 2]
      with n hs he hn
  intro start base lanes labels hD hT A _ f hf X T E L z Y
  have hp := pairInput_positions S labels hD
  change X.positions = initialPositions b n at hp
  have hθ : (u.θ : ℝ) ≤ 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr u.theta_lt
    norm_num at this; linarith
  have hL := cursor_level_count_le F (b := b) hn S.steps start hθ
  have hpos : 0 < L.positions := X.positions_pos.trans_le hp.le
  have hlev : 0 < L.levels := by dsimp [L,cursorLayout]; omega
  have hd := endAddress_le L hpos hlev
  change endAddress L ≤ start + C*initialPositions b n * L.levels at hd
  let Q := C * initialPositions b n * L.levels
  have hmul : 2*Q ≤ 2*C*p*(S.steps+2)*processorCount b n*n^2*(n.log2+1)^2 := by
    calc
      _ = 2*C*initialPositions b n * L.levels := by dsimp only [Q]; ring
      _ ≤ 2*C*(p*processorCount b n*n*(n.log2+1)^2) * ((S.steps+2)*n) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (cursor_positions_le hn)) hL
      _ = _ := by ring
  let Z := X.positions + processorCount b n + Y.positions*B.growthConstant^T + Y.totalWidth
  have he' := (he labels hD hT A f hf z).trans_le (min_le_right _ _)
  change (2*K+2)*Z+1 < (processorCount b n)^2 at he'
  have hZ : 0 < Z := Nat.lt_add_right _ (Nat.lt_add_right _ (Nat.lt_add_right _ X.positions_pos))
  change endAddress L ≤ start + Q at hd
  change endAddress L + K*Z + 1 < start + (processorCount b n)^2
  rw [Nat.add_mul,Nat.mul_assoc] at he'
  omega

end CompressorRecords.DescriptorSpace

end VPVNP
end Computability
end OAI
