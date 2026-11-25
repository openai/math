import OAI.ThreeFlat.Diagonal.TraceStaticRecordData
import OAI.ThreeFlat.Diagonal.TraceRecordWord

namespace OAI
/-! # Word bounds for the complete static trace control table -/

namespace ThreeFlat.Diagonal.TraceAddressRecord

open Computability.VPVNP

private theorem interval_fits {a b l h W d : ℕ} (v : Fin (2^d))
    (room : 2*2^d+2 < 2^W) (ha : a ≤ 2) (hb : b ≤ 1)
    (hl : l ≤ 2*2^d+2) (hh : h ≤ 2*2^d+2) : (interval a b l h).Fits W v.val := by
  have hv := v.isLt
  have prod := Nat.mul_le_mul ha hv.le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · change 0 < 2^W; omega
  · change a*v.val+b < 2^W; omega
  · change l < 2^W; omega
  · change h < 2^W; omega
  · change 1+0*(v.val ^^^ 0) < 2^W; rw [Nat.zero_mul, Nat.add_zero]; omega
  · change 0 < 2^W; omega
  · change 0 < 2^W; omega

private theorem digit_fits {a b s j W d : ℕ} (v : Fin (2^d))
    (room : 2*2^d+2 < 2^W) (ha : a ≤ 2) (hb : b ≤ 1)
    (hs : s ≤ 2*2^d+2) (hj : j < 2^W) : (digit a b s j).Fits W v.val := by
  have hv := v.isLt
  have prod := Nat.mul_le_mul ha hv.le
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · change 0 < 2^W; omega
  · change 0*v.val+0 < 2^W; rw [Nat.zero_mul, Nat.add_zero]; omega
  · change 0 < 2^W; omega
  · change 1 < 2^W; omega
  · change b+a*(v.val ^^^ 0) < 2^W
    rw [Nat.xor_zero]
    omega
  · change s < 2^W; omega
  · exact hj

/-- Every static control record fits whenever the full physical port table fits. -/
theorem staticPort_fits_of_capacity {W d p r k base S f : ℕ} (hw : 3 ≤ W+1)
    (time : S+f ≤ 2^(1+d)) (text : base+(1+6*p+k)*W ≤ S)
    (cap : 40*(2^d * portRowWords W p r k d) < 2^W)
    (v : Fin (2^d)) (z : StaticPortIndex W p r k d) :
    (staticPort hw base S f z).Fits W v.val := by
  let D := 2^d
  let B := portRowWords W p r k d
  have bb : W+2 ≤ B := by dsimp [B,portRowWords]; omega
  have dp : 0 < D := Nat.two_pow_pos _
  have bpos : 0 < B := by omega
  have hb : B ≤ D*B := Nat.le_mul_of_pos_left _ dp
  have hD : D ≤ D*B := Nat.le_mul_of_pos_right _ bpos
  change 40*(D*B) < 2^W at cap
  have room : 2*2^d+2 < 2^W := by change 2*D+2 < _; omega
  have width : W+2 < 2^W := by omega
  have ts : S+f ≤ 2*D := by simpa [D,pow_add] using time
  rcases z with z | ((a | a) | a)
  · exact portRecord_fits_of_capacity (by omega) time cap v z
  · rcases a with ⟨s,b | ⟨b,j⟩⟩ <;> cases b
    · apply interval_fits v room <;> have := s.isLt <;> omega
    · apply interval_fits v room <;> first | (split <;> omega) | (have := s.isLt; omega)
    · apply digit_fits v room <;> have := s.isLt <;> have := j.isLt <;> omega
    · apply digit_fits v room <;> have := s.isLt <;> have := j.isLt <;> omega
  · rcases a with ⟨j,s⟩ | a
    · have depth : d < 2^d := Nat.lt_two_pow_self
      apply digit_fits v room <;> have := j.isLt <;> have := s.isLt <;> omega
    · apply interval_fits v room <;> omega
  · rcases a with s | (s | (b | j))
    · apply interval_fits v room <;> have := s.isLt <;> omega
    · apply interval_fits v room <;> first | (split <;> omega) | (have := s.isLt; omega)
    · cases b <;> apply interval_fits v room <;> omega
    · have hj : (finProdFinEquiv j).val < (1+6*p+k)*W := (finProdFinEquiv j).isLt
      have anchor : (base+(finProdFinEquiv j).val)/2 ≤ S := (Nat.div_le_self _ _).trans
        ((Nat.add_le_add_left hj.le base).trans text)
      apply interval_fits v room <;> omega

/-- All comparisons, XOR masks, bit positions and address numerators of
the static port table fit at the same public polynomial threshold. The
program-text bound is the advice-layout condition for its anchor slots. -/
theorem staticPort_fits_of_public_bounds {u d p r k base S f c e : ℕ} (hw : 3 ≤ 16*u^10+1)
    (time : S+f ≤ 2^(1+d)) (text : base+(1+6*p+k)*(16*u^10) ≤ S)
    (hu : RAM.traceWordThreshold (40*(64*(c+1))) (e+3) ≤ u)
    (hd : d ≤ 15*u^10) (hp : p ≤ c*(16*u^10+1)^e)
    (hr : r ≤ c*(16*u^10+1)^e) (hk : k ≤ c*(16*u^10+1)^e)
    (v : Fin (2^d)) (z : StaticPortIndex (16*u^10) p r k d) :
    (staticPort hw base S f z).Fits (16*u^10) v.val := by
  apply staticPort_fits_of_capacity hw time text _ v z
  have hrow := portRowWords_polynomial (show d ≤ 16*u^10 by omega) hp hr hk
  exact RAM.trace_word_address_lt (control := 0) hu hd hrow (Nat.zero_le _) (by simp)

end ThreeFlat.Diagonal.TraceAddressRecord

end OAI
