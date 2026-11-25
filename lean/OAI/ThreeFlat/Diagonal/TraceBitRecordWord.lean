import OAI.ThreeFlat.Diagonal.TraceStaticRecordWord
import OAI.ThreeFlat.Diagonal.TraceBitRecordData

namespace OAI
/-! # Word safety after packing each input word into one low bit -/

namespace ThreeFlat.Diagonal.TraceAddressRecord

/-- Repacking the input leaves all masks and numerators intact. The
enlarged subtraction constant supplies the same native fit conditions. -/
theorem fits_changeBase {R : Record} {W v drop : ℕ} (fit : R.Fits W v)
    (hsub : R.sub+drop < 2^W) : (changeBase R drop).Fits W v :=
  ⟨fit.row, fit.mask, fit.test, fit.lo, fit.hi, fit.numerator, hsub, fit.bit⟩

/-- Capacity of all low-bit records at an arbitrary word width. -/
theorem staticBitPort_fits_of_capacity {W d p r k base S f : ℕ} (hw : 3 ≤ W+1)
    (time : S+f ≤ 2^(1+d)) (text : base+(1+6*p+k)*W ≤ S)
    (cap : 40*(2^d * portRowWords W p r k d) < 2^W)
    (v : Fin (2^d)) (z : StaticPortIndex W p r k d) :
    (staticBitPort hw base S f z).Fits W v.val := by
  let D := 2^d
  let B := portRowWords W p r k d
  have w2 : 2 ≤ W+1 := by omega
  have dp : 0 < D := Nat.two_pow_pos _
  have bpos : 0 < B := by dsimp [B,portRowWords]; omega
  have ld : D ≤ D*B := Nat.le_mul_of_pos_right _ bpos
  change 40*(D*B) < 2^W at cap
  have moved (a : TraceUniformRow.Port W p r k d) :
      (changeBase (portRecord w2 S f a) (S*W-S)).Fits W v.val :=
    fits_changeBase (portRecord_fits_of_capacity w2 time cap v a)
      (portRecord_add_sub_lt_of_capacity w2 time cap a)
  rcases z with (a | a) | ctl
  · rcases a with cpu | ⟨s,j⟩ | sorting | boundary
    · exact moved (.inl (.inl cpu))
    · change (bitHeader s.val j.val S).Fits W v.val
      have room : 2*2^d+4 < 2^W := by change 2*D+4 < _; omega
      have ts : S+f ≤ 2*2^d := by simpa [pow_add] using time
      have hs := s.isLt
      have hv := v.isLt
      by_cases hj : j.val = 0 <;> constructor <;>
        (try simp only [bitHeader, hj, ite_true, ite_false, Record.test, Record.numerator,
          Nat.xor_zero, Nat.zero_mul, Nat.add_zero, Option.getD_none]) <;> omega
    · exact moved (.inl (.inr (.inr (.inl sorting))))
    · exact moved (.inl (.inr (.inr (.inr boundary))))
  · exact moved (.inr a)
  · exact staticPort_fits_of_capacity (r:=r) hw time text cap v (.inr ctl)

/-- Every compressed static trace address can be evaluated in the fixed
word, including the special low-bit header address and relocated hidden
cells. The threshold depends only on the local public polynomial. -/
theorem staticBitPort_fits_of_public_bounds {u d p r k base S f c e : ℕ} (hw : 3 ≤ 16*u^10+1)
    (time : S+f ≤ 2^(1+d)) (text : base+(1+6*p+k)*(16*u^10) ≤ S)
    (hu : RAM.traceWordThreshold (40*(64*(c+1))) (e+3) ≤ u)
    (hd : d ≤ 15*u^10) (hp : p ≤ c*(16*u^10+1)^e)
    (hr : r ≤ c*(16*u^10+1)^e) (hk : k ≤ c*(16*u^10+1)^e)
    (v : Fin (2^d)) (z : StaticPortIndex (16*u^10) p r k d) :
    (staticBitPort hw base S f z).Fits (16*u^10) v.val := by
  apply staticBitPort_fits_of_capacity hw time text _ v z
  have hrow := portRowWords_polynomial (show d ≤ 16*u^10 by omega) hp hr hk
  exact RAM.trace_word_address_lt (control := 0) hu hd hrow (Nat.zero_le _) (by simp)

end ThreeFlat.Diagonal.TraceAddressRecord

end OAI
