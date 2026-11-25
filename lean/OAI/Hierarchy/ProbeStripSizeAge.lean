import OAI.Hierarchy.ProbeStageAddress

namespace OAI
/-! # Fitting a fixed finite catalogue and a height-dependent number of copies -/

namespace Hierarchy.ProtocolRAM.CatalystArchive
open ProbeStage.Native

/-- All scalar fields of the stock-commit decoder fit the same physical word. -/
structure ScalarRoom (ports letters copies entries maximum bits : ℕ) : Prop where
  portFit : ports≤2^bits
  termFit : letters≤2^bits
  copyFit : copies<2^bits
  sumFit : letters*copies<2^bits
  codeFit : 1+entries≤2^bits
  fieldFit : maximum<2^bits
  wide : copies*maximum<2^bits

/-- A fixed linear number of physical rows fits the word used by that height. -/
theorem linear_count (z d banks C : ℕ) (late : C≤z) : 2^z*C<2^(wordBits z d banks) := by
  have small : C<2^z := late.trans_lt Nat.lt_two_pow_self
  have q := Nat.mul_lt_mul_of_pos_left small (Nat.two_pow_pos z)
  rw [←pow_add] at q
  exact q.trans_le (Nat.pow_le_pow_right (by decide) (by rw [wordBits_linear]; omega))

/-- The address format supplies more than twice the row-height exponent. Each
catalogue bound fits one half and each copied multiplicity fits the other. -/
theorem ScalarRoom.at_height (z degree banks ports letters copies entries maximum : ℕ)
    (fixed : ports+letters+(1+entries)+maximum≤z) (mass : copies≤2^z) :
    ScalarRoom ports letters copies entries maximum (wordBits z degree banks) := by
  let b := wordBits z degree banks
  have hz : 2*z<b := by dsimp [b]; rw [wordBits_linear]; omega
  have square : (2^z:ℕ)*2^z < 2^b := by
    rw [←pow_add,show z+z=2*z by omega]
    exact Nat.pow_lt_pow_right (by decide) hz
  have half : (2^z:ℕ)<2^b := Nat.pow_lt_pow_right (by decide) (by omega)
  have cap : z≤(2:ℕ)^z := Nat.lt_two_pow_self.le
  have p : ports≤2^z := by omega
  have q : letters≤2^z := by omega
  have e : 1+entries≤2^z := by omega
  have m : maximum≤2^z := by omega
  exact ⟨p.trans half.le,q.trans half.le,mass.trans_lt half,(Nat.mul_le_mul q mass).trans_lt square,
    e.trans half.le,m.trans_lt half,(Nat.mul_le_mul mass m).trans_lt square⟩

end Hierarchy.ProtocolRAM.CatalystArchive

end OAI
