import OAI.Hierarchy.DescentSignedCableFields
import OAI.Hierarchy.DescentResetWalshScale
import OAI.Hierarchy.DescentOccurrenceAllowance

namespace OAI
/-! # Signed-token lookup keys at the original reset Walsh pitch -/
namespace Hierarchy.DescentResetSignedTokens
open DescentSharedCableNames DescentWalshPrecision DescentPackedWalsh DescentCompiler
noncomputable section

private theorem wordBits {x u : ℕ} (bound : x≤2^u) : Packed.bits x≤u+1 := by
  change Nat.clog 2 (x+1)≤u+1
  apply (Nat.clog_le_iff_le_pow (by decide)).2
  rw [pow_succ]
  have := Nat.two_pow_pos u
  omega

theorem signed_le_walsh {D cap u K : ℕ} (m f : ℕ) (degree : D≤K) (capacity : cap≤2^u) :
    DescentSignedCableCodec.width D cap≤2*bits m f K u := by
  have cd := wordBits (degree.trans (Nat.le_pow_clog (by decide : 1<2) K))
  have cc := wordBits capacity
  have rateK : 2*Nat.clog 2 K≤rate m K := Nat.le_max_right ..
  have rateTwo : 2≤rate m K :=
    (show 2≤2+(m+7)/8 by omega).trans (Nat.le_max_left ..)
  unfold DescentSignedCableCodec.width bits gainBits
  omega

/-- Two complete field widths still leave room for the polynomially many
alignment and fragment pages in the physical overlap subroutine. -/
theorem quarter_key {a b h m ℓ : ℕ} (pos : 0<b) (small : 8*b≤h)
    (width : a≤2*b) (pitch : ℓ≤laneBits m h b) : a*2^ℓ≤h/4 := by
  have divPos : 0<h/(8*b) := Nat.div_pos small (by omega)
  have up : 2^ℓ≤h/(8*b) :=
    (Nat.pow_le_pow_right (by decide) (pitch.trans (Nat.min_le_right ..))).trans
      (Nat.pow_log_le_self 2 divPos.ne')
  have used := (Nat.le_div_iff_mul_le (show 0<8*b by omega)).mp up
  have field := Nat.mul_le_mul_right (2^ℓ) width
  apply (Nat.le_div_iff_mul_le (by decide : 0<4)).2
  nlinarith only [used,field]

theorem signed_quarter {D cap u K h m f ℓ : ℕ} (degree : D≤K) (capacity : cap≤2^u)
    (short : 8*bits m f K u≤h) (pitch : ℓ≤laneBits m h (bits m f K u)) :
    DescentSignedCableCodec.width D cap*2^ℓ≤h/4 :=
  quarter_key (by unfold bits;omega) short (signed_le_walsh m f degree capacity) pitch

theorem signed_key {D cap u K h m f ℓ : ℕ} (degree : D≤K) (capacity : cap≤2^u)
    (short : 8*bits m f K u≤h) (pitch : ℓ≤laneBits m h (bits m f K u)) :
    DescentSignedCableCodec.width D cap*2^ℓ≤h/2 := by
  have := signed_quarter degree capacity short pitch
  omega

theorem signed_quarter_at (S : AtomSchedule) {D cap i h K m f ℓ : ℕ} (p : ℕ)
    (height : 0<S.height) (age : i≤S.length) (capacity : cap≤2^(8+S.capGain*i))
    (degree : D≤K) (short : 8*S.localWalshBits p m f K≤h)
    (pitch : ℓ≤laneBits m h (S.localWalshBits p m f K)) :
    DescentSignedCableCodec.width D cap*2^ℓ≤h/4 := by
  have room:=S.local_capacity height age capacity
  change cap≤(2^S.height)^S.localCapacityExponent at room
  rw [←pow_mul] at room
  have u : S.height*S.localCapacityExponent≤S.censusBits p := by
    unfold AtomSchedule.censusBits AtomSchedule.censusExponent
    have includeCap : S.localCapacityExponent≤S.priceExponent+S.localGrainExponent+S.localCapacityExponent := by omega
    exact (Nat.mul_le_mul_left S.height includeCap).trans (Nat.le_add_left ..)
  exact signed_quarter degree (room.trans (Nat.pow_le_pow_right (by decide) u)) short pitch

theorem signed_key_at (S : AtomSchedule) {D cap i h K m f ℓ : ℕ} (p : ℕ)
    (height : 0<S.height) (age : i≤S.length) (capacity : cap≤2^(8+S.capGain*i))
    (degree : D≤K) (short : 8*S.localWalshBits p m f K≤h)
    (pitch : ℓ≤laneBits m h (S.localWalshBits p m f K)) :
    DescentSignedCableCodec.width D cap*2^ℓ≤h/2 := by
  have := signed_quarter_at S p height age capacity degree short pitch
  omega

/-- The physical date can use every retained group lane of the selected Walsh word. -/
theorem eventually_signed_key {F : Type} [Field F] (G : DescentSixParty.PoweredGadget F)
    (t f g reset B K T : ℕ) :
    ∀ᶠ h : ℕ in Filter.atTop, ∀ copies tail i p D cap,
      let J:=Nat.log 2 h/(2*B)
      let S:=DescentSixParty.stageNumbers G t J f g reset copies tail
      let k:=groupBits t J S.hostGain S.capGain (DescentSixParty.cutRate t f g)
      let m:=S.groupWidth k tail i+k
      let b:=S.localWalshBits p m f K
      0<S.height → p≤h → tail≤T*(Nat.log 2 h+1)^2 → i≤S.length →
        D≤K → cap≤2^(8+S.capGain*i) →
        DescentSignedCableCodec.width D cap*2^(laneBits m h b-k)≤h/2 := by
  filter_upwards [DescentSixParty.eventually_actual_width G t f g reset B K T] with h room
  intro copies tail i p D cap
  dsimp only
  intro height small tailSize age degree capacity
  have word:=(room copies tail i p small tailSize age).1
  exact signed_key_at _ p height age capacity degree (word.trans (Nat.div_le_self ..))
    (Nat.sub_le ..)


end
end Hierarchy.DescentResetSignedTokens

end OAI
