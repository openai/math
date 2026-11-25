import OAI.Computability.BorderVNP.CubeRouteIncidentLoad
import OAI.Computability.BorderVNP.CubeISAHeaderSpellingCard
import OAI.Computability.BorderVNP.CubeScales
import OAI.Computability.BorderVNP.TransmissionHeaderFields
import OAI.Computability.BorderVNP.TransmissionReferencePacket

/-! # Capacity of the complete emitted common header

The native prefix consists of the branch bit, the reserved profile bits, the
upper-triangle cube declaration and the team subtotal fields. The actual
reader packet bounds its word width and the subtotal tail. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.RouteRecords

open Physical TeamScales TeamContraction TeamContraction.JointHeader TeamContraction.ProcessorSlots Filter

private theorem unordered_le_square (d : ℕ) : Fintype.card (Sym2 (Fin d)) ≤ d^2 := by
  simpa only [Fintype.card_prod,Fintype.card_fin,pow_two] using
    Fintype.card_le_of_surjective (Sym2.mk (α := Fin d)).uncurry Sym2.mk_surjective

/-- Count the actual binary positions of the compact declaration using the
word width admitted by its native decoder. -/
theorem declaration_length_le_word (a d cap w : ℕ) (fit : cap < 2^w) :
    DeclarationBits.length a d cap ≤ Nat.clog 2 (a+1) + d^2*(a+1)*w := by
  have digit := Nat.clog_le_of_le_pow (show cap+1 ≤ 2^w from fit)
  exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_right _ (unordered_le_square d)) digit) _

/-- The exact common header used by evaluation, with an optional fixed zero tail. -/
def emittedHeader {a d cap teams dim reserve : ℕ} (profile : Fin reserve → Bool) (raw : Broadcast a d cap)
    (tally : ℕ) (claims : Fin teams → Fin dim → ℕ) (extra : ℕ) : List Bool :=
  JointHeader.padded (evaluation (List.ofFn profile ++ DeclarationBits.spelling raw) tally claims) extra

/-- All term-dependent bit values have the same declared physical width. -/
theorem emittedHeader_length {a d cap teams dim reserve : ℕ} (profile : Fin reserve → Bool)
    (raw : Broadcast a d cap) (tally : ℕ) (claims : Fin teams → Fin dim → ℕ) (extra : ℕ) :
    (emittedHeader profile raw tally claims extra).length =
      reserve + DeclarationBits.length a d cap + (1+teams*dim*tally+extra) := by
  simp only [emittedHeader,JointHeader.padded,List.length_append,List.length_replicate,evaluation_length,List.length_ofFn,DeclarationBits.spelling_length]
  omega

/-- The actual reference packet's bit allocation and subtotal-prefix estimate
also bound the machine word width, because the packet carries all extended
frame words. -/
theorem header_room_of_packet {w pin teams dim tally r rest : ℕ} (packet : ReferencePacket w pin)
    (room : packet.bits.length+rest+1+teams*(dim*tally) ≤ r) :
    w ≤ r ∧ 1+teams*dim*tally ≤ r := by
  have hw : w ≤ packet.bits.length := by
    rw [ReferencePacket.bits_length,ReferencePacket.offset]
    exact (Nat.le_mul_of_pos_right w (by omega)).trans (Nat.le_add_right _ _)
  rw [← Nat.mul_assoc] at room
  omega

/-- At each permitted length, the combined emitted bits fit the actual real
header budget for the links; the profile can use its full stated reservation. -/
def HeaderFitsAt (α : ℝ) (a n : ℕ) : Prop :=
  ∀ {r reserve teams dim tally extra w cap : ℕ}, 1 ≤ r →
    ((reserve+extra:ℕ):ℝ) ≤ r*(n:ℝ)^(19/20:ℝ) → cap < 2^w → w ≤ r → 1+teams*dim*tally ≤ r →
    ∀ (profile : Fin reserve → Bool) (raw : Broadcast a (alphabet α n) cap) (claims : Fin teams → Fin dim → ℕ),
      ((emittedHeader profile raw tally claims extra).length:ℝ) ≤ r*(n:ℝ)^(24/25:ℝ)

/-- A single threshold accommodates every admitted profile, cube declaration
and subtotal choice. The alphabet is the one the native label scan uses. -/
theorem eventually_emitted_headers (a : ℕ) {α : ℝ} (pos : 0 < α) (small : 8*α ≤ 19/20) :
    ∀ᶠ n : ℕ in atTop, HeaderFitsAt α a n := by
  let C := Nat.clog 2 (a+1)+(a+1)+2
  filter_upwards [eventually_labelCount_power pos 1 2,
    TeamScales.eventually_rpow_gap (by norm_num : (19/20:ℝ) < 24/25) C,eventually_ge_atTop 1]
    with n labels gap hn
  intro r reserve teams dim tally extra w cap hr profileFit capFit word subtotal profile raw claims
  let M := (n:ℝ)^(19/20:ℝ)
  have nn : 1 ≤ (n:ℝ) := by exact_mod_cast hn
  have rr : 1 ≤ (r:ℝ) := by exact_mod_cast hr
  have Mone : 1 ≤ M := Real.one_le_rpow nn (by norm_num)
  have room : 1 ≤ (r:ℝ)*M := one_le_mul_of_one_le_of_one_le rr Mone
  have sq : ((alphabet α n:ℕ):ℝ)^2 ≤ M := by
    have h : ((alphabet α n:ℕ):ℝ)^2 ≤ (n:ℝ)^(8*α) := by
      simpa only [labelCount,pow_one,Nat.cast_one,Nat.cast_ofNat,mul_one,show 4*α*2=8*α by ring] using labels
    exact h.trans (Real.rpow_le_rpow_of_exponent_le nn small)
  have declared := declaration_length_le_word a (alphabet α n) cap w capFit
  have decl : (DeclarationBits.length a (alphabet α n) cap:ℝ) ≤
      (Nat.clog 2 (a+1):ℝ) + ((alphabet α n:ℕ):ℝ)^2*((a+1:ℕ):ℝ)*(w:ℝ) := by exact_mod_cast declared
  have cut : (DeclarationBits.length a (alphabet α n) cap:ℝ) ≤
      ((Nat.clog 2 (a+1):ℝ)+((a+1:ℕ):ℝ))*((r:ℝ)*M) := by
    have ww : (w:ℝ) ≤ r := by exact_mod_cast word
    calc
      _ ≤ _ := decl
      _ ≤ (Nat.clog 2 (a+1):ℝ)*((r:ℝ)*M) + M*((a+1:ℕ):ℝ)*r := by
        gcongr
        exact le_mul_of_one_le_right (by positivity) room
      _ = _ := by ring
  have tail : ((1+teams*dim*tally:ℕ):ℝ) ≤ (r:ℝ)*M :=
    (show ((1+teams*dim*tally:ℕ):ℝ) ≤ (r:ℝ) by exact_mod_cast subtotal).trans
      (le_mul_of_one_le_right (by positivity) Mone)
  rw [emittedHeader_length]
  push_cast only [Nat.cast_add] at profileFit cut tail ⊢
  have sum : (reserve:ℝ) + (DeclarationBits.length a (alphabet α n) cap:ℝ) +
      ((1:ℝ)+(teams*dim*tally:ℕ)+extra) ≤ (C:ℝ)*(r*M) := by
    dsimp only [C]; push_cast
    dsimp only [M] at *
    push_cast at *
    nlinarith only [profileFit,cut,tail]
  calc
    _ ≤ (C:ℝ)*(r*M) := by simpa only [Nat.cast_one,Nat.cast_mul] using sum
    _ = (r:ℝ)*(C*M) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left gap (by positivity)

end Cube.RouteRecords

end BorderVNP
end Computability
end OAI
