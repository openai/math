import OAI.Computability.BorderVNP.CellPrivateTranslateBudget
import OAI.Computability.BorderVNP.CellTypedDirectorySize

/-! # Combining source-scale bounds for the private translator -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet

/-- The first packet field contains the entire private wire count in binary. -/
theorem privateBits_le_packet (D : Directory) (k : ℕ) : k.bits.length ≤ (bits D k).length := by
  obtain ⟨tail,ht⟩ : ∃ tail : List Bool, bits D k = true :: (RationalHitting.StackLanguage.codeWord k.bits ++ tail) :=
    ⟨_,rfl⟩
  rw [ht,List.length_cons,List.length_append,RationalHitting.StackLanguage.codeWord_length]
  omega

/-- A bound for the packed burst also bounds the separately extracted sparse packet. -/
theorem packet_le_input (D : Directory) (k : ℕ) (external : List Bool) :
    (bits D k).length ≤ (input D k external).length := by
  simp only [input,List.length_append,RationalHitting.StackLanguage.codeWord_length]
  omega

open private scalar_records_le from OAI.Computability.BorderVNP.CellPacketInputSize

/-- A common load and numerical bit bound control both the public transport
packet and the internal typed directory on which the four private passes run. -/
theorem compiler_input_sizes (A B j : ℕ) : ∃ C : ℕ, ∀ (D : Directory) k M E U L,
    1 ≤ L → D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D k U →
    U.size+1 ≤ B*L^j →
    (bits D k).length ≤ C*(M+E+1)^2*L^j ∧
    (Typed.directory D).length ≤ C*(M+E+1)^2*L^j := by
  refine ⟨320*(8*A+4)*(B+3),fun D k M E U L hL hs hm hr hu => ?_⟩
  have hw := words_length_from_static D k hs hm
  have ht := typed_directory_length D k hr
  have hp := scalar_records_le (words D k) (L:=(max 3 U).size)
    (fun x hx => Nat.size_le_size (words_bounded D k hr x hx))
  have hwidth : (max 3 U).size ≤ U.size+2 := by
    by_cases h : 3 ≤ U
    · rw [max_eq_right h]; omega
    · rw [max_eq_left (by omega)]
      have h3 : (3:ℕ).size = 2 := by decide
      omega
  have h1 := Nat.one_le_pow j L hL
  have hfield : 2*(max 3 U).size+2 ≤ 2*(B+3)*L^j := by nlinarith
  have hwords : (words D k).length ≤ (8*A+4)*(M+E+1)^2 :=
    hw.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
  let core := (8*A+4)*(B+3)*(M+E+1)^2*L^j
  constructor
  · calc
      (bits D k).length ≤ _ := hp
      _ ≤ ((8*A+4)*(M+E+1)^2)*(2*(B+3)*L^j) := Nat.mul_le_mul hwords hfield
      _ = 2*core := by dsimp [core]; ring
      _ ≤ 320*core := Nat.mul_le_mul_right _ (by decide)
      _ = _ := by dsimp [core]; ring
  · calc
      (Typed.directory D).length ≤ _ := ht
      _ ≤ 300*((8*A+4)*(M+E+1)^2)*((B+3)*L^j) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hwords) (hu.trans (Nat.mul_le_mul_right _ (by omega)))
      _ = 300*core := by dsimp [core]; ring
      _ ≤ 320*core := Nat.mul_le_mul_right _ (by decide)
      _ = _ := by dsimp [core]; ring

end CellSparse.Packet

namespace CellPrivate

open CellSparse

/-- With one common expanded-size bound `W` and a separate field bit length
`L`, the four actual sparse passes and a quadratic-size packet give the stated
full translator clock. The exponent of `W` is preserved. -/
theorem translateClock_of_degree (d : ℕ) (hd : 4 ≤ d) : ∃ C : ℕ, ∀ (D : Directory) k B W L j,
    1 ≤ W → 1 ≤ L →
    Packet.Emit.passMeters D ≤ B*W^d*L^j →
    (Packet.bits D k).length ≤ B*W^2*L^j →
    translateClock D k ≤ C*(B+1)^2*W^d*L^(j+j+2) := by
  obtain ⟨C,hC⟩ := translateClock_le_passes
  refine ⟨3*C,fun D k B W L j hW hL hpasses hpacket => ?_⟩
  let T := (B+1)^2*W^d*L^(j+j+2)
  have hB : B ≤ (B+1)^2 := by nlinarith
  have hp : Packet.Emit.passMeters D ≤ T := hpasses.trans (by
    dsimp [T]
    gcongr; omega)
  have hW2 : 1 ≤ W^2 := Nat.one_le_pow _ _ hW
  have hLj := Nat.one_le_pow j L hL
  have hl : (Packet.bits D k).length+1 ≤ (B+1)*W^2*L^j := by
    have := Nat.mul_le_mul hW2 hLj
    nlinarith
  have hlen : ((Packet.bits D k).length+1)^2 ≤ T := calc
    _ ≤ ((B+1)*W^2*L^j)^2 := Nat.pow_le_pow_left hl 2
    _ = (B+1)^2*W^4*L^(j+j) := by rw [pow_add]; ring
    _ ≤ T := by
      exact Nat.mul_le_mul (Nat.mul_le_mul_left ((B+1)^2)
        (Nat.pow_le_pow_right hW hd)) (Nat.pow_le_pow_right hL (show j+j ≤ j+j+2 by omega))
  have hpriv := Packet.privateBits_le_packet D k
  have hlin : (Packet.bits D k).length+1 ≤ ((Packet.bits D k).length+1)^2 := by nlinarith
  have hsum : Packet.Emit.passMeters D+((Packet.bits D k).length+1)^2+k.bits.length+1 ≤ 3*T := by omega
  calc
    translateClock D k ≤ _ := hC D k
    _ ≤ C*(3*T) := Nat.mul_le_mul_left C hsum
    _ = _ := by dsimp [T]; ring

/-- The exponent accepted by the complete private multitape clock. -/
theorem translateClock_of_passBounds : ∃ C : ℕ, ∀ (D : Directory) k B W L j,
    1 ≤ W → 1 ≤ L →
    Packet.Emit.passMeters D ≤ B*W^96*L^j →
    (Packet.bits D k).length ≤ B*W^2*L^j →
    translateClock D k ≤ C*(B+1)^2*W^96*L^(j+j+2) := translateClock_of_degree 96 (by decide)

end CellPrivate

end BorderVNP
end Computability
end OAI
