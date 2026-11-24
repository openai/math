import OAI.Computability.VPVNP.RAMTapeInputParametersWidth

/-!
# Cost of computing the incident width

The exact instruction count includes every copy, multiplication and scratch clear. The
largest term is proportional to the payload `(d+10)^4 * H * (d+1).choose 2`, which gives
a degree-seven bound in the combined address and bucket sizes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.InputWidth

open Tally

/-- Total instruction count of the four stages, grouped by the intermediate register values. -/
theorem work_eq (d H : ℕ) :
    program.work (initial d H) =
      548 + 14*d + 15*(d+10) + 20*(d+10)^2 + 93*(d+10)^4 + 5*d.choose 2 +
        7*(H*(d+1).choose 2) + 6*H + 207*((d+10)^4*(H*(d+1).choose 2)) + 2*(d+1).choose 2 := by
  rw [work_program]
  simp (config := { decide := true }) [wordProgram, payloadProgram, countProgram, cleanup,
    words, initial, payloads, counted]
  ring

private theorem choose_two_le_square (n : ℕ) : n.choose 2 ≤ n^2 := by
  rw [Nat.choose_two_right, pow_two]
  exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le ..))

theorem work_le_seventh (d H : ℕ) : program.work (initial d H) ≤ 917*(d+H+11)^7 := by
  let B := d + H + 11
  have hB : 0 < B := by dsimp [B]; omega
  have mono {i j : ℕ} (h : i ≤ j) : B^i ≤ B^j := Nat.pow_le_pow_right hB h
  have ht : d + 10 ≤ B := by dsimp [B]; omega
  have hh : H ≤ B := by dsimp [B]; omega
  have hs : (d+10)^2 ≤ B^2 := Nat.pow_le_pow_left ht _
  have hw : (d+10)^4 ≤ B^4 := Nat.pow_le_pow_left ht _
  have hL : (d+1).choose 2 ≤ B^2 :=
    (choose_two_le_square _).trans (Nat.pow_le_pow_left (by omega) _)
  have hJ : d.choose 2 ≤ B^2 :=
    (choose_two_le_square _).trans (Nat.pow_le_pow_left (by omega) _)
  have hblocks : H * (d+1).choose 2 ≤ B^3 := by
    calc
      _ ≤ B * B^2 := Nat.mul_le_mul hh hL
      _ = B^3 := by ring
  have hpayload : (d+10)^4 * (H*(d+1).choose 2) ≤ B^7 := by
    calc
      _ ≤ B^4 * B^3 := Nat.mul_le_mul hw hblocks
      _ = B^7 := by ring
  have h1 : 1 ≤ B^7 := (by simpa using mono (by decide : 0 ≤ 7))
  have h2 : B ≤ B^7 := by simpa using mono (by decide : 1 ≤ 7)
  have h3 := mono (by decide : 2 ≤ 7)
  have h4 := mono (by decide : 3 ≤ 7)
  have h5 := mono (by decide : 4 ≤ 7)
  rw [work_eq]
  change _ ≤ 917 * B^7
  omega

/-- Bound used by the fixed live-validator clock. -/
theorem work_le (d H : ℕ) : program.work (initial d H) ≤ 10^12 * (d+H+11)^12 :=
  (work_le_seventh d H).trans (Nat.mul_le_mul (by decide)
    (Nat.pow_le_pow_right (by omega) (by decide)))

end RAMTape.InputWidth

end VPVNP
end Computability
end OAI
