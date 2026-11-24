import OAI.Computability.VPVNP.RAMTapeInputParametersWidthCost

/-!
# Preparing the word width and sorting block length after parsing

The validator retains the public address count `d` and bucket size `H`. The
following fixed pass gives the successor reader its word width and the sorter
its block length. The input and the two output counts occupy distinct stacks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.InputWidth

open Tally

private def blockProgram : Program Port :=
  let add := Program.copy Port.bucket Port.blocks Port.tmp (by decide) (by decide) (by decide)
  add.seq <| add.seq <| add.seq <| add.seq <| (Program.clear .base).seq (Program.clear .square)

/-- Write the word width and the number of five-word sorting slots. -/
def siteSizeProgram : Program Port := wordProgram.seq blockProgram

/-- Prepared site-size tallies with word width `(d + 10)^4` and sorting block length `4*H`. -/
def siteSizes (d H : ℕ) : State Port
  | .word => (d+10)^4
  | .blocks => 4*H
  | p => initial d H p

theorem siteSizes_runs (d H : ℕ) : siteSizeProgram.code.Runs (siteSizeProgram.work (initial d H))
    (encode (initial d H)) (encode (siteSizes d H)) := by
  have he : siteSizeProgram.eval (initial d H) = siteSizes d H := by
    funext p
    cases p <;> simp (config := { decide := true }) [siteSizeProgram, blockProgram, wordProgram,
      initial, siteSizes] <;> ring
  apply he ▸ siteSizeProgram.spec (initial d H)
  simp (config := { decide := true }) [siteSizeProgram, blockProgram, wordProgram, initial]

theorem siteSizes_work_le (d H : ℕ) :
    siteSizeProgram.work (initial d H) ≤ 1000*(d+H+11)^7 := by
  have h₁ : wordProgram.work (initial d H) ≤ 917*(d+H+11)^7 := by
    exact (show _ ≤ program.work (initial d H) by rw [work_program]; omega).trans (work_le_seventh d H)
  have he : siteSizeProgram.work (initial d H) =
      wordProgram.work (initial d H) + (20*H + 10 + 2*(d+10) + 2*(d+10)^2) := by
    simp only [siteSizeProgram, Program.seq_work, Nat.add_left_cancel_iff]
    simp (config := { decide := true }) [blockProgram, wordProgram, initial]
    ring
  rw [he]
  let B := d+H+11
  have hpos : 0 < B := by dsimp [B]; omega
  have hsmall : d+10 ≤ B := by dsimp [B]; omega
  have hH : H ≤ B := by dsimp [B]; omega
  have hB : B ≤ B^7 := by simpa using Nat.pow_le_pow_right hpos (by decide : 1 ≤ 7)
  have hs : (d+10)^2 ≤ B^7 :=
    (Nat.pow_le_pow_left hsmall _).trans (Nat.pow_le_pow_right hpos (by decide))
  change wordProgram.work (initial d H) ≤ 917*B^7 at h₁
  change _ ≤ 1000*B^7
  omega

end RAMTape.InputWidth

end VPVNP
end Computability
end OAI
