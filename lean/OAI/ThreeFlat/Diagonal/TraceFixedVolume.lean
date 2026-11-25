import OAI.ThreeFlat.Diagonal.TraceDiagonalVolume
import OAI.ThreeFlat.Diagonal.TraceVolumePins
import OAI.ThreeFlat.RAM.FixedTraceProgram

namespace OAI
/-! # Native fixed-table generation of the tick template within its full volume -/

namespace ThreeFlat.Diagonal.TraceVolume

open Computability.VPVNP BurstRAM TraceStaticRow

/-- Use the actual 430-bind native ROM with the full four replaceable
strings and all advice bits. The sole extra input length is a fixed
polynomial amount of public addressing and scheduling data. -/
theorem fixed_tick_total {F : Type*} [CommRing F] [Fintype F] {u e params : ℕ}
    (hu : 10^26*17^14 ≤ u) (hq : Fintype.card F ≤ u) (he : e ≤ u) (hparams : params ≤ u^e)
    (base : ℕ) (st : Word (16*u^10)) :
    let W := 16*u^10
    let d := depth u
    let f := 2^d
    let S := 4*2^(u^10-u^4)+2^(u^3)+params
    let ht := RAM.CapacityPadding.textFits_scale (show 128 ≤ u by omega)
    let hF : Fintype.card F ≤ 2^W := hq.trans ht.registers
    let hw : 3 ≤ W+1 := by have := Nat.le_self_pow (by decide : 10 ≠ 0) u; dsimp [W]; omega
    let hp : u ≤ 2^(W+1) := ht.registers.trans (Nat.pow_le_pow_right (by decide) (by omega))
    let table := gateTable hF hw hp base f st u u d
    work f S (TraceUniformRow.SharedCount W u u u d f) table.internal table.cells
      (Fintype.card (Port W u u u d)) W (RAM.FixedTraceProgram.program W).binds ≤ 2^(u^10) := by
  intro W d f S ht hF hw hp table
  have hcm : cm ≤ u := by dsimp [cm]; omega
  have hs : S ≤ f := (pins_at_scale hcm he hparams).1
  change S ≤ 2^(depth u) at hs
  have grid : S+f ≤ 2^(1+depth u) := by
    change S+2^(depth u) ≤ _
    rw [pow_add,pow_one]
    omega
  exact actual_work_le hu hq hF hw hp base st grid _ ((RAM.FixedTraceProgram.size W).trans
    (by unfold bindAllowance; omega))

end ThreeFlat.Diagonal.TraceVolume

end OAI
