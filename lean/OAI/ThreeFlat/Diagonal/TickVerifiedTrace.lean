import OAI.ThreeFlat.Diagonal.TickInstalledTrace
import OAI.ThreeFlat.RAM.TickFuel

namespace OAI
/-! # The installed diagonal trace at the actual common native time bound -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMMemory ApproximateImage RAM.TickMountedPins RAM.TickFuel
variable {F : Type*} [Field F] [Fintype F] {u pc rg words nt ns np a depth budget fuel : ℕ}

/-- Specializing the real mounted native return proof at the chosen padded
fuel identifies the tensor of the single installed physical text. -/
theorem eval_mounted_returns (hu : 128 ≤ u) (hF : Fintype.card F ≤ 2^(16*u^10))
    (M : Machine (16*u^10) pc rg words) (hp : pc ≤ u) (hr : rg ≤ u) (hk : words ≤ u)
    (tail : Fin (2^(u^3)) → Bool) (team step : ℕ) (par : Fin np → Bool)
    (oa na oc nc : Fin a → Bool) (st : Word (16*u^10))
    (hs : 2+pinCount (2^(u^3)) nt ns np a ≤ 2^(16*u^10))
    (hf : fuel ≤ 2^(16*u^10+1))
    (grid : 2+pinCount (2^(u^3)) nt ns np a+fuel ≤ 2^(1+depth))
    (room : budget ≤ fuel) (expected : F) :
    let D := RAM.installProgram (RAM.CapacityPadding.pad M hp hr hk) tail
    let pin := fields D (digits team nt) (digits step ns) par oa na oc nc
    let hw : 3 ≤ 16*u^10+1 := by have := Nat.le_self_pow (by decide : 10 ≠ 0) u; omega
    let text := RAM.CapacityPadding.textFits_scale hu
    let hpc : u ≤ 2^(16*u^10+1) := text.registers.trans (Nat.pow_le_pow_right (by decide) (by omega))
    (∀ cfg : Config (16*u^10) pc rg, cfg.pc=M.entry →
      Returns (RAM.FieldCode.ofCardLe hF) M.program budget cfg (memory pin) expected) →
    (network hF hw hpc 2 st hs hf u u depth).eval (advicePins 2 D (raw pin)) = expected := by
  intro D pin hw text hpc run
  rw [eval_mounted_tick hu hF M hp hr hk tail team step par oa na oc nc st hs hf grid]
  exact by
    change RAM.mass _ M.program fuel _ _ = _
    have h := (run (M.program.start st) rfl).later room 0
    simpa only [Nat.zero_add] using h

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
