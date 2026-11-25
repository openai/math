import OAI.ThreeFlat.Diagonal.TickVerifiedTrace
import OAI.ThreeFlat.Diagonal.TraceVolumePins

namespace OAI
/-! # The fixed mounted evaluator on the dyadic trace grid -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMMemory ApproximateImage RAM.TickMountedPins RAM.TickFuel
variable {F : Type*} [Field F] [Fintype F] {u e pc rg words nt ns np budget : ℕ}

theorem eval_age_returns (age : TraceVolume.cm ≤ u) (hF : Fintype.card F ≤ 2^(16*u^10))
    (M : Machine (16*u^10) pc rg words) (hp : pc ≤ u) (hr : rg ≤ u) (hk : words ≤ u)
    (tail : Fin (2^(u^3)) → Bool) (team step : ℕ) (par : Fin np → Bool)
    (oa na oc nc : Fin (2^(u^10-u^4)) → Bool) (st : Word (16*u^10))
    (he : e ≤ u) (params : 2+nt+ns+np ≤ u^e) (bound : budget ≤ TraceVolume.cap u / 2)
    (z : F) :
    let a := 2^(u^10-u^4)
    let q := 2^(u^3)
    let d := TraceVolume.depth u
    let D := RAM.installProgram (RAM.CapacityPadding.pad M hp hr hk) tail
    let pin := fields D (digits team nt) (digits step ns) par oa na oc nc
    let hu : 128 ≤ u := by dsimp [TraceVolume.cm] at age; omega
    let hw : 3 ≤ 16*u^10+1 := by have := Nat.le_self_pow (by decide : 10 ≠ 0) u; omega
    let text := RAM.CapacityPadding.textFits_scale hu
    let hpc : u ≤ 2^(16*u^10+1) := text.registers.trans (Nat.pow_le_pow_right (by decide) (by omega))
    let hs : 2+pinCount q nt ns np a ≤ 2^(16*u^10) := by
      have g := (TraceVolume.tick_grid age he params).1
      dsimp [q,a,pinCount]
      omega
    let hf : 2^d ≤ 2^(16*u^10+1) := (TraceVolume.tick_grid age he params).2.1
    (∀ cfg : Config (16*u^10) pc rg, cfg.pc=M.entry →
      Returns (RAM.FieldCode.ofCardLe hF) M.program budget cfg (memory pin) z) →
    let _grid : 2+pinCount q nt ns np a+2^d ≤ 2^(1+d) := by
      have g := (TraceVolume.tick_grid age he params).2.2
      dsimp [q,a,d,pinCount]
      omega
    (network hF hw hpc 2 st hs hf u u d).eval (advicePins 2 D (raw pin)) = z := by
  intro a q d D pin hu hw text hpc hs hf run grid
  have dyadic : budget ≤ 2^d := by have h := (TraceVolume.sites_cap age).2; dsimp [d]; omega
  exact eval_mounted_returns hu hF M hp hr hk tail team step par oa na oc nc st hs hf grid dyadic z run

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
