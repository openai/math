import OAI.ThreeFlat.Diagonal.TraceDiagonal
import OAI.ThreeFlat.RAM.TickMountedPins

namespace OAI
/-! # Running the bounded native tick through the common self-advice trace -/

namespace ThreeFlat.Diagonal.TraceBitHeader

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMMemory ApproximateImage
open RAM.TickMountedPins

variable {F : Type*} [Fintype F] [CommRing F]
variable {u pc rg words nt ns np a depth fuel : ℕ}

/-- The fixed trace's bit inputs are exactly the mounted physical tick.
A common-capacity program is installed into the same advice prefix visible to
the computation. Slots use the remaining advice bits and the two low literals
directly from the original tape. -/
theorem eval_mounted_tick (hu : 128 ≤ u) (hF : Fintype.card F ≤ 2^(16*u^10))
    (M : Machine (16*u^10) pc rg words) (hp : pc ≤ u) (hr : rg ≤ u) (hk : words ≤ u)
    (tail : Fin (2^(u^3)) → Bool) (team step : ℕ) (par : Fin np → Bool)
    (oa na oc nc : Fin a → Bool) (st : Word (16*u^10))
    (hs : 2+pinCount (2^(u^3)) nt ns np a ≤ 2^(16*u^10))
    (hf : fuel ≤ 2^(16*u^10+1))
    (grid : 2+pinCount (2^(u^3)) nt ns np a+fuel ≤ 2^(1+depth)) :
    let D := RAM.installProgram (RAM.CapacityPadding.pad M hp hr hk) tail
    let pin := fields D (digits team nt) (digits step ns) par oa na oc nc
    let hw : 3 ≤ 16*u^10+1 := by have := Nat.le_self_pow (by decide : 10 ≠ 0) u; omega
    let text := RAM.CapacityPadding.textFits_scale hu
    let hpc : u ≤ 2^(16*u^10+1) := text.registers.trans (Nat.pow_le_pow_right (by decide) (by omega))
    (network hF hw hpc 2 st hs hf u u depth).eval (advicePins 2 D (raw pin)) =
      RAM.value (RAM.FieldCode.ofCardLe hF) M fuel st (memory pin) := by
  intro D pin hw text hpc
  have ternary : (fun j => binaryWord (16*u^10) (raw pin j)) = word pin := by
    funext j
    unfold word binaryWord RAM.BitLayout.bitWord
    cases raw pin j <;> rfl
  have embedded : 2+2^(u^3) ≤ 2+pinCount (2^(u^3)) nt ns np a := by unfold pinCount; omega
  have h := eval_installed hu hF M hp hr hk depth 2 st hs hf grid embedded tail (raw pin)
  dsimp only at h
  rw [ternary] at h
  change _ = RAM.value _ M fuel st (RAM.memoryWithAdvice 2 D (memory pin)) at h
  exact h.trans (congrArg (RAM.value (RAM.FieldCode.ofCardLe hF) M fuel st)
    (mounted_advice D (digits team nt) (digits step ns) par oa na oc nc))

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
