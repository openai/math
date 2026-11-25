import OAI.ThreeFlat.Diagonal.TraceVolumePins
import OAI.ThreeFlat.Diagonal.TraceBitPins
import OAI.ThreeFlat.Diagonal.TraceDiagonalBudget
import OAI.ThreeFlat.RAM.CapacityPadding

namespace OAI
/-! # Tracing fixed native programs with a single common table at each diagonal scale -/

namespace ThreeFlat.Diagonal.TraceBitHeader

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMMemory
variable {F : Type*} [Fintype F] [CommRing F] {p₀ r₀ k₀ u f S : ℕ}

/-- The same physical network at scale u simulates any native executable
with all three fixed capacities at most u. The caller's padding, advice
and input bits remain visible to the simulated RAM. -/
theorem eval_installed (hu : 128 ≤ u) (hF : Fintype.card F ≤ 2^(16*u^10))
    (M : Machine (16*u^10) p₀ r₀ k₀) (hp : p₀ ≤ u) (hr : r₀ ≤ u) (hk : k₀ ≤ u)
    (d base : ℕ) (st : Word (16*u^10)) (hs : S ≤ 2^(16*u^10)) (hf : f ≤ 2^(16*u^10+1))
    (grid : S+f ≤ 2^(1+d)) (inMemory : base+2^(u^3) ≤ S) (tail : Fin (2^(u^3)) → Bool) (x : ℕ → Bool) :
    let h := RAM.CapacityPadding.textFits_scale hu
    let D := RAM.installProgram (RAM.CapacityPadding.pad M hp hr hk) tail
    let hw : 3 ≤ 16*u^10+1 := by have := Nat.le_self_pow (by decide : 10 ≠ 0) u; omega
    let hpc : u ≤ 2^(16*u^10+1) := h.registers.trans (Nat.pow_le_pow_right (by decide) (by omega))
    (network hF hw hpc base st hs hf u u d).eval (advicePins base D x) =
      RAM.value (RAM.FieldCode.ofCardLe hF) M f st
        (RAM.memoryWithAdvice base D (initialMemory S (fun a => binaryWord (16*u^10) (x a)))) := by
  intro h D hw hpc
  have hfit := RAM.CapacityPadding.text_add_advice_fit hu
  have text : (1+6*u+u)*(16*u^10) ≤ 2^(u^3) := (Nat.le_add_right _ _).trans hfit
  rw [eval_advice hF hw hpc (by omega) base st hs hf grid text inMemory]
  exact RAM.CapacityPadding.adviceValue_pad _ M u hp hr hk h text tail f st base _

/-- Exact evaluation on the four replaceable strings at the same rounded
m-step cap used in the public ROM volume bound. -/
theorem eval_tick_installed {e params : ℕ} (hu : TraceVolume.cm ≤ u)
    (he : e ≤ u) (hparams : params ≤ u^e) (hq : Fintype.card F ≤ u)
    (M : Machine (16*u^10) p₀ r₀ k₀) (hp : p₀ ≤ u) (hr : r₀ ≤ u) (hk : k₀ ≤ u)
    (base : ℕ) (hbase : base ≤ 4*2^(u^10-u^4)+params)
    (st : Word (16*u^10)) (tail : Fin (2^(u^3)) → Bool) (x : ℕ → Bool) :
    let S := (4*2^(u^10-u^4)+params)+2^(u^3)
    let d := TraceVolume.depth u
    let grid := TraceVolume.tick_grid hu he hparams
    let h128 : 128 ≤ u := by dsimp [TraceVolume.cm] at hu; omega
    let fits := RAM.CapacityPadding.textFits_scale h128
    let hF : Fintype.card F ≤ 2^(16*u^10) := hq.trans fits.registers
    let hw : 3 ≤ 16*u^10+1 := by have := Nat.le_self_pow (by decide : 10 ≠ 0) u; omega
    let hpc : u ≤ 2^(16*u^10+1) := fits.registers.trans (Nat.pow_le_pow_right (by decide) (by omega))
    let D := RAM.installProgram (RAM.CapacityPadding.pad M hp hr hk) tail
    (network hF hw hpc base st grid.1 grid.2.1 u u d).eval (advicePins base D x) =
      RAM.value (RAM.FieldCode.ofCardLe hF) M (2^d) st
        (RAM.memoryWithAdvice base D (initialMemory S (fun a => binaryWord (16*u^10) (x a)))) := by
  intro S d grid h128 fits hF hw hpc D
  exact eval_installed h128 hF M hp hr hk d base st grid.1 grid.2.1 grid.2.2 (Nat.add_le_add_right hbase _) tail x

end ThreeFlat.Diagonal.TraceBitHeader

end OAI
