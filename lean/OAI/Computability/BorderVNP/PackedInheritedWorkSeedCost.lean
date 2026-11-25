import OAI.Computability.BorderVNP.PackedInheritedWorkBottomPrep
import OAI.Computability.BorderVNP.PackedInheritedWorkSelectedScanCost

/-! # Sparse gate budget of the repeated bottom work and extent initializer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords.BottomPrep

open Shortening.PublicEndpoints Shortening.PublicCapacity PackedHistoryCircuit
open PackedHistoryCircuit.Normalized.SelectedSchedule VPVNP.VerifierNetwork

variable {V E n w : ℕ} {σ Geo Data : Type} [Fintype σ] [Fintype Geo]
    (geom : Frame σ Geo) (read : Inputs Data V E w w → Geo) (ports : Ports n)
    (fits : V ≤ 2^w) (occupied : Fin V → Bool) (copies fine report : ℕ)

/-- Count every gate of the repeated bottom box initializer, including its physical
geometry and both incidence scans, with the one leaf flag charged to the same rectangle. -/
theorem frame_rowWork (tiles L : ℕ) (small : geom.size ≤ 2) (groups : n ≤ V) (cables : E ≤ 2^w)
    (word : w = 60*L) (hL : 1 ≤ L) :
    (frame geom read ports fits occupied copies fine report).size+1 ≤
      rowWork (3+64000*66^3) tiles L 3 ⟨V,E⟩ := by
  have counted := frame_size geom read ports fits occupied copies fine report
  have scan := widthCharge_cubic E groups fits cables word hL
  let s : Shape := ⟨V,E⟩
  have used : V+E+1 ≤ s.volume tiles := by dsimp only [s,Shape.volume]; omega
  have size := Nat.mul_le_mul_right (L^3) (Nat.mul_le_mul_right (66^3) (Nat.mul_le_mul_left 32000 used))
  have base : 1 ≤ s.volume tiles*L^3 := Nat.mul_pos ((by omega : 1 ≤ V+E+1).trans used) (Nat.pow_pos hL)
  calc
    _ ≤ 3+2*(32000*s.volume tiles*66^3*L^3) := by
      have cost := scan.trans size
      omega
    _ ≤ 3*(s.volume tiles*L^3)+2*(32000*s.volume tiles*66^3*L^3) :=
      Nat.add_le_add_right (by omega) _
    _ = _ := by unfold rowWork; dsimp only [s]; ring

end Packing.Inherited.WorkWords.BottomPrep

end BorderVNP
end Computability
end OAI
