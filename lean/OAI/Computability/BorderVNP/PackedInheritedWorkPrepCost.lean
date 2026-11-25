import OAI.Computability.BorderVNP.PackedInheritedWorkPrepFrame
import OAI.Computability.BorderVNP.PackedRoutingCost

/-! # Sparse gate cost of the subdivision's inherited width columns -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords.Prep

open Crossing CellAddressCircuit CellAddressViews PackedHistogram
open private sort_poly lookup_poly padded from OAI.Computability.BorderVNP.PackedRoutingCost
open scoped Classical

/-- The two width fields add a linear number of word operations in the sparse site, cable
and port rectangle. The sorter and row additions cost at most a cubic in the word budget. -/
theorem charge_cubic {V E n w R W : ℕ} (rows : 1+CellAddressCircuit.count V E n V ≤ R)
    (width : w ≤ W) (depth : Nat.clog 2 R ≤ W) :
    charge V E n w ≤ 4000*R*(W+1)^3 := by
  let unit := R*(W+1)^3
  have ar : 1+((E+V)+(V+V))+(((E+E)+n)+V) ≤ R := by
    simpa only [CellAddressCircuit.count,Nat.add_assoc] using rows
  have hr : 0<R := by omega
  have hu : 0<unit := Nat.mul_pos hr (by positivity)
  have logBound (x : ℕ) (hx : x ≤ R) := (Nat.clog_mono_right 2 hx).trans depth
  have label : labelBound V E n w w ≤ 1000*unit := by
    have lrows : V+(E+E+n) ≤ R := by omega
    unfold labelBound
    exact (Nat.mul_le_mul (padded lrows hr) (lookup_poly width width (logBound _ lrows))).trans
      (by dsimp [unit]; ring_nf; rfl)
  have cap : CellAddressCircuit.count V E n V ≤ R := by omega
  have sort := Nat.mul_le_mul (padded cap hr) (sort_poly width width (logBound _ cap))
  rw [show 2*R*(500*(W+1)^3) = 1000*unit by dsimp [unit]; ring] at sort
  have gate : gateBound V E n V w w w ≤ 2001*unit := by dsimp only [gateBound]; omega
  have per : w*(60*w+16) ≤ 100*(W+1)^3 := by
    calc _ ≤ W*(60*W+16) := by gcongr
         _ ≤ _ := by nlinarith only [Nat.zero_le (W^3),Nat.zero_le (W^2),Nat.zero_le W]
  have tail := Nat.mul_le_mul (show E+E+n+(V+3*V) ≤ R by omega) per
  rw [show R*(100*(W+1)^3) = 100*unit by dsimp [unit]; ring] at tail
  have square : (w+1)^2 ≤ (W+1)^3 :=
    (Nat.pow_le_pow_left (by omega) 2).trans (Nat.pow_le_pow_right (by positivity) (by decide : 2≤3))
  have addition := Nat.mul_le_mul (by omega : V ≤ R) (Nat.mul_le_mul_left 300 square)
  rw [show R*(300*(W+1)^3) = 300*unit by dsimp [unit]; ring] at addition
  simp only [charge,View,End,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  rw [Nat.mul_assoc (E+E+n+(V+3*V)) w,show V*3*(100*(w+1)^2) = V*(300*(w+1)^2) by ring,
    Nat.mul_assoc 4000 R,←show unit = R*(W+1)^3 from rfl]
  omega

end Packing.Inherited.WorkWords.Prep

end BorderVNP
end Computability
end OAI
