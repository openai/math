import OAI.Hierarchy.TaggedWideReadoutPurchases
import OAI.Hierarchy.TaggedWideNativeReadout

namespace OAI
/-! # Installing the two purchased compactors on the main native readout -/
noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open Tagged TaggedPrune TaggedShorterBudget TaggedShorterPacking TaggedShorterSupergroups Tagged.WideControlJoin
open ThreeFlat Routing Spill TaggedShorterCompaction TaggedShorterNetwork Real Filter
open scoped Classical Topology BigOperators
variable {F : Type*} [Field F] {κ A C : ℝ} {M k : ℕ} (menu : WideMenu κ A)
variable (x : WideParent κ A)
abbrev PurchaseList (D S count : Fin menu.types→ℕ) :=
  ∀i,Purchased F menu x i (D i) (S i) (count i) C

variable (D S count : Fin menu.types→ℕ) (frame : Frame F k x.h x.w M)
local notation "V" => SitePins (OpenPins x.h x.w frame.routing.catalyst) (Fin frame.routing.selectors) frame.data frame.paid

def attachPurchases (items : PurchaseList (F:=F) (C:=C) menu x D S count)
    (read : ∀i,Input (S i) (D i) (menu.height i x+menu.payload i x)→V) : Parts F k x.h x.w M menu.types :=
  {toFrame:=frame,cut:=fun i=>(items i).cut (read i),cap:=fun i=>⌊(menu.height i x:ℝ)^A⌋₊}

theorem attached_bank (board : Frame F k x.h x.w M)
    (items : PurchaseList (F:=F) (C:=C) menu x D S count)
    (wire : ∀ i, Input (S i) (D i) (menu.height i x+menu.payload i x) →
      SitePins (OpenPins x.h x.w board.routing.catalyst) (Fin board.routing.selectors) board.data board.paid)
    (i : Fin menu.types) :
    let p := attachPurchases menu x D S count board items wire
    (p.cut i).bank (p.cap i) = menu.bank x i :=
  (items i).bank (wire i)

theorem attached_work (board : Frame F k x.h x.w M)
    (items : PurchaseList (F:=F) (C:=C) menu x D S count)
    (wire : ∀ i, Input (S i) (D i) (menu.height i x+menu.payload i x) →
      SitePins (OpenPins x.h x.w board.routing.catalyst) (Fin board.routing.selectors) board.data board.paid)
    (i : Fin menu.types) :
    let p := attachPurchases menu x D S count board items wire
    WidePhysicalBill.Part.fee p.charges (.cut i) ≤
      C*(WidePhysicalBill.Part.scale x.h x.w (.cut i)*(log (x.h:ℝ))^(0:ℝ)) := by
  dsimp only
  simpa only [Real.rpow_zero,mul_one,WidePhysicalBill.Part.fee,WidePhysicalBill.Part.scale,
    Parts.charges,nativeCharges,attachPurchases] using (items i).work (wire i)


end Hierarchy.ProbeStage.ReportSockets

end
end OAI
