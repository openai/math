import OAI.Hierarchy.TaggedWidePurchasedPinVolumes
import OAI.Hierarchy.TaggedWidePurchasedReadout

namespace OAI
/-! # Socket fees of the attached native compactor hardware -/

noncomputable section
namespace Hierarchy.ProbeStage.ReportSockets
open Tagged TaggedPrune TaggedShorterBudget TaggedShorterPacking TaggedShorterSupergroups Tagged.WideControlJoin
open ThreeFlat Routing Spill TaggedShorterCompaction TaggedShorterNetwork Real Filter
open scoped Classical Topology BigOperators

variable {F : Type*} [Field F] {κ A : ℝ} {M k : ℕ}

theorem attached_socket {K C : ℝ} (menu : WideMenu κ A) (x : WideParent κ A)
    (D S count : Fin menu.types→ℕ) (frame : Frame F k x.h x.w M)
    (items : PurchaseList (F:=F) (C:=C) menu x D S count)
    (read : ∀i,Input (S i) (D i) (menu.height i x+menu.payload i x)→
      SitePins (OpenPins x.h x.w frame.routing.catalyst) (Fin frame.routing.selectors) frame.data frame.paid)
    (i : Fin menu.types)
    (bound : (menu.copies i x:ℝ)*pins (menu.height i x) (menu.payload i x)≤K*((2:ℝ)^x.h*x.w)) :
    WidePhysicalBill.Part.fee (attachPurchases menu x D S count frame items read).charges (.socket i)≤
      K*(WidePhysicalBill.Part.scale x.h x.w (.socket i)*(log (x.h:ℝ))^(0:ℝ)) := by
  have copies : count i*2=menu.copies i x := (Nat.mul_comm ..).trans (items i).copies.symm
  change (((count i*2)*pins (menu.height i x) (menu.payload i x):ℕ):ℝ)≤
    K*(((2:ℝ)^x.h*x.w)*(log (x.h:ℝ))^(0:ℝ))
  simpa only [copies,Nat.cast_mul,Real.rpow_zero,pow_zero,mul_one] using bound

theorem purchased_sockets {u : ℝ→ℝ} {s ε p q Q σ L δ η ξ : ℝ} {C : ℝ}
    (profile : TaggedWidthProfile.Admissible s u) (price : Choice u A ε p q Q σ L δ η ξ)
    (W n attempts ell short : ℕ) (hW : 0<W) (hk : 0≤κ) :
    let menu := (typeMenu κ A W n k attempts ell hW (fun _=>short+ell)).menu u δ ξ
    ∃ K : ℝ, 0≤K ∧ ∀ᶠ x in WideParent.large κ A,
      ∀(D S count : Fin (n+1)→ℕ) (frame : Frame F k x.h x.w M)
       (items : PurchaseList (F:=F) (C:=C) menu x D S count)
       (read : ∀i,Input (S i) (D i) (menu.height i x+menu.payload i x)→
          SitePins (OpenPins x.h x.w frame.routing.catalyst) (Fin frame.routing.selectors) frame.data frame.paid)
       (i : Fin (n+1)),
       WidePhysicalBill.Part.fee (attachPurchases menu x D S count frame items read).charges (.socket i)≤
         K*(WidePhysicalBill.Part.scale x.h x.w (.socket i)*(log (x.h:ℝ))^(0:ℝ)) := by
  intro menu
  obtain ⟨K,pos,ready⟩ := purchased_pin_volumes profile price W n k attempts ell short hW hk
  refine ⟨K,pos,?_⟩
  filter_upwards [ready] with x room D S count frame items read i
  exact attached_socket menu x D S count frame items read i (room i)

end Hierarchy.ProbeStage.ReportSockets

end
end OAI
