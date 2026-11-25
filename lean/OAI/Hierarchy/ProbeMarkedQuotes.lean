import OAI.Hierarchy.ProbePublicPrices
import OAI.Hierarchy.ProbePurchasedOccurrence

namespace OAI
/-! # Every actual native purchased tile met the analytic signed-price threshold -/

namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen
open scoped BigOperators Classical
noncomputable section

/-- Upon freezing the stock during an actual purchase, every physical signed record
chosen by its bit test has the precise old-quote motion required by `StrictPayment`. -/
theorem actualMarks_paid {z d k : ℕ} (sh : Shelf) (phase : PhasePrice) (T : ℝ) (payload signed : ℕ)
    (frozen : Shelf.Mem z d) (pos : 0<T) (room : 2^z≤2^(wordBits z d copies))
    (fit : ∀ (v : Σ _ : StageAt z d, Fin (2^z)) (axis : Fin k×Bool),
      PurchaseInventory.stock sh.stockBase frozen (.inr ((v.2,stageNumber v.1),axis))<sh.table.size)
    (t : StageAt z d) (c : Fin k×Bool) (r : Fin (2^z)) (hit : r∈actualMarks sh phase T signed frozen t c) :
    T^2/(4*k)≤phase.time*(rise phase.M (stageQuotes phase payload signed sh.stockBase frozen (.inr ((r,t),c))))^2 := by
  let j := (PurchaseMarks.signedDirection k).symm c
  have bank : sh.stock (z:=z) (d:=d) (k:=k) t =
      PurchaseInventory.bank (k:=k) sh.stockBase z (stageNumber t) := by
    funext axis
    rfl
  have selected : r∈PurchaseMarks.stratum (n:=2^z) (k:=k) phase T signed sh.table
      (PurchaseInventory.bank sh.stockBase z (stageNumber t)) frozen j := by
    rw [←bank]
    simpa only [actualMarks,Shelf.marked,stage_key,axis_key,j] using hit
  have eligible := PurchaseInventory.qualifies phase T signed sh.stockBase sh.table (stageNumber t) j r frozen room selected
    (show PurchaseInventory.stock sh.stockBase frozen (.inr ((r,stageNumber t),PurchaseMarks.signedDirection k j))<sh.table.size
      from fit ⟨t,r⟩ (PurchaseMarks.signedDirection k j))
  simp only [j,Equiv.apply_symm_apply] at eligible
  rw [div_pow,← mul_div_assoc,le_div_iff₀ (sq_pos_of_pos pos)] at eligible
  calc T^2/(4*k) = (1/(4*(k:ℝ)))*T^2 := by ring
       _ ≤ _ := eligible

end
end Hierarchy.ProtocolRAM.StripDirectory

end OAI
