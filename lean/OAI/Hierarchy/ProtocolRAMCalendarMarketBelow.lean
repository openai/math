import OAI.Hierarchy.ProtocolRAMPurchaseMarketBelow
import OAI.Hierarchy.ProtocolRAMCalendarFrozen

namespace OAI
/-! # Full low-memory agreement for a calendar's compiled market prefix -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen
noncomputable section
variable {z d k cut : ℕ}

/-- Future hidden words can differ, and each initial state may have chosen
its own encoding witness. Every cell below the current cutoff is preserved
in agreement through both the failure scan and the complete frozen market. -/
theorem Market.prefix_below (v : Market z d k) (left right : Shelf.Mem z d)
    (readyL : v.ready left) (readyR : v.ready right)
    (limit : v.flags≤ cut) (same : Below cut left right) :
    Below cut (v.prefix.after left) (v.prefix.after right) := by
  obtain ⟨fit,band,hd,room,π,fixtureL,inputL,prepL⟩:=readyL
  obtain ⟨_,_,_,_,_,fixtureR,inputR,prepR⟩:=readyR
  have low := (v.shelf.first_le_flags v.sampler z d k v.depth).trans limit
  have stamped := same.pass v.failures.pass fit
    (show v.failures.base≤ cut from (Nat.le_add_right _ _).trans (band.trans low))
  have heap := inputL.afterCT.trans low
  have matchCT (i : Key z d k) : ∃ enc : Shelf.StageEncoding i,
      (v.shelf.L v.sampler v.depth i).CTLoaded (banks (stage i)) (advisedStage z d π (stage i)) enc (v.failures.pass.apply right) := by
    obtain ⟨enc,ct⟩:=inputL.ct i
    exact Exists.intro enc (v.shelf.ct_below v.sampler π v.depth i enc ct heap stamped)
  have aligned : v.shelf.Incoming (k:=k) v.sampler π v.depth v.phase v.temperature v.kind
      (v.failures.pass.apply right) :=
    ⟨inputR.dimensions,matchCT,inputR.table,inputR.bankEnd,inputR.stockEnd,inputR.afterCT⟩
  exact v.shelf.result_below v.sampler π v.depth hd v.phase v.temperature v.kind _ _ fixtureL fixtureR inputL aligned
    prepL prepR room limit stamped

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
