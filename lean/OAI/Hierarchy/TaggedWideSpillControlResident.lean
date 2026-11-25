import OAI.Hierarchy.TaggedWideControlResident
import OAI.Hierarchy.TaggedWideSpillLayout

namespace OAI
/-! # Finite inputs of the physical spilled-chord controls -/
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open ProbeStage.CoreBoard.HistoryRoles SiteControls
variable {W cut : ℕ}

theorem spill_fits (sites n D cap : ℕ) (table : Bank) (pre post left right : ℕ)
    (stride : table.Fits W cut)
    (whole : ∀b : Bool,∀f,(DatedRoleSheets.bank n (if b then post else pre) (sites*D)
      (ProtocolRAMPurchaseSampler.bits (sites*D)) f).Fits W cut)
    (only : ∀b : Bool,∀f,(DatedRoleSheets.bank n (if b then right else left) (sites*D)
      (ProtocolRAMPurchaseSampler.bits (sites*D)) f).Fits W cut) :
    let x:=spillControls sites n D cap table pre post left right
    ∀i,(x.selected i).Fits W cut ∧ (x.site i).Fits W cut ∧ ∀f,(x.value i f).Fits W cut := by
  intro x i
  let rows (first last : ℕ) (b : Bool) : Fin D → LocalPrefix.Columns :=
    columns n (if b then last else first) sites (ProtocolRAMPurchaseSampler.bits (sites*D)) table .row
  have full (b : Bool) (q : Fin D) : RowFits (W:=W) (cut:=cut) (rows pre post b q) :=
    column_fits _ _ _ _ _ q (whole b) stride
  have clipped (b : Bool) (q : Fin D) : RowFits (W:=W) (cut:=cut) (rows left right b q) :=
    column_fits _ _ _ _ _ q (only b) stride
  have low (b : Bool) (q : Fin D) : (spillLow (rows pre post b) (rows left right b) q).Fits W cut :=
    total_fits D _ (fun j=>weight_fits (clipped b j) (full b q))
  exact ⟨trivial,trivial,fun c=>compile_fits cap (rows pre post)
    (fun b=>spillLow (rows pre post b) (rows left right b)) full low ((fieldNumber D).symm c)⟩

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end OAI
