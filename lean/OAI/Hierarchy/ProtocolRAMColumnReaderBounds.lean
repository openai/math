import OAI.Hierarchy.ProtocolRAMStoredColumnFits
import OAI.Hierarchy.ProtocolRAMBoughtPositionColumn
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueCost
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueFits

namespace OAI
/-! # Constant-size global column instructions for chronological role writers -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage PurchaseFrozen PurchaseCT ReportSockets Calendar CoreBoard
open scoped Classical Fin.CommRing
variable {h W k depth K G H attempts w : ℕ}

theorem ColumnROM.stage_work (base remap sitesBase super K G H k attempts : ℕ)
    (t : StageAt h (2^W)) (s : Bool) (tile : Expr) :
    (stageColumn base remap sitesBase super K G H k attempts t s tile).work=
      2*tile.work+52+ReportSockets.copies k attempts*(tile.work+6) := by
  simp only [stageColumn,stageInputs,project,SiteROM.atPort,SiteROM.siteExpr,addressExpr,Expr.work,
    ProtocolRAM.scale_work,Nat.one_mul]
  ring

theorem ColumnROM.payload_work (base remap sitesBase super K G H k attempts : ℕ) (choice : PayloadChoice h W) :
    (payloadColumn base remap sitesBase super K G H k attempts choice).work≤56+8*ReportSockets.copies k attempts := by
  cases choice <;> simp only [payloadColumn,Expr.work,stage_work] <;> omega

theorem Directory.position_work (v : Directory attempts) (base : ℕ) (S : PurchaseSampler)
    (h W k depth K G H : ℕ) (j : Fin (depth+1)) (s : Bool) :
    (v.atPosition base S h W k depth K G H j s).work ≤ selectWork attempts
      (selectWork ((2*rounds (2^W)+1)*(2*k)) (70+15*ReportSockets.copies k attempts)) := by
  rw [←count_eq h (2^W) k]
  apply select_work
  intro a
  apply select_work
  intro i
  rw [ColumnROM.stage_work]
  change 2*9+52+ReportSockets.copies k attempts*(9+6)≤ _
  omega

theorem Directory.Cover.columns {v : Directory attempts} {S : PurchaseSampler} {out : ℕ}
    (C : v.Cover S h W k depth K G H out) : ColumnROM.Cover h W v.remapBase v.sitesBase v.superBase K G H out :=
  ⟨C.ct,C.names,C.super,C.offsets,C.sites⟩

theorem ColumnROM.stage_fits (base : ℕ) (v : Directory attempts) (S : PurchaseSampler) (depth K G H out : ℕ)
    (t : StageAt h (2^W)) (s : Bool) (tile : Expr) (word : out<2^w) (room : base+words h (2^W) k≤ out)
    (C : v.Cover S h W k depth K G H out) (read : tile.Fits w out) :
    (stageColumn base v.remapBase v.sitesBase v.superBase K G H k attempts t s tile).Fits w out :=
  stage_fits_cols base v.remapBase v.sitesBase v.superBase K G H out t s tile word room C.columns read

theorem ColumnROM.payload_fits (base : ℕ) (v : Directory attempts) (S : PurchaseSampler) (depth K G H out : ℕ)
    (choice : PayloadChoice h W) (word : out<2^w) (room : base+words h (2^W) k≤ out)
    (C : v.Cover S h W k depth K G H out) :
    (payloadColumn base v.remapBase v.sitesBase v.superBase K G H k attempts choice).Fits w out :=
  payload_fits_cols base v.remapBase v.sitesBase v.superBase K G H out choice word room C.columns

theorem Directory.position_fits (v : Directory attempts) (base : ℕ) (S : PurchaseSampler) (depth K G H out : ℕ)
    (j : Fin (depth+1)) (s : Bool) (word : out<2^w) (room : base+ColumnROM.words h (2^W) k≤ out)
    (C : v.Cover S h W k depth K G H out) :
    (v.atPosition base S h W k depth K G H j s).Fits w out := by
  apply select_fits _ _ word C.outer
  intro a
  apply select_fits _ _ word C.keys
  intro i
  apply ColumnROM.stage_fits _ _ S depth _ _ _ _ _ _ _ word room C
  let L := (v.shelf a).L S depth i
  have ⟨_,_,_,_,_,so,ga,pa,en⟩ := L.regions
  have high : L.endAddress≤ out := C.source a i
  have limit : L.source.base+L.source.size≤out := by omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (limit.trans_lt word),limit⟩,trivial,trivial⟩

end Hierarchy.ProtocolRAM.BoughtSockets
end

end OAI
