import OAI.Hierarchy.ProtocolRAMStoredStageColumns
import OAI.Hierarchy.ProtocolRAMColumnSelectFits
import OAI.Hierarchy.ProbeStageExport

namespace OAI
/-! Bounds of the stored stage and payload column instructions. -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage PurchaseFrozen PurchaseCT ReportSockets Calendar CoreBoard
open scoped Classical Fin.CommRing
variable {h W k depth K G H attempts w : ℕ}

private theorem safe (b : Bank) (out : ℕ) (word : out<2^w) (limit : b.base+b.size≤ out) : b.Fits w out :=
  ⟨Nat.two_pow_pos _,by omega,limit⟩

structure ColumnROM.Cover (h W remap siteBase superBase K G H out : ℕ) : Prop where
  ct : Native.heapEnd h (2^W) Native.copies≤ out
  names : remap+ReportGroupROM.words h (2^W)≤ out
  super : superBase+2*ProtocolRAMSupergroupDirectory.span K≤ out
  offsets : siteBase+(SiteROM.offsets siteBase G).size≤ out
  sites : siteBase+G+(SiteROM.sites siteBase G H).size≤ out

theorem ColumnROM.stage_fits_cols (base remap siteBase superBase K G H out : ℕ)
    (t : StageAt h (2^W)) (s : Bool) (tile : Expr) (word : out<2^w) (room : base+words h (2^W) k≤ out)
    (C : Cover h W remap siteBase superBase K G H out) (read : tile.Fits w out) :
    (stageColumn base remap siteBase superBase K G H k attempts t s tile).Fits w out := by
  have ct (j : Fin 3) : (Native.stageBank h (2^W) (stageNumber t) j).Fits w out :=
    safe _ out word ((Native.stageBank_end h (2^W) (stageNumber t) j).trans C.ct)
  have index : (Expr.lookup (ReportGroupROM.bank remap h (2^W) t) (.lookup (banks t).group tile)).Fits w out :=
    ⟨safe _ out word ((remap_end remap t).trans C.names),ct 0,read⟩
  have port : (Expr.lookup (if s then (banks t).output else (banks t).input) tile).Fits w out := by
    cases s
    · exact ⟨ct 1,read⟩
    · exact ⟨ct 2,read⟩
  have a := C.super
  have groups : (ProtocolRAMSupergroupDirectory.groupBank superBase K).Fits w out :=
    safe _ out word (by change superBase+ProtocolRAMSupergroupDirectory.span K≤ out;omega)
  have offsets : (ProtocolRAMSupergroupDirectory.offsetBank superBase K).Fits w out :=
    safe _ out word (by change superBase+ProtocolRAMSupergroupDirectory.span K+ProtocolRAMSupergroupDirectory.span K≤ out;omega)
  have mult (n : ℕ) (e : Expr) (ok : e.Fits w out) : (scale n e).Fits w out := by
    induction n with
    | zero => trivial
    | succ n ih => exact ⟨ok,ih⟩
  have below : (sites base h (2^W) k).base+(sites base h (2^W) k).size≤ out := by
    dsimp only [words,sites,Bank.size] at room ⊢
    omega
  exact ⟨safe _ out word below,safe _ out word C.sites,⟨safe _ out word C.offsets,groups,index⟩,
    ⟨offsets,index⟩,mult 1 _ ⟨trivial,mult _ _ port⟩⟩

theorem ColumnROM.payload_fits_cols (base remap siteBase superBase K G H out : ℕ)
    (choice : PayloadChoice h W) (word : out<2^w) (room : base+words h (2^W) k≤ out)
    (C : Cover h W remap siteBase superBase K G H out) :
    (payloadColumn base remap siteBase superBase K G H k attempts choice).Fits w out := by
  have outerFit (s : Bool) : (outer base h (2^W) k s).Fits w out := by
    apply safe _ _ word
    cases s <;> simp [outer,words,sites,Bank.size] at room ⊢ <;> omega
  cases choice with
  | source => exact ⟨outerFit false,trivial⟩
  | target =>
    have words : 2^h≤ out := by dsimp only [ColumnROM.words] at room;omega
    exact ⟨outerFit true,safe _ _ word (by simpa [Native.initialOutput,Bank.size] using words),trivial⟩
  | stage t s => exact stage_fits_cols base remap siteBase superBase K G H out t s .row word room C trivial

end Hierarchy.ProtocolRAM.BoughtSockets
end

end OAI
