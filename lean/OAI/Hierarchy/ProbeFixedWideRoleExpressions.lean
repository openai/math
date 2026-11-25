import OAI.Hierarchy.ProbeFixedWidePrefixLayouts
import OAI.Hierarchy.ProbeFixedWideEventCode
import OAI.Hierarchy.ProbeFixedDatedRoleInput
import OAI.Hierarchy.TaggedWideDatedMask
import OAI.Hierarchy.TaggedWideAddressShape
import OAI.Hierarchy.TaggedWireRoleRoomShape

namespace OAI
/-! # Physical role identifiers and date-indexed width operands -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires WireTelescope
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
variable (bits : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "start" => v.catalystStaticStart P h width
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "rows" => (P).catalogue.rows
local notation "sizes" => RoleRoom.shape (R:=WideMemory.R v.sampler h v.W k) v.sampler directory rows
local notation "stock" => v.fixedTerminalStock P h width
local notation "page" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement page stock
local notation "ss" => v.widePaidSlices h width bits
local notation "hi" => v.wideRoleStart h width stock ss
local notation "base" => (sizes).stop hi
local notation "lw" => v.wideWidthLayout h width ss
local notation "lr" => v.wideReserveLayout h width ss
local notation "source" => TerminalLayout.source page
local notation "table" => TerminalLayout.table page
local notation "target" => TerminalLayout.destination page
local notation "owners" => sinkBank start cnt r rows
local notation "cells" => PurchaseInventory.footprint h N k
local notation "K" => Fintype.card (RoleProgram.Old h v.W k rows)

def wideRoleInventory (j : ℕ) : RoleProgram.Inventory :=
  RoleProgram.Inventory.ofOriginal base K ((lw).bank j) ((lw).bank j) (PrefixReserve.banks lr old j).reserved
    (PrefixReserve.banks lr old j).used

def wideRoleID : Expr := DatedRoleInput.id (v.wideRoleInventory h width bits 0) rows (PurchaseInventory.footprint h N k)

def wideRoleWidth (j : ℕ) : Expr :=
  DatedRoleInput.mask (P).catalogue (v.wideRoleInventory h width bits j)
    (DatedRoleInput.nativeAmount v P h width r old source table target owners base lw lr old j)

theorem wide_old_rows : K=rows+(cells+num) := by
  have goods : Fintype.card (Goods h v.W k) = cells :=
    PurchaseInventory.card_commodity h N k
  have reserve : Fintype.card (Catalysts h v.W k) = num := by
    change Fintype.card (Columns h D × Fin k) = Fintype.card (Columns h D) * k
    rw [Fintype.card_prod,Fintype.card_fin]
  calc
    K = rows + (Fintype.card (Goods h v.W k) + Fintype.card (Catalysts h v.W k)) := by
      simp only [RoleProgram.Old,SettledMatrix.Source,Fintype.card_sum,Fintype.card_fin]
    _ = _ := by rw [goods,reserve]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
