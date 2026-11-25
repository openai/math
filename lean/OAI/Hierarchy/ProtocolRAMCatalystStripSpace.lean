import OAI.Hierarchy.ProtocolRAMCatalystArchiveDates
import OAI.Hierarchy.ProtocolRAMCatalystArchiveMaster
import OAI.Hierarchy.ProtocolRAMCatalystStripGrowth
import OAI.Hierarchy.ProtocolRAMCoreCatalogueSpace

namespace OAI
/-! # The terminal archive on the chosen strip has a linear physical footprint -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe ColumnWires CoreBoard ReportSockets CatalystArchive
open CoreRoute CatalogueRows StripDirectory BoughtSockets PurchaseFrozen
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical

variable {z W k q depth : ℕ}
local notation "d" => 2^W
local notation "N" => Stages z d
local notation "w" => Native.wordBits z d Native.copies
local notation "r" => Fintype.card (Slots z d k)
variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : CatalogueRows.Board)
    (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

def stripRecordFactor (c : Mesh) («d» k degree depth : ℕ) :=
  fuel c*ownerRowFactor «d» k degree depth (fixedOwnerRoles «d» k depth)

theorem declared_records (arena : Arena) :
    rowOnlyCount c (declaredRows c (ownerLedger s c b G F arena))≤ stripRecordFactor c d k s.sampler.degree depth*2^z := by
  let D:=fixedOwnerRoles d k depth
  let R:=ownerRowFactor d k s.sampler.degree depth D
  have phase : N=18*(d-1)+1:=CoreCatalogue.total_stages z d
  have roleEq : max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole depth k))=D := by
    unfold D fixedOwnerRoles
    rw [phase]
  calc
    _ ≤ fuel c*(R*2^z) := by
      apply rowOnlyCount_le
      intro t
      unfold declaredRows
      split
      · simpa only [roleEq] using ledger_owner_rows s c b G F arena (.attempt t)
      · exact Nat.zero_le _
    _ = _ := (Nat.mul_assoc ..).symm

def staticFactor (c : Mesh) (S : PurchaseSampler) («d» k depth header : ℕ) :=
  header+8*stripRecordFactor c «d» k S.degree depth+12*CatalystArchive.slotFactor «d» k+16*CoreCatalogue.coreFactor S «d» k+12

/-- The occurrence count uses just the dates and the actual paid ledger. The
sink row count and the two native route index scans use the same physical graph. -/
theorem strip_bank_bound (arena : Arena) (start header : ℕ) (small : start≤header*2^z) :
    let n:=rowOnlyCount c (declaredRows c (ownerLedger s c b G F arena))
    let e:=Fintype.card (Edges s.sampler z d k)
    let endBank:=sinkBank start n r e
    endBank.base+endBank.size≤ staticFactor c s.sampler d k depth header*2^z := by
  intro n e endBank
  have records : n≤ stripRecordFactor c d k s.sampler.degree depth*2^z := declared_records s c b G F arena
  have slots:=slot_count z d k (Nat.two_pow_pos _)
  have edges : e≤CoreCatalogue.coreFactor s.sampler d k*2^z:=CoreCatalogue.rows_linear s.sampler z W k
  have absorb : 12≤12*2^z:=by simpa using Nat.mul_le_mul_left 12 (Nat.two_pow_pos z)
  apply (static_footprint start n r e).trans
  unfold staticFactor
  nlinarith only [small,records,slots,edges,absorb]

/-- After fixing the calendar and header coefficient, every sufficiently large
physical height admits all six simultaneously resident terminal banks. -/
theorem strip_bank_room (arena : Arena) (start header : ℕ) (small : start≤header*2^z)
    (large : staticFactor c s.sampler d k depth header≤z) (history : Bank) (scratch : ℕ) :
    let n:=rowOnlyCount c (declaredRows c (ownerLedger s c b G F arena))
    let e:=Fintype.card (Edges s.sampler z d k)
    let endBank:=sinkBank start n r e
    endBank.base+endBank.size<2^w ∧
      StaticSpace (banks start n history scratch) (routeBanks start n r) endBank n r e w := by
  intro n e endBank
  have high := strip_bank_bound s c b G F arena start header small
  have fit : endBank.base+endBank.size<2^w := high.trans_lt (by
    rw [Nat.mul_comm]
    exact GlobalTests.linear_room z d _ large)
  exact ⟨fit,allocated_space start n r e w history scratch fit⟩

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
