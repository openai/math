import OAI.Hierarchy.ProtocolRAMCatalystTerminalLayout
import OAI.Hierarchy.ProtocolRAMCatalystStripSpace

namespace OAI
/-! # Height bound for every native terminal bank, including the bought catalogue -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive.TerminalLayout
open Calendar ProbeStage

def wordFactor (c : Mesh) (calendarEnd stockEnd ownerStride rows slots resources records : ℕ) :=
  56*(calendarEnd+stockEnd+fuel c*ownerStride+rows+2*slots+resources+2*records+2)

theorem top_bound (c : Mesh) (A : Arena) (stock : Bank) (ownerStride rows slots resources records z : ℕ)
    (a s o e r g n : ℕ)
    (calendarEnd : A.endAddress c≤a*2^z) (stockEnd : stock.base+stock.size≤ s*2^z)
    (stride : ownerStride≤o*2^z) (edges : rows≤e*2^z) (slotsFit : slots≤ r*2^z)
    (resourcesFit : resources≤g*2^z) (entries : records≤n*2^z) :
    28*2^(pageBits c A stock ownerStride rows slots resources records)≤wordFactor c a s o e r g n*2^z := by
  let t:=footprint c A stock ownerStride rows slots resources records
  have nz : t≠0 := by unfold t footprint;omega
  have scale : 2^t.log2≤t := Nat.log2_self_le nz
  have rounded : 2^(pageBits c A stock ownerStride rows slots resources records)≤2*t := by
    change 2^(t.log2+1)≤2*t
    rw [pow_succ]
    omega
  have ev : (events c).length=fuel c:=event_count c
  have lanes:=Nat.mul_le_mul_left (fuel c) stride
  have base : 1≤2^z:=Nat.two_pow_pos z
  dsimp only [t,footprint] at rounded
  rw [ev] at rounded
  unfold wordFactor
  nlinarith only [rounded,calendarEnd,stockEnd,lanes,edges,slotsFit,resourcesFit,entries,base]

theorem top_room (c : Mesh) (A : Arena) (stock : Bank) (ownerStride rows slots resources records z d : ℕ)
    (a s o e r g n : ℕ)
    (calendarEnd : A.endAddress c≤a*2^z) (stockEnd : stock.base+stock.size≤ s*2^z)
    (stride : ownerStride≤o*2^z) (edges : rows≤e*2^z) (slotsFit : slots≤ r*2^z)
    (resourcesFit : resources≤g*2^z) (entries : records≤n*2^z)
    (large : wordFactor c a s o e r g n≤z) :
    28*2^(pageBits c A stock ownerStride rows slots resources records)<2^(Native.wordBits z d Native.copies) := by
  apply (top_bound c A stock ownerStride rows slots resources records z a s o e r g n
    calendarEnd stockEnd stride edges slotsFit resourcesFit entries).trans_lt
  rw [Nat.mul_comm]
  exact GlobalTests.linear_room z d _ large

end Hierarchy.ProtocolRAM.CatalystArchive.TerminalLayout

namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe ColumnWires CoreBoard ReportSockets CatalystArchive
open CoreRoute CatalogueRows StripDirectory BoughtSockets PurchaseFrozen
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical
variable {z W k q depth : ℕ}
local notation "D" => 2^W
local notation "N" => Stages z D
local notation "roles" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole depth k))
variable (s : Boards z (2^W) k q depth) (c : Mesh) (cat : CatalogueRows.Board)
    (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

def stripWordFactor (c : Mesh) (d k degree depth a stock rows : ℕ) :=
  let o:=ownerRowFactor d k degree depth (fixedOwnerRoles d k depth)
  TerminalLayout.wordFactor c a stock o rows (CatalystArchive.slotFactor d k) (resourceFactor d k) (stripRecordFactor c d k degree depth)

/-- Specializes to the original number of core and bought rows and to the
actual widths chosen by the signed payload and purchased local programs. -/
theorem terminal_word_room (A : Arena) (stock : Bank) (a stockFactor rowFactor : ℕ)
    (calendarEnd : A.endAddress c≤a*2^z) (stockEnd : stock.base+stock.size≤ stockFactor*2^z)
    (catalogue : cat.rows≤ rowFactor*2^z) (large : stripWordFactor c D k s.sampler.degree depth a stockFactor rowFactor≤z) :
    let stride:=ownerRowFactor D k s.sampler.degree depth roles*2^z
    let n:=rowOnlyCount c (declaredRows c (ownerLedger s c cat G F A))
    28*2^(TerminalLayout.pageBits c A stock stride cat.rows (Fintype.card (Slots z D k))
      (Fintype.card (Columns z D)*k) n)<2^(Native.wordBits z D Native.copies) := by
  intro stride n
  have phase : N=18*(D-1)+1:=CoreCatalogue.total_stages z D
  have shape : roles=fixedOwnerRoles D k depth:=by unfold fixedOwnerRoles;rw [phase]
  apply TerminalLayout.top_room c A stock stride cat.rows _ _ n z D a stockFactor _ rowFactor _ _ _
    calendarEnd stockEnd _ catalogue (slot_count z D k (Nat.two_pow_pos _)) (physical_resources z D k (Nat.two_pow_pos _))
    (declared_records s c cat G F A) large
  unfold stride
  rw [shape]

def catalogueFactor (c : Mesh) (S : PurchaseSampler) (d k depth : ℕ) :=
  CoreCatalogue.coreFactor S d k+((c.inject+c.cool)*c.outerFuel)*((2*rounds d+1)*(2*k))*S.degree^depth

/-- The bought side uses the entire padded signed rectangle for every dated
attempt, including the dormant candidates charged by the physical serializer. -/
theorem catalogue_linear (c : Mesh) (S : PurchaseSampler) (cat : CatalogueRows.Board) (z W k depth : ℕ)
    (order : Fin cat.coreRows≃Edges S z (2^W) k)
    (paid : ((c.inject+c.cool)*c.outerFuel)*(PurchaseFrozen.count z (2^W) k*
      PurchaseFrozen.paths z S.degree depth)=cat.boughtRows) :
    cat.rows≤ catalogueFactor c S (2^W) k depth*2^z := by
  let boughtFactor:=((c.inject+c.cool)*c.outerFuel)*((2*rounds (2^W)+1)*(2*k))*S.degree^depth
  have rc : cat.coreRows=Fintype.card (Edges S z (2^W) k):=
    (Fintype.card_fin cat.coreRows).symm.trans (Fintype.card_congr order)
  have rb : cat.boughtRows=boughtFactor*2^z := by
    rw [←paid,PurchaseFrozen.count_eq]
    dsimp only [PurchaseFrozen.paths,boughtFactor]
    ac_rfl
  calc
    cat.rows = Fintype.card (Edges S z (2^W) k)+boughtFactor*2^z :=
      congrArg₂ Nat.add rc rb
    _ ≤ CoreCatalogue.coreFactor S (2^W) k*2^z+boughtFactor*2^z :=
      Nat.add_le_add_right (CoreCatalogue.rows_linear S z W k) _
    _ = catalogueFactor c S (2^W) k depth*2^z := (Nat.add_mul ..).symm

theorem terminal_word_room_of_layout (A : Arena) (stock : Bank) (a stockFactor : ℕ)
    (calendarEnd : A.endAddress c≤a*2^z) (stockEnd : stock.base+stock.size≤ stockFactor*2^z)
    (order : Fin cat.coreRows≃Edges s.sampler z D k)
    (paid : ((c.inject+c.cool)*c.outerFuel)*(PurchaseFrozen.count z D k*PurchaseFrozen.paths z s.sampler.degree depth)=cat.boughtRows)
    (large : stripWordFactor c D k s.sampler.degree depth a stockFactor (catalogueFactor c s.sampler D k depth)≤z) :
    let stride:=ownerRowFactor D k s.sampler.degree depth roles*2^z
    let n:=rowOnlyCount c (declaredRows c (ownerLedger s c cat G F A))
    28*2^(TerminalLayout.pageBits c A stock stride cat.rows (Fintype.card (Slots z D k))
      (Fintype.card (Columns z D)*k) n)<2^(Native.wordBits z D Native.copies) :=
  terminal_word_room s c cat G F A stock a stockFactor _ calendarEnd stockEnd
    (catalogue_linear c s.sampler cat z W k depth order paid) large

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
