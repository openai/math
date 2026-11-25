import OAI.Hierarchy.ProbeFixedWideSettlementPage
import OAI.Hierarchy.ProbeFixedStripSizes
import OAI.Hierarchy.ProtocolRAMCatalystTerminalScale
import OAI.Hierarchy.TaggedWideNativeArena

namespace OAI
/-! # A fixed height bound for the complete signed settlement page -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "s" => v.nativeBoards P h width
local notation "A" => v.privateArena P h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "r" => Fintype.card (Slots h D k)
local notation "num" => Fintype.card (Columns h D)*k
local notation "w" => Native.wordBits h D Native.copies
local notation "decl" => declaredRows v.mesh (ownerLedger s v.mesh (P).catalogue (P).routes F A)
local notation "cnt" => rowOnlyCount v.mesh decl
local notation "stride" => ownerRowFactor D k v.sampler.degree v.depth
  (max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k)))*2^h

local notation "page" => v.wideSignedPage h width

/-- A single, height-independent integer controls both the phase clock and
the complete price-and-owner archive, including every original strip row. -/
def wideSignedHeight :=
  let a:=Classical.choose v.wideArena
  max (max (max v.stripHeight ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊)
    (max (max (fuel v.mesh) v.keepLimit) (Fintype.card (Actions (publicStages v.W) k))))
    (stripWordFactor v.mesh D k v.sampler.degree v.depth a a v.rowFactor)

/-- The public fixed height bound covers both the entire phase arena and the
last page of the physical signed reporter. -/
theorem wide_signed_room (stock : Bank) (stockEnd : stock.base+stock.size≤(A).endAddress v.mesh)
    (age : v.wideSignedHeight≤h) (budget : v.keepLimit*width+1≤2^h) :
    28*2^(page stock)<2^w ∧ (A).endAddress v.mesh<2^w := by
  let a:=Classical.choose v.wideArena
  have bound : (A).endAddress v.mesh≤a*2^h:=Classical.choose_spec v.wideArena h width budget
  have enough : stripWordFactor v.mesh D k v.sampler.degree v.depth a a v.rowFactor≤h:=(le_max_right ..).trans age
  have room : 28*2^(page stock)<2^w:=terminal_word_room s v.mesh (P).catalogue (P).routes F A stock a a
    v.rowFactor bound (stockEnd.trans bound) (v.wideCatalogueRows h width) enough
  have high : TerminalLayout.footprint v.mesh A stock stride (P).catalogue.rows r num cnt<2^(page stock):=Nat.lt_log2_self
  unfold TerminalLayout.footprint at high
  exact ⟨room,by omega⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
