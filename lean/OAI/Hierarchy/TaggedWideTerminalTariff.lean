import OAI.Hierarchy.ProbeFixedWideSettlement
import OAI.Hierarchy.ProtocolRAMCatalystTerminalUpper
import OAI.Hierarchy.TaggedWideWidthRoom

namespace OAI
/-! # The actual terminal pages occupy a fixed number of words per original input row -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires Filter
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "D" => 2^v.W

def widePageFactor :=
  let a:=Classical.choose v.wideArena
  stripWordFactor v.mesh D k v.sampler.degree v.depth a a v.rowFactor

theorem page_charge (h width : ℕ) (stock : Bank)
    (stride : v.keepLimit*width+1≤2^h)
    (stored : stock.base+stock.size≤(v.privateArena (v.widePlacement h width) h width).endAddress v.mesh) :
    28*2^v.wideSignedPage h width stock≤v.widePageFactor*2^h := by
  let P:=v.widePlacement h width
  let A:=v.privateArena P h width
  let s:=v.nativeBoards P h width
  let N:=Stages h D
  let roles:=max (Fintype.card (StripDirectory.PayloadRole N k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k))
  let off:=ownerRowFactor D k v.sampler.degree v.depth roles*2^h
  let cnt:=rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger s v.mesh P.catalogue P.routes F A))
  let a:=Classical.choose v.wideArena
  have fits : A.endAddress v.mesh≤a*2^h:=(Classical.choose_spec v.wideArena) h width stride
  have fixed : roles=fixedOwnerRoles D k v.depth:=by
    exact congrArg (fun phases => max (Fintype.card (StripDirectory.PayloadRole phases k))
      (Fintype.card (StripDirectory.PurchasedRole v.depth k))) (show N = 18*(D-1)+1 from CoreCatalogue.total_stages h D)
  apply TerminalLayout.top_bound v.mesh A stock off P.catalogue.rows (Fintype.card (Slots h D k))
    (Fintype.card (Columns h D)*k) cnt h a a _ v.rowFactor _ _ _ fits (stored.trans fits) _
    (v.wideCatalogueRows h width) (slot_count h D k (Nat.two_pow_pos _))
    (physical_resources h D k (Nat.two_pow_pos _)) (declared_records s v.mesh P.catalogue P.routes F A)
  dsimp only [off]
  rw [fixed]

theorem cofinal_pages {κ A : ℝ} :
    ∀ᶠ x:Tagged.WideParent κ A in Tagged.WideParent.large κ A,∀stock:Bank,
      stock.base+stock.size≤(v.privateArena (v.widePlacement x.h x.w) x.h x.w).endAddress v.mesh →
      28*2^v.wideSignedPage x.h x.w stock≤v.widePageFactor*2^x.h ∧
      28*2^v.wideSignedPage x.h x.w stock<2^Native.wordBits x.h D Native.copies := by
  have high : Tendsto (Tagged.WideParent.h (κ:=κ) (A:=A)) (Tagged.WideParent.large κ A) atTop:=tendsto_comap
  filter_upwards [Tagged.WideParent.fixed_mul_width (κ:=κ) (A:=A) v.keepLimit,
    high.eventually (eventually_ge_atTop v.widePageFactor)] with x small ranked
  intro stock stored
  have size:=v.page_charge x.h x.w stock small stored
  apply And.intro size
  apply size.trans_lt
  rw [Nat.mul_comm]
  exact GlobalTests.linear_room x.h D _ ranked

theorem priced_extent (h width : ℕ) (stock bank : Bank) (edges : ℕ) (ss : List PaidWidths.Slice)
    (fit : v.keepLimit*width+1≤2^h)
    (stored : stock.base+stock.size≤(v.privateArena (v.widePlacement h width) h width).endAddress v.mesh) :
    TerminalLayout.extent (v.wideSignedPage h width stock) ss≤
      v.widePageFactor*2^h+PaidWidths.clock bank edges ss :=
  (TerminalLayout.extent_le_paid_clock _ _ _ _).trans (Nat.add_le_add_right (v.page_charge h width stock fit stored) _)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
