import OAI.Hierarchy.ProbeFixedWidePrefixProgram
import OAI.Hierarchy.TaggedWideTerminalTariff

namespace OAI
/-! # Address space of the two permanent prefix tables and their replay scan -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires Filter
open scoped Classical

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "D" => 2^v.W
local notation "P" => v.widePlacement
local notation "stock" => (fun h width=>v.fixedTerminalStock (P h width) h width)
local notation "A" => (fun h width=>v.privateArena (P h width) h width)
local notation "s" => (fun h width=>v.nativeBoards (P h width) h width)
local notation "cnt" => (fun h width=>rowOnlyCount v.mesh (declaredRows v.mesh
  (ownerLedger (s h width) v.mesh (P h width).catalogue (P h width).routes F (A h width))))
local notation "page" => (fun h width=>v.wideSignedPage h width (stock h width))
local notation "last" => (events v.mesh).length

def wideScanEnd (h width : ℕ) (ss : List PaidWidths.Slice) (maxRows : ℕ) :=
  (v.wideReserveLayout h width ss).scratch+2*max maxRows (cnt h width)

def prefixSpaceFactor := (last+1)*5+(2*last+2)*5+2

/-- All width and reserve pages, including the sentinel of every dated bank,
and both temporary row vectors fit above the actual mounted role pages. -/
theorem wide_scan_bound (h width : ℕ) (ss : List PaidWidths.Slice) (maxRows : ℕ)
    (small : maxRows≤2^page h width) :
    v.wideScanEnd h width ss maxRows≤
      v.wideRoleSize h width (stock h width) ss+v.prefixSpaceFactor*2^page h width := by
  let edges:=(P h width).catalogue.rows
  let num:=Fintype.card (Columns h D)*k
  let span:=2^page h width
  let archive:=v.wideRoleSize h width (stock h width) ss
  let count:=cnt h width
  let roles:=max (Fintype.card (StripDirectory.PayloadRole (Stages h D) k)) (Fintype.card (StripDirectory.PurchasedRole v.depth k))
  let stride:=ownerRowFactor D k v.sampler.degree v.depth roles*2^h
  have footprint : TerminalLayout.footprint v.mesh (A h width) (stock h width) stride edges
      (Fintype.card (Slots h D k)) num count< span := Nat.lt_log2_self
  unfold TerminalLayout.footprint at footprint
  have pos : 0< span := Nat.two_pow_pos _
  have edgesFit : 2*edges+3≤5*span := by omega
  have axesFit : 2*num+3≤5*span := by omega
  have countFit : max maxRows count≤ span := max_le small (by omega)
  have permanent : (v.wideReserveLayout h width ss).scratch ≤
      archive+(last+1)*(2*edges+3)+(2*last+2)*(2*num+3) := PrefixWidths.Layout.dense_extent edges num archive last
  unfold wideScanEnd
  calc
    _≤(archive+(last+1)*(5*span)+(2*last+2)*(5*span))+2*span :=
      Nat.add_le_add (permanent.trans (Nat.add_le_add
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ edgesFit) _) (Nat.mul_le_mul_left _ axesFit)))
        (Nat.mul_le_mul_left 2 countFit)
    _=_ := by dsimp only [archive,span,prefixSpaceFactor]; ring

/-- A linear mounted archive gives a linear bound on the whole replay arena,
uniformly in the public width, slice descriptors, and row bound. -/
theorem cofinal_scan_linear {κ X : ℝ} (K : ℕ) :
    ∃ C : ℕ,∀ᶠ x : Tagged.WideParent κ X in Tagged.WideParent.large κ X,
      ∀ (ss : List PaidWidths.Slice) (maxRows : ℕ), maxRows≤2^page x.h x.w →
      v.wideRoleSize x.h x.w (stock x.h x.w) ss≤K*2^x.h →
      v.wideScanEnd x.h x.w ss maxRows≤C*2^x.h ∧
      v.wideScanEnd x.h x.w ss maxRows<2^Native.wordBits x.h D Native.copies := by
  let C:=K+v.prefixSpaceFactor*v.widePageFactor
  refine ⟨C,?_⟩
  have tall : Tendsto (Tagged.WideParent.h (κ:=κ) («A»:=X)) (Tagged.WideParent.large κ X) atTop := tendsto_comap
  filter_upwards [v.cofinal_pages (κ:=κ) («A»:=X),tall.eventually_ge_atTop C] with x pages large
  intro ss maxRows small store
  have bill:=(pages (stock x.h x.w) (v.fixedTerminalStock_end (P x.h x.w) x.h x.w)).1
  have cap : 2^page x.h x.w≤v.widePageFactor*2^x.h :=
    (Nat.le_mul_of_pos_left (2^page x.h x.w) (by decide : 0<28)).trans bill
  have total : v.wideScanEnd x.h x.w ss maxRows≤C*2^x.h := calc
    _≤_ := v.wide_scan_bound x.h x.w ss maxRows small
    _≤K*2^x.h+v.prefixSpaceFactor*(v.widePageFactor*2^x.h) :=
      Nat.add_le_add store (Nat.mul_le_mul_left _ cap)
    _=_ := by dsimp only [C];ring
  exact ⟨total,total.trans_lt (by simpa only [Nat.mul_comm] using GlobalTests.linear_room x.h D C large)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
