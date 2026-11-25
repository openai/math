import OAI.Hierarchy.ProbeFixedStripCurvature
import OAI.Hierarchy.ProbeCommittedMenuRead

namespace OAI
/-! # Native row receipts for the common signed tape, retaining its actual occurrence data -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.CatalystArchive

open AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM Calendar Calendar.StockCommit PurchaseStage RepairHistogram
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical Fin.CommRing BigOperators

variable {A B C H F : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype H] [Field F]
  {k sites N w q D z d : ℕ} [Nonempty (Fin sites)] [Nonempty (Fin k)] [Nonempty (Role C H (A⊕B) k)]
  {M ε tree : ℝ} {len : H → ℝ} {cap : A → ℝ}
local notation "Roles" => Role C H (A⊕B) k
local notation "req" => demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B))
local notation "prices" => (fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap
variable {e : Role C H (A⊕B) k → Chord sites}
variable {menu : Probe.FixedMenu F e
    (demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B)))
    ((fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap)
    ε tree N}


namespace StripInput
variable (x : _root_.OAI.Hierarchy.ProtocolRAM.CatalystArchive.StripInput (A:=A) (B:=B) (C:=C) (H:=H) (k:=k) menu w z d q D)
local notation "cmt" => fresh x.form.pricedArea x.form.stockSource
local notation "header" => (⟨x.start,x.raw.market.rows,D⟩ : PortHeader)
local notation "realField" => fun r : Roles => PortPadding.inject x.ports (Fintype.equivFin Roles r)
variable {paths : ℕ} (mount : ((fresh x.form.pricedArea x.form.stockSource).native w x.raw.market.rows x.ballot).ready x.mem)
  (bc : BroadcastRoom (fresh x.form.pricedArea x.form.stockSource) x.ballot x.raw.market.rows w) (keys : CashKeys (fresh x.form.pricedArea x.form.stockSource).occurrences x.raw.market.rows (fresh x.form.pricedArea x.form.stockSource).goods paths)
  (link : Fin (fresh x.form.pricedArea x.form.stockSource).occurrences → ℕ → ℝ) (pricesAt : Fin x.raw.market.rows → ℕ → ℝ)
local notation "tape" => (cmt).tape x.ballot x.mem x.plan mount bc keys link pricesAt


/-- Primitive observations for one selected row. The native packet word and its
alphabet come from the public menu, the true ordinary address from the compiled
slot, and the cash-only fields from the measured label ROM. -/
structure RowRead (j : Fin x.raw.market.rows) (price : Fin x.raw.coordinates → ℝ) (ep : ℝ) where
  idx : A → Fin x.raw.coordinates
  grid : A → ℝ
  inside : quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) grid) ∈ prices
  recommendation : ∃ h : ε ≤ Probe.discrepancy F e req (quote M len (LocalCommodity.extraPrice (B:=B) grid)),
    let i := menu.select ⟨_,inside,h⟩
    x.ballot.packet.eval x.mem (j.val:Word w)=(((Fintype.equivFin menu.index i).val+1:ℕ):Word w) ∧
    x.ballot.termCount.read x.mem (x.ballot.packet.eval x.mem (j.val:Word w))=((menu.packet i).terms:Word w)
  address : ∀ a,((x.addr a).eval x.mem (j.val:Word w)).val=(idx a).val
  printed : ∀ r,account idx r=none → (tape).weight (x.plan.enum ⟨j,(realField) r⟩)=ColumnWires.printed M len r
  digit : ∀ a,grid a ≤ price (idx a) ∧ price (idx a) ≤ grid a+ep

/-- Build the selected-row observation directly from the affirmative
discrepancy word and the resident public menu/alphabet pages. No decoded
choice, signed packet gain or real-valued discrepancy is an input. -/
def RowRead.ofROM {phases digits : ℕ} (j : Fin x.raw.market.rows) (p : Fin x.raw.coordinates → ℝ) (ep : ℝ)
    (idx : A → Fin x.raw.coordinates) (grid : A → ℝ)
    (inside : quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) grid) ∈ prices)
    (test : StripTest digits) (base alphabet : ℕ) (pre : Memory w) (row : Fin test.rows) (atRow : row.val=j.val)
    (pagePrice : Fin phases → (Fin digits → Fin test.radix) → Roles → ℝ)
    (u : Fin phases) (key : Fin digits → Fin test.radix)
    (gridAt : pagePrice u key=quote M len (LocalCommodity.extraPrice (B:=B) grid))
    (cut : test.tolerance=ε) (err : 0≤ε) (scale : 0<test.precision)
    (positive : test.failure.cut<test.failure.value pre row)
    (before : ∀ l,(test.quoted l).eval pre (row.val:Word w)=((key l).val:Word w))
    (discrepancy : test.table.read pre ((finFunctionFinEquiv key).val:Word w) =
      (AttemptGate.discrepancyWord F e req (pagePrice u) test.precision key:Word w))
    (wordFits : AttemptGate.discrepancyWord F e req (pagePrice u) test.precision key < 2^w)
    (page : x.ballot.menu=(MenuROM.menus menu base test.radix pagePrice).bank u) (rad : x.ballot.radix=test.radix)
    (qs : x.ballot.quotes=List.ofFn test.quoted) (terms : x.ballot.termCount=(MenuROM.alphabets menu alphabet).bank 0)
    (resident : (MenuROM.menus menu base test.radix pagePrice).Resident x.mem)
    (letters : (MenuROM.alphabets menu alphabet).Resident x.mem)
    (after : ∀ l,(test.quoted l).eval x.mem (row.val:Word w)=((key l).val:Word w))
    (address : ∀ a,((x.addr a).eval x.mem (j.val:Word w)).val=(idx a).val)
    (fees : ∀ r,account idx r=none → (tape).weight (x.plan.enum ⟨j,(realField) r⟩)=ColumnWires.printed M len r)
    (points : ∀ a,grid a ≤ p (idx a) ∧ p (idx a) ≤ grid a+ep) : x.RowRead mount bc keys link pricesAt j p ep := by
  have ok : pagePrice u key∈prices := gridAt.symm ▸ inside
  have choice := MenuROM.selected_packet menu test base alphabet pagePrice u x.ballot pre x.mem row key
    cut err scale positive before discrepancy wordFits ok page rad qs terms resident letters after
  refine ⟨idx,grid,inside,?_,address,fees,points⟩
  obtain ⟨qualified,packet,arity⟩ := choice
  have eligible : ε ≤ Probe.discrepancy F e req (quote M len (LocalCommodity.extraPrice (B:=B) grid)) := by
    rw [←gridAt]
    exact qualified
  have selected : menu.select ⟨pagePrice u key,ok,qualified⟩ = menu.select ⟨_,inside,eligible⟩ :=
    congrArg menu.select (Subtype.ext gridAt)
  refine ⟨eligible,?_,?_⟩
  · simpa only [atRow] using packet.trans (congrArg (fun i : menu.index =>
      (((Fintype.equivFin menu.index i).val+1:ℕ):Word w)) selected)
  · simpa only [atRow] using arity.trans (congrArg (fun i : menu.index =>
      (((menu.packet i).terms:ℕ):Word w)) selected)

omit [Nonempty (Fin k)] in
/-- All selected row gains, active incidence and the real per-packet movement
bound in precisely the original mounted tape. The same code read supplies both
the rate/width and the selector charge. -/
theorem row_economy (placed : x.Placed) (price : Fin x.raw.coordinates → ℝ)
    (γ ep : ℝ) (K nominal payload base : ℕ)
    (positive : 0 ≤ γ) (margin : γ ≤ menu.margin) (epPos : 0 ≤ ep) (treePos : 0 ≤ tree)
    (ordinals : ∀ i,(menu.packet i).terms ≤ q ∧ (menu.packet i).terms < 2^w)
    (table : (cmt).price=(MenuROM.selectorCharges menu base).bank 0)
    (resident : (MenuROM.selectorCharges menu base).Resident x.mem)
    (lengths : ∀ j code,pricesAt j code ≤ tree)
    (precise : ∀ i,(Fintype.card Roles:ℝ)*x.ballot.maxWidth*ep ≤ (menu.packet i).width*γ/2)
    (mass : ∀ i,copied nominal (menu.packet i).width payload ≤ x.ballot.copies ∧
      x.ballot.copies ≤ copied K (menu.packet i).width payload)
    (read : ∀j,j∈liveRows x.ballot x.mem x.raw.market.rows →
      Nonempty (x.RowRead mount bc keys link pricesAt j price ep)) :
    (∀ j,j∈(tape).selected →
      let r := fun v : Fin D => x.plan.enum ⟨j,v⟩
      let p := activePrice (tape).kind (tape).weight price
      (∑v,((tape).put (r v):ℝ)*p (r v))+(tape).broadcast j+
        (copied nominal (x.nominal j) payload:ℝ)*(x.nominal j*γ/2) ≤
          ∑v,((tape).take (r v):ℝ)*p (r v)) ∧
      (∀ i : Fin x.raw.coordinates,(Finset.univ.filter (fun f => (tape).activeKind f=some i)).card ≤ 1) ∧
      ∀ f : Σ j,Fin ((tape).ports (SelectedRows.row (tape).selected j)),∃ i : menu.index,
        K*((tape).put ((tape).use f)+(tape).take ((tape).use f)) ≤ payload*packetRate (menu.packet i) := by
  refine ⟨?_,x.degree_one mount bc keys link pricesAt placed,?_⟩
  · intro j live
    obtain ⟨R⟩ := read j live
    exact x.quote_at_live j live R.grid R.inside R.recommendation ordinals mount bc keys link pricesAt R.idx
      price γ ep nominal payload base positive margin epPos treePos R.address R.printed R.digit table resident
      (lengths j) precise (fun i => (mass i).1)
  · apply x.rate_at_used mount bc keys link pricesAt K payload ordinals (fun i => (mass i).2)
    intro j live
    obtain ⟨R⟩ := read j live
    obtain ⟨h,record⟩ := R.recommendation
    exact ⟨menu.select ⟨_,R.inside,h⟩,record⟩

end StripInput
end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
