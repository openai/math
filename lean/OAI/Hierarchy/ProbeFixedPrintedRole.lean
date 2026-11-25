import OAI.Hierarchy.ProbeFixedPostedBills
import OAI.Hierarchy.ProtocolRAMStripPriceCode

namespace OAI
/-! # Pricing the actual occurrence recorded in the fixed protocol's link-key column -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory CatalogueRows StockCommit PortPadding
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "n₀" => Fintype.card (PayloadRole N k)
local notation "n₁" => Fintype.card (PurchasedRole v.depth k)
local notation "D" => max n₀ n₁
local notation "bs" => v.nativeBoards P z width
local notation "board" => P.catalogue
local notation "H" => StripChart.header F bs

/-- Public immutable occurrence enumeration shared by the price/stock tape
and the finite histogram packet. -/
def roleOccurrence (a : Attempt) (row : Fin (H a).rows) (j : Fin D) :
    Fin (v.nativeFormats P z width a).pricedArea.occurrences :=
  (finCongr (v.occurrence_count P z width a)).symm ((H a).enum ⟨row,j⟩)

theorem occurrence_port (a : Attempt) (row : Fin (H a).rows) (j : Fin D) :
    v.occurrencePort P z width a (v.roleOccurrence P z width a row j)=j := by
  simp [occurrencePort,roleOccurrence]
  rfl

/-- The native key address used by `reportedKeys.link` at the actual phase
has precisely the loaded role's length code on the corresponding strip row. -/
theorem role_code {letters : ℕ} (a : Attempt) (row : Fin (H a).rows) (j : Fin D)
    (m : Memory W) (batch : Batch letters D) (h : (H a).Loaded m) (size : D≤2^W)
    (room : P.catalogue.rows<2^W) :
    let pf:=v.nativeFormats P z width a
    let g:=LabelSource.fromPorts pf.labelStart P.catalogue.idBase P.catalogue.geometry (H a).fieldTerm (StripChart.id F bs board a)
    let u:=v.roleOccurrence P z width a row j
    let seg:=pricedSegment pf.pricedArea pf.stockSource g W batch
    seg.ready m → seg.after m (g.out+u.val)=
      (P.catalogue.geometry 5).eval m ((StripChart.rawEdge bs P.catalogue.rows a j).eval m (row.val:Word W)) := by
  intro pf g u seg ready
  let h':=(H a).enum ⟨row,j⟩
  have pos : u.val=h'.val:=rfl
  have fields : ((H a).fieldTerm.eval m (u.val:Word W)).val=j.val := by
    rw [pos]
    have got:=h.second h'
    change (H a).fieldTerm.eval m (h'.val:Word W)=(((H a).enum.symm h').2.val:Word W) at got
    rw [show (H a).enum.symm h'=⟨row,j⟩ from (H a).enum.symm_apply_apply _] at got
    exact (congrArg Fin.val got).trans (Fin.val_cast_of_lt (j.isLt.trans_le size))
  have ball : (H a).ballTerm.eval m (u.val:Word W)=(row.val:Word W) := by
    rw [pos]
    have got:=h.first h'
    change (H a).ballTerm.eval m (h'.val:Word W)=(((H a).enum.symm h').1.val:Word W) at got
    rw [show (H a).enum.symm h'=⟨row,j⟩ from (H a).enum.symm_apply_apply _] at got
    exact got
  have stored:=P.catalogue.price_word pf.pricedArea pf.stockSource batch m pf.labelStart (H a).fieldTerm
    (StripChart.id F bs board a) u j (StripChart.retainedAt F bs a) (StripChart.edge F bs P.catalogue.rows a j)
    room size fields rfl ready (by rfl)
  refine stored.trans ?_
  rw [StripChart.edge,eval_atRow,ball]

/-- Both geometry-specific role alphabets have the same selected price at
their padded physical field ordinal. -/
theorem payload_supply (p a : ℕ) (row : Fin (H (.outer p a)).rows) (r : PayloadRole N k) :
    let i:=v.roleOccurrence P z width (.outer p a) row (inject (Nat.le_max_left n₀ n₁) ((Fintype.equivFin _) r))
    v.paidSupply z (.outer p a) (v.occurrencePort P z width (.outer p a) i).val=decide (catalystBit r=1) := by
  intro i
  change v.paidSupply z (.outer p a) (v.occurrencePort P z width (.outer p a)
    (v.roleOccurrence P z width (.outer p a) row _)).val=_
  rw [occurrence_port]
  simp [paidSupply,inject,(Fintype.equivFin _ r).isLt]

theorem purchased_supply (p a j t : ℕ) (row : Fin (H (.inner p a j t)).rows) (r : PurchasedRole v.depth k) :
    let i:=v.roleOccurrence P z width (.inner p a j t) row (inject (Nat.le_max_right n₀ n₁) ((Fintype.equivFin _) r))
    v.paidSupply z (.inner p a j t) (v.occurrencePort P z width (.inner p a j t) i).val=decide (catalystBit r=1) := by
  intro i
  change v.paidSupply z (.inner p a j t) (v.occurrencePort P z width (.inner p a j t)
    (v.roleOccurrence P z width (.inner p a j t) row _)).val=_
  rw [occurrence_port]
  simp [paidSupply,inject,(Fintype.equivFin _ r).isLt]

/-- These are the exact native port expressions installed by the fixed format.
The later menu, reserve and charge updates do not change their code. -/
def payloadPricePorts :=
  payloadPortsAt (v.located (v.seed P z width) P width) v.mesh P.routes

def purchasedPricePorts (phase trial : ℕ) :=
  boughtPortsAt (v.located (v.seed P z width) P width) v.mesh board P.routes phase trial

theorem payload_operand (phase trial : ℕ) (role : PayloadRole N k) :
    StripChart.rawEdge bs P.catalogue.rows (.outer phase trial) (inject (Nat.le_max_left n₀ n₁) ((Fintype.equivFin _) role))=
      (v.payloadPricePorts P z width).primary board role := by
  change extend _ (Expr.lit P.catalogue.rows) (inject (Nat.le_max_left n₀ n₁) ((Fintype.equivFin _) role))=_
  rw [extend_real]
  change (v.payloadPricePorts P z width).primary board ((Fintype.equivFin _).symm ((Fintype.equivFin _) role))=_
  rw [Equiv.symm_apply_apply]

theorem purchased_operand (phase trial j t : ℕ) (role : PurchasedRole v.depth k) :
    StripChart.rawEdge bs P.catalogue.rows (.inner phase trial j t) (inject (Nat.le_max_right n₀ n₁) ((Fintype.equivFin _) role))=
      (v.purchasedPricePorts P z width phase trial).primary board role := by
  change extend _ (Expr.lit P.catalogue.rows) (inject (Nat.le_max_right n₀ n₁) ((Fintype.equivFin _) role))=_
  rw [extend_real]
  change (v.purchasedPricePorts P z width phase trial).primary board ((Fintype.equivFin _).symm ((Fintype.equivFin _) role))=_
  rw [Equiv.symm_apply_apply]

/-- The stored length in the genuinely executed signed-link column prices
the physical payload packet role at the printed catalogue tariff. -/
theorem payload_printed {letters : ℕ} (phase trial : ℕ) (row : Fin (H (.outer phase trial)).rows)
    (m : Memory W) (batch : Batch letters D) (headerLoaded : (H (.outer phase trial)).Loaded m)
    (size : D≤2^W) (room : P.catalogue.rows<2^W) (wide : 0< W)
    (order : Fin P.catalogue.coreRows≃Edges v.sampler z (2^v.W) k)
    (loaded : CoreLookup.Loaded P.routes.core order m)
    (codes : ∀f,P.catalogue.core.lengthCode.eval m ((order.symm f).val:Word W)=(coreCode v.sampler v.radius f:Word W))
    (fits : ∀f : Edges v.sampler z (2^v.W) k,coreCode v.sampler v.radius f<2^W)
    (global : PayloadStrip.Columns N → Columns z (2^v.W))
    (columns : ∀c,(((v.payloadPricePorts P z width).column c).eval m (row.val:Word W)).val=((Fintype.equivFin _) (global c)).val)
    (horizontal : ∀e l,∃f : Edges v.sampler z (2^v.W) k,
      ((v.payloadPricePorts P z width).horizontal e l).eval m (row.val:Word W)=((order.symm f).val:Word W) ∧
      (coreCode v.sampler v.radius f:ℝ)=PayloadStrip.length N e)
    (role : PayloadRole N k) (cash : ColumnWires.account _root_.id role=none) :
    let u : Attempt:=(.outer phase trial)
    let pf:=v.nativeFormats P z width u
    let i:=v.roleOccurrence P z width u row (inject (Nat.le_max_left n₀ n₁) ((Fintype.equivFin _) role))
    let g:=LabelSource.fromPorts pf.labelStart P.catalogue.idBase P.catalogue.geometry (H u).fieldTerm (StripChart.id F bs board u)
    let seg:=pricedSegment pf.pricedArea pf.stockSource g W batch
    seg.ready m → v.printedCharge P z width u i ((seg.after m (g.out+i.val)).val)=
      ColumnWires.printed v.radius (PayloadStrip.length N) role := by
  intro u pf i g seg ready
  have actual:=v.role_code P z width u row (inject (Nat.le_max_left n₀ n₁) ((Fintype.equivFin _) role)) m batch headerLoaded size room ready
  rw [actual,v.payload_operand P z width phase trial role]
  change externalPrice (v.paidSupply z u (v.occurrencePort P z width u i).val) v.radius 1 _=_
  rw [v.payload_supply P z width phase trial row role]
  exact (v.payloadPricePorts P z width).printed_metric board order v.radius (PayloadStrip.length N) m (row.val:Word W)
    loaded room wide codes fits global columns horizontal (fun u=>nomatch u) role cash

/-- The stored length in the genuinely executed signed-link column prices
the physical purchased packet role at the printed catalogue tariff. -/
theorem purchased_printed {letters : ℕ} (phase trial j t : ℕ) (row : Fin (H (.inner phase trial j t)).rows)
    (m : Memory W) (batch : Batch letters D) (headerLoaded : (H (.inner phase trial j t)).Loaded m)
    (size : D≤2^W) (room : P.catalogue.rows<2^W) (wide : 0< W)
    (order : Fin P.catalogue.coreRows≃Edges v.sampler z (2^v.W) k)
    (loaded : CoreLookup.Loaded P.routes.core order m)
    (codes : ∀f,P.catalogue.core.lengthCode.eval m ((order.symm f).val:Word W)=(coreCode v.sampler v.radius f:Word W))
    (fits : ∀f : Edges v.sampler z (2^v.W) k,coreCode v.sampler v.radius f<2^W)
    (global : ChainStrip.Columns v.depth → Columns z (2^v.W))
    (columns : ∀c,(((v.purchasedPricePorts P z width phase trial).column c).eval m (row.val:Word W)).val=((Fintype.equivFin _) (global c)).val)
    (horizontal : ∀e l,∃f : Edges v.sampler z (2^v.W) k,
      ((v.purchasedPricePorts P z width phase trial).horizontal e l).eval m (row.val:Word W)=((order.symm f).val:Word W) ∧
      (coreCode v.sampler v.radius f:ℝ)=ChainStrip.length v.depth e)
    (birth : P.catalogue.coreRows≤(((v.purchasedPricePorts P z width phase trial).probe ()).eval m (row.val:Word W)).val)
    (role : PurchasedRole v.depth k) (cash : ColumnWires.account _root_.id role=none) :
    let u : Attempt:=(.inner phase trial j t)
    let pf:=v.nativeFormats P z width u
    let i:=v.roleOccurrence P z width u row (inject (Nat.le_max_right n₀ n₁) ((Fintype.equivFin _) role))
    let g:=LabelSource.fromPorts pf.labelStart P.catalogue.idBase P.catalogue.geometry (H u).fieldTerm (StripChart.id F bs board u)
    let seg:=pricedSegment pf.pricedArea pf.stockSource g W batch
    seg.ready m → v.printedCharge P z width u i ((seg.after m (g.out+i.val)).val)=
      ColumnWires.printed v.radius (ChainStrip.length v.depth) role := by
  intro u pf i g seg ready
  have actual:=v.role_code P z width u row (inject (Nat.le_max_right n₀ n₁) ((Fintype.equivFin _) role)) m batch headerLoaded size room ready
  rw [actual,v.purchased_operand P z width phase trial j t role]
  change externalPrice (v.paidSupply z u (v.occurrencePort P z width u i).val) v.radius 1 _=_
  rw [v.purchased_supply P z width phase trial j t row role]
  exact (v.purchasedPricePorts P z width phase trial).printed_metric board order v.radius (ChainStrip.length v.depth) m (row.val:Word W)
    loaded room wide codes fits global columns horizontal (fun u=>by cases u;exact birth) role cash

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
