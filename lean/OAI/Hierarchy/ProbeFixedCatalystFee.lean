import OAI.Hierarchy.ProbeFixedFailureWords
import OAI.Hierarchy.ProbeFixedPrintedRole
import OAI.Hierarchy.ProbeFixedReceipts
import OAI.Hierarchy.ProbeFixedOriginalPrice
import OAI.Hierarchy.ProbeFixedCatalystHeaders
import OAI.Hierarchy.ProbeFixedMountedForest
import OAI.Hierarchy.ProtocolRAMStripRadiusFees

namespace OAI
/-! # Both terminal positive catalyst contributions use the one recorded charge -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard ReportSockets
open StripChart StripDirectory CatalogueRows StockCommit PurchaseFrozen
open ThreeFlat.RAM
open scoped Classical Fin.CommRing

/-- The original catalogue numbers the two radius edges separately, at their
two genuine signs and with the same center column. -/
theorem CatalogueRows.Board.radius_metric (b : CatalogueRows.Board) (S : PurchaseSampler)
    {z W k jobs depth : ℕ} (π : Equiv.Perm (Fin (2^z))) (marks : Marks z W k jobs)
    (order : Fin b.coreRows≃Edges S z (2^W) k) (size : jobs*(count z (2^W) k*paths z S.degree depth)=b.boughtRows)
    (M : ℕ) (col : Columns z (2^W)) (axis : Fin k) (side : Bool) :
    extendedLength (b.ordinal S π depth marks order size) (lenCode S π depth marks M)
      (b.coreIndex (order.symm (.inl (.inl (col,axis,side)))))=M :=
  extendedLength_apply (b.ordinal S π depth marks order size) (lenCode S π depth marks M)
    (.inl (.inl (.inl (col,axis,side))))

namespace FixedProtocolFormat
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
  (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W₀" => wordBits z (2^v.W) copies
local notation "n₀" => Fintype.card (PayloadRole N k)
local notation "n₁" => Fintype.card (PurchasedRole v.depth k)
local notation "dim" => max n₀ n₁
local notation "jobs" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "fs" => v.nativeFormats P z width
local notation "bs" => v.nativeBoards P z width
local notation "g" => P.catalogue
local notation "H" => StripChart.header F bs
local notation "L" => v.stamp P z width r banks src tab dst owners

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
set_option cleanup.letToHave false
attribute [local irreducible] permutationFabric

private def CatalystFeeReadback {w rows : ℕ} (m : Memory w) (idx : Word w)
    (pair : Option (Expr × Expr)) (edge : Expr) (addr : Bool → Fin rows)
    (len : Fin rows → ℝ) (rate : ℝ) : Prop :=
  ∃ mask mate : Expr, pair = some (mask,mate) ∧ edge.eval m idx = ((addr false).val : Word w) ∧
    mask.eval m idx = 1 ∧ mate.eval m idx = ((addr true).val : Word w) ∧ len (addr false) + len (addr true) = rate

private def payloadFeeIndex (phase trial : ℕ) (row : Fin (H (.outer phase trial)).rows)
    (c : PayloadStrip.Columns N) (axis : Fin k) : Fin (fs (.outer phase trial)).pricedArea.occurrences :=
  v.roleOccurrence P z width (.outer phase trial) row (PortPadding.inject (Nat.le_max_left n₀ n₁)
    ((Fintype.equivFin (PayloadRole N k)) (.catalyst c axis)))

/-- On the actual payload physical row, the addressed direct and guarded
mate catalogue entries carry one radius tariff each on the issued paid rate. -/
theorem payload_catalyst_fee (phase trial : ℕ) (π : Equiv.Perm (Fin (2^z)))
    (marks : Marks z v.W k jobs) (order : Fin (g).coreRows≃Edges v.sampler z (2^v.W) k)
    (size : jobs*(count z (2^v.W) k*paths z v.sampler.degree v.depth)=(g).boughtRows)
    (m ledger : Memory W₀) (row : Fin (H (.outer phase trial)).rows) (c : PayloadStrip.Columns N) (col : Columns z (2^v.W))
    (axis : Fin k) (wide : dim≤2^W₀) (fit : (g).rows<2^W₀) (loaded : CoreLookup.Loaded P.routes.core order m)
    (dir : (H (.outer phase trial)).Loaded m)
    (column : (((v.payloadPricePorts P z width).column c).eval m (row.val:Word W₀)).val=((Fintype.equivFin _) col).val) :
    let i := payloadFeeIndex v P z width phase trial row c axis
    let addr (side : Bool) : Fin (g).rows := (g).coreIndex (order.symm (.inl (.inl (col,axis,side))))
    let len : Fin (g).rows → ℝ := extendedLength ((g).ordinal v.sampler π v.depth marks order size)
      (lenCode v.sampler π v.depth marks v.radius)
    CatalystFeeReadback m (i.val : Word W₀) (v.nativeTrees P z width (.outer phase trial)).catalystMate
      (L (.outer phase trial)).edge addr len (v.paidRate P z width r banks src tab dst owners ledger (.outer phase trial) i) := by
  intro i addr len
  let role : PayloadRole N k := .catalyst c axis
  let j : Fin dim := PortPadding.inject (Nat.le_max_left n₀ n₁) ((Fintype.equivFin (PayloadRole N k)) role)
  let a : Attempt := .outer phase trial
  have reads := StripDirectory.header_pair (H (.outer phase trial)) m dir row j
  have ball : (H a).ballTerm.eval m (i.val:Word W₀)=(row.val:Word W₀) := reads.1
  have field : ((H a).fieldTerm.eval m (i.val:Word W₀)).val=j.val :=
    (congrArg Fin.val reads.2).trans (Fin.val_cast_of_lt (j.isLt.trans_le wide))
  have nativeColumn : (payloadPortsAt bs v.mesh P.routes).column c = (v.payloadPricePorts P z width).column c := rfl
  have colRead : (((payloadPortsAt bs v.mesh P.routes).column c).eval m (row.val:Word W₀)).val =
      ((Fintype.equivFin _) col).val := by rw [nativeColumn]; exact column
  have readRadii := StripChart.payload_radius_ids (z:=z) (W:=v.W) (k:=k) (w:=W₀)
    (q:=(StripChart.catalogue F (v.configured (v.seed P z width)) v.cost).alphabet) (depth:=v.depth)
    bs v.mesh g P.routes F phase trial (fs a).labelStart order m
    (i.val:Word W₀) (row.val:Word W₀) c col axis fit wide loaded
  have stamped := readRadii colRead
  simp only [v.catalyst_boards] at stamped
  have terms := stamped field ball
  refine ⟨_,_,v.nativeTrees_mounted_header P z width a,?_,?_,?_,?_⟩
  · exact terms.1
  · exact terms.2.1
  · exact terms.2.2
  have flagged:v.paidSupply z a (v.occurrencePort P z width a i).val=true:=
    v.payload_supply P z width phase trial row role
  change len (addr false)+len (addr true)=v.printedCharge P z width a i _
  rw [v.supply_price P z width a i _ flagged]
  have radius (side : Bool) : len (addr side)=v.radius:=(g).radius_metric v.sampler π marks order size v.radius col axis side
  rw [radius,radius,two_mul]

/-- On the actual purchased physical row, the addressed direct and guarded
mate catalogue entries carry one radius tariff each on the issued paid rate. -/
theorem purchased_catalyst_fee (phase trial tick trial₂ : ℕ) (π : Equiv.Perm (Fin (2^z)))
    (marks : Marks z v.W k jobs) (order : Fin (g).coreRows≃Edges v.sampler z (2^v.W) k)
    (size : jobs*(count z (2^v.W) k*paths z v.sampler.degree v.depth)=(g).boughtRows)
    (m ledger : Memory W₀) (row : Fin (H (.inner phase trial tick trial₂)).rows) (c : ChainStrip.Columns v.depth) (col : Columns z (2^v.W))
    (axis : Fin k) (wide : dim≤2^W₀) (fit : (g).rows<2^W₀) (loaded : CoreLookup.Loaded P.routes.core order m)
    (dir : (H (.inner phase trial tick trial₂)).Loaded m)
    (column : (((v.purchasedPricePorts P z width phase trial).column c).eval m (row.val:Word W₀)).val=((Fintype.equivFin _) col).val) :
    let role : PurchasedRole v.depth k:=.catalyst c axis
    let j : Fin dim:=PortPadding.inject (Nat.le_max_right n₀ n₁) ((Fintype.equivFin (PurchasedRole v.depth k)) role)
    let i : Fin (fs (.inner phase trial tick trial₂)).pricedArea.occurrences:=
      v.roleOccurrence P z width (.inner phase trial tick trial₂) row j
    let addr (side : Bool):=(g).coreIndex (order.symm (.inl (.inl (col,axis,side))))
    let len:=extendedLength ((g).ordinal v.sampler π v.depth marks order size) (lenCode v.sampler π v.depth marks v.radius)
    CatalystFeeReadback m (i.val : Word W₀) (v.nativeTrees P z width (.inner phase trial tick trial₂)).catalystMate
      (L (.inner phase trial tick trial₂)).edge addr len
      (v.paidRate P z width r banks src tab dst owners ledger (.inner phase trial tick trial₂) i) := by
  intro role j i addr len
  let a : Attempt := .inner phase trial tick trial₂
  have reads := StripDirectory.header_pair (H (.inner phase trial tick trial₂)) m dir row j
  have ball : (H a).ballTerm.eval m (i.val:Word W₀)=(row.val:Word W₀) := reads.1
  have field : ((H a).fieldTerm.eval m (i.val:Word W₀)).val=j.val :=
    (congrArg Fin.val reads.2).trans (Fin.val_cast_of_lt (j.isLt.trans_le wide))
  have nativeColumn : (boughtPortsAt bs v.mesh g P.routes phase trial).column c =
      (v.purchasedPricePorts P z width phase trial).column c := rfl
  have colRead : (((boughtPortsAt bs v.mesh g P.routes phase trial).column c).eval m (row.val:Word W₀)).val =
      ((Fintype.equivFin _) col).val := by rw [nativeColumn]; exact column
  have readRadii := StripChart.purchased_radius_ids (z:=z) (W:=v.W) (k:=k) (w:=W₀)
    (q:=(StripChart.catalogue F (v.configured (v.seed P z width)) v.cost).alphabet) (depth:=v.depth)
    bs v.mesh g P.routes F phase trial tick trial₂ (fs a).labelStart order m
    (i.val:Word W₀) (row.val:Word W₀) c col axis fit wide loaded
  have stamped := readRadii colRead
  simp only [v.catalyst_boards] at stamped
  have roleRead := stamped field
  have terms := roleRead ball
  refine ⟨_,_,v.nativeTrees_mounted_header P z width a,terms.1,terms.2.1,terms.2.2,?_⟩
  have flagged:v.paidSupply z a (v.occurrencePort P z width a i).val=true:=
    v.purchased_supply P z width phase trial tick trial₂ row role
  change len (addr false)+len (addr true)=v.printedCharge P z width a i _
  rw [v.supply_price P z width a i _ flagged]
  have radius (side : Bool) : len (addr side)=v.radius:=(g).radius_metric v.sampler π marks order size v.radius col axis side
  rw [radius,radius,two_mul]

end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
