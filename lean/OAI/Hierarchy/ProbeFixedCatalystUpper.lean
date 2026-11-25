import OAI.Hierarchy.ProtocolRAMBilledRadii
import OAI.Hierarchy.ProbeFixedDirectUpper
import OAI.Hierarchy.ProbeFixedCatalystFee

namespace OAI
/-! # Both terminal positive catalyst contributions use the one recorded charge -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard ReportSockets
open StripChart StripDirectory CatalogueRows StockCommit PurchaseFrozen
open ThreeFlat.RAM
open scoped Classical Fin.CommRing

theorem CatalogueRows.Board.radius_le {S : PurchaseSampler} {z W k jobs depth : ℕ} (b : Board)
    (π : Equiv.Perm (Fin (2^z))) (marks : Marks z W k jobs) (order : Fin b.coreRows≃Edges S z (2^W) k)
    (sz : jobs*(count z (2^W) k*paths z S.degree depth)=b.boughtRows) (M : ℕ) (axis : Fin k) (side : Bool)
    {n : ℕ} (hit : b.RadiusAddress order axis side n) :
    addressPrice (extendedLength (b.ordinal S π depth marks order sz) (lenCode S π depth marks M)) n≤ M := by
  rcases hit with ⟨col,rfl⟩|rfl
  · let r:=b.coreIndex (order.symm (.inl (.inl (col,axis,side))))
    change addressPrice _ r.val≤_
    rw [addressPrice_fin]
    exact (b.radius_metric S π marks order sz M col axis side).le
  · simp [addressPrice]

private theorem catalyst_of_flag {C H A B : Type*} {k : ℕ} (r : ColumnWires.Role C H (A⊕B) k)
    (h : catalystBit r=1) : ∃c axis,r=.catalyst c axis := by
  cases r with
  | catalyst c axis => exact ⟨c,axis,rfl⟩
  | radius | cross | horizontal | extra => simp [catalystBit] at h

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
local notation "s" => v.located (v.seed P z width) P width
local notation "g" => P.catalogue
local notation "H" => StripChart.header F bs
local notation "L" => v.stamp P z width r banks src tab dst owners

set_option maxHeartbeats 1600000 in
private theorem payload_bounds (phase trial : ℕ) (π : Equiv.Perm (Fin (2^z))) (marks : Marks z v.W k jobs)
    (order : Fin (g).coreRows≃Edges v.sampler z (2^v.W) k)
    (size : jobs*(count z (2^v.W) k*paths z v.sampler.degree v.depth)=(g).boughtRows)
    (m : Memory W₀) (i : Fin (fs (.outer phase trial)).occurrences) (mask mate : Expr)
    (pair : (v.nativeTrees P z width (.outer phase trial)).catalystMate=some (mask,mate))
    (wide : dim≤2^W₀) (room : (g).rows<2^W₀) (loaded : CoreLookup.Padded P.routes.core order m)
    (hdr : (H (.outer phase trial)).Loaded m) (supply : v.paidSupply z (.outer phase trial) (v.occurrencePort P z width (.outer phase trial) i).val=true) :
    let len:=extendedLength ((g).ordinal v.sampler π v.depth marks order size) (lenCode v.sampler π v.depth marks v.radius)
    addressPrice len ((L (.outer phase trial)).edge.eval m (i.val:Word W₀)).val≤v.radius ∧
      addressPrice len (mate.eval m (i.val:Word W₀)).val≤v.radius := by
  intro len
  let a : Attempt:=(.outer phase trial)
  let idx:=finCongr (v.occurrence_count P z width a) i
  let f:=v.occurrencePort P z width a i
  let ball:=((H a).enum.symm idx).1
  have pos : f.val<n₀:=by
    by_contra h
    simp [paidSupply, show ¬(v.occurrencePort P z width (.outer phase trial) i).val<n₀ from h] at supply
  let role:= (Fintype.equivFin (PayloadRole N k)).symm ⟨f.val,pos⟩
  have named : (Fintype.equivFin _) role=⟨f.val,pos⟩:=(Fintype.equivFin _).apply_symm_apply _
  have kind : catalystBit role=1:=by
    change (if h : f.val<n₀ then decide (catalystBit ((Fintype.equivFin (PayloadRole N k)).symm ⟨f.val,h⟩)=1) else false)=true at supply
    simpa only [dite_eq_left pos,decide_eq_true_eq] using supply
  obtain ⟨c,axis,roleEq⟩:=catalyst_of_flag role kind
  have selected : (Fintype.equivFin _) (.catalyst c axis : PayloadRole N k)=⟨f.val,pos⟩ :=
    (congrArg (Fintype.equivFin _) roleEq).symm.trans named
  have field : (H a).fieldTerm.eval m (idx.val:Word W₀)=(((H a).enum.symm idx).2.val:Word W₀) :=
    hdr.second idx
  have value : ((H a).fieldTerm.eval m (i.val:Word W₀)).val=f.val :=
    (congrArg Fin.val field).trans (Fin.val_cast_of_lt (f.isLt.trans_le wide))
  have index : ((H a).fieldTerm.eval m (i.val:Word W₀)).val=
      (PortPadding.inject (Nat.le_max_left n₀ n₁) ((Fintype.equivFin _) (.catalyst c axis : PayloadRole N k))).val :=
    value.trans (congrArg Fin.val selected).symm
  have atBall : (H a).ballTerm.eval m (i.val:Word W₀)=(ball.val:Word W₀) := hdr.first idx
  have radii := StripChart.payload_billed_radii bs v.mesh g P.routes F phase trial (fs a).labelStart
    order m (i.val:Word W₀) (ball.val:Word W₀) c axis room wide loaded
  simp only [v.catalyst_boards P z width] at radii
  have hit := radii index atBall
  have ports : radiusMate bs v.mesh g P.routes a=radiusMate s v.mesh g P.routes a := rfl
  have actual : (g).checkedEdge (chooseField dim 0
      (fun j=>((radiusMate s v.mesh g P.routes a j).atRow (H a).ballTerm)) (H a).fieldTerm)=mate :=
    congrArg Prod.snd (Option.some.inj ((v.nativeTrees_mounted_header P z width a).symm.trans pair))
  refine ⟨(g).radius_le π marks order size v.radius axis false hit.1,?_⟩
  rw [←actual,←ports]
  exact (g).radius_le π marks order size v.radius axis true hit.2

set_option maxHeartbeats 1600000 in
private theorem purchased_bounds (phase trial slice jtrial : ℕ) (π : Equiv.Perm (Fin (2^z))) (marks : Marks z v.W k jobs)
    (order : Fin (g).coreRows≃Edges v.sampler z (2^v.W) k)
    (size : jobs*(count z (2^v.W) k*paths z v.sampler.degree v.depth)=(g).boughtRows)
    (m : Memory W₀) (i : Fin (fs (.inner phase trial slice jtrial)).occurrences) (mask mate : Expr)
    (pair : (v.nativeTrees P z width (.inner phase trial slice jtrial)).catalystMate=some (mask,mate))
    (wide : dim≤2^W₀) (room : (g).rows<2^W₀) (loaded : CoreLookup.Padded P.routes.core order m)
    (hdr : (H (.inner phase trial slice jtrial)).Loaded m) (supply : v.paidSupply z (.inner phase trial slice jtrial) (v.occurrencePort P z width (.inner phase trial slice jtrial) i).val=true) :
    let len:=extendedLength ((g).ordinal v.sampler π v.depth marks order size) (lenCode v.sampler π v.depth marks v.radius)
    addressPrice len ((L (.inner phase trial slice jtrial)).edge.eval m (i.val:Word W₀)).val≤v.radius ∧
      addressPrice len (mate.eval m (i.val:Word W₀)).val≤v.radius := by
  intro len
  let a : Attempt:=(.inner phase trial slice jtrial)
  let idx:=finCongr (v.occurrence_count P z width a) i
  let f:=v.occurrencePort P z width a i
  let ball:=((H a).enum.symm idx).1
  have pos : f.val<n₁:=by
    by_contra h
    simp [paidSupply, show ¬(v.occurrencePort P z width (.inner phase trial slice jtrial) i).val<n₁ from h] at supply
  let role:= (Fintype.equivFin (PurchasedRole v.depth k)).symm ⟨f.val,pos⟩
  have named : (Fintype.equivFin _) role=⟨f.val,pos⟩:=(Fintype.equivFin _).apply_symm_apply _
  have kind : catalystBit role=1:=by
    change (if h : f.val<n₁ then decide (catalystBit ((Fintype.equivFin (PurchasedRole v.depth k)).symm ⟨f.val,h⟩)=1) else false)=true at supply
    simpa only [dite_eq_left pos,decide_eq_true_eq] using supply
  obtain ⟨c,axis,roleEq⟩:=catalyst_of_flag role kind
  have selected : (Fintype.equivFin _) (.catalyst c axis : PurchasedRole v.depth k)=⟨f.val,pos⟩ :=
    (congrArg (Fintype.equivFin _) roleEq).symm.trans named
  have field : (H a).fieldTerm.eval m (idx.val:Word W₀)=(((H a).enum.symm idx).2.val:Word W₀) :=
    hdr.second idx
  have value : ((H a).fieldTerm.eval m (i.val:Word W₀)).val=f.val :=
    (congrArg Fin.val field).trans (Fin.val_cast_of_lt (f.isLt.trans_le wide))
  have index : ((H a).fieldTerm.eval m (i.val:Word W₀)).val=
      (PortPadding.inject (Nat.le_max_right n₀ n₁) ((Fintype.equivFin _) (.catalyst c axis : PurchasedRole v.depth k))).val :=
    value.trans (congrArg Fin.val selected).symm
  have atBall : (H a).ballTerm.eval m (i.val:Word W₀)=(ball.val:Word W₀) := hdr.first idx
  have radii := StripChart.purchased_billed_radii bs v.mesh g P.routes F phase trial slice jtrial (fs a).labelStart
    order m (i.val:Word W₀) (ball.val:Word W₀) c axis room wide loaded
  simp only [v.catalyst_boards P z width] at radii
  have hit := radii index atBall
  have ports : radiusMate bs v.mesh g P.routes a=radiusMate s v.mesh g P.routes a := rfl
  have actual : (g).checkedEdge (chooseField dim 0
      (fun j=>((radiusMate s v.mesh g P.routes a j).atRow (H a).ballTerm)) (H a).fieldTerm)=mate :=
    congrArg Prod.snd (Option.some.inj ((v.nativeTrees_mounted_header P z width a).symm.trans pair))
  refine ⟨(g).radius_le π marks order size v.radius axis false hit.1,?_⟩
  rw [←actual,←ports]
  exact (g).radius_le π marks order size v.radius axis true hit.2

theorem physical_catalyst_bounds (a : Attempt) (π : Equiv.Perm (Fin (2^z))) (marks : Marks z v.W k jobs)
    (order : Fin (g).coreRows≃Edges v.sampler z (2^v.W) k)
    (size : jobs*(count z (2^v.W) k*paths z v.sampler.degree v.depth)=(g).boughtRows)
    (m : Memory W₀) (i : Fin (fs a).occurrences) (mask mate : Expr)
    (pair : (v.nativeTrees P z width a).catalystMate=some (mask,mate))
    (wide : dim≤2^W₀) (room : (g).rows<2^W₀) (loaded : CoreLookup.Padded P.routes.core order m)
    (hdr : (H a).Loaded m) (supply : v.paidSupply z a (v.occurrencePort P z width a i).val=true) :
    let len:=extendedLength ((g).ordinal v.sampler π v.depth marks order size) (lenCode v.sampler π v.depth marks v.radius)
    addressPrice len ((L a).edge.eval m (i.val:Word W₀)).val≤v.radius ∧
      addressPrice len (mate.eval m (i.val:Word W₀)).val≤v.radius := by
  cases a with
  | outer phase trial => exact v.payload_bounds P z width r banks src tab dst owners phase trial π marks order size m i mask mate pair wide room loaded hdr supply
  | inner phase trial tick j => exact v.purchased_bounds P z width r banks src tab dst owners phase trial tick j π marks order size m i mask mate pair wide room loaded hdr supply

end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
