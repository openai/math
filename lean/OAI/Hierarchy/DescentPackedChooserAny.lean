import OAI.Hierarchy.DescentPackedMatchChooserInput
import OAI.Hierarchy.DescentPackedPhaseAny

namespace OAI
/-! # Fixed-time execution from every malformed or accepted ordinary calendar header -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Chooser
open DescentSixParty DescentSIMDLookup DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k G L ℓ w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (hosts : V≃Fin L) (hv : L≤2^ℓ)
    (C : Layout) (b quota payload unit ratio : ℕ)
local notation "M" => lanes payload unit
local notation "H" => 2^ℓ

theorem Geometry.any (rs : DescentColonies.DynamicSplit.Roster ℓ A.degree)
    (geom : Geometry (G:=G) (w:=w) A hosts hv C b quota payload unit ratio rs) (m : Memory w) :
    ∃o,(C.program A.degree k b quota H G M w).Exec m o (C.ticks A.degree k b quota H G M w) := by
  let shape:=(1+b+2*quota)*2^k
  have span : max shape (b*2^k)≤unit :=
    (max_le (le_max_right ..) ((Nat.mul_le_mul_right (2^k) (show b≤1+b+2*quota by omega)).trans (le_max_right ..))).trans geom.covered
  have capM : M*max shape (b*2^k)≤w/2 := by
    have floor : M*(2*unit)≤payload := Nat.div_mul_le_self _ _
    have room:=Nat.mul_le_mul_left M span
    rw [Nat.mul_left_comm M 2 unit] at floor
    have embed:=geom.embed
    omega
  have lo : C.chart.weights.base≤C.marked.base := (Nat.le_add_right ..).trans geom.apart
  have extent : C.chart.weights.base+H*chunks G M<2^w := (Nat.add_le_add_right lo _).trans_lt geom.extent
  have src : C.source.Fits w C.marked.base := ⟨geom.sourceFits.1,geom.sourceFits.2.1,geom.sourceFits.2.2.trans lo⟩
  obtain ⟨mid,start⟩:=PackedCensus.any (C.census k b quota H G M false) (C.census k b quota H G M true)
    (Phase.CensusTables.fits C.source C.origin C.chart.weights.base false geom.sourceFits geom.sourceRows geom.censusEnd extent capM)
    (Phase.CensusTables.fits C.source C.origin C.marked.base true src geom.sourceRows (geom.censusEnd.trans lo) geom.extent capM) m
  have lanes' : lanes (2*Phase.unit k b*M) (Phase.unit k b)=M :=
    Nat.mul_div_cancel_left _ (by dsimp [Phase.unit];omega)
  have layout:=Phase.Arena.space C.chart C.marked A.fieldBits H G geom.room
  rw [lanes'] at layout
  obtain ⟨out,run⟩:=Phase.any (C.shelves A.degree k b M) layout mid
  exact ⟨out,start.then run⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Chooser

end OAI
