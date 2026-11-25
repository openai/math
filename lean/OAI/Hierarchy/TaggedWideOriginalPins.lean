import OAI.Hierarchy.TaggedWireFixedAdmission
import OAI.Hierarchy.TaggedWideSelectorBill
import OAI.Hierarchy.TaggedWireBoardLayout
import OAI.Hierarchy.ProtocolRAMCoreRouteImage

namespace OAI
/-! # The actual selector and exterior pin counts of the fixed pair of native programs -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart CoreBoard
open TaggedPrune WireTelescope Tagged
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "d" => 2^v.W

def wideMarketFactor := publicStages v.W*(2*k)*v.sampler.degree^v.depth

set_option maxHeartbeats 1000000 in
theorem original_candidates (P : v.Placement) (h width r : ℕ) (banks : RouteSettlement.Banks)
    (src tbl dst : ℕ) (owners : Bank) (a : Attempt) :
    ((v.nativeChart P h width r banks src tbl dst owners).layout a).candidates=
      v.wideMarketFactor*2^h := by
  have rows : (v.nativeFormats P h width a).market.rows =
      PurchaseFrozen.count h d k * PurchaseFrozen.paths h v.sampler.degree v.depth :=
    StripChart.candidate_count F v.mesh (v.privateArena P h width) P.joint.initial
      (v.nativeBoards P h width) a
  change (v.nativeFormats P h width a).market.rows=_
  rw [rows]
  change (Stages h d*(2*k))*(2^h*v.sampler.degree^v.depth)=
    (publicStages v.W*(2*k)*v.sampler.degree^v.depth)*2^h
  rw [show Stages h d=publicStages v.W from fixed_stage_count h v.W]
  ring

def wideSelectorFactor :=
  1+8*((v.mesh.inject+v.mesh.cool)*(v.mesh.outerFuel*(1+v.mesh.reserveSteps*(v.mesh.innerFuel+1))+1))*
    v.wideMarketFactor*v.menu.alphabet

set_option maxHeartbeats 1000000 in
theorem original_selectors (P : v.Placement) (h width r : ℕ) (banks : RouteSettlement.Banks)
    (src tbl dst : ℕ) (owners : Bank) (fits copiesFit) (positive : 0<h)
    (clock : 2*(rounds d+1)+3+rounds d*stride d copies≤h) :
    h*2^h+CalendarTape.bits (v.nativeSelector P h width r banks src tbl dst owners fits copiesFit).format.slot
      (events v.mesh)≤v.wideSelectorFactor*(2^h*h) := by
  let D:=v.nativeSelector P h width r banks src tbl dst owners fits copiesFit
  have rawWidth : wordBits h d copies≤4*(h+1):=by rw [wordBits_linear];omega
  have total:=D.format.selector_bill h v.wideMarketFactor positive rawWidth
    (fun a=>(v.original_candidates P h width r banks src tbl dst owners a).le)
  have alphabet:=(v.catalogue_words (v.seed P h width) width).1
  change h*2^h+CalendarTape.bits D.format.slot (events v.mesh) ≤
    (1+8*((v.mesh.inject+v.mesh.cool)*(v.mesh.outerFuel*(1+v.mesh.reserveSteps*(v.mesh.innerFuel+1))+1))*
      v.wideMarketFactor*(catalogue F (v.configured (v.seed P h width)) v.cost).alphabet)*(2^h*h) at total
  simpa only [alphabet,wideSelectorFactor] using total

def wideExteriorFactor := 3+2*k*(siteFactor d k)*CatalystArchive.fuel v.mesh

private theorem openPins_count (h width k size : ℕ) :
    Fintype.card (OpenPins h width (fun _ : Fin k => size)) = pins h width+k*size*2 := by
  have wires : Nat.card (Catalyst.Wire (fun _ : Fin k => size))=k*size := by
    exact (Nat.card_congr (Equiv.sigmaEquivProd (Fin k) (Fin size))).trans
      (by simp only [Nat.card_prod,Nat.card_fin])
  have sides : Nat.card Bool=2 := Nat.card_eq_fintype_card.trans Fintype.card_bool
  rw [←Nat.card_eq_fintype_card]
  simp only [OpenPins,Catalyst.Port,Nat.card_sum,Nat.card_prod,Nat.card_fin,wires,sides]

theorem original_exterior (h width : ℕ) (paid : h≤width) :
    Fintype.card (OpenPins h width (fun _ : Fin k=>Fintype.card (Columns h d)*(CatalystArchive.fuel v.mesh*width)))≤
      v.wideExteriorFactor*(2^h*width) := by
  have cols:=CoreRoute.column_count h d k (Nat.two_pow_pos _)
  rw [openPins_count]
  unfold pins wideExteriorFactor
  calc
    _ ≤ 2^h*width+(2^h*width+2^h*width)+
        k*((siteFactor d k*2^h)*(CatalystArchive.fuel v.mesh*width))*2 := by
      exact Nat.add_le_add
        (Nat.add_le_add_left (Nat.add_le_add_right (Nat.mul_le_mul_left (2^h) paid) _) _)
        (Nat.mul_le_mul_right 2 (Nat.mul_le_mul_left k
          (Nat.mul_le_mul_right (CatalystArchive.fuel v.mesh*width) cols)))
    _ = _ := by ring

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
