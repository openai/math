import OAI.Hierarchy.ProbeFixedActivationDensity
import OAI.Hierarchy.ProbeFixedReplayCalibration
import OAI.Hierarchy.ProbeFixedDiscrepancyCeilings

namespace OAI
/-! # The complete activation field of an observed purchase in the physical priced calendar -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart
open PurchaseFrozen PurchaseCT StripDirectory
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

/-- On every sufficiently large dimension the native priced calendar meets
the activation inequality for every buying date and every successful replay,
using the single booted tape and its chronological capped stock. -/
theorem purchase_activation :
    ∀ᶠ z : ℕ in Filter.atTop,∀ (P : v.Placement) (width r : ℕ) (banks : RouteSettlement.Banks)
      (src tab dst : ℕ) (owners : Bank) (mem : Shelf.Mem z (2^v.W)) (π : Equiv.Perm (Fin (2^z)))
      (u : Fin (v.mesh.inject+v.mesh.cool)) (h : Fin v.mesh.outerFuel)
      (j : Fin v.mesh.reserveSteps) (b : Fin v.mesh.innerFuel),
    let w:=wordBits z (2^v.W) copies
    let N:=Stages z (2^v.W)
    let C:=v.nativeChart P z width r banks src tab dst owners
    let A:=v.billedAccount P z width r banks src tab dst owners
    let H:=v.publicHeader P z width
    let G:=v.privateArena P z width
    let key:=stratumHeader z (2^v.W) k v.sampler.degree v.depth ((v.nativeBoards P z width).stratumHeader u h)
    let s:=outerTime v.mesh v.finish u
    StockBound.Run C (v.stockBanks P z width) mem z N k (v.keepLimit*width) →
    H.Resident mem → InitialPrices P.joint z N k (DeadlineROM.prices v.mesh v.finish (v.basePhase width)) (fun _=>0) mem →
    P.joint.precision=v.precision → P.joint.cap*P.joint.width=v.keepLimit*width →
    v.keepLimit*width+1≤2^z → width≤2^z →
    Shelf.Geometry π mem → heapEnd z (2^v.W) copies≤G.first → key.stop≤G.first → key.Loaded mem →
    G.endAddress v.mesh<2^w → ArchiveRoom C mem (v.mesh.inject+v.mesh.cool) →
    observedMode C mem u h=3 → observedInnerMode C mem u h j b=1 →
    2*((purchaseCount C mem u h:ℝ)*(Λ*(dyadicScale v.W)^p)+(2^z:ℕ)*probeDensity k v.W*purchaseReward k v.W/4) ≤
      s*divergence A.a A.M A.coefficient
        (maximizer A.a A.M s A.coefficient A.box (A.bank.units A.payloadWidth (A.trial C mem u h)))
        (maximizer A.a A.M (OuterBank.replayTime s C.mesh.reserveSteps j) A.coefficient A.box
          (A.bank.units A.payloadWidth (A.inner C mem u h j b))) := by
  filter_upwards [v.dated_purchase_density_uniform,v.discrepancy_word_room,Filter.eventually_ge_atTop v.stripHeight]
    with z dense fits late
  intro P width r banks src tab dst owners mem π u h j b w N C A H G key s stock «public» prices precision budget
    scale payload geometry heap keyRoom loaded space archive buy advance
  have words:=fits P width
  have acquired:=dense P width r banks src tab dst owners mem π u h stock «public» prices precision budget scale
    geometry heap keyRoom loaded space payload buy
  obtain ⟨fixture,input,prepared,header⟩:=v.activation_parent P z width r banks src tab dst owners mem π u h
    u.isLt h.isLt stock.mounted_all geometry heap keyRoom loaded
  have stride : v.keepLimit*width<(JointHeader.scores P.joint z N k).stride:=by
    change v.keepLimit*width<P.joint.cap*P.joint.width+1
    rw [budget]
    omega
  exact v.purchase_activation_of_density P z width r banks src tab dst owners mem fixture π u h j b late payload «public»
    (fun _=>0) prices stock stride words.2 keyRoom archive buy advance input prepared header acquired

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
