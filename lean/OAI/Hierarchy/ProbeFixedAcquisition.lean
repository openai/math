import OAI.Hierarchy.ProbeFixedDatedRepairs

namespace OAI
/-! # Every field of an acquired replay is read from the same native execution -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe AdaptiveProbe.OuterBank ProbeStage ProbeStage.Native CoreBoard
open StripChart StockCommit CatalystArchive PurchaseFrozen StripDirectory PurchaseCT
open scoped Classical
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  {v : FixedProtocolFormat F k p q Q σ Λ} {P : v.Placement} {z width r : ℕ}
  {banks : RouteSettlement.Banks} {src tab dst : ℕ} {owners : Bank}
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.billedAccount P z width r banks src tab dst owners
local notation "G" => v.privateArena P z width
local notation "f" => v.nativeFormats P z width
variable {π : Equiv.Perm (Fin (2^z))} {mem fixture : Memory (wordBits z (2^v.W) copies)}
  (D : v.ReadbackRun P z width r banks src tab dst owners π mem fixture)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
include D in
theorem ReadbackRun.acquired (B : RepairWordBounds v P z width) (u h : ℕ)
    (hu : u<v.mesh.inject+v.mesh.cool) (hh : h<v.mesh.outerFuel) (buy : observedMode C mem u h=3)
    (activation : ∀ (j : Fin v.mesh.reserveSteps) (b : Fin v.mesh.innerFuel),
      observedInnerMode C mem u h j b=1 →
      let s:=outerTime v.mesh v.finish u
      2*((purchaseCount C mem u h:ℝ)*(Λ*(dyadicScale v.W)^p)+(2^z:ℕ)*probeDensity k v.W*purchaseReward k v.W/4)≤
        s*divergence (A).a (A).M (A).coefficient
          (maximizer (A).a (A).M s (A).coefficient (A).box ((A).bank.units width ((A).trial C mem u h)))
          (maximizer (A).a (A).M (replayTime s v.mesh.reserveSteps j) (A).coefficient (A).box
            ((A).bank.units width ((A).inner C mem u h j b)))) :
    Nonempty (Acquisition A C mem u h (2^z) v.actualK v.keepLimit v.loss v.menu.margin
      (probeDensity k v.W) (purchaseReward k v.W) (phaseTime v.finish v.mesh.inject u)) := by
  obtain ⟨later,cut⟩:=outer_slot C mem u h hu hh D.nativeStock.mounted_all
  have e : Event.attempt (.outer u h)∈events (C).mesh := by rw [cut.events];simp
  let data:=v.slot_inputs P z width r banks src tab dst owners mem fixture D.boards (.outer u h) _ later _ cut
  have inventory:=v.stock_cap C rfl G f P.joint.initial (v.emptyReserve P z width).base width
    (v.issued P z width r banks src tab dst owners) mem D.nativeStock
  have bounded:=inventory.1 u hu h hh.le
  have startKey:=D.keys u h
  obtain ⟨rom,incoming,prepared,_⟩:=v.activation_parent P z width r banks src tab dst owners mem π u h hu hh
    D.nativeStock.mounted_all D.geometry D.heap startKey.1 startKey.2
  have carry:=v.replay_purchase_feed P z width r banks src tab dst owners mem fixture D.nativeStock D.steps
    D.digitBudget D.endFits D.payload (by have:=D.dimension;omega) D.slices u h hu hh data buy
  have cost:=v.purchase_initial_cash P z width r banks src tab dst owners mem fixture u h e cut.currentReady
    data buy bounded D.positive π rom D.archives hu hh incoming prepared
  have fee:=v.purchase_fee_bound P z width r banks src tab dst owners mem u h π rom D.archives hu hh incoming prepared
  have payload_width : (A).payloadWidth = width := rfl
  have reserve_steps : (C).mesh.reserveSteps = v.mesh.reserveSteps := rfl
  refine ⟨{
    fee:=Λ*(dyadicScale v.W)^p
    feeBound:=Λ*(dyadicScale v.W)^p
    dimension:=(1+2*(publicStages v.W)*k:ℕ)
    boxMax:=upperBox (publicStages v.W) v.radius
    mesh_pos:=v.clock.reserve_pos
    mesh_fits:=v.clock.reserve_width.trans D.widths
    dimension_bound:=(v.acquisition_dimension z).le
    cap_pos:=(Nat.cast_nonneg _).trans (le_max_left ..)
    cap_bound:=fun i=>(v.acquisition_box z i).2
    entry_fits:=bounded
    fee_bound:=fee.2
    fuel_budget:=v.acquisition_fuel
    initial_cash:=cost.le
    initial_stock:=fun i=>(v.purchase_initial_stock P z width r banks src tab dst owners mem fixture u h e cut.currentReady
      data buy bounded i).1
    terminal:=carry.1
    repaired:=?_
    skipped:=fun j hj b hb dead=>D.inner_skipped u h j b hu hh hj hb dead
    retained:=fun j hj i=>(carry.2 j hj).1 i
    charged:=fun j hj=>(carry.2 j hj).2.le
    activation:=?_
    mesh_error:=v.acquisition_mesh z width u D.widths hu.le}⟩
  · intro j hj b hb failed
    simpa only [payload_width, reserve_steps, v.replay_clock] using D.inner_failed B u h j b hu hh hj hb failed
  · intro j hj b hb advance
    simpa only [payload_width, reserve_steps, v.phase_clock] using activation ⟨j,hj⟩ ⟨b,hb⟩ advance

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
