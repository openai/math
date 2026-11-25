import OAI.Hierarchy.ProbeInstalledReplayPayment
import OAI.Hierarchy.ProtocolRAMCalendarLiveCount

namespace OAI
/-! # Translating the physical replay payment into the chronological signed account -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe OuterBank ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen StripDirectory
open scoped Classical Fin.CommRing
variable {z d k q goods r edges : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))

theorem live_activation_iff (c : Mesh) (arena : Arena) (initial : ℕ) (build : Attempt→ℕ→Format z d k q goods)
    (capacity : ∀u addr,(build u addr).pricedArea=(build u initial).pricedArea)
    (atStock : ∀u addr,(build u addr).market.shelf.stockBase=addr) (finish a M : ℝ) (W : ℕ) (hd : d=2^W)
    (width precision : ℕ) (fee ρ reward cash : ℝ) (billed : Event→WordRows)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr)
    (ids : Attempt→Fin goods→Expr) (mem fixture : Shelf.Mem z d) (π : Equiv.Perm (Fin (2^z))) (p h j b total : ℕ) :
    let T:=probeHeat W
    let fm:=liveFormats c arena initial build
    let prices:=publicPhase (2*rounds d+1) a M W T 1 width precision
    let C:=pricedInstalled c finish prices fm feeds sink idBase role ids
    let u:=Attempt.outer p h
    let v:= (fm u).atTime c finish prices u
    let u':=Attempt.inner p h j b
    let s:=outerTime c finish p
    let t:=reserveTime c finish p j
    let oldState:=trialState C mem p h
    let frozen:=v.failures.pass.apply ((guard C u).apply oldState)
    let tested:=replayScoreMemory C mem p h j b
    let A:=nativeAccounts («N»:=N) c arena fm initial width billed cash a M ((W:ℝ)⁻¹^4/(N*T^2)) (routeCap N M)
    let live:=Fintype.card (LiveChains v.sampler π v.depth (actualMarks (k:=k) v.shelf v.phase v.temperature v.kind frozen))
    let later:=publicPhase (2*rounds d+1) a M W T t width precision
    ArchiveRoom C mem total → p< total → h< c.outerFuel → v.rows≤2^(fm u).batch.decisionBits →
    observedMode C mem p h=3 → v.shelf.Incoming (k:=k) v.sampler π v.depth v.phase v.temperature v.kind frozen →
    (∀i : Key z d k,v.shelf.Prepared v.sampler v.depth fixture i frozen) →
    v.shelf.stockBase+PurchaseInventory.footprint z N k≤ C.stopAt u →
    v.shelf.stockBase+PurchaseInventory.footprint z N k≤ v.failures.base →
    ready C (.attempt u') (innerState C mem p h j b) →
    (∀i : Commodity (Fin (2^z)) N k,protected C ((fm u').market.shelf.stockBase+PurchaseInventory.slot i) (.attempt u')) →
    ((2*((purchaseCount C mem p h:ℝ)*fee+(2^z:ℕ)*ρ*reward/4) ≤
      s*divergence A.a A.M A.coefficient
        (maximizer A.a A.M s A.coefficient A.box (A.bank.units A.payloadWidth (A.trial C mem p h)))
        (maximizer A.a A.M (replayTime s C.mesh.reserveSteps j) A.coefficient A.box
          (A.bank.units A.payloadWidth (A.inner C mem p h j b)))) ↔
    2*((live:ℝ)*fee+(2^z:ℕ)*ρ*reward/4) ≤ s*divergence a M (bonus (probeBonus W))
      (stageQuotes (z:=z) (d:=d) (k:=k) v.phase 0 1 v.shelf.stockBase frozen)
      (stageQuotes (z:=z) (d:=d) (k:=k) later 0 1 (fm u').market.shelf.stockBase tested)) := by
  intro T fm prices C u v u' s t oldState frozen tested A live later archive hp hh padded bought incoming prepared lowGuard lowFailures step protectedStock
  have quantity:=priced_purchaseCount c finish prices fm feeds sink idBase role ids mem p h total π fixture incoming prepared archive hp hh padded bought
  have frozenPrice:=outer_frozen_quotes (k:=k) C mem v p h 0 1 v.phase lowGuard lowFailures
  have postPrice:=replay_stock_quotes (k:=k) C mem p h j b 0 1 (fm u').market.shelf.stockBase later step protectedStock
  have first:=native_live_quotes c arena initial build capacity atStock width precision billed cash a M W T s u oldState
  have second:=native_live_quotes c arena initial build capacity atStock width precision billed cash a M W T t u' (innerState C mem p h j b)
  change maximizer A.a A.M s A.coefficient A.box (A.bank.units A.payloadWidth (A.trial C mem p h))=
    stageQuotes v.phase 0 1 v.shelf.stockBase oldState at first
  change maximizer A.a A.M (replayTime s C.mesh.reserveSteps j) A.coefficient A.box
    (A.bank.units A.payloadWidth (A.inner C mem p h j b))=stageQuotes later 0 1 (fm u').market.shelf.stockBase
    (innerState C mem p h j b) at second
  have stages : N=publicStages W := by subst d;exact fixed_stage_count z W
  have bonusEq : A.coefficient=bonus (probeBonus W) := by
    have scalar : (W:ℝ)⁻¹^4/(N*T^2)=probeBonus W := by rw [stages];rfl
    change bonus ((W:ℝ)⁻¹^4/(N*T^2))=_
    rw [scalar]
  rw [quantity,first,second,←frozenPrice,←postPrice,bonusEq]
  exact Iff.rfl

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
