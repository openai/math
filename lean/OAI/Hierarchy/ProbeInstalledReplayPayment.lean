import OAI.Hierarchy.ProbeMarketStockFrame
import OAI.Hierarchy.ProbePurchaseArchiveLifetime
import OAI.Hierarchy.ProbeDiscrepancyBoot

namespace OAI
/-! # A low native replay check pays the divergence of the actual purchased stock -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe OuterBank ProbeStage ProbeStage.Native PurchaseCT PurchaseStage PurchaseFrozen StripDirectory
open scoped Classical Fin.CommRing
variable {z d k W M J q goods r edges : ℕ} {P σ Λ ε : ℝ}
local notation "B" => wordBits z d copies
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))

theorem installed_replay_payment (F : Type*) [Field F] [SiteNaming (ChainStrip.Site (publicTiles k W-1) k)]
    (cfg : PublicCalibration F k P σ Λ W M ε) (hk : 0< k) (hd : d=2^W)
    (c : Mesh) (finish a : ℝ) (ha : 0< a) (width precision : ℕ) (prec : 0< precision)
    (format : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn) (sink : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (mem : Shelf.Mem z d)
    (p h j b : ℕ) (sh : Shelf) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z))) (frozen : Shelf.Mem z d)
    (start : ℕ) (test : StripTest (Fintype.card (ChainStrip.Axes (publicTiles k W-1) k))) (price offset stock : Bank)
    (stride : ℕ) (global : ColumnSite (StageColumns z d) k ↪Fin J)
    (nFit : 2^z≤2^B) (keyFit : count z d k≤2^B) (wide : 0< B) (stockRoom : PurchaseInventory.footprint z N k≤2^B)
    (fit : ∀v : Σ _ : StageAt z d, Fin (2^z),∀u : Fin k×Bool,
      PurchaseInventory.stock sh.stockBase frozen (.inr ((v.2,stageNumber v.1),u))< sh.table.size)
    (hQ : 0< test.precision) (hs : 0< outerTime c finish p) (ss : outerTime c finish p≤1)
    (hs' : 0< reserveTime c finish p j) :
    let s:=outerTime c finish p
    let t:=reserveTime c finish p j
    let T:=probeHeat W
    let depth:=publicTiles k W-1
    let ρ:=probeDensity k W
    let cut:=failureTolerance (publicStages W) ε ρ
    let prices:=publicPhase (2*rounds d+1) a M W T 1 width precision
    let first:=publicPhase (2*rounds d+1) a M W T s width precision
    let later:=publicPhase (2*rounds d+1) a M W T t width precision
    let C:=pricedInstalled c finish prices format feeds sink idBase role ids
    let u:=Attempt.inner p h j b
    let m:=replayScoreMemory C mem p h j b
    let mark:=actualMarks sh first T 1 frozen (k:=k)
    let live:=Fintype.card (LiveChains S π depth mark)
    (depth+1)*paths z S.degree depth≤2^B → count z d k*paths z S.degree depth≤2^B →
    test.tolerance=cut → 1/(precision:ℝ)+1/(test.precision:ℝ)≤ cut →
    (format u).market.failures=(checkedPurchase (z:=z) (d:=d) sh S start test price offset stock).failure →
    ArchiveReads sh S π depth start first T 1 frozen m k →
    QuoteCells (U:=Commodity (Fin (2^z)) N k) later m price offset stock
      PurchaseInventory.slot PurchaseInventory.lane (PurchaseInventory.stock stock.base m) stride →
    (∀i : Commodity (Fin (2^z)) N k,later.word (PurchaseInventory.lane i) (PurchaseInventory.stock stock.base m i)< test.radix) →
    (∀v,test.table.read m ((finFunctionFinEquiv v).val:Word B)=
      (discrepancyCode (depth:=depth) (k:=k) F later later.M test.precision test.radix v:Word B) ∧
      discrepancyCode (depth:=depth) (k:=k) F later later.M test.precision test.radix v<2^B) →
    ρ*(2^z:ℕ)≤ live → TestRoom (repair C u) B → observedInnerMode C mem p h j b=1 →
    2*((live:ℝ)*(Λ*(dyadicScale W)^P)+(2^z:ℕ)*ρ*(probeBonus W*probeMotion k W/8)/4) ≤
      s*divergence a M (bonus (probeBonus W)) (stageQuotes (z:=z) (d:=d) (k:=k) first 0 1 sh.stockBase frozen)
        (stageQuotes (z:=z) (d:=d) (k:=k) later 0 1 stock.base m) := by
  intro s t T depth ρ cut prices first later C u m mark live sizes all tol resolution installed archive quotes digit words many space advance
  have deadline_later : deadline c finish prices u=later := rfl
  have score := priced_replay_words F c finish prices format feeds sink idBase role ids mem p h j b sh S π start hk
    first T 1 frozen test price offset stock stride (PurchaseInventory.stock stock.base m) cut tol global keyFit
    sizes all wide stockRoom
  dsimp only at score
  rw [deadline_later] at score
  have bonusNonneg (i : Commodity (Fin (2^z)) N k) : 0≤ later.bonus (PurchaseInventory.lane i) := by
    dsimp [later,publicPhase]
    split <;> positivity
  have capNonneg (i : Commodity (Fin (2^z)) N k) : 0≤ later.cap (PurchaseInventory.lane i) := by
    dsimp [later,publicPhase]
    split <;> positivity
  obtain ⟨_,bound,pick,measured⟩:=score installed archive quotes ha bonusNonneg (Nat.cast_nonneg M) hs'
    capNonneg prec hQ resolution digit (fun v=>(words v).1) (fun v=>(words v).2)
  have physical:=physical_payment cfg hk hd a s t ha hs ss hs' width precision sh S π frozen m stock.base
    global C mem p h j b nFit fit hQ space advance
  simp only [Nat.cast_pow,Nat.cast_ofNat] at many bound ⊢
  apply physical many bound pick
  intro path
  have fixed:=measured path
  rw [real_post_quote a M W T t width precision stock.base m] at fixed
  exact fixed

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
