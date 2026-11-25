import OAI.Hierarchy.ProbeInstalledReplayStock

namespace OAI
/-! # Physical price operands at the original frozen purchase and the later native test -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe OuterBank ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen
open scoped Classical Fin.CommRing
variable {z d k w q goods : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))

/-- Stock words are read in the packed stage order, with one physical cell per signed commodity. -/
theorem stageQuotes_frame (s : PhasePrice) (pay axis base : ℕ) (old new : Memory w)
    (same : ∀i : Commodity (Fin (2^z)) N k,new (base+PurchaseInventory.slot i)=old (base+PurchaseInventory.slot i)) :
    stageQuotes (z:=z) (d:=d) (k:=k) s pay axis base new=stageQuotes s pay axis base old := by
  funext i
  rcases i with row|⟨⟨row,t⟩,j⟩
  · exact congrArg (fun word : Word w=>s.quote pay word.val) (same (.inl row))
  · exact congrArg (fun word : Word w=>s.quote axis word.val) (same (.inr ((row,t),j)))

theorem outer_frozen_quotes (C : Chart w q goods) (mem : Memory w) (v : Market z d k)
    (p h pay axis : ℕ) (s : PhasePrice) (beforeGuard : v.shelf.stockBase+PurchaseInventory.footprint z N k≤ C.stopAt (.outer p h))
    (beforeFailures : v.shelf.stockBase+PurchaseInventory.footprint z N k≤ v.failures.base) :
    let current:=trialState C mem p h
    let frozen:=v.failures.pass.apply ((guard C (.outer p h)).apply current)
    stageQuotes (z:=z) (d:=d) (k:=k) s pay axis v.shelf.stockBase frozen=
      stageQuotes s pay axis v.shelf.stockBase current := by
  intro current frozen
  apply stageQuotes_frame
  intro i
  have inside:=Nat.add_lt_add_left (PurchaseInventory.slot_lt i) v.shelf.stockBase
  have low:=inside.trans_le beforeGuard
  change v.failures.pass.apply ((guard C (.outer p h)).apply current) _=_
  rw [v.failures.frame _ _ (.inl (inside.trans_le beforeFailures))]
  simp [guard,Pass.apply,image,ThreeFlat.RAM.fillSegment,not_le.mpr low]

theorem replay_stock_quotes (C : Chart w q goods) (mem : Memory w) (p h j b pay axis base : ℕ) (s : PhasePrice)
    (step : ready C (.attempt (.inner p h j b)) (innerState C mem p h j b))
    (keep : ∀i : Commodity (Fin (2^z)) N k,protected C (base+PurchaseInventory.slot i) (.attempt (.inner p h j b))) :
    stageQuotes (z:=z) (d:=d) (k:=k) s pay axis base (replayScoreMemory C mem p h j b)=
      stageQuotes s pay axis base (innerState C mem p h j b) := by
  apply stageQuotes_frame
  exact fun i=>replay_prior C mem p h j b _ step (keep i)

theorem real_post_quote (a M W T t : ℝ) (width precision base : ℕ) (m : Memory w) :
    let s:=publicPhase (2*rounds d+1) a M W T t width precision
    (fun i : Commodity (Fin (2^z)) N k=>s.quote (PurchaseInventory.lane i)
      (PurchaseInventory.stock base m i))=stageQuotes s 0 1 base m := by
  intro s
  funext i
  rcases i with p|⟨⟨p,stage⟩,j⟩
  · rfl
  · let c : Commodity (Fin (2^z)) (2*rounds d+1) k:=.inr ((p,stageNumber stage),j)
    exact public_lane_quote a M W T t width precision (PurchaseInventory.stock base m c) c

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
