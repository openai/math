import OAI.Hierarchy.ProbeCoreWalks
import OAI.Hierarchy.ProbePayloadPlacement
import OAI.Hierarchy.ProbeChainPlacement
import OAI.Hierarchy.ProbePayloadAccounts
import OAI.Hierarchy.ProbeStripAccounts

namespace OAI
/-! # Endpoints of the original commodity held by an elected strip row -/

namespace Hierarchy.ProbeStage.CoreBoard
open AdaptiveProbe
open scoped Classical

variable {h d k : ℕ} (π : Equiv.Perm (Fin (2^h)))

theorem earned_payload_goods (r : Fin (2^h)) (u : PayloadStrip.Quotes (Stages h d) k) :
    let pair := LocalCommodity.extraEnds (PayloadStrip.commodity (Stages h d) k)
      (PayloadStrip.noProbe (Stages h d)) (.inl u)
    commodityEnds π (PayloadStrip.rowAddress r u) =
      (Prod.map (payloadPlace π r) id pair.left,Prod.map (payloadPlace π r) id pair.right) := by
  rcases u with _ | ⟨t,axis,side⟩
  · simp only [PayloadStrip.rowAddress,commodityEnds,PayloadStrip.commodity,PayloadStrip.external,
      LocalCommodity.extraEnds,LocalCommodity.ends,Prod.map, id_eq,payloadPlace_input,payloadPlace_output]
  · simp only [PayloadStrip.rowAddress,commodityEnds,PayloadStrip.commodity,LocalCommodity.extraEnds,
      LocalCommodity.ends,Prod.map,id_eq,payloadPlace_stage_in,payloadPlace_stage_out,inputCol,outputCol]

theorem earned_purchase_goods (S : PurchaseSampler) (depth : ℕ)
    (marks : StageAt h d→(Fin k×Bool)→Finset (Fin (2^h))) (path : LiveChains S π depth marks)
    (u : ChainStrip.Axes depth k) :
    let pair := LocalCommodity.extraEnds (ChainStrip.commodity depth k) (ChainStrip.probe depth) (.inl u)
    -- This is the same original stage-column inclusion used by `CatalogueRows.retainedCol`.
    let place : ChainStrip.Columns depth → Columns h d := fun c=>.inr (.inl (stripPlace S π depth marks path c))
    commodityEnds π (stripAddress S π depth marks path u) =
      (Prod.map place id pair.left,Prod.map place id pair.right) := by
  rcases u with ⟨j,axis,side⟩
  have same := (live_in_ball S π depth marks path j).1
  simp only [stripAddress,commodityEnds,ChainStrip.commodity,LocalCommodity.extraEnds,
    LocalCommodity.ends,Prod.map,id_eq,stripPlace_in,stripPlace_out,inputCol,outputCol,same]

end Hierarchy.ProbeStage.CoreBoard

end OAI
