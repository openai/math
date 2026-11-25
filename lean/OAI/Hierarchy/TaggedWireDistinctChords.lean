import OAI.Hierarchy.ProbeSortedCommodityChords
import OAI.Hierarchy.TaggedWireHistorySockets

namespace OAI
/-! # Parallel-wire order inside the goods and catalyst blocks -/
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open WireTelescope AdaptiveProbe ReportSockets
variable {h W k attempts : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
  (marks : Marks h W k attempts)

theorem sorted_goods_injective : Function.Injective (fun g : Commodity (Fin (2^h)) (Stages h (2^W)) k=>
    sorted S π depth marks (.inr (.inl g))) :=
  ordered_row_injective (name (h:=h) (W:=W) (k:=k)).toEmbedding (commodityEnds π)
    (commodity_ends_injective π) (commodity_input_ne_output π)

theorem sorted_catalysts_injective : Function.Injective (fun a : Columns h (2^W)×Fin k=>
    sorted S π depth marks (.inr (.inr a))) := by
  apply ordered_row_injective (name (h:=h) (W:=W) (k:=k)).toEmbedding
    (fun a : Columns h (2^W)×Fin k=>(((a.1,some (a.2,false)),(a.1,some (a.2,true))) : _×_))
    catalyst_ends_injective
  intro a b eqn
  have same:=Option.some.inj (congrArg (fun s : Site h (2^W) k=>s.2) eqn)
  have impossible : false=true:=congrArg Prod.snd same
  contradiction

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles

end OAI
