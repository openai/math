import OAI.Hierarchy.DescentIssuedNodeOrder
import OAI.Hierarchy.DescentEpochHistory

namespace OAI
/-! # Matched-pair order families on the input branches of a fixed schedule -/

namespace Hierarchy.DescentTerminalEpochDecoder
open DescentSixParty DescentStageEdgeReceipt
noncomputable section
universe v
variable {F P : Type} [Field F] {d : ℕ} {portBits : P→ℕ} {u ε : ℝ}
variable (G : PoweredGadget F) (hu : 0≤u) (he : 0≤ε)

abbrev OrdersAt {H : Histories F d P portBits} (input : SubroundInput H G (u:=u) he) :=
  ∀c,ScanNumbers he (input.placement c)

def ScheduleOrders : {t : ℕ} → {H : Histories.{0, 0, v} F d P portBits} →
    Schedule G (u:=u) he t H → Type v
  | 0,_,_ => PUnit
  | _+1,_,run => OrdersAt G he run.1 × ScheduleOrders run.2

def EpochOrders {t h C Ht : ℕ} : {J : ℕ} → {H : Histories.{0, 0, v} F d P portBits} →
    Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H → Type v
  | 0,_,_ => PUnit
  | _+1,_,run => ScheduleOrders G he run.1.subrounds × EpochOrders run.2

end
end Hierarchy.DescentTerminalEpochDecoder

end OAI
