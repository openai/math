import OAI.Hierarchy.DescentTerminalEpochDecoder
import OAI.Hierarchy.DescentEpochOrderTypes

namespace OAI
/-! # Using each incoming branch's actual published matched-row ordering -/
namespace Hierarchy.DescentTerminalEpochDecoder
open DescentSixParty DescentTerminalEpochChart DescentTerminalEpochBits DescentKernelHistory.BitDescription
open DescentInitialHost DescentSeedRoot Computability.BorderVNP.Crossing DescentStageEdgeReceipt
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {portBits : P→ℕ} {u ε : ℝ}
variable (G : PoweredGadget F) (hu : 0≤u) (he : 0≤ε)

variable {S Z : Type} {bits : Z→S→Bool} {ok : (S→Bool)→Prop}

def extendWith {H : Histories F d P portBits} (input : SubroundInput H G (u:=u) he) (order : OrdersAt G he input)
    {source : H.Choice→Z} (old : Chart bits ok source) :
    Chart bits ok (fun v : (H.extend he input).Choice=>source v.1) :=
  DescentTerminalEpochChart.extend old (count G he input) order (count_le G he input)
    (fun c=>(scannedRows he (input.placement c)).profile)

def scheduledWith : {t : ℕ} → {H : Histories F d P portBits} → (plan : Schedule G (u:=u) he t H) →
    ScheduleOrders G he plan → {source : H.Choice→Z} → Chart bits ok source →
    Chart bits ok (fun c=>source (Schedule.seedChoice G he plan c))
  | 0,_,_,_,_,old => old
  | _+1,_,plan,order,_,old => scheduledWith plan.2 order.2 (extendWith G he plan.1 order.1 old)

def epochsWith {t h C Ht : ℕ} : {J : ℕ} → {H : Histories F d P portBits} →
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H) → EpochOrders G hu he run →
    {source : H.Choice→Z} → Chart bits ok source → Chart bits ok (fun c=>source (Epochs.seedChoice G hu he run c))
  | 0,_,_,_,_,old => old
  | _+1,_,run,order,_,old => epochsWith run.2 order.2 (scheduledWith G he run.1.subrounds order.1 old)

theorem scheduleWith_size {t : ℕ} {H : Histories F d P portBits} (plan : Schedule G (u:=u) he t H)
    (order : ScheduleOrders G he plan) {source : H.Choice→Z} (old : Chart bits ok source) :
    Fintype.card (scheduledWith G he plan order old).Pin =
      Fintype.card old.Pin + scheduleSeats G he plan*DescentTerminalEpochBits.width G.C := by
  induction t generalizing H with
  | zero =>
    simp only [scheduledWith, scheduleSeats, Nat.zero_mul, Nat.add_zero];
      exact Fintype.card_congr (Equiv.refl _)
  | succ t ih=>
    rw [scheduledWith,scheduleSeats,ih]
    change Fintype.card (old.Pin ⊕ Pins G.C (maxSeats G he plan.1)) + _=_
    simp [Pins]
    ring

theorem epochsWith_size {t h C Ht J : ℕ} {H : Histories F d P portBits}
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H) (order : EpochOrders G hu he run)
    {source : H.Choice→Z} (old : Chart bits ok source) :
    Fintype.card (epochsWith G hu he run order old).Pin =
      Fintype.card old.Pin + epochSeats G hu he run * DescentTerminalEpochBits.width G.C := by
  induction J generalizing H with
  | zero =>
    simp only [epochsWith, epochSeats, Nat.zero_mul, Nat.add_zero];
      exact Fintype.card_congr (Equiv.refl _)
  | succ J ih =>
    rcases run with ⟨one, rest⟩
    rcases order with ⟨firstOrder, laterOrder⟩
    let next := scheduledWith G he one.subrounds firstOrder old
    have tail := ih (H := one.finish G hu he) rest laterOrder
      (source := fun c => source (Schedule.seedChoice G he one.subrounds c)) next
    have head := scheduleWith_size G he one.subrounds firstOrder old
    change _ = Fintype.card old.Pin +
      (scheduleSeats G he one.subrounds + epochSeats G hu he rest) * DescentTerminalEpochBits.width G.C
    exact tail.trans ((congrArg (fun n => n + epochSeats G hu he rest * DescentTerminalEpochBits.width G.C)
      head).trans (by ring))

variable {k p : ℕ} (X : Catalyst.Approximation F k p) (R s w : ℕ) (word : s<2^w) {J h C Ht t : ℕ}
variable (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J (initialGroup X R s))

def actualWith (order : EpochOrders G hu he run) :
    Chart (selectBit X (R:=R) (s:=s) w) (valid X (R:=R) (s:=s))
      (fun c : (Epochs.finish G hu he run).Choice => Epochs.seedChoice G hu he run c) := by
  exact epochsWith G hu he (H:=initialGroup X R s) (t:=t) (h:=h) (C:=C) (Ht:=Ht) (J:=J)
    run order (seedChart X R s w word)

theorem actualWith_seed (order : EpochOrders G hu he run)
    (z : (actualWith G hu he X R s w word run order).Pin→Bool)
    (t : (Epochs.finish G hu he run).Choice) (hit : (actualWith G hu he X R s w word run order).read z=some t)
    (key : CountKey X R) :
    let b := actualWith G hu he X R s w word run order
    (rawCount X (z∘b.seed) key).val=selected X (Epochs.seedChoice G hu he run t) key := by
  let b := actualWith G hu he X R s w word run order
  have eqn := (b.read_iff z t).mp hit
  have old : z∘b.seed=selectBit X w (Epochs.seedChoice G hu he run t) :=
    funext fun a=>(congrFun eqn (b.seed a)).trans (b.original t a)
  exact (congrArg (fun bits => (rawCount X bits key).val) old).trans
    (raw_select X word (Epochs.seedChoice G hu he run t) key)

end
end Hierarchy.DescentTerminalEpochDecoder

end OAI
