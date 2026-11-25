import OAI.Hierarchy.DescentTerminalEpochOrders
import OAI.Hierarchy.DescentTerminalEpochCapacity
import OAI.Hierarchy.DescentTerminalPartialRoute

namespace OAI
/-! # Every raw selector prefix follows the actual reached group cardinalities -/
namespace Hierarchy.DescentTerminalEpochDecoder
open Catalyst DescentInitialHost DescentSeedRoot DescentSixParty DescentSixParty.Chronology
open DescentTerminalEpochChart DescentTerminalEpochBits DescentKernelHistory.BitDescription Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {portBits : P→ℕ} {u ε : ℝ}
variable (G : PoweredGadget F) (hu : 0≤u) (he : 0≤ε)
variable {S Z : Type} {bits : Z→S→Bool} {ok : (S→Bool)→Prop}

def scheduleRoute : {t : ℕ} → {H : Histories F d P portBits} → (s : Schedule G (u:=u) he t H) →
    (order : ScheduleOrders G he s) → {root : H.Choice→Z} → (b : Chart bits ok root) → Route b →
    Route (scheduledWith G he s order b)
  | 0,_,_,_,_,_,p=>p
  | _+1,_,s,order,_,b,p=>scheduleRoute s.2 order.2 (extendWith G he s.1 order.1 b)
      (Route.extend b (count G he s.1) order.1 (count_le G he s.1)
        (fun c=>(scannedRows he (s.1.placement c)).profile) p)

def epochRoute {t h C Ht : ℕ} : {J : ℕ} → {H : Histories F d P portBits} →
    (s : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H) → (order : EpochOrders G hu he s) →
    {root : H.Choice→Z} → (b : Chart bits ok root) → Route b → Route (epochsWith G hu he s order b)
  | 0,_,_,_,_,_,p=>p
  | _+1,_,s,order,_,b,p=>epochRoute s.2 order.2 (scheduledWith G he s.1.subrounds order.1 b)
      (scheduleRoute G he s.1.subrounds order.1 b p)

theorem schedule_counts {t : ℕ} {H : Histories F d P portBits} (s : Schedule G (u:=u) he t H)
    (order : ScheduleOrders G he s) {root : H.Choice→Z} (b : Chart bits ok root)
    (c : (Schedule.finish G he s).Choice) :
    let chart:=scheduledWith G he s order b
    chart.counts (chart.store c)=b.counts (b.store (sourceChoice he s c))++
      (scheduled he s c).map (selectionCount G) := by
  induction t generalizing H with
  | zero=>
    simp [scheduledWith,sourceChoice,scheduled]
    rfl
  | succ t ih=>
    obtain ⟨one,rest⟩:=s
    have step:=extend_stored_counts b (count G he one) order.1 (count_le G he one)
      (fun x=>(scannedRows he (one.placement x)).profile) (sourceChoice he rest c)
    have rr:=ih rest order.2 (extendWith G he one order.1 b) c
    change (extendWith G he one order.1 b).counts ((extendWith G he one order.1 b).store _) = _ at step
    rw [step] at rr
    simp only [scheduledWith,sourceChoice,scheduled,List.map_cons,List.append_assoc,List.singleton_append,count,selectionCount] at rr ⊢
    exact rr

theorem epochs_counts {t h C Ht J : ℕ} {H : Histories F d P portBits}
    (s : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H) (order : EpochOrders G hu he s)
    {root : H.Choice→Z} (b : Chart bits ok root) (c : (Epochs.finish G hu he s).Choice) :
    let chart:=epochsWith G hu he s order b
    chart.counts (chart.store c)=b.counts (b.store (epochsSource G s c))++
      (epochsSelections G s c).map (selectionCount G) := by
  induction J generalizing H with
  | zero=>
    simp [epochsWith,epochsSource,epochsSelections]
    rfl
  | succ j ih=>
    obtain ⟨one,rest⟩:=s
    have rr:=ih rest order.2 (scheduledWith G he one.subrounds order.1 b) c
    have first:=schedule_counts G he one.subrounds order.1 b (epochsSource G (J:=j) (H:=one.finish G hu he) rest c)
    let more := (epochsSelections G (J:=j) (H:=one.finish G hu he) rest c).map (selectionCount G)
    have joined := rr.trans (congrArg (fun xs => xs ++ more) first)
    simp only [more,epochsWith,epochsSource,epochsSelections,List.map_append,List.append_assoc] at joined ⊢
    exact joined

variable {k p : ℕ} (X : Approximation F k p) (R s w : ℕ) (word : s < 2^w)
variable {t h C Ht J : ℕ}
variable (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J (initialGroup X R s))
variable (order : EpochOrders G hu he run)
set_option quotPrecheck false
local notation "b" => actualWith G hu he X R s w word run order

def seedRoute : Route (seedChart X R s w word) where
  follow z := (DescentSeedRoot.decode X z).getD (fun _ v=>match v with | .inl _=>fun _=>0 | .inr _=>())
  stored c := by
    change (DescentSeedRoot.decode X (selectBit X w c)).getD _=c
    rw [(decode_iff X word _ c).mpr rfl]
    rfl
  «prefix» _ := ⟨[],rfl⟩

def actualRoute : Route b := epochRoute G hu he run order (seedChart X R s w word) (seedRoute X R s w word)

theorem raw_prefix (z : (b).Pin→Bool) :
    let c:=(actualRoute G hu he X R s w word run order).follow z
    List.IsPrefix ((b).counts z) ((epochsSelections G run c).map (selectionCount G)) := by
  let route:=actualRoute G hu he X R s w word run order
  have native:=epochs_counts G hu he run order (seedChart X R s w word) (route.follow z)
  have eqn : (b).counts ((b).store (route.follow z))=(epochsSelections G run (route.follow z)).map (selectionCount G) :=
    native
  have prefix_ := route.prefix z
  rw [eqn] at prefix_
  exact prefix_

end
end Hierarchy.DescentTerminalEpochDecoder

end OAI
