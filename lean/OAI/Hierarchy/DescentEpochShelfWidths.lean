import OAI.Hierarchy.DescentTerminalEpochCapacity
import OAI.Hierarchy.DescentTerminalEpochOrders

namespace OAI
/-! Each genuine ordinary shelf uses the gadget's profile alphabet, and its padded seat
count is bounded by the issued path capacity even when capacities vary between branches. -/
namespace Hierarchy.DescentTerminalEpochDecoder
open DescentTerminalEpochChart DescentTerminalEpochBits DescentSixParty DescentSixParty.Chronology
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bs : P→ℕ} {u ε : ℝ}
    (G : PoweredGadget F) (hu : 0 ≤ u) (he : 0 ≤ ε)
    {Seed Z : Type} {bits : Z→Seed→Bool} {ok : (Seed→Bool)→Prop}

theorem extend_widths {H : Histories F d P bs} (a : SubroundInput H G (u:=u) he)
    (o : OrdersAt G he a) {s : H.Choice→Z} (prev : Chart bits ok s) {B : ℕ}
    (keep : ∀v∈prev.layout,v.C=G.C ∧ v.seats≤B) (first : maxSeats G he a ≤ B) :
    ∀v∈(extendWith G he a o prev).layout,v.C=G.C ∧ v.seats≤B :=by
  intro v hv
  change v∈(prev.layout.map (Source.map Sum.inl))++[_] at hv
  rcases List.mem_append.mp hv with old|now
  · obtain ⟨x,hx,rfl⟩:=List.mem_map.mp old
    exact keep x hx
  · obtain rfl:=List.mem_singleton.mp now
    exact ⟨rfl,first⟩

theorem schedule_widths {H : Histories F d P bs} {t B : ℕ} (run : Schedule G (u:=u) he t H)
    (o : ScheduleOrders G he run) {s : H.Choice→Z} (prev : Chart bits ok s)
    (keep : ∀v∈prev.layout,v.C=G.C ∧ v.seats≤B)
    (paid : ∀c,∀e∈scheduled he run c,selectionCount G e≤B) :
    ∀v∈(scheduledWith G he run o prev).layout,v.C=G.C ∧ v.seats≤B :=by
  induction t generalizing H with
  | zero=>exact keep
  | succ t ih=>
    exact ih run.2 o.2 _ (extend_widths G he run.1 o.1 prev keep (first_shelf_paid G he run paid))
      (fun c e seen=>paid c e (List.mem_cons_of_mem _ seen))

theorem epoch_widths {H : Histories F d P bs} {t J h C Ht B : ℕ}
    (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H) (o : EpochOrders G hu he run)
    {s : H.Choice→Z} (prev : Chart bits ok s) (keep : ∀v∈prev.layout,v.C=G.C ∧ v.seats≤B)
    (paid : ∀c,∀e∈epochsSelections G run c,selectionCount G e≤B) :
    ∀v∈(epochsWith G hu he run o prev).layout,v.C=G.C ∧ v.seats≤B :=by
  induction J generalizing H with
  | zero=>exact keep
  | succ J ih=>
    obtain ⟨one,rest⟩:=run
    apply ih rest o.2 _
    · apply schedule_widths G he one.subrounds o.1 prev keep
      intro c sel seen
      obtain ⟨last,same⟩:=epochs_source_surjective G hu he rest c
      exact paid last sel (List.mem_append_left _ (by simpa only [same] using seen))
    · exact fun c sel seen=>paid c sel (List.mem_append_right _ seen)

end
end Hierarchy.DescentTerminalEpochDecoder

end OAI
