import OAI.Hierarchy.DescentTerminalEpochRoutes
import Mathlib.Data.List.Forall2

namespace OAI
/-! # Every ranked ordinary selection fits in its original public selector row -/
namespace Hierarchy.DescentTerminalEpochDecoder
open DescentSixParty DescentSixParty.Chronology DescentTerminalEpochChart
open DescentKernelHistory.BitDescription
noncomputable section
variable {F P Z U : Type} [Field F] {d : ℕ} {portBits : P→ℕ} {u ε : ℝ}
    (G : PoweredGadget F) (he : 0≤ε) {bits : Z→U→Bool} {ok : (U→Bool)→Prop}

def rankedCount (x : RankedSelection F P d portBits G ε) := selectionCount G x.1

private theorem extended_seats {H : Histories F d P portBits} (a : SubroundInput H G (u:=u) he)
    (o : OrdersAt G he a) {root : H.Choice → Z} (b : Chart bits ok root) :
    (extendWith G he a o b).layout.map Source.seats = b.layout.map Source.seats ++ [maxSeats G he a] := by
  change (extendedLayout (C:=G.C) (seats:=maxSeats G he a) b).map Source.seats = _
  simp only [extendedLayout,List.map_append,List.map_cons,List.map_nil,List.map_map]
  rfl

theorem scheduled_ranked_seats {t : ℕ} {H : Histories F d P portBits}
    (s : Schedule G (u:=u) he t H) (o : ScheduleOrders G he s)
    {root : H.Choice → Z} (b : Chart bits ok root) (c : (Schedule.finish G he s).Choice)
    (prior : List ℕ) (paid : List.Forall₂ (· ≤ ·) prior (b.layout.map Source.seats)) :
    List.Forall₂ (· ≤ ·) (prior ++ (rankedSchedule he s o c).map (rankedCount G))
      ((scheduledWith G he s o b).layout.map Source.seats) := by
  induction t generalizing H prior with
  | zero => simpa only [rankedSchedule,scheduledWith,List.map_nil,List.append_nil] using paid
  | succ t ih =>
    rcases s with ⟨stage,restSchedule⟩
    let x := (sourceChoice he restSchedule c).1
    have step : List.Forall₂ (· ≤ ·) (prior ++ [count G he stage x])
        ((extendWith G he stage o.1 b).layout.map Source.seats) := by
      rw [extended_seats]
      exact List.rel_append paid (.cons (count_le G he stage x) .nil)
    have rest := ih restSchedule o.2 (extendWith G he stage o.1 b) c (prior ++ [count G he stage x]) step
    simpa only [scheduledWith,rankedSchedule,List.map_cons,List.append_assoc,List.singleton_append,
      rankedCount,selectionCount,count,x] using rest

theorem epochs_ranked_seats (hu : 0≤u) {h C Ht t J : ℕ} {H : Histories F d P portBits}
    (s : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H) (o : EpochOrders G hu he s)
    {root : H.Choice → Z} (b : Chart bits ok root) (c : (Epochs.finish G hu he s).Choice)
    (prior : List ℕ) (paid : List.Forall₂ (· ≤ ·) prior (b.layout.map Source.seats)) :
    List.Forall₂ (· ≤ ·) (prior ++ (epochsRanked G s o c).map (rankedCount G))
      ((epochsWith G hu he s o b).layout.map Source.seats) := by
  induction J generalizing H prior with
  | zero => simpa only [epochsRanked,epochsWith,List.map_nil,List.append_nil] using paid
  | succ J ih =>
    have first := scheduled_ranked_seats G he s.1.subrounds o.1 b (epochsSource G (H := s.1.finish G hu he) (J := J) s.2 c) prior paid
    have rest := ih s.2 o.2 (scheduledWith G he s.1.subrounds o.1 b) c _ first
    simpa only [epochsWith,epochsRanked,List.map_append,List.append_assoc] using rest

private theorem aligned_at {A B : Type*} {f : A→ℕ} {g : B→ℕ} {xs : List A} {ys : List B}
    (fit : List.Forall₂ (· ≤ ·) (xs.map f) (ys.map g)) {i : ℕ} {x : A} {y : B}
    (left : xs[i]?=some x) (right : ys[i]?=some y) : f x ≤ g y := by
  obtain ⟨hi,hx⟩ := List.getElem?_eq_some_iff.mp left
  obtain ⟨hj,hy⟩ := List.getElem?_eq_some_iff.mp right
  have bounds := fit.get (i:=i) (by simpa only [List.length_map] using hi)
    (by simpa only [List.length_map] using hj)
  simpa only [List.get_eq_getElem,List.getElem_map,hx,hy] using bounds

theorem epochs_seat_at (hu : 0≤u) {h C Ht t J : ℕ} {H : Histories F d P portBits}
    (s : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J H) (o : EpochOrders G hu he s)
    {root : H.Choice → Z} (b : Chart bits ok root) (empty : b.layout=[])
    (c : (Epochs.finish G hu he s).Choice) (i : ℕ)
    (v : RankedSelection F P d portBits G ε) (row : Source (epochsWith G hu he s o b).Pin)
    (entered : (epochsRanked G s o c)[i]?=some v) (selected : (epochsWith G hu he s o b).layout[i]?=some row) :
    selectionCount G v.1 ≤ row.seats := by
  have all := epochs_ranked_seats G he hu s o b c [] (by rw [empty];exact .nil)
  apply aligned_at (f := rankedCount G) (g := Source.seats) _ entered selected
  simpa only [List.nil_append] using all

end
end Hierarchy.DescentTerminalEpochDecoder

end OAI
