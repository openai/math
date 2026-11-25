import OAI.Computability.BorderVNP.CubeScatterTrialPrefix
import OAI.Computability.BorderVNP.CubeScatterVisits
import OAI.Computability.BorderVNP.CubeISAOwnedPacketRowModel

/-! # Feeding every native packet trial from the common row streams -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter.PacketRowData

open RoutingISA Physical Physical.Owned VPVNP.BurstRAM VPVNP.MotifBase DiagonalResidueRAM Tally

variable {w n d blocks b h K s : ℕ} (D : PacketRowData n d blocks b h K s)

/-- Actual bits emitted by this candidate, or the empty list when it is rejected. -/
def trialWords (f : Packet n d blocks → List Bool) (t : Fin (packetTrials n d blocks)) : List Bool :=
  (packetTrial D.axis D.pair t).toList.flatMap f

/-- Concatenating all trial words preserves the order of the accepted packet visits. -/
theorem all_words (f : Packet n d blocks → List Bool) :
    (List.finRange (packetTrials n d blocks)).flatMap (D.trialWords f) =
      (packetVisits blocks D.axis D.pair).flatMap f := by
  simp only [packetVisits,List.filterMap_eq_flatMap_toList,List.flatMap_assoc]
  rfl

/-- The actual native cursors after any prefix equal their starting addresses
plus the lengths of the selector and crossing streams emitted by precisely those trials. -/
theorem before_cursors (m : Memory w) (k : ℕ) (hk : k ≤ packetTrials n d blocks) :
    (D.before m k).sel = D.selector+(trialPrefix (D.trialWords (selectorStream ∘ D.select)) k).length ∧
    (D.before m k).cross = D.crossing+(trialPrefix (D.trialWords (fun p => crossingStream b (D.select p) D.axis (D.supply p))) k).length := by
  induction k with
  | zero => simp [before,trialPrefix]
  | succ k ih =>
    let t : Fin (packetTrials n d blocks) := ⟨k,hk⟩
    have tv : t.val = k := rfl
    obtain ⟨hsel,hcross⟩ := ih (by omega)
    by_cases ok : packetTrialValid t
    · rw [D.before_visit m t ok,trialPrefix_step _ t,trialPrefix_step _ t]
      simp only [visit,trialWords,packetTrial,dite_eq_left ok,Option.toList_some,List.flatMap_cons,
        List.flatMap_nil,List.append_nil,List.length_append,Function.comp_apply,selectorStream_length,
        crossingStream_length,tv,hsel,hcross,crossLength,Nat.add_assoc,true_and]
    · rw [D.before_skip m t ok,trialPrefix_step _ t,trialPrefix_step _ t]
      simpa only [trialWords,packetTrial,dite_eq_right ok,Option.toList_none,List.flatMap_nil,List.append_nil] using ⟨hsel,hcross⟩

/-- At row exit the crossing cursor is the actual entry address for the first
singleton orientation. The selector cursor has consumed the entire selector prefix. -/
theorem final_cursors (m : Memory w) :
    (D.before m (packetTrials n d blocks)).sel = D.selector+((packetVisits blocks D.axis D.pair).flatMap (selectorStream ∘ D.select)).length ∧
    (D.before m (packetTrials n d blocks)).cross = D.crossing+((packetVisits blocks D.axis D.pair).flatMap
      (fun p => crossingStream b (D.select p) D.axis (D.supply p))).length := by
  simpa only [trialPrefix_full,all_words] using D.before_cursors m _ le_rfl

/-- Complete resident input lists and separated packet banks prepare every valid
trial, including trials after skipped candidates and after earlier packet writes. -/
theorem preparedRow_of_streams (src : Set ℕ) (m : Memory w)
    (sels : Resident src m D.selector ((packetVisits blocks D.axis D.pair).flatMap (selectorStream ∘ D.select)))
    (cross : Resident src m D.crossing ((packetVisits blocks D.axis D.pair).flatMap
      (fun p => crossingStream b (D.select p) D.axis (D.supply p))))
    (dest : ∀ p : Packet n d blocks, p.1.1 D.axis = D.pair → ∀ j < bankWidth n b h K s,
      RoutingISA.OwnedVertex.bankAt D.base D.stride p+j ∉ src ∧ RoutingISA.OwnedVertex.bankAt D.base D.stride p+j < 2^w) :
    D.PreparedRow src m := by
  rw [← D.all_words] at sels cross
  intro t ok
  let p := D.packet t ok
  let c := D.cursor p (D.before m t.val)
  let ps := selectorPositions (D.select p) ++ D.body p
  have psel : ps.filterMap Position.selectorBit = selectorStream (D.select p) := by
    simp only [ps,List.filterMap_append,(selector_streams _).1,body,body_selector_nil,List.append_nil]
  have pcross : ps.filterMap Position.crossBit = crossingStream b (D.select p) D.axis (D.supply p) := by
    simp only [ps,List.filterMap_append,(selector_streams _).2,body,body_cross_stream,List.nil_append]
  have plen : ps.length = bankWidth n b h K s := by
    simp only [ps,List.length_append,selectorPositions,body,bodyPositions,List.length_ofFn,bodyWidth,
      bankWidth,supplyBase,Nat.add_assoc]
  obtain ⟨csel,ccross⟩ := D.before_cursors m t.val t.isLt.le
  have selAt : Resident src m c.selector (ps.filterMap Position.selectorBit) := by
    change Resident src m (D.before m t.val).sel _
    rw [psel,csel]
    simpa only [trialWords,packetTrial,dite_eq_left ok,Option.toList_some,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,Function.comp_apply] using Resident.atTrial _ t sels
  have crossAt : Resident src m c.crossing (ps.filterMap Position.crossBit) := by
    change Resident src m (D.before m t.val).cross _
    rw [pcross,ccross]
    simpa only [trialWords,packetTrial,dite_eq_left ok,Option.toList_some,List.flatMap_cons,List.flatMap_nil,
      List.append_nil] using Resident.atTrial _ t cross
  exact prepared_of_streams src ps c m selAt.bits crossAt.bits selAt.addresses crossAt.addresses
    (fun j hj => dest p (packetRowEquiv D.axis D.pair ⟨t,ok⟩).property j (plen ▸ hj))

end Cube.Scatter.PacketRowData

end BorderVNP
end Computability
end OAI
