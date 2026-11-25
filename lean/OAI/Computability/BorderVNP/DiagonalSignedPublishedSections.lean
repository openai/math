import OAI.Computability.BorderVNP.CellPacketGeometrySignedPublished
import OAI.Computability.BorderVNP.RoutingISAScheduleClockMergeRangesGeometry
import OAI.Computability.BorderVNP.PackedHistoryPinGeometry
import OAI.Computability.BorderVNP.PackedTerminalRetainedReturn
import OAI.Computability.BorderVNP.DiagonalFrozenSignedOperandRoom

/-! # Sizes and absolute source intervals for the emitted history packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open Packing.Inherited.FrozenTape CellSparse.Packet CellPacketGeometry.SiteWords
open scoped BigOperators Classical

/-- The source charge includes the padded roster (with its unused marker),
the complete lengths of both row banks, and both words of every typed
report length. The actual segmented count scan consequently fits its native
word for every receiver and for the spare. -/
theorem terminal_source_counts {R B U V E Orig : Type} [Fintype E] {a C w : ℕ}
    (S : Schema R B) (L : Schema U V) (boxes : Fin a → List (Source.Box Orig))
    (rep : Fin (C+1) → List (List E))
    (room : sourceVolume S L boxes rep < 2^w) :
    (roster a S L).length < 2^w ∧ S.rows.length+L.rows.length < 2^w ∧
      (∑ i, (boxes i).length) < 2^w ∧
      (∀ c, (rep c).length < 2^w) ∧ (∀ c v, v ∈ rep c → v.length < 2^w) := by
  have rowLength (rs : List (List E)) : rs.length ≤ (rs.map (fun r => 1+r.length)).sum := by
    induction rs with
    | nil => rfl
    | cons s ss ih => simp only [List.map_cons,List.length_cons,List.sum_cons]; omega
  have vectorLength (rs : List (List E)) (r : List E) (mem : r ∈ rs) : r.length ≤ (rs.map (fun v => 1+v.length)).sum := by
    induction rs with
    | nil => cases mem
    | cons s ss ih =>
      rcases List.mem_cons.mp mem with rfl | h
      · simp only [List.map_cons,List.sum_cons]; omega
      · exact (ih h).trans (Nat.le_add_left _ _)
  have forCell (c : Fin (C+1)) : (1+((rep c).map (fun r => 1+r.length)).sum) ≤
      ∑ j, (1+((rep j).map (fun r => 1+r.length)).sum) :=
    Finset.single_le_sum (f:=fun j => 1+((rep j).map (fun r => 1+r.length)).sum)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
  unfold sourceVolume at room
  simp only [roster,List.length_append,List.length_map,List.length_finRange,List.length_cons,List.length_nil]
  exact ⟨by omega,by omega,by omega,fun c => by have := forCell c; have := rowLength (rep c); omega,
    fun c v hv => by have := forCell c; have := vectorLength (rep c) v hv; omega⟩

end CellPacketGeometry.History

namespace CellPacketGeometry.History.Native

open CellSparse Packet Packet.Source RoutingISA RoutingISA.Evaluator RoutingISA.CellPacket GeometryFrameEncoding
open scoped Classical

/-- On the actual public permutation the source words of the real cell have
the advertised contiguous RAM interval. Every location the compactor reads
is above both changed frame/control words and below the descriptor sort. -/
theorem Published.ordinary_region {S Orig E : Type} {C p d ctl H frame : ℕ}
    {G : SiteWords.Directory S Orig (C+1)} {ptr : Orig → E} {arg : E → ℕ} {mem : ℕ → ℕ}
    (out : Published G p d (ctl+37) H ptr arg mem) (order : frame+112 ≤ ctl) (c : Fin C) :
    let words := (plan (G.privateWires c.castSucc) (G.cellBoxes c.castSucc) (G.cellRecords c.castSucc)
      (G.reports c.castSucc)).flatMap Part.publicBuffer
    ∃ hf : C+1+G.words.length+(C+1) ≤ 2^p,
      let reg := sectionRange mem (ctl+37) (Markers.start hf c.castSucc) (Markers.stop hf c.castSucc)
      reg.2=words.length ∧ WordsAt mem reg.1 words ∧ reg.1+words.length ≤ descriptorBank (ctl+37) p ∧
        ∀ addr ≥ reg.1, addr ≠ frame+90 ∧ addr ≠ ctl+29 := by
  intro words
  obtain ⟨hf,hs,π,buf⟩ := out
  refine ⟨hf,?_⟩
  intro reg
  have raw := buf.publicWords c.castSucc
  exact ⟨raw.1,raw.2,ScheduleClock.publicSection_end buf c.castSucc,fun addr bound => by
    change ctl+37+_+1 ≤ addr at bound
    omega⟩

end CellPacketGeometry.History.Native

namespace PackedHistoryCircuit.Retained

open CellPacketGeometry Packing.RoutingOutputs GeometryAdvice

/-- Word representability of the actual two packet sorts from the charged
native allocation. The extent used here includes the routing rows, private
views, and every real scalar control before the packet. -/
theorem packet_allocation_room (fresh reserve gates edges cells original live controls p d field w : ℕ) :
    let outputs := edges*3+(count edges cells original live+((cells+(original+cells))+(controls+Total p d)))
    let dest := Allocation.dest fresh reserve gates outputs field
    let start := packetBase dest edges cells original live controls
    Allocation.stop fresh reserve gates outputs field w < 2^w →
      start+2^p < 2^w ∧ 2^d ≤ 2^w ∧ start+Total p d < 2^w := by
  intro outputs dest start stop
  have limit : dest+outputs < 2^w := by
    change dest+outputs+_+_ < _ at stop
    omega
  have span : start + Total p d = dest+outputs := by
    dsimp only [start,outputs,packetBase,controlsBase,bases,count]
    omega
  change start+2^p < _ ∧ 2^d ≤ _ ∧ start+((2^p+2^p)+(2^d+2^d)) < _
  change start+((2^p+2^p)+(2^d+2^d))=dest+outputs at span
  have publicPositive : 0 < (2:ℕ)^p := by positivity
  have descriptorPositive : 0 < (2:ℕ)^d := by positivity
  omega

end PackedHistoryCircuit.Retained

end BorderVNP
end Computability
end OAI
