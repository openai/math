import OAI.Hierarchy.TaggedWireChosenPackets
import OAI.Hierarchy.ProbeNativePacketRows

namespace OAI
/-! # The signed packet chosen at one measured candidate row -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StockCommit.NativePacketRow
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open Probe WireTelescope ChosenPackets
open scoped BigOperators Classical

variable {F E A B : Type} [Field F] [Fintype E] [Fintype A] [Fintype B]
variable {k S w d rows : ℕ} [Nonempty (Fin k)]
variable {edge : E→Chord k} {req : A→E} {P : Packet F edge req} {extra : ℕ}
variable {b : Batch (P.terms+extra) d} {s : StockCommit} {mem : Memory w}
variable {layout : PortPlan s b mem rows} {j : Fin rows}

/-- The native width counters use one field per role. Several requests of the
same role are all consumed at that one field. -/
theorem optionWidths_debits (whereAt : E→Chord S) (units : ℕ) :
    optionWidths whereAt (debited req units) =
      optionWidths (fun a=>whereAt (req a)) (fun _=>units) := by
  classical
  simp only [optionWidths,debited,Finsupp.single_finsetSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (req a)]
  · simp
  · intro e _ h
    simp [Ne.symm h]
  · simp

/-- The active native packet supplies both the true finite alphabet and the
signed local map of the rectangular histogram tape. -/
def placed (_R : NativePacketRow P extra b layout j) (place : Fin k ↪ Fin S)
    (rt : Fin k) (G : PortGraph (Fin k) B) (conn : BroadcastConnected G) : Placed F S where
  sites := k
  Edges := E
  Requests := A
  Tree := B
  edge := edge
  wanted := req
  data := P
  place := place
  root := rt
  graph := G
  connected := conn

def chosen (R : NativePacketRow P extra b layout j) (place : Fin k ↪ Fin S)
    (rt : Fin k) (G : PortGraph (Fin k) B) (conn : BroadcastConnected G) :
    Row F S P.terms b.copies :=
  .packet (placed R place rt G conn) b.copies

theorem native_source (R : NativePacketRow P extra b layout j) (place : Fin k ↪ Fin S)
    (rt : Fin k) (G : PortGraph (Fin k) B) (conn : BroadcastConnected G) :
    (chosen R place rt G conn).input =
      optionWidths (fun e=>physicalChord place (edge e))
        (fun e=>consumedBits s.columns mem (layout.enum ⟨j,R.ports e⟩)) := by
  change optionWidths (fun a=>physicalChord place (edge (req a))) (fun _=>b.copies*P.width)=_
  simp_rw [(R.amounts _).2]
  exact (optionWidths_debits (req:=req) (fun e=>physicalChord place (edge e)) _).symm

theorem native_target (R : NativePacketRow P extra b layout j) (place : Fin k ↪ Fin S)
    (rt : Fin k) (G : PortGraph (Fin k) B) (conn : BroadcastConnected G) :
    (chosen R place rt G conn).output R.h =
      optionWidths (fun e=>physicalChord place (edge e))
        (fun e=>installedBits s.columns mem (layout.enum ⟨j,R.ports e⟩))+
      placeWidths place (G.chordWidths (fun _=>b.copies*P.selectorBits)) := by
  change optionWidths _ (histWidth P.count R.h)+_=_
  simp_rw [(R.amounts _).1]
  rfl

/-- Padding a native occurrence table with dormant common role slots neither
creates nor drops wires, even when several genuine role chords coincide. -/
private theorem padding (ports : E ↪ Fin d) (wire : Fin d→Chord S) (bits : Fin d→ℕ)
    (quiet : ∀v,(∀e,ports e≠v)→bits v=0) :
    optionWidths wire bits=optionWidths (fun e=>wire (ports e)) (fun e=>bits (ports e)) := by
  classical
  unfold optionWidths
  rw [← Finset.sum_map Finset.univ ports (fun v=>Finsupp.single (wire v) (bits v))]
  apply (Finset.sum_subset (Finset.subset_univ _) ?_).symm
  intro v _ absent
  apply Eq.trans (congrArg (Finsupp.single (wire v)) (quiet v ?_)) (Finsupp.single_zero _)
  intro e h
  apply absent
  exact Finset.mem_map.mpr ⟨e,Finset.mem_univ _,h⟩

theorem padded_source (R : NativePacketRow P extra b layout j) (place : Fin k ↪ Fin S)
    (rt : Fin k) (G : PortGraph (Fin k) B) (conn : BroadcastConnected G) (wire : Fin d→Chord S)
    (named : ∀e,wire (R.ports e)=physicalChord place (edge e)) :
    (chosen R place rt G conn).input =
      optionWidths wire (fun v=>consumedBits s.columns mem (layout.enum ⟨j,v⟩)) := by
  rw [native_source R place rt G conn,padding R.ports wire _ (fun v h=>(R.unused v h).2)]
  simp_rw [named]

theorem padded_target (R : NativePacketRow P extra b layout j) (place : Fin k ↪ Fin S)
    (rt : Fin k) (G : PortGraph (Fin k) B) (conn : BroadcastConnected G) (wire : Fin d→Chord S)
    (named : ∀e,wire (R.ports e)=physicalChord place (edge e)) :
    (chosen R place rt G conn).output R.h =
      optionWidths wire (fun v=>installedBits s.columns mem (layout.enum ⟨j,v⟩))+
        placeWidths place (G.chordWidths (fun _=>b.copies*P.selectorBits)) := by
  rw [native_target R place rt G conn,padding R.ports wire _ (fun v h=>(R.unused v h).1)]
  simp_rw [named]

end Hierarchy.ProtocolRAM.Calendar.StockCommit.NativePacketRow

end
end OAI
