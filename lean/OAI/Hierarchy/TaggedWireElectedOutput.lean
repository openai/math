import OAI.Hierarchy.TaggedWireElectionRows

namespace OAI
/-! # The real branch deposit for a packet elected before its raw tape is read -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.CalendarTape.HistogramFormat
open ProtocolRAM ProtocolRAM.Calendar ProtocolRAM.Calendar.StockCommit ProtocolRAM.PurchaseStage ProtocolRAM.RepairHistogram
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.Diagonal.MotifOuterTerms
open ChosenPackets Probe Tagged Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators Fin.CommRing

private theorem offers_retype {F : Type} [Field F] {S H r t : ℕ} (P : Placed F S)
    (letters : H=P.data.terms) (copies : r=t) (j : Histogram (Fin H) r) (h : Histogram (Fin P.data.terms) t)
    (native : h=cast (congrArg₂ (fun a b=>Histogram (Fin a) b) letters copies) j) :
    (Row.retype P letters r).output j=P.offers h := by
  subst H t h
  rfl

private theorem offers_identified {F : Type} [Field F] {S H r t : ℕ} (Q P : Placed F S)
    (same : Q=P) (original : H=Q.data.terms) (letters : H=P.data.terms) (copies : r=t)
    (j : Histogram (Fin H) r) (h : Histogram (Fin P.data.terms) t)
    (native : h=cast (congrArg₂ (fun a b=>Histogram (Fin a) b) letters copies) j) :
    (Row.retype Q original r).output j=P.offers h := by
  subst Q
  exact offers_retype P letters copies j h native

variable {F E A B X : Type} [Field F] [Fintype E] [Fintype A] [Fintype B]
    {W k S d extra : ℕ} [Nonempty (Fin k)] {edge : E→Chord k} {req : A→E}
    {P : Packet F edge req} {C : Chart W (P.terms+extra) d} (D : HistogramFormat C X)
    (a : Attempt) (x : X) (before committed : Memory W)
local notation "b" => enabledBatch (C.layout a) (ProtocolRAM.Calendar.repair C a)
local notation "snap" m => HistogramShelf.snapshot C a m
local notation "I" => Fin (C.layout a).candidates
local notation "live" => fun i:I=>(b).selected (snap before) (i.val:Word W)

theorem recorded_source (original : D.observed a x before) (menu : ∀i:I,live i→Placed F S)
    (menuRead : ∀i hi,(menu i hi).data.terms=((b).termCount.read (snap before) ((b).packet.eval (snap before) (i.val:Word W))).val)
    (i : I) (hi : live i) {st : StockCommit} {layout : PortPlan st b (snap committed) (C.layout a).candidates}
    (R : NativePacketRow P extra b layout i) (place : Fin k↪Fin S) (rt : Fin k)
    (G : PortGraph (Fin k) B) (conn : BroadcastConnected G) (identified : menu i hi=R.placed place rt G conn)
    (wire : Fin d→Chord S) (named : ∀e,wire (R.ports e)=physicalChord place (edge e)) :
    (D.electedRow a x before original menu menuRead i).input=
      optionWidths wire (fun v=>consumedBits st.columns (snap committed) (layout.enum ⟨i,v⟩)) := by
  rw [D.electedRow_source a x before original menu menuRead i hi,identified]
  exact R.padded_source place rt G conn wire named

theorem recorded_output (original : D.observed a x before) (menu : ∀i:I,live i→Placed F S)
    (menuRead : ∀i hi,(menu i hi).data.terms=((b).termCount.read (snap before) ((b).packet.eval (snap before) (i.val:Word W))).val)
    (i : I) (hi : live i) {st : StockCommit} {layout : PortPlan st b (snap committed) (C.layout a).candidates}
    (R : NativePacketRow P extra b layout i) (place : Fin k↪Fin S) (rt : Fin k)
    (G : PortGraph (Fin k) B) (conn : BroadcastConnected G) (identified : menu i hi=R.placed place rt G conn)
    (choice : BallChoices (D.letters a x) (D.copies a x)) (physical : D.observed a x committed)
    (arity : ((b).termCount.read (snap committed) ((b).packet.eval (snap committed) (i.val:Word W))).val=P.terms)
    (ok : ready C (.attempt a) committed)
    (safe : ∀l : Fin ((C.layout a).candidates*(P.terms+extra)),protected C ((D.bank a).base+l.val) (.attempt a))
    (tape : (D.slot (.attempt a)).word x choice=D.windows.read (.attempt a) committed)
    (wire : Fin d→Chord S) (named : ∀e,wire (R.ports e)=physicalChord place (edge e)) :
    (D.electedRow a x before original menu menuRead i).output (choice i)=
      optionWidths wire (fun v=>installedBits st.columns (snap committed) (layout.enum ⟨i,v⟩))+
      placeWidths place (G.chordWidths (fun _=>(b).copies*P.selectorBits)) := by
  obtain ⟨letters,copies,same⟩:=D.chosen_histogram a x committed i R choice physical arity ok safe tape
  simp only [electedRow,dite_eq_left hi]
  rw [←R.padded_target place rt G conn wire named]
  exact offers_identified (menu i hi) (R.placed place rt G conn) identified _ letters copies (choice i) R.h same

end Hierarchy.WireTelescope.CalendarTape.HistogramFormat

end
end OAI
