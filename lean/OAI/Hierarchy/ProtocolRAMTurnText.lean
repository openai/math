import OAI.Hierarchy.ProtocolRAMTurnRankProgram
import OAI.Hierarchy.ProtocolRAMTurnShelfProgram
import OAI.Hierarchy.ProtocolRAMRowText

namespace OAI
/-! # Fixed native text of the counted occurrence-rank and chronological shelf programs -/
noncomputable section
namespace Hierarchy.ProtocolRAMTurnText
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProtocolRAM.Calendar ProbeStage.Native
open ProtocolRAMTurnItinerary ProtocolRAMTurnChart

private def zero : Bank := ⟨0,0⟩
private def accounts : RouteSettlement.Banks := ⟨zero,zero,zero,zero,zero,zero⟩
private def inputs : Data := ⟨zero,zero,zero,zero,zero,zero,zero⟩
private def path : Banks := ⟨zero,zero,zero,zero,zero,zero,zero⟩

theorem generated (W a b n : ℕ) (A V : Expr) :
    text (ProtocolRAMGeneratedWrite.program W a b n A V)=rowText A+rowText V+20 := by
  rw [ProtocolRAMGeneratedWrite.program,text_seq,text_seq,text_scan,text_scan]
  rfl

def rankTexts := text (ProtocolRAMTurnReplayed.procedure 0 0 0 0 accounts zero)

set_option maxRecDepth 4096 in
theorem rank_text (W base n rows : ℕ) (b : RouteSettlement.Banks) (paid : Bank) :
    text (ProtocolRAMTurnReplayed.procedure W base n rows b paid)=rankTexts := by
  simp only [rankTexts,ProtocolRAMTurnReplayed.procedure,ProtocolRAMTurnPrefix.program,ProtocolRAMTurnPrefix.rankCode,
    ProtocolRAMPackedCommon.program,ProtocolRAMRankGather.fields,ProtocolRAMRankGather.program,text_seq,text_scan,generated]; rfl

def shelfTexts := text (ProtocolRAMChronologicalShelf.program 0 0 0 0 0 0 0 0 0 0 0 0 0 0 inputs zero path)

set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

/-- A chronology uses the two public pointer/sum columns and the fixed subtract walk. -/
theorem visit_text (W N header bits first : ℕ) (d : Data) (edge tail heads : Bank) :
    text (ProtocolRAMVisitColumns.program W N first (walk header bits d edge tail heads))=445 := by
  rw [ProtocolRAMVisitColumns.program,text_seq,text_seq,text_scan,text_passes]
  rfl

private theorem column_text (N start : ℕ) (terms : List Expr) :
    listText (ProbeStage.Native.columns N start terms)=15+(terms.map rowText).sum := by
  have same : ((ProbeStage.Native.columns N start terms).map fun p=>rowText p.term)=terms.map rowText := by
    induction terms generalizing start with
    | nil => rfl
    | cons t ts ih => exact congrArg (List.cons (rowText t)) (ih (start+N))
  exact congrArg (fun l : List ℕ=>15+l.sum) same

private def fieldWork : Fin 7→ℕ := ![550,556,658,664,72,7,54]

private theorem field_work (header bits : ℕ) (d : Data) (b : Banks) (i : Fin 7) :
    (field (chart header bits d) b i).work=fieldWork i := by
  fin_cases i <;> rfl

/-- All seven queried fields in the stored chronological row. -/
theorem itinerary_text (W N header bits src : ℕ) (d : Data) (b : Banks) :
    text (ProtocolRAMTurnItinerary.program W src N (chart header bits d) b)=10336 := by
  rw [ProtocolRAMTurnItinerary.program,text_passes,column_text,List.map_ofFn]
  have each : rowText ∘ field (chart header bits d) b=fun i=>11+4*fieldWork i := by
    funext i
    exact congrArg (fun n=>11+4*n) (field_work header bits d b i)
  rw [each]
  decide

/-- The zero-initialization and sparse writes for the five fixed shelf fields. -/
theorem publish_text (W N sites slots base scratch sink : ℕ) (t : ProtocolRAMTurnShelf.Tables) :
    text (ProtocolRAMTurnShelf.program W N sites slots base scratch sink t)=317 := by
  obtain ⟨labels,regs,params⟩:=ProtocolRAMTurnShelf.size W N sites slots base scratch sink t
  rw [text,labels,regs,params]

theorem chrono_text (W N sites slots header bits start src sb rom rb base scratch sink : ℕ)
    (d : Data) (heads : Bank) (b : Banks) :
    text (ProtocolRAMChronologicalShelf.program W N sites slots header bits start src sb rom rb base scratch sink d heads b)=11098 := by
  rw [ProtocolRAMChronologicalShelf.program,text_seq,visit_text,ProtocolRAMTurnInstalled.program,text_seq,
    itinerary_text,publish_text]

theorem shelf_text (W N sites slots header bits start src sb rom rb base scratch sink : ℕ)
    (d : Data) (heads : Bank) (b : Banks) :
    text (ProtocolRAMChronologicalShelf.program W N sites slots header bits start src sb rom rb base scratch sink d heads b)=
      shelfTexts := by
  rw [chrono_text,shelfTexts,chrono_text]

end Hierarchy.ProtocolRAMTurnText
end

end OAI
