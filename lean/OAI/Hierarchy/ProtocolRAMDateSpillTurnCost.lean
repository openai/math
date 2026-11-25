import OAI.Hierarchy.ProtocolRAMDateSpillTurnPage

namespace OAI
/-! # Native text and time for one complete original-order dated spill shelf -/
namespace Hierarchy.ProtocolRAM.DateSpill
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native Calendar
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAMTurnChart ProtocolRAMTurnItinerary
open scoped Classical

private theorem column_text (W base rows maxWork : ℕ) (es : List Expr)
    (bounded : ∀e∈es,e.work≤ maxWork) :
    text (ProtocolRAM.program W (ProbeStage.Native.columns rows base es))≤15+es.length*(11+4*maxWork) := by
  induction es generalizing base with
  | nil =>
    simp [Calendar.text_passes, Calendar.listText, ProbeStage.Native.columns]
  | cons e es ih =>
    have tail := ih (base+rows) (fun t ht=>bounded t (List.mem_cons_of_mem _ ht))
    have head := bounded e List.mem_cons_self
    change text ((scan W base rows e).seq (ProtocolRAM.program W (ProbeStage.Native.columns rows (base+rows) es)))≤_
    rw [text_seq,Calendar.text_scan]
    simp only [Calendar.rowText,List.length_cons,Nat.succ_mul es.length]
    omega

namespace TurnPage
variable {roles : ℕ} (P : TurnPage roles)

private def gatherWork : Fin 7 → ℕ := ![550,556,883,895,72,7,54]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 3000000 in
private theorem chart_gather_work (header bits : ℕ) (d : ProtocolRAMTurnChart.Data)
    (b : ProtocolRAMTurnItinerary.Banks) (off : Turns.Offsets) (f : Fin 7) :
    (Turns.fields (ProtocolRAMTurnChart.chart header bits d) b off f).work = gatherWork f := by
  fin_cases f <;> rfl

theorem gather_work (f : Fin 7) : (Turns.fields P.chart P.banks P.added f).work≤3000 := by
  change (Turns.fields (ProtocolRAMTurnChart.chart P.terminal.header P.terminal.headerBits P.data)
    P.banks P.added f).work ≤ 3000
  rw [chart_gather_work]
  fin_cases f <;> decide

theorem relocated_work (f : Fin 4) : (Relocate.term P.terminal.rom P.terminal.romBits P.terminal.turns
    P.terminal.base P.base f).work≤20 := by fin_cases f <;> exact of_decide_eq_true rfl

theorem text_le (W limit : ℕ)
    (hl : P.left.prefix.work≤limit) (hr : P.right.prefix.work≤limit) :
    text (P.program W)≤ProtocolRAMTurnText.shelfTexts+90000+8*limit := by
  have ws:=column_text W P.window.src P.terminal.turns 3000 (List.ofFn (Turns.fields P.chart P.banks P.added))
    (by intro e he;obtain ⟨f,rfl⟩:=List.mem_ofFn.mp he;exact P.gather_work f)
  have rs:=column_text W P.directory (2^P.terminal.romBits) 20 (List.ofFn (Relocate.term P.terminal.rom P.terminal.romBits
    P.terminal.turns P.terminal.base P.base))
    (by intro e he;obtain ⟨f,rfl⟩:=List.mem_ofFn.mp he;exact P.relocated_work f)
  simp only [List.length_ofFn] at ws rs
  change text (ProtocolRAM.program W P.words)≤_ at ws
  change text (ProtocolRAM.program W P.romPasses)≤_ at rs
  have original:=ProtocolRAMTurnText.shelf_text W P.terminal.turns P.terminal.sites P.terminal.seats
    P.terminal.header P.terminal.headerBits P.window.zero P.window.src P.window.srcBits P.directory P.terminal.romBits
    P.base P.window.scratch P.window.sink P.data P.terminal.heads P.banks
  change text ((P.visit W).seq ((ProtocolRAMTurnItinerary.program W P.window.src P.terminal.turns P.chart P.banks).seq
    (P.write W)))=_ at original
  simp only [text_seq] at original
  rw [program,output,text_seq,text_seq,text_seq,text_seq,DatedSpillOffsets.Layout.text]
  omega

theorem ticks_le (limit : ℕ) (hl : P.left.prefix.work≤limit) (hr : P.right.prefix.work≤limit) :
    P.ticks≤160+((2*limit+4)*(P.ranks.old+P.ranks.edges))+
      176*2^P.terminal.romBits+44000*P.terminal.turns+30*(P.terminal.sites*P.terminal.seats) := by
  have ws:=columns_clock P.terminal.turns P.window.src 3000 (List.ofFn (Turns.fields P.chart P.banks P.added))
    (by intro e he;obtain ⟨f,rfl⟩:=List.mem_ofFn.mp he;exact P.gather_work f)
  have rs:=columns_clock (2^P.terminal.romBits) P.directory 20 (List.ofFn (Relocate.term P.terminal.rom
    P.terminal.romBits P.terminal.turns P.terminal.base P.base))
    (by intro e he;obtain ⟨f,rfl⟩:=List.mem_ofFn.mp he;exact P.relocated_work f)
  simp only [List.length_ofFn] at ws rs
  change clock P.words≤_ at ws
  change clock P.romPasses≤_ at rs
  have old:=Nat.mul_le_mul_left P.ranks.old (show 2*P.left.prefix.work+4≤2*limit+4 by omega)
  have new:=Nat.mul_le_mul_left P.ranks.edges (show 2*P.right.prefix.work+4≤2*limit+4 by omega)
  change ((4+P.ranks.old*(2*P.left.prefix.work+4)+(4+P.ranks.edges*(2*P.right.prefix.work+4)))+clock P.romPasses)+_≤_
  nlinarith


end TurnPage
end Hierarchy.ProtocolRAM.DateSpill

end OAI
