import OAI.Hierarchy.ProtocolRAMTurnChart

namespace OAI
/-! # Exact costs of the fixed seven field gather and of the chronological site walk -/

namespace Hierarchy.ProtocolRAMTurnCost
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProbeStage.Native

theorem site_ticks (base bits initial N : ℕ) (d : ProtocolRAMTurnChart.Data) (edge tail head : Bank) :
    ProtocolRAMVisitColumns.ticks N initial (ProtocolRAMTurnChart.walk base bits d edge tail head)=25+206*N := by
  rw [ProtocolRAMVisitColumns.ticks_eq]
  change 25+N*(22+2*16+2*76)=_
  omega

theorem site_cheap (W base bits initial N : ℕ) (d : ProtocolRAMTurnChart.Data) (edge tail head : Bank) :
    CheapCode (ProtocolRAMVisitColumns.program W N initial (ProtocolRAMTurnChart.walk base bits d edge tail head)) :=
  cheap_seq (cheap_seq (scan_cheap _ _ _ _) (program_cheap _ _)) (ProtocolRAMTurnWalk.cheap _ _ _ _ _)

private theorem column_clock (n start : ℕ) (terms : List Expr) :
    ProtocolRAM.clock (columns n start terms) =
      4+terms.length*(4+4*n)+(terms.map Expr.work).sum*(2*n) := by
  induction terms generalizing start with
  | nil => simp [columns,ProtocolRAM.clock]
  | cons term tail ih =>
    simp only [columns,ProtocolRAM.clock,Pass.clock,List.length_cons,List.map_cons,List.sum_cons,ih]
    ring

private def fieldWork : Fin 7→ℕ := ![550,556,658,664,72,7,54]

set_option maxRecDepth 16384 in
private theorem field_work (base bits : ℕ) (d : ProtocolRAMTurnChart.Data)
    (b : ProtocolRAMTurnItinerary.Banks) (i : Fin 7) :
    (ProtocolRAMTurnItinerary.field (ProtocolRAMTurnChart.chart base bits d) b i).work=fieldWork i := by
  fin_cases i <;> rfl

theorem gather_ticks (base bits output N : ℕ) (d : ProtocolRAMTurnChart.Data) (b : ProtocolRAMTurnItinerary.Banks) :
    ProtocolRAMTurnItinerary.ticks output N (ProtocolRAMTurnChart.chart base bits d) b=32+5150*N := by
  rw [ProtocolRAMTurnItinerary.ticks,column_clock,List.length_ofFn,List.map_ofFn]
  have listed : Expr.work ∘ ProtocolRAMTurnItinerary.field (ProtocolRAMTurnChart.chart base bits d) b=fieldWork :=
    funext (field_work base bits d b)
  rw [listed,show (List.ofFn fieldWork).sum=2561 by decide]
  ring

theorem full_ticks (base bits initial output N sites seats : ℕ) (d : ProtocolRAMTurnChart.Data)
    (edge tail head : Bank) (b : ProtocolRAMTurnItinerary.Banks) :
    ProtocolRAMVisitColumns.ticks N initial (ProtocolRAMTurnChart.walk base bits d edge tail head)+
      (ProtocolRAMTurnItinerary.ticks output N (ProtocolRAMTurnChart.chart base bits d) b+
        (15+30*(sites*seats)+740*N)) = 72+6096*N+30*(sites*seats) := by
  rw [site_ticks,gather_ticks]
  ring

end Hierarchy.ProtocolRAMTurnCost

end OAI
