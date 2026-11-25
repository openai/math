import OAI.Hierarchy.ProtocolRAMPurchaseStage

namespace OAI
/-! # Native purchase-stage running time in terms of the finite local menu -/

namespace Hierarchy.ProtocolRAM.PurchaseStage
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators

variable {q d : ℕ}

/-- Path decoding and marking use a fixed number of CPU steps per gate and per tile. -/
theorem dispatch_time (L : Dispatch) : dispatchClock L ≤
    23+209*(L.candidates*(4*L.depth+3))+42*(4+L.tiles+L.first+L.candidates) := by
  have clock := dispatchClock_le L
  have size : (MarkTape.loadTerm L.tiles L.marks).work=19 := rfl
  rw [MarkTape.loadClock,size] at clock
  omega

private theorem audit_columns (ps : List Pass) : auditTicks (columns ps)=clock ps ∧
    verdict (columns ps)=.lit 0 := by
  induction ps with
  | nil => exact ⟨rfl,rfl⟩
  | cons p ps ih =>
    change p.clock+auditTicks (columns ps)=p.clock+clock ps ∧ verdict (columns ps)=.lit 0
    simp [ih.1,ih.2]

theorem verdict_work (L : Dispatch) (B : Repair q d) : (verdict (audits L B)).work=10 := by
  simp only [audits,verdict,(audit_columns (writes L B)).2,Expr.work]

theorem write_rows (L : Dispatch) (B : Repair q d) {p : Pass} (hp : p∈writes L B) :
    p.rows=L.candidates := by
  simp only [writes,priceColumns,List.mem_cons,List.mem_append,List.mem_ofFn,List.mem_flatten] at hp
  rcases hp with h | h | h | ((⟨k,h⟩ | ⟨k,h⟩) | (⟨g,⟨k,h⟩,hg⟩ | ⟨k,h⟩))
  all_goals first | subst p; rfl | subst g
  simp only [stockWrites,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with h | h | h <;> subst p <;> rfl

private theorem list_clock_bound (ps : List Pass) (rows expr : ℕ)
    (rowBound : ∀ p∈ps,p.rows≤ rows) (workBound : ∀ p∈ps,p.term.work≤expr) :
    clock ps≤4+ps.length*(4+rows*(2*expr+4)) := by
  exact clock_le ps rows expr (fun p hp => ⟨rowBound p hp,workBound p hp⟩)

/-- Counts the two complete descriptor records, installed stock, reserve and discharge,
and every actually quoted price column. The three leading words are menu, buy, and mode. -/
theorem writes_length (L : Dispatch) (B : Repair q d) :
    (writes L B).length=17+3*d+B.batch.quotes.length := by
  simp [writes,priceColumns,stockWrites,List.length_flatten,List.map_ofFn,Function.comp_def]
 ; omega

/-- A bound uniform over all matches, inventories, admitted histograms and purchases.
The local expression work is the sole menu-dependent quantity. -/
theorem ticks_bound (L : Dispatch) (B : Repair q d) (expr : ℕ)
    (workBound : ∀ p∈writes L B,p.term.work≤expr) :
    ticks L B ≤ 23+209*(L.candidates*(4*L.depth+3))+42*(4+L.tiles+L.first+L.candidates)+
      B.tests.ticks+(4+L.candidates*(2*(repairMask B).work+4))+
      ((4+L.candidates*(2*(invalidExpr (enabledBatch L B)).work+4))+(7+6*2+11*L.candidates))+
      (4+(17+3*d+B.batch.quotes.length)*(4+L.candidates*(2*expr+4)))+28 := by
  have cost := list_clock_bound (writes L B) L.candidates expr (fun _ hp => (write_rows L B hp).le) workBound
  rw [writes_length] at cost
  have dispatch := dispatch_time L
  have ctrl:=verdict_work L B
  change dispatchClock L + (B.tests.ticks + ((4+L.candidates*(2*(repairMask B).work+4)) +
    ((Audit.ticks (.check (inspection L B))+auditTicks (columns (writes L B))) +
      (4+1*(2*(verdict (audits L B)).work+4))))) ≤ _
  rw [ctrl,(audit_columns _).1]
  simp only [Audit.ticks,inspection]
  omega

end Hierarchy.ProtocolRAM.PurchaseStage

end OAI
