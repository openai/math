import OAI.ThreeFlat.RAM.TickChunkProgram
import OAI.ThreeFlat.RAM.TickChunkReads
import OAI.ThreeFlat.RAM.TickRequestStream
import OAI.ThreeFlat.RAM.TickCheckedStream

namespace OAI
/-! # Group comparison records for a physical external chunk -/

namespace ThreeFlat.RAM.TickChunkCheck

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan Diagonal.TickAuxiliary
open Diagonal.TickGroupIntervals TickIntervalCursor TickBitRelation ChunkRequests
open scoped Fin.CommRing Classical

/-- The live rule expression remains correct after any partial overwrite of
the generated-record area. In a nonscan phase the constant rule compares the
two words of every external endpoint for equality. -/
theorem eval_rule {w k : ℕ} (par : Fin k → Word w) (groupScan : Bool)
    (L : Layout) (fit : L.Fits w) (es : List Interval) (disj : es.Pairwise Compatible)
    (m m' : Memory w) (start oldPtr newPtr : ℕ) (op np : ℕ → Bool)
    (same : agreesOutside start (start+8*chunkSize L) m' (output L m es))
    (inputs : groupScan = true →
      (∀ j < chunkSize L, m (L.mapBase+j) = 0) ∧
      (∀ i : Fin (chunkSize L), codeAt L es i.val < 2^w) ∧
      (∀ i : Fin (chunkSize L), outside start (chunkSize L) ((L.mapBase : Word w)+(i.val : Word w)).val) ∧
      PairReads (output L m es) start L es oldPtr op ∧
      PairReads (output L m es) start L es newPtr np)
    (i : Fin (chunkSize L)) :
    (ruleExpr w k groupScan L oldPtr newPtr).eval par m' (fun _ => (i.val : Word w)) =
      ((rules groupScan L es op np i.val).tag : Word w) := by
  cases groupScan with
  | false => simp [ruleExpr,rules,Rule.tag]
  | true =>
    obtain ⟨zero,size,mapSafe,old,new⟩ := inputs rfl
    apply TickChunkRule.atRow_eval par m' L.mapBase oldPtr newPtr (i.val : Word w)
      (codeAt L es i.val) op np (size i)
    · exact (same _ (mapSafe i)).trans (read_code L fit es disj m zero i)
    · exact pairRead old same i
    · exact pairRead new same i

theorem holds_iff (groupScan : Bool) (L : Layout) (es : List Interval) (op np : ℕ → Bool)
    (a b : Fin (chunkSize L) → Bool) :
    (∀ i, (rules groupScan L es op np i.val).holds (a i) (b i)) ↔ valid groupScan L es op np a b := by
  unfold valid
  apply forall_congr'
  intro i
  cases groupScan with
  | false => simp [rules,Rule.holds]
  | true =>
    by_cases h : codeAt L es i.val = 0 <;>
      simpa [rules,h] using TickChunkRule.rule_holds (codeAt L es i.val) op np (a i) (b i)

/-- A group phase uses the overlap map already produced by the physical interval
cursor. In other phases the empty interval list gives the same native check
on the untouched input memory. -/
theorem mass_chunk {w p r k : ℕ} {F : Type*} [Semiring F] (field : FieldCode F w)
    (M : Machine w p r k) (groupScan : Bool) (layout : Layout) (rooms : layout.Fits w)
    (es : List Interval) (disj : es.Pairwise Compatible) (start oldPtr newPtr : ℕ)
    (op np : ℕ → Bool) (old new : Word w) (a b : Fin (chunkSize layout) → Bool)
    (c : Config w p r) (m : Memory w) (fit : 64 ≤ 2^w)
    (endFit : start+8*chunkSize layout < 2^w)
    (genPC : Fin ((TickRequestStream.program start (ruleExpr w k groupScan layout oldPtr newPtr)).labels+6) → Fin p)
    (genRegs : Fin (4+(TickRequestStream.program start (ruleExpr w k groupScan layout oldPtr newPtr)).binds) ↪ Fin r)
    (setup : Fin 7 → Fin p) (R : Registers w k r) (L : ChunkRequests.Labels w k p)
    (zeroReg : Fin r) (test bad next : Fin p)
    (genROM : ∀ i, M.code (genPC i) = TickGenerateTable.emit
      (TickRequestStream.program start (ruleExpr w k groupScan layout oldPtr newPtr))
      (start : Word w) (start+8*chunkSize layout : ℕ) genPC genRegs (setup 0) i)
    (setupROM : ∀ i, M.code (setup i) = TickCheckSetup.emit setup R.slot
      (TickCheckSetup.values (start : Word w) old new (start+8*chunkSize layout : ℕ)) L.guard i)
    (checkROM : ContinueInstalled M R L zeroReg test bad next)
    (entry : c.pc = TickGenerateTable.driver
      (TickRequestStream.program start (ruleExpr w k groupScan layout oldPtr newPtr)) genPC 0)
    (inputs : groupScan = true →
      (∀ j < chunkSize layout, m (layout.mapBase+j) = 0) ∧
      (∀ i : Fin (chunkSize layout), codeAt layout es i.val < 2^w) ∧
      (∀ i : Fin (chunkSize layout), outside start (chunkSize layout)
        ((layout.mapBase : Word w)+(i.val : Word w)).val) ∧
      PairReads (output layout m es) start layout es oldPtr op ∧
      PairReads (output layout m es) start layout es newPtr np)
    (oldOutside : ∀ i : Fin (chunkSize layout), (old+(i.val : Word w)).val < start)
    (newOutside : ∀ i : Fin (chunkSize layout), (new+(i.val : Word w)).val < start)
    (old_ok : ∀ i : Fin (chunkSize layout), bitAt (output layout m es) old (i.val : Word w) = bitWord w (a i))
    (new_ok : ∀ i : Fin (chunkSize layout), bitAt (output layout m es) new (i.val : Word w) = bitWord w (b i)) :
    let expr := TickRequestStream.program start (ruleExpr w k groupScan layout oldPtr newPtr)
    let packed := output layout m es
    let saved := fillSegment start (8*chunkSize layout) (TickRequestStream.dataWord start
      (rules groupScan layout es op np)) packed
    ∃ t ≤ 14+8*chunkSize layout*(expr.steps+3)+chunkSize layout*122,
      ∃ out : Config w p r, out.pc = next ∧ ∀ fuel, mass field M.program (fuel+t) c packed =
        if valid groupScan layout es op np a b then mass field M.program fuel out saved else 0 := by
  dsimp only
  simpa only [holds_iff groupScan layout es op np a b] using
    TickCheckedStream.mass_generated field M (ruleExpr w k groupScan layout oldPtr newPtr)
      (rules groupScan layout es op np) start old new a b c (output layout m es) fit endFit
      genPC genRegs setup R L zeroReg test bad next genROM setupROM checkROM entry
      (fun mm agree => eval_rule M.publicData groupScan layout rooms es disj m mm start oldPtr newPtr
        op np agree inputs) oldOutside newOutside old_ok new_ok

/-- Prepend the actual interval cursor to a chunk check. The combined bound
charges once for the descriptor list and once for the local chunk bits. -/
theorem with_intervals {w p r k : ℕ} {F : Type*} [Semiring F] (field : FieldCode F w)
    (M : Machine w p r k) (pc : Fin 27 → Fin p) (reg : Fin 15 ↪ Fin r) (entry next : Fin p)
    (rom : TickIntervalCursor.Installed M pc reg entry)
    (L : Layout) (fit : L.Fits w) (es : List Interval) (disj : es.Pairwise Compatible)
    (addr : ℕ) (endFit : addr+4*es.length < 2^w) (rows : ∀ e ∈ es, FitsRow e w)
    (c : Config w p r) (m : Memory w) (head : c.pc = pc 0) (stored : Stores m addr es)
    (cursor : c.reg (reg 0) = (addr : Word w))
    (endReg : c.reg (reg 1) = ((addr+4*es.length : ℕ) : Word w))
    (lo : c.reg (reg 2) = (L.chunkStart : Word w)) (hi : c.reg (reg 3) = (L.chunkEnd : Word w))
    (mapReg : c.reg (reg 4) = (L.mapBase : Word w)) (group : c.reg (reg 5) = (L.group : Word w))
    (separate : ∀ x, addr ≤ x → x < addr+4*es.length →
      x < L.mapBase ∨ L.mapBase+chunkSize L ≤ x)
    (saved : Memory w) (guard : Prop)
    (check : ∀ d : Config w p r, d.pc = entry →
      ∃ t ≤ 14+4314*chunkSize L, ∃ out : Config w p r, out.pc = next ∧
        ∀ fuel, mass field M.program (fuel+t) d (output L m es) =
          if guard then mass field M.program fuel out saved else 0) :
    ∃ t ≤ 16+20*es.length+4319*chunkSize L, ∃ out : Config w p r, out.pc = next ∧
      ∀ fuel, mass field M.program (fuel+t) c m = if guard then mass field M.program fuel out saved else 0 := by
  obtain ⟨d,ran,atEntry,_⟩ := advance_intervals M pc reg entry rom L fit es addr endFit rows
    c m head stored cursor endReg lo hi mapReg group separate
  obtain ⟨t,price,out,atNext,sem⟩ := check d atEntry
  have bound := TickIntervalCursor.cost_le L es disj
  change TickIntervalCursor.cost L es ≤ 2+20*es.length+5*chunkSize L at bound
  refine ⟨TickIntervalCursor.cost L es+t,by omega,out,atNext,?_⟩
  intro fuel
  rw [show fuel+(TickIntervalCursor.cost L es+t) = (fuel+t)+TickIntervalCursor.cost L es by omega]
  exact (mass_of_advance field M.program ran (fuel+t)).trans (sem fuel)


end ThreeFlat.RAM.TickChunkCheck

end OAI
