import OAI.Computability.VPVNP.RAMProcessorGraphRuns

/-!
# Emitting and closing the physical site record buffer

The linked emission routine pops one vacant slot and copies the five staged words
into the reversed buffer. Closing fills each vacant slot with zero words and reverses
the bits onto the output stack for the site's sorting circuit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessor

open BurstRAM BurstRAM.PrivateRAM RAMSerialization

variable {w p r k H : ℕ}

private def Snapshot.setBuffer (s : Snapshot w p r k) (left reverseBuffer output : List Bool) :=
  {s with remaining := left, reverseBuffer := reverseBuffer, output := output}

private theorem Snapshot.buffer_frame (s : Snapshot w p r k) (left buf out : List Bool)
    (j : Port r k) (hj : ∀ i, recordPorts i ≠ j) :
    (s.setBuffer left buf out).bank j = s.bank j := by
  cases j with
  | record i =>
    cases i with
    | remaining => exact (hj .remaining rfl).elim
    | reverseBuffer => exact (hj .reverseBuffer rfl).elim
    | output => exact (hj .output rfl).elim
    | field i => rfl
    | temp | zeros => rfl
  | test i => cases i with | word f => cases f <;> rfl | _ => rfl
  | _ => rfl

private theorem record_routine (T : Template p r k) (s : Snapshot w p r k)
    {rt : FiniteRoutine RecordBuffer.Port} {l next : Label p r}
    (link : blocks T l = (Fragment.returning rt next).onPorts recordPorts)
    {t left buf out} (h : rt.Runs t s.records (s.setBuffer left buf out).records) :
    StackRuns (table T) t (atLabel T l) s.bank (atLabel T next) (s.setBuffer left buf out).bank := by
  apply ProcessorFlow.run (blocks := blocks T)
  rw [link]
  exact Fragment.runs_framed recordPorts_injective (Fragment.returning_runs h next)
    s.record_at (s.setBuffer left buf out).record_at (s.buffer_frame left buf out)

/-- A single slot holds the reversed serialization of the actual staged record. -/
def Snapshot.afterEmit (s : Snapshot w p r k) (hw : 2 ≤ w) (record : WordRecord w) :=
  s.setBuffer s.remaining.tail
    ((List.ofFn ((recordFormat hw).encode (some record))).reverse ++ s.reverseBuffer) s.output

/-- Emit a staged initialization or probe record at its linked occurrence. -/
theorem record_emit_run (T : Template p r k) (s : Snapshot w p r k) (hw : 2 ≤ w)
    {l next : Label p r}
    (link : blocks T l = (Fragment.returning RecordBuffer.appendRecord next).onPorts recordPorts)
    {records : List (WordRecord w)} (hbuf : RecordBuffer.Holds hw H records s.records)
    (hfree : records.length < 4*H) (record : WordRecord w)
    (hf : ∀ j, s.records (.field j) = BurstRAM.wordBits ((recordFormat hw).words (some record) j)) :
    StackRuns (table T) (25*w+12) (atLabel T l) s.bank (atLabel T next) (s.afterEmit hw record).bank ∧
      RecordBuffer.Holds hw H (records ++ [record]) (s.afterEmit hw record).records := by
  obtain ⟨hr,hh⟩ := hbuf.emit hfree record hf
  have hremaining : s.remaining = true :: List.replicate (4*H-(records.length+1)) true := by
    change s.records .remaining = _
    rw [hbuf.remaining, show 4*H-records.length = (4*H-(records.length+1))+1 by omega, List.replicate_succ]
  have he : (s.afterEmit hw record).records =
      RecordBuffer.emitted s.records (List.replicate (4*H-(records.length+1)) true)
        (List.ofFn ((recordFormat hw).encode (some record))) := by
    funext j
    cases j with
    | remaining => exact congrArg List.tail hremaining
    | _ => rfl
  rw [← he] at hr hh
  exact ⟨record_routine T s link hr, hh⟩

/-- A probe reaches its ordinal increment after exactly the five word copies. -/
theorem emit_run (T : Template p r k) (s : Snapshot w p r k) (hw : 2 ≤ w) (next : Fin p)
    {records : List (WordRecord w)} (hbuf : RecordBuffer.Holds hw H records s.records)
    (hfree : records.length < 4*H) (record : WordRecord w)
    (hf : ∀ j, s.records (.field j) = BurstRAM.wordBits ((recordFormat hw).words (some record) j)) :
    StackRuns (table T) (25*w+12) (atLabel T (.emit next)) s.bank (atLabel T (.increment next))
        (s.afterEmit hw record).bank ∧
      RecordBuffer.Holds hw H (records ++ [record]) (s.afterEmit hw record).records :=
  record_emit_run T s hw rfl hbuf hfree record hf

/-- The actual pop reaches a rejecting row in one step when the slot stack is empty
or when its top is a false mark. -/
theorem record_emit_reject (T : Template p r k) (s : Snapshot w p r k) {l next : Label p r}
    (link : blocks T l = (Fragment.returning RecordBuffer.appendRecord next).onPorts recordPorts)
    (hbad : s.remaining.head? ≠ some true) :
    RejectRun (table T) 1 (atLabel T l) s.bank := by
  let rt := RecordBuffer.appendRecord
  have hs : StackStep rt.body.standalone (some rt.body.entry) s.records _ _ :=
    StackStep.pop (k := RecordBuffer.Port.remaining) rfl
  change (s.records .remaining).head? ≠ some true at hbad
  cases he : (s.records .remaining).head? with
  | none =>
    rw [he] at hs
    exact ProcessorFlow.routine_reject (blocks := blocks T) recordPorts_injective link
      (StackRuns.cons hs (.nil _ _)) rfl s.record_at
  | some b =>
    cases b with
    | false =>
      rw [he] at hs
      exact ProcessorFlow.routine_reject (blocks := blocks T) recordPorts_injective link
        (StackRuns.cons hs (.nil _ _)) rfl s.record_at
    | true => exact (hbad he).elim

/-- After the close routine, the padded record array is serialized on the output stack. -/
def Snapshot.afterClose (s : Snapshot w p r k) (hw : 2 ≤ w) (H : ℕ) (records : List (WordRecord w)) :=
  s.setBuffer [] [] (List.ofFn ((blockFormat H hw).encode (RecordBuffer.slots H records)))

/-- The site reaches its accepting row with the canonical serialized, padded record block. -/
theorem close_run (T : Template p r k) (s : Snapshot w p r k) (hw : 2 ≤ w)
    {records : List (WordRecord w)} (hbuf : RecordBuffer.Holds hw H records s.records) :
    StackRuns (table T) ((4*H-records.length)*(25*w+12)+1+(2*(4*H*5*w)+1)) (atLabel T .close) s.bank
      (atLabel T .done) (s.afterClose hw H records).bank := by
  have hr := hbuf.close
  apply record_routine T s (rt := RecordBuffer.close) rfl
  convert hr using 2
  funext j
  cases j <;> rfl

end RAMTape.SiteProcessor

end VPVNP
end Computability
end OAI
