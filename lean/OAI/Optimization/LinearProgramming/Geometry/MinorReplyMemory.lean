import OAI.Optimization.LinearProgramming.Geometry.BorderProtocol
import OAI.Optimization.LinearProgramming.Geometry.OracleSegments
import OAI.Optimization.LinearProgramming.RAM.Array
import OAI.Optimization.LinearProgramming.RAM.CallableReturn

/-! Concrete scalar-bank form of the sealed geometric reply, ready for native serialization. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace MinorInstall

open RAM RAM.Callable OracleSpec Contraction.Machine OracleSegments

def responseTag : Option ℚ → ℕ
  | none => 1
  | some _ => 0

def responseSink : TagSink := .scalar 2 (fun tag => (tag:ℚ))

theorem responseTag_lt (ans : Option ℚ) : responseTag ans < 2 := by cases ans <;> simp [responseTag]

theorem emits_tag {z : State ℚ} {ans : Option ℚ} (h : MinorLog.emits z ans) : z.output=some (responseTag ans) := by
  cases ans with
  | none => exact h
  | some q => exact h.1

theorem responseSink_safe (m : Memory ℚ) (P : ℚ → Prop) (ans : Option ℚ) (hm : m.AllData P) (hz : P 0) (ho : P 1) :
    (responseSink.store (responseTag ans) m).AllData P := by
  cases ans with
  | none => simpa [responseTag,responseSink,TagSink.store] using hm.putData 2 ho
  | some _ => simpa [responseTag,responseSink,TagSink.store] using hm.putData 2 hz

private theorem received_outside (m : Memory ℚ) (xs : List ℚ) (p : ℕ)
    (out : p < m.index 82 ∨ m.index 82+xs.length ≤ p) : (received m 82 83 xs).data p=m.data p := by
  change (if m.index 82 ≤ p then xs[p-m.index 82]?.getD (m.data p) else m.data p)=m.data p
  split
  · rename_i le
    rw [List.getElem?_eq_none (by omega : xs.length ≤ p-m.index 82)]
    rfl
  · rfl

private theorem memory_eq {m t : Memory ℚ} (hd : ∀p,m.data p=t.data p) (hi : m.index=t.index) : m=t := by
  exact congrArg₂ Memory.mk (funext hd) hi

theorem received_none (m : Memory ℚ) :
    received m 82 83 (BorderBatch.reply none)=(m.putData (m.index 82) 1).putIndex 83 1 := by
  refine memory_eq (m := received m 82 83 (BorderBatch.reply none))
    (t := (m.putData (m.index 82) 1).putIndex 83 1) ?_ rfl
  intro p
  by_cases eq : p=m.index 82
  · subst p
    simp [received,receivePacket,State.memory,Memory.atPC,BorderBatch.reply]
  · rw [received_outside m _ p (by change p < m.index 82 ∨ m.index 82+1 ≤ p; omega)]
    simp [eq]

theorem received_some (m : Memory ℚ) (q : ℚ) :
    received m 82 83 (BorderBatch.reply (some q))=
      ((m.putData (m.index 82) 0).putData (m.index 82+1) q).putIndex 83 2 := by
  refine memory_eq (m := received m 82 83 (BorderBatch.reply (some q)))
    (t := ((m.putData (m.index 82) 0).putData (m.index 82+1) q).putIndex 83 2) ?_ rfl
  intro p
  by_cases first : p=m.index 82
  · subst p
    simp [received,receivePacket,State.memory,Memory.atPC,BorderBatch.reply]
  by_cases second : p=m.index 82+1
  · subst p
    simp [received,receivePacket,State.memory,Memory.atPC,BorderBatch.reply]
  · rw [received_outside m _ p (by change p < m.index 82 ∨ m.index 82+2 ≤ p; omega)]
    simp [first,second]

end MinorInstall
end Geometry
end LinearProgramming
end Optimization
end OAI
