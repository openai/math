import OAI.Optimization.LinearProgramming.RAM.CallableBase
import OAI.Optimization.LinearProgramming.RAM.CallableReturn
import OAI.Optimization.LinearProgramming.RAM.CallPrepared

/-! A native program used as one statement of a structured caller. Return instructions in
the callee are relocated to an in-line tag table, which writes the return value and jumps
back to the following statement. The caller's saved registers occupy the odd addresses. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

private def subroutineWidth (p : Program) : ℕ := (p.map Call.width).sum

private theorem subroutine_length (p : Program) (pc : ℕ) (ret : ℕ → ℕ) :
    (Call.subroutine p pc ret).length = subroutineWidth p :=
  Layout.assemble_length p Call.width pc _ (Call.emit_length ret)

private def returnPC (table endPC count tag : ℕ) := if tag < count then table+2*tag else endPC

namespace Fragment

/-- Invoke `p` at the current code location. Each of the `count` supported return tags
has a literal instruction writing the result followed by a jump to the continuation. -/
def invoke (p : Program) (count : ℕ) (sink : TagSink) : Fragment where
  size := subroutineWidth p + 2*count
  emit pc :=
    let table := pc + subroutineWidth p
    let endPC := pc + (subroutineWidth p + 2*count)
    Call.subroutine p pc (returnPC table endPC count) ++ tagTable sink count endPC
  length_emit pc := by simp only [List.length_append, subroutine_length, length_tagTable]

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The memory after a supported return. Its even bank is the callee's actual final bank.
The literal return instruction updates one physical scalar or index register. -/
def returnMemory (sink : TagSink) (tag : ℕ) (physical : Memory K) (last : State K) : Memory K :=
  sink.store tag (Call.pack last.memory (Call.savedOddFrame physical))

/-- Start a native program from its ordinary input tape, already packed in the even
registers. A native run of `k` steps uses at most `2*k+2` physical caller instructions,
including writing the tag and jumping to the next statement. -/
theorem invoke_prepared {p : Program} (count : ℕ) (sink : TagSink) (P : K → Prop)
    (physical : Memory K) (dims : List ℕ) (input : List K) {k tag : ℕ}
    (trace : Fin (k+1) → State K) (htag : tag < count)
    (hdata : ∀ j, physical.data (2*j) = (start dims input).data j)
    (hindex : ∀ j, physical.index (2*j) = 2*(start dims input).index j)
    (hphysical : ∀ j, P (physical.data j)) (hrun : Trace p (start dims input) k trace)
    (hsafe : ∀ i j, P ((trace i).data j)) (hdone : (trace (Fin.last k)).output = some tag)
    (hresult : ∀ j, P ((returnMemory sink tag physical (trace (Fin.last k))).data j)) :
    (invoke p count sink).Run P physical (2*k+2) (returnMemory sink tag physical (trace (Fin.last k))) := by
  intro prog pc code
  let base := pc + subroutineWidth p
  let endPC := pc + (subroutineWidth p + 2*count)
  let ret := returnPC base endPC count
  let last := trace (Fin.last k)
  have whole : CodeAt prog pc (Call.subroutine p pc ret ++ tagTable sink count endPC) := code
  have returning := Call.invoke_prepared_trace (original := p) physical dims input P
    whole.left hdata hindex hphysical trace hrun hsafe hdone
  obtain ⟨l,hl,s,hr,hed,hei,hod,hoi⟩ := returning
  have hframe : Call.savedOddFrame s = Call.savedOddFrame physical :=
    congrArg₂ Memory.mk (funext hod) (funext hoi)
  have hs : s = Call.pack last.memory (Call.savedOddFrame physical) :=
    (Call.eq_pack_of_even s last.memory hed hei).trans (congrArg (Call.pack last.memory) hframe)
  have hret : ret tag = base + 2*tag := by simp [ret,returnPC,htag]
  have htab : CodeAt prog base (tagTable sink count endPC) := by
    simpa only [base, subroutine_length] using whole.right
  rw [hret] at hr
  have hsink : ∀ j, P ((sink.store tag s).data j) := hs ▸ hresult
  have finish := tagTable_exec (safe := fun m : Memory K => ∀ j, P (m.data j))
    sink count endPC base tag s htab htag hr.safe_end hsink
  refine ⟨l+2,Nat.add_le_add_right hl 2,?_⟩
  rw [hs] at finish hr
  exact hr.append finish

end Fragment

variable {K : Type*}

/-- The odd projection through a native call is literally the preserved logical memory. -/
@[simp] theorem savedOddFrame_pack (callee caller : Memory K) :
    Call.savedOddFrame (Call.pack callee caller) = caller := by
  cases caller with
  | mk d a =>
    apply congrArg₂ Memory.mk
    · funext i; exact Call.data_odd ..
    · funext i; exact Call.index_odd ..

@[simp] theorem savedOddFrame_putData (m : Memory K) (dst : ℕ) (x : K) :
    Call.savedOddFrame (m.putData (2*dst+1) x) = (Call.savedOddFrame m).putData dst x := by
  apply congrArg₂ Memory.mk
  · funext j
    by_cases hj : j=dst
    · subst j; simp [Call.savedOddFrame, Memory.putData]
    · simp [Call.savedOddFrame, Memory.putData, hj]
  · rfl

@[simp] theorem savedOddFrame_putIndex (m : Memory K) (dst v : ℕ) :
    Call.savedOddFrame (m.putIndex (2*dst+1) v) = (Call.savedOddFrame m).putIndex dst v := by
  apply congrArg₂ Memory.mk
  · rfl
  · funext j
    by_cases hj : j=dst
    · subst j; simp [Call.savedOddFrame, Memory.putIndex]
    · simp [Call.savedOddFrame, Memory.putIndex, hj]

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
