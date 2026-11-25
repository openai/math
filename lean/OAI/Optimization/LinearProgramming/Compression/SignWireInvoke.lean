import OAI.Optimization.LinearProgramming.RAM.CallableInvoke
import OAI.Optimization.LinearProgramming.Compression.SignWireTagProgram

/-! Isolate an entire numerical comparison in the outer even RAM bank. The
odd caller frame can contain the actual linked BitRAM heap and need not encode
an inner logical machine. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open RAM RAM.Callable

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Run a native program from a live, already allocated memory, instead of
restricting the interface to a canonical constant input list. Address 14 is
the return port, while every odd caller address survives every native call. -/
theorem invokeTag14_trace (p : Program) (P : K → Prop) (v frame : Memory K)
    {k tag : ℕ} (tr : Fin (k+1) → State K) (ht : tag < 3)
    (hr : Trace p (v.atPC 0) k tr) (hs : ∀ i j,P ((tr i).data j))
    (hf : frame.AllData P) (done : (tr (Fin.last k)).output=some tag) :
    (Fragment.invoke p 3 (.index 14)).Run P (Call.pack v frame) (2*k+2)
      ((Call.pack (tr (Fin.last k)).memory frame).putIndex 14 tag) := by
  intro prog pc code
  let width := (p.map Call.width).sum
  let table := pc+width
  let endPC := pc+(width+2*3)
  let ret (i : ℕ) := if i<3 then table+2*i else endPC
  have installed : CodeAt prog pc (Call.subroutine p pc ret ++ tagTable (.index 14) 3 endPC) := code
  have safe (i : Fin (k+1)) : ∀ j,P ((Call.pack (tr i).memory frame).data j) := by
    intro j
    simp only [Call.pack]
    split
    · exact hs i _
    · exact hf _
  obtain ⟨time,cost,run⟩ := Call.simulate_execution (ret:=ret) (good:=fun data => ∀ j,P (data j))
    installed.left (Execution.of_trace hr safe)
  let last := tr (Fin.last k)
  have startPC : Call.image frame ret (Layout.addr p Call.width pc) (v.atPC 0) = (Call.pack v frame).atPC pc := by
    change (Call.pack v frame).atPC (Layout.addr p Call.width pc 0)=_
    simp [Layout.addr]
  have endAt : Call.image frame ret (Layout.addr p Call.width pc) last =
      (Call.pack last.memory frame).atPC (table+2*tag) := by
    simp [Call.image,Call.position,last,done,ret,ht]
  change Execution _ _ (Call.image frame ret (Layout.addr p Call.width pc) (v.atPC 0)) _
    (Call.image frame ret (Layout.addr p Call.width pc) last) at run
  rw [startPC,endAt] at run
  have clen : (Call.subroutine p pc ret).length = width :=
    Layout.assemble_length p Call.width pc _ (Call.emit_length ret)
  have tbl : CodeAt prog table (tagTable (.index 14) 3 endPC) := by
    simpa only [table,clen] using installed.right
  have lastSafe (i : ℕ) : P ((Call.pack last.memory frame).data i) := by
    simpa only [Memory.atPC] using run.safe_end i
  have finish := tagTable_exec (safe:=fun s : Memory K => ∀ j,P (s.data j)) (.index 14)
    3 endPC table tag (Call.pack last.memory frame) tbl ht lastSafe (by
      intro i
      change P ((Call.pack last.memory frame).data i)
      exact lastSafe i)
  exact ⟨time+2,Nat.add_le_add_right cost 2,run.append finish⟩

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
/-- Preserve the literal VM heap addresses, including unknown allocations. -/
theorem isolated_odd_frame (u v frame : Memory K) (tag : ℕ) (i : ℕ) (odd : i%2=1) :
    ((Call.pack v frame).putIndex 14 tag).index i=(Call.pack u frame).index i := by
  rw [Memory.putIndex_ne _ (by omega)]
  have eq : i=2*(i/2)+1 := by omega
  conv_lhs => rw [eq]
  conv_rhs => rw [eq]
  simp only [Call.index_odd]

/-- Absolute code entry for the numerical subroutine. All tags come from the
conditional halts appended to its verified arithmetic run. -/
def isolatedSign (f : Fragment) : Fragment := Fragment.invoke (tagReturningProgram f) 3 (.index 14)

theorem isolatedSign_run {f : Fragment} {P : K → Prop} {s t frame : Memory K} {B : ℕ}
    (run : f.Run P s B t) (o : Ordering) (tag : t.index 29=2*comparisonTag o+1)
    (hs : frame.AllData P) :
    ∃ last, (isolatedSign f).Run P (Call.pack s frame) (2*(B+5)+2) ((Call.pack last frame).putIndex 14 (comparisonTag o)) := by
  obtain ⟨k,hk,tr,ht,ho,hgood⟩ := tagReturningProgram_trace run o tag
  exact ⟨(tr (Fin.last k)).memory,(invokeTag14_trace _ P s frame tr (by cases o <;> decide) ht hgood hs ho).mono
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hk) 2)⟩

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
