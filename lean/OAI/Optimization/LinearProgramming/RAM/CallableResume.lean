import OAI.Optimization.LinearProgramming.RAM.CallableOddCalls

/-! Resume a native service with its existing scalar and address memory intact. The
caller may selectively install a request prefix before invoking this entry point. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Invoke a persistent native memory at pc zero, with an arbitrary physical odd frame. -/
theorem Fragment.invoke_frame {p : Program} (count : ℕ) (sink : TagSink) (P : K → Prop)
    (native reserved : Memory K) {k tag : ℕ} (tr : Fin (k+1) → State K) (htag : tag<count)
    (hf : reserved.AllData P) (ht : Trace p (native.atPC 0) k tr) (hs : ∀i j,P ((tr i).data j))
    (ho : (tr (Fin.last k)).output=some tag)
    (hout : (sink.store tag (Call.pack (tr (Fin.last k)).memory reserved)).AllData P) :
    (Fragment.invoke p count sink).Run P (Call.pack native reserved) (2*k+2)
      (sink.store tag (Call.pack (tr (Fin.last k)).memory reserved)) := by
  intro prog pc code
  let sz := (p.map Call.width).sum
  let tab := pc+sz
  let post := pc+(sz+2*count)
  let ret (v : ℕ) := if v<count then tab+2*v else post
  have whole : CodeAt prog pc (Call.subroutine p pc ret ++ tagTable sink count post) := code
  have safe (i : Fin (k+1)) : ∀ j,P ((Call.pack (tr i).memory reserved).data j) := by
    intro j
    simp only [Call.pack]
    split
    · exact hs i _
    · exact hf _
  have sim := Call.simulate_execution (good := fun data => ∀j,P (data j)) whole.left (Execution.of_trace ht safe)
  obtain ⟨l,hl,body⟩ := sim
  let addr := Layout.addr p Call.width pc
  have startPC : Call.image reserved ret addr (native.atPC 0)=(Call.pack native reserved).atPC pc := by
    change (Call.pack native reserved).atPC (addr 0)=_
    simp [addr,Layout.addr]
  have endPC : Call.image reserved ret addr (tr (Fin.last k))=
      (Call.pack (tr (Fin.last k)).memory reserved).atPC (tab+2*tag) := by
    simp [Call.image,Call.position,ho,ret,htag]
  change Execution _ _ (Call.image reserved ret addr _) _ (Call.image reserved ret addr _) at body
  rw [startPC,endPC] at body
  have hlen : (Call.subroutine p pc ret).length=sz := Layout.assemble_length p Call.width pc _ (Call.emit_length ret)
  have htab : CodeAt prog tab (tagTable sink count post) := by simpa only [tab,hlen] using whole.right
  have done := tagTable_exec (safe := fun z : Memory K => ∀j,P (z.data j)) sink count post tab tag
    (Call.pack (tr (Fin.last k)).memory reserved) htab htag body.safe_end hout
  exact ⟨l+2,Nat.add_le_add_right hl 2,body.append done⟩

/-- In the logical odd-bank protocol, update exactly one caller register and give the
native service its exact new memory to retain between successive requests. -/
theorem Odd.invoke_memory {p : Program} (count : ℕ) (dest : TagSink) (P : K → Prop)
    (native caller : Memory K) {k tag : ℕ} (tr : Fin (k+1) → State K) (htag : tag<count)
    (hc : caller.AllData P) (ht : Trace p (native.atPC 0) k tr) (hs : ∀i j,P ((tr i).data j))
    (ho : (tr (Fin.last k)).output=some tag) (hout : (dest.store tag caller).AllData P) :
    (Fragment.invoke p count (Odd.sink dest)).Run P (Odd.memory native caller) (2*k+2)
      (Odd.memory (tr (Fin.last k)).memory (dest.store tag caller)) := by
  let last := (tr (Fin.last k)).memory
  have hresult : ((Odd.sink dest).store tag (Odd.memory last caller)).AllData P := by
    rw [Odd.sink_store]
    exact Odd.allData _ _ (hs _) hout
  have run := Fragment.invoke_frame count (Odd.sink dest) P native (Odd.frame caller) tr htag hc ht hs ho hresult
  change (Fragment.invoke p count (Odd.sink dest)).Run P (Odd.memory native caller) (2*k+2)
    ((Odd.sink dest).store tag (Odd.memory last caller)) at run
  rw [Odd.sink_store] at run
  exact run

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
