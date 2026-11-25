import OAI.Optimization.LinearProgramming.RAM.CallMemory
import OAI.Optimization.LinearProgramming.RAM.Layout

/-! Inlining any fixed program as a subroutine, with its original register space isolated
from the caller and a separate continuation address for each return tag. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Call

universe u
variable {K : Type u}

def position (ret addr : Nat → Nat) (s : State K) : Nat :=
  match s.output with
  | none => addr s.pc
  | some tag => ret tag

def image (f : Memory K) (ret addr : Nat → Nat) (s : State K) : State K :=
  (pack s.memory f).atPC (position ret addr s)

@[simp] private theorem at_memory (m : Memory K) (j : Nat) : (m.atPC j).memory = m := rfl
@[simp] private theorem at_data (m : Memory K) (j i : Nat) : (m.atPC j).data i = m.data i := rfl
@[simp] private theorem at_index (m : Memory K) (j i : Nat) : (m.atPC j).index i = m.index i := rfl
@[simp] private theorem data_at (m : Memory K) (j i : Nat) (x : K) :
    (m.atPC j).putData i x = (m.putData i x).atPC (j+1) := rfl
@[simp] private theorem index_at (m : Memory K) (j i n : Nat) :
    (m.atPC j).putIndex i n = (m.putIndex i n).atPC (j+1) := rfl
@[simp] private theorem image_at (m f : Memory K) (ret addr : Nat → Nat) (j : Nat) :
    image f ret addr (m.atPC j) = (pack m f).atPC (addr j) := rfl

private theorem step_at [Field K] [LinearOrder K] [IsStrictOrderedRing K] {p : Program} {pc : Nat} {i : Instr} (m : Memory K)
    (h : p[pc]? = some i) : step p (m.atPC pc) = execInstr i (m.atPC pc) := by
  simp [step, Memory.atPC, h]

private theorem putIndex_twice (m : Memory K) (i a b : Nat) :
    (m.putIndex i a).putIndex i b = m.putIndex i b := by
  simp [Memory.putIndex, Function.update_idem]

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The one- or two-instruction simulation. The invariant concerns scalar values and is
therefore preserved also halfway through a doubled address increment or decrement. -/
private theorem simulate_instr {p : Program} {v f : Memory K} {pc : Nat}
    {t : State K} {op : Instr} {ret addr : Nat → Nat} {good : (Nat → K) → Prop}
    (src : execInstr op (v.atPC pc) = some t)
    (code : CodeAt p (addr pc) (emit ret addr op))
    (fall : addr (pc+1) = addr pc + width op)
    (hs : good (pack v f).data) (ht : good (pack t.memory f).data) :
    Execution p (fun st => good st.data) ((pack v f).atPC (addr pc)) (width op) (image f ret addr t) := by
  cases op with
  | const d q | copy d q | add d q _ | sub d q _ | mul d q _ | load d q | store d q | addrConst d q | addrCopy d q | addrLoad d q | addrStore d q =>
    simp only [execInstr, data_at, index_at, at_data, at_index, Option.some.injEq] at src
    subst t
    apply Execution.one hs _ ht
    rw [step_at _ code.head]
    simp [execInstr, fall, width]
  | div d a b =>
    by_cases hz : v.data b = 0
    · simp [execInstr, hz] at src
    · simp [execInstr, hz] at src
      subst t
      apply Execution.one hs _ ht
      rw [step_at _ code.head]
      simp [execInstr, hz, fall, width]
  | incr d a =>
    simp only [execInstr, index_at, at_index, Option.some.injEq] at src
    subst t
    let m := pack v f
    let intermediate := m.putIndex (2*d) (2*v.index a+1)
    have hi := code.head
    have second := (CodeAt.right (a := [.incr (2*d) (2*a)]) code).head
    simp only [List.length_singleton] at second
    have h1 : step p (m.atPC (addr pc)) = some (intermediate.atPC (addr pc+1)) := by
      rw [step_at _ hi]
      simp [execInstr, m, intermediate]
    have h2 : step p (intermediate.atPC (addr pc+1)) =
        some (image f ret addr ((v.putIndex d (v.index a+1)).atPC (pc+1))) := by
      rw [step_at _ second]
      simp only [execInstr, index_at, at_index, image_at]
      have at_d : intermediate.index (2*d) = 2*v.index a+1 := Function.update_self ..
      rw [at_d]
      change some (((m.putIndex (2*d) _).putIndex (2*d) _).atPC _) = _
      rw [putIndex_twice, show 2*v.index a+1+1 = 2*(v.index a+1) by omega]
      simp [m, fall, width, Nat.add_assoc]
    exact .next hs h1 (.one (show good intermediate.data from hs) h2 ht)
  | decr d a =>
    simp only [execInstr, index_at, at_index, Option.some.injEq] at src
    subst t
    let m := pack v f
    let intermediate := m.putIndex (2*d) (2*v.index a-1)
    have hi := code.head
    have second := (CodeAt.right (a := [.decr (2*d) (2*a)]) code).head
    simp only [List.length_singleton] at second
    have h1 : step p (m.atPC (addr pc)) = some (intermediate.atPC (addr pc+1)) := by
      rw [step_at _ hi]
      simp [execInstr, m, intermediate]
    have h2 : step p (intermediate.atPC (addr pc+1)) =
        some (image f ret addr ((v.putIndex d (v.index a-1)).atPC (pc+1))) := by
      rw [step_at _ second]
      simp only [execInstr, index_at, at_index, image_at]
      have at_d : intermediate.index (2*d) = 2*v.index a-1 := Function.update_self ..
      rw [at_d]
      change some (((m.putIndex (2*d) _).putIndex (2*d) _).atPC _) = _
      rw [putIndex_twice, show 2*v.index a-1-1 = 2*(v.index a-1) by omega]
      simp [m, fall, width, Nat.add_assoc]
    exact .next hs h1 (.one (show good intermediate.data from hs) h2 ht)
  | branchLT a b y n =>
    by_cases test : v.data a < v.data b <;>
      simp [execInstr, test] at src <;> subst t <;> apply Execution.one hs _ ht <;>
      rw [step_at _ code.head] <;> simp [execInstr, test, image, position, State.memory, Memory.atPC, pack]
  | branchAddrLT a b y n =>
    by_cases test : v.index a < v.index b <;>
      simp [execInstr, test] at src <;> subst t <;> apply Execution.one hs _ ht <;>
      rw [step_at _ code.head] <;> simp [execInstr, test, image, position, State.memory, Memory.atPC, pack]
  | jump j | halt j =>
    simp [execInstr] at src
    subst t
    apply Execution.one hs _ ht
    rw [step_at _ code.head]
    rfl

/-- Embed any fixed program at an absolute location. All saved frame cells survive in
odd registers, even if the callee makes writes at indirect addresses. -/
def subroutine (original : Program) (base : Nat) (ret : Nat → Nat) : Program :=
  Layout.assemble original width base (emit ret)

/-- Calling the program takes at most twice the original instruction count. A bound
on the input and output scalar banks at each original step applies throughout the
simulation, including the extra address-only steps. -/
theorem simulate_execution {original target : Program} {base : Nat} {ret : Nat → Nat}
    {s t : State K} {k : Nat} {f : Memory K} {good : (Nat → K) → Prop}
    (code : CodeAt target base (subroutine original base ret))
    (h : Execution original (fun st => good (pack st.memory f).data) s k t) :
    ∃ l ≤ 2*k, Execution target (fun st => good st.data)
      (image f ret (Layout.addr original width base) s) l
      (image f ret (Layout.addr original width base) t) := by
  induction h with
  | done x hx => exact ⟨0, by omega, .done _ hx⟩
  | @next x y z k hx hs hrest ih =>
    obtain ⟨l, hl, htail⟩ := ih
    have live : x.output = none := by
      cases h : x.output with
      | none => rfl
      | some tag => simp [step, h] at hs
    obtain ⟨op, hf, hex⟩ : ∃ i : Instr, original[x.pc]? = some i ∧
        execInstr i x = some y := by
      cases hf : original[x.pc]? with
      | none => simp [step, live, hf] at hs
      | some op => exact ⟨op, rfl, by simpa [step, live, hf] using hs⟩
    have rebuild : x.memory.atPC x.pc = x := by
      cases x with
      | mk pc ds idx out => simp_all [State.memory, Memory.atPC]
    have src : execInstr op (x.memory.atPC x.pc) = some y := by rw [rebuild, hex]
    have part := Layout.codeAt_emit (emit_length ret) code hf
    have head := simulate_instr (ret := ret) src part (Layout.addr_succ hf) hx hrest.safe_start
    have hi : image f ret (Layout.addr original width base) x =
        (pack x.memory f).atPC (Layout.addr original width base x.pc) := by simp [image, position, live]
    refine ⟨width op+l, ?_, ?_⟩
    · have := width_le_two op; omega
    · rw [hi]; exact head.append htail

/-- Simulate an original trace as a subroutine of any caller, with an unchanged
saved register bank and explicit exact endpoints for the new trace. -/
theorem simulate_trace {original target : Program} {base : Nat} {ret : Nat → Nat}
    {s : State K} {k : Nat} {t : Fin (k+1) → State K} (frame : Memory K)
    (good : (Nat → K) → Prop) (code : CodeAt target base (subroutine original base ret))
    (h : Trace original s k t) (hs : ∀ i, good (pack (t i).memory frame).data) :
    ∃ l ≤ 2*k, ∃ u : Fin (l+1) → State K,
      Trace target (image frame ret (Layout.addr original width base) s) l u ∧
      u (Fin.last l) = image frame ret (Layout.addr original width base) (t (Fin.last k)) ∧
      ∀ i, good (u i).data := by
  obtain ⟨l, hl, hh⟩ := simulate_execution code (Execution.of_trace h hs)
  exact ⟨l, hl, hh.to_trace⟩

end Call
end RAM
end LinearProgramming
end Optimization
end OAI
