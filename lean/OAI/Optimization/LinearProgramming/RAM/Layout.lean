import OAI.Optimization.LinearProgramming.RAM.Execution

/-! Relocation of RAM instructions whose implementations occupy variable-width blocks. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Layout

/-- Absolute address of source instruction `j`, including the one-past-the-end address. -/
def addr (p : Program) (width : Instr → Nat) (base j : Nat) : Nat :=
  base + ((p.take j).map width).sum

/-- Emit each instruction using the absolute-address map of the whole caller. -/
def assemble (p : Program) (width : Instr → Nat) (base : Nat)
    (emit : (Nat → Nat) → Instr → Program) : Program :=
  p.flatMap (emit (addr p width base))

private theorem block_length (width : Instr → Nat) (f : Instr → Program)
    (hw : ∀ i, (f i).length = width i) (code : Program) :
    (code.flatMap f).length = (code.map width).sum := by
  induction code with
  | nil => rfl
  | cons i t ih => simp [hw, ih]

theorem addr_succ {p : Program} {width : Instr → Nat} {base j : Nat} {i : Instr}
    (h : p[j]? = some i) : addr p width base (j + 1) = addr p width base j + width i := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp h
  unfold addr
  rw [List.take_succ_eq_append_getElem hj]
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, Nat.add_zero, Nat.add_assoc]

theorem addr_end (p : Program) (width : Instr → Nat) (base : Nat) :
    addr p width base p.length = base + (p.map width).sum := by simp [addr]

theorem assemble_length (p : Program) (width : Instr → Nat) (base : Nat)
    (emit : (Nat → Nat) → Instr → Program) (hw : ∀ a i, (emit a i).length = width i) :
    (assemble p width base emit).length = (p.map width).sum :=
  block_length width _ (hw _) p

theorem addr_end_eq (p : Program) (width : Instr → Nat) (base : Nat)
    (emit : (Nat → Nat) → Instr → Program) (hw : ∀ a i, (emit a i).length = width i) :
    addr p width base p.length = base + (assemble p width base emit).length := by
  rw [addr_end, assemble_length p width base emit hw]

/-- Lookup in the source program gives a complete contiguous chunk in the installed target.
`CodeAt` permits both an arbitrary caller prefix and arbitrary code after the relocation. -/
theorem codeAt_emit {target p : Program} {width : Instr → Nat} {base j : Nat}
    {emit : (Nat → Nat) → Instr → Program} {i : Instr}
    (hw : ∀ a i, (emit a i).length = width i)
    (h : CodeAt target base (assemble p width base emit)) (hj : p[j]? = some i) :
    CodeAt target (addr p width base j) (emit (addr p width base) i) := by
  let f := emit (addr p width base)
  have hsplit : p = p.take j ++ i :: p.drop (j+1) := by
    obtain ⟨hj', hi⟩ := List.getElem?_eq_some_iff.mp hj
    rw [← hi, ← List.drop_eq_getElem_cons hj', List.take_append_drop]
  obtain ⟨pre, post, hp, htarget⟩ := h
  refine ⟨pre ++ (p.take j).flatMap f, (p.drop (j+1)).flatMap f ++ post, ?_, ?_⟩
  · rw [List.length_append, hp, block_length width f (hw _)]
    rfl
  · have hf := congrArg (List.flatMap f) hsplit
    simp only [List.flatMap_append, List.flatMap_cons] at hf
    change target = _ ++ f i ++ _
    change target = pre ++ p.flatMap f ++ post at htarget
    rw [htarget, hf]
    simp [List.append_assoc]

end Layout
end RAM
end LinearProgramming
end Optimization
end OAI
