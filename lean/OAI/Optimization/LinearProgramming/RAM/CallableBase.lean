import OAI.Optimization.LinearProgramming.RAM.Code

/-! Relocatable structured fragments use their real RAM instructions at every call site.
The same simulation lemma applies at any address in a larger program. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

structure Fragment where
  size : ℕ
  emit : ℕ → Program
  length_emit : ∀ pc, (emit pc).length = size

namespace Fragment

/-- All intermediate scalar values satisfy `P`. `bound` bounds the actual number of
physical transitions in any caller containing this fragment. -/
def Run {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (f : Fragment)
    (P : K → Prop) (m : Memory K) (bound : ℕ) (t : Memory K) : Prop :=
  ∀ (prog : Program) (pc : ℕ), CodeAt prog pc (f.emit pc) →
    ∃ k ≤ bound, Execution prog (fun s => ∀ j, P (s.data j))
      (m.atPC pc) k (t.atPC (pc+f.size))

/-- An existing structured block is already a relocatable fragment. -/
def ofBlock (b : Block) : Fragment := ⟨b.size, b.compile, b.length_compile⟩

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {P : K → Prop} {m t : Memory K} {k : ℕ} {f : Fragment}

theorem Run.ofBlock {b : Block} (h : Block.Eval (fun z => ∀ j, P (z.data j)) b m k t) :
    (Fragment.ofBlock b).Run P m k t :=
  fun _ _ code => ⟨k, le_rfl, h.compile_correct code⟩

theorem Run.mono (h : f.Run P m k t) {b : ℕ} (hkb : k ≤ b) : f.Run P m b t := by
  intro prog pc code
  obtain ⟨l,hl,run⟩ := h prog pc code
  exact ⟨l,hl.trans hkb,run⟩

theorem Run.safe_start (h : f.Run P m k t) : ∀ j, P (m.data j) := by
  obtain ⟨_,_,hr⟩ := h (f.emit 0) 0 (CodeAt.whole _)
  exact hr.safe_start

theorem Run.safe_end (h : f.Run P m k t) : ∀ j, P (t.data j) := by
  obtain ⟨_,_,hr⟩ := h (f.emit 0) 0 (CodeAt.whole _)
  exact hr.safe_end

/-- Append the real halt instruction to the compiled fragment. -/
def program (f : Fragment) (tag : ℕ) : Program := f.emit 0 ++ [.halt tag]

theorem run_halt (h : f.Run P m k t) (tag : ℕ) :
    ∃ l ≤ k+1, ∃ tr : Fin (l+1) → State K, Trace (f.program tag) (m.atPC 0) l tr ∧
      (tr (Fin.last l)).output = some tag ∧ (tr (Fin.last l)).memory=t ∧
      ∀ i j, P ((tr i).data j) := by
  let prog := f.program tag
  have whole : CodeAt prog 0 (f.emit 0 ++ [.halt tag]) := CodeAt.whole _
  obtain ⟨l,hl,run⟩ := h prog 0 whole.left
  have fetch := whole.right.head
  rw [f.length_emit, Nat.zero_add] at fetch
  let last : State K := {t.atPC (0+f.size) with output := some tag}
  have halt : Execution prog (fun s => ∀ j,P (s.data j)) (t.atPC (0+f.size)) 1 last :=
    .one run.safe_end (by simp [step, Memory.atPC, fetch, execInstr, last]) run.safe_end
  obtain ⟨tr, ht, he, hs⟩ := (run.append halt).to_trace
  exact ⟨l+1, Nat.add_le_add_right hl 1, tr, ht, he ▸ rfl, he ▸ rfl, hs⟩

end Fragment
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
