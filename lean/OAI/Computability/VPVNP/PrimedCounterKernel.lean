import OAI.Computability.VPVNP.PrimedCounterKernelExact
import OAI.Computability.VPVNP.PrimedCounterAdminExec
import OAI.Computability.VPVNP.PrimedStackRAMChoices

/-!
# Choice suffixes and structured executions of the preorder counter

The kernel for a node consumes a canonical word for a leaf and three words for
a binary node. Its remaining choice suffix can be passed to any further block.
These equivalences describe every successful derivation and every rejecting tape.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM PrimedInputRAM PrimedCounter

variable {w r k : ℕ}

/-- The kernel realizes exactly the finite executions whose choice prefix is available. -/
def KernelExec (a : Flow r k) (f : Kernel w r k) : Prop :=
  ∀ {pub st rs m bits o}, f pub st rs m bits = some o ↔
    Flow.Exec pub st a rs m o.events o.regs o.mem ∧ bits = choiceBits o.events ++ o.bits

theorem lines_kernel_exec (ops : List (Op r k)) (hn : ops ≠ []) :
    KernelExec (lines ops hn) (lineKernel (w := w) ops) := by
  intro pub st rs m bits o
  constructor
  · intro h
    obtain ⟨⟨es,rs',m'⟩, ht, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨(Admin.exec_lines_iff_trace hn).mpr ht, by simp [Admin.trace_choiceBits ht]⟩
  · rintro ⟨he,hb⟩
    have ht := (Admin.exec_lines_iff_trace hn).mp he
    rw [Admin.trace_choiceBits ht, List.nil_append] at hb
    simp [lineKernel, ht, hb]

private theorem guess_events_memory (bs : List Bool) (m : Memory w) :
    after m (GuessWord.events bs) = m := by
  induction bs with
  | nil => rfl
  | cons b bs ih => exact ih

private theorem guess_replays (reg : Fin 3 ↪ Fin r) : Replays (guessKernel (w := w) (k := k) reg) := by
  intro pub st rs m bits o h
  obtain ⟨⟨v,t⟩, _, rfl⟩ := Option.map_eq_some_iff.mp h
  exact guess_events_memory (wordBits v) m

theorem guess_kernel_exec (reg : Fin 3 ↪ Fin r) :
    KernelExec (GuessWord.flow (k := k) reg) (guessKernel (w := w) reg) := by
  intro pub st rs m bits o
  have h := guess_refine (w := w) (k := k) reg
  have replay : Replays (guessKernel (w := w) (k := k) reg) := guess_replays reg
  constructor
  · intro hx
    obtain ⟨⟨v,t⟩, hv, rfl⟩ := Option.map_eq_some_iff.mp hx
    have ht : takeWord w (wordBits v) = some (v,[]) := (takeWord_eq_some_iff ..).mpr (by simp)
    have ho : guessKernel reg pub st rs m (wordBits v) =
        some ⟨GuessWord.trace v, GuessWord.resultRegs reg rs v, m, []⟩ := by simp [guessKernel, ht]
    exact ⟨((h.kernel_iff_exec replay ..).mp ho).1,
      by simpa [GuessWord.trace, choiceBits] using (takeWord_eq_some_iff ..).mp hv⟩
  · rintro ⟨he,rfl⟩
    have hx := h.kernel_of_exec replay he
    obtain ⟨⟨v,t⟩, hv, hout⟩ := Option.map_eq_some_iff.mp hx
    cases o with
    | mk es rs' m' tail =>
      simp only [Output.mk.injEq] at hout
      obtain ⟨rfl,rfl,rfl,rfl⟩ := hout
      have ht : takeWord w (choiceBits (GuessWord.trace v) ++ tail) = some (v,tail) :=
        (takeWord_eq_some_iff ..).mpr (by simp [GuessWord.trace, choiceBits])
      simp [guessKernel, ht]

theorem KernelExec.seq {a b : Flow r k} {fa fb : Kernel w r k}
    (ha : KernelExec a fa) (hb : KernelExec b fb) : KernelExec (.seq a b) (seqKernel fa fb) := by
  intro pub st rs m bits o
  constructor
  · intro h
    simp only [seqKernel, bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, y, hy, hout⟩ := h
    cases hout
    obtain ⟨he,hbits⟩ := ha.mp hx
    obtain ⟨hf,hrest⟩ := hb.mp hy
    exact ⟨.seq he hf, by simp [Output.prepend, Flow.choiceBits_append, hbits, hrest]⟩
  · rintro ⟨he,hbits⟩
    cases o with
    | mk es out mem tail =>
      cases he with
      | @seq _ _ _ _ es r₁ m₁ fs _ _ he hf =>
        let rest := choiceBits fs ++ tail
        have hx : fa pub st rs m bits = some ⟨es,r₁,m₁,rest⟩ := ha.mpr ⟨he, by
          simpa [Flow.choiceBits_append, List.append_assoc, rest] using hbits⟩
        have hy : fb pub st r₁ m₁ rest = some ⟨fs,out,mem,tail⟩ := hb.mpr ⟨hf,rfl⟩
        simp [seqKernel, hx, hy, Output.prepend]

theorem KernelExec.ifEq {a b : Flow r k} {fa fb : Kernel w r k}
    (l q : Fin r) (ha : KernelExec a fa) (hb : KernelExec b fb) :
    KernelExec (.ifEq l q a b) (eqKernel l q fa fb) := by
  intro pub st rs m bits o
  constructor
  · intro h
    unfold eqKernel at h
    split at h <;> rename_i test <;> obtain ⟨x,hx,rfl⟩ := Option.map_eq_some_iff.mp h
    · obtain ⟨he,ht⟩ := ha.mp hx
      exact ⟨.ifEqYes test he, ht⟩
    · obtain ⟨he,ht⟩ := hb.mp hx
      exact ⟨.ifEqNo test he, ht⟩
  · rintro ⟨he, ht⟩
    cases o with
    | mk es out mem tail =>
      cases he with
      | ifEqYes test he =>
        have hx : fa pub st rs m bits = some ⟨_,out,mem,tail⟩ := ha.mpr ⟨he,ht⟩
        simp [eqKernel, test, hx, Output.prepend]
      | ifEqNo test he =>
        have hx : fb pub st rs m bits = some ⟨_,out,mem,tail⟩ := hb.mpr ⟨he,ht⟩
        simp [eqKernel, test, hx, Output.prepend]

/-- The exact node kernel, including the unused suffix and the complete post-state. -/
theorem node_kernel_iff : KernelExec nodeFlow (nodeKernel (w := w)) :=
  KernelExec.seq (lines_kernel_exec pop (by decide)) <| KernelExec.ifEq 0 12
    (KernelExec.seq (guess_kernel_exec _) (lines_kernel_exec leafLines (by decide)))
    (KernelExec.seq (guess_kernel_exec _) (KernelExec.seq (guess_kernel_exec _)
      (KernelExec.seq (guess_kernel_exec _) (lines_kernel_exec binaryLines (by decide)))))

/-- A completed node accepts precisely its finite executions that consume the entire tape. -/
theorem completeNode_iff_exec {pub : Fin 11 → Word w} {st : Word w} {rs : Regs w 16} {m : Memory w}
    {bits : List Bool} {o : Output w 16} :
    completeNode pub st rs m bits = some o ↔
      Flow.Exec pub st nodeFlow rs m o.events o.regs o.mem ∧ bits = choiceBits o.events ∧ o.bits = [] := by
  rw [completeNode, Option.filter_eq_some_iff, node_kernel_iff]
  simp only [List.isEmpty_iff]
  constructor
  · rintro ⟨⟨he,ht⟩,hb⟩
    exact ⟨he, by simpa [hb] using ht, hb⟩
  · rintro ⟨he,ht,hb⟩
    exact ⟨⟨he,by simpa [hb] using ht⟩,hb⟩

end PrimedStackRAM

end VPVNP
end Computability
end OAI
