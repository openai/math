import OAI.Computability.VPVNP.PrimedInputRAMFlowEval
import OAI.Computability.VPVNP.PrimedCounterGuessWord

/-!
# From a tick-only structured flow to a native configuration prefix

The linked guards execute a single local step. An elementary instruction
whose event is a tick also has a local native successor and preserves both
memories. Composing those successors yields the concrete endpoint and the
exact instruction count independently of the behavior at the exit label.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Flow
open BurstRAM PrivateRAM PrimedStackRAM PrimedCounter.GuessWord

variable {w p r k : ℕ} {M : Machine w p r k} {st : Word w}
  {op : Op r k} {a : PrimedInputRAM.Flow r k} {rs out : Regs w r} {m m' : Memory w}
  {stop bad : Fin p} {es : List (Event w)}

private theorem line_tick {label : (Flow.line op).Label → Fin p}
    (h : op.effect M.publicData st rs m = some (.tick,out,m'))
    (hl : Linked M (.line op) label stop bad) (priv : Word w → Word w) :
    m' = m ∧ M.program.step ⟨label (Flow.line op).entry,st,rs,priv⟩ =
      .localStep ⟨stop,st,out,priv⟩ := by
  have hc := hl.atLabel (Flow.line op).entry
  change M.code (label (Flow.line op).entry) = (op.emit stop bad).resize w at hc
  change m' = m ∧ (M.code (label (Flow.line op).entry)).run M.publicData _ = _
  rw [hc]
  cases op <;> simp only [Op.effect, Option.some.injEq, Prod.mk.injEq, reduceCtorEq, false_and, true_and] at h
  all_goals try (split at h <;> simp only [Option.some.injEq,Prod.mk.injEq,true_and,reduceCtorEq] at h)
  all_goals first | contradiction | exact ⟨h.2.symm,by rw [← h.1]; rfl⟩ |
    exact ⟨h.2.symm,by rw [← h.1]; simp_all [Op.emit,Instr.resize,Instr.run]⟩

private theorem stepEq {l q : Fin r} {a b : PrimedInputRAM.Flow r k}
    {label : (Flow.ifEq l q a b).Label → Fin p} (hl : Linked M (.ifEq l q a b) label stop bad)
    (priv : Word w → Word w) :
    M.program.step ⟨label (.inl ()),st,rs,priv⟩ = .localStep
      ⟨if rs l = rs q then label (.inr (.inl a.entry)) else label (.inr (.inr b.entry)),st,rs,priv⟩ := by
  change (M.code (label (.inl ()))).run M.publicData _ = _
  erw [hl.atLabel (.inl ())]
  rfl

private theorem stepLt {l q : Fin r} {a b : PrimedInputRAM.Flow r k}
    {label : (Flow.ifLt l q a b).Label → Fin p} (hl : Linked M (.ifLt l q a b) label stop bad)
    (priv : Word w → Word w) :
    M.program.step ⟨label (.inl ()),st,rs,priv⟩ = .localStep
      ⟨if rs l < rs q then label (.inr (.inl a.entry)) else label (.inr (.inr b.entry)),st,rs,priv⟩ := by
  change (M.code (label (.inl ()))).run M.publicData _ = _
  erw [hl.atLabel (.inl ())]
  rfl

/-- Local steps in the structured derivation give a genuine native prefix
from the entry registers to the exit registers. -/
theorem Exec.toPrefix_of_ticks (h : Exec M.publicData st a rs m es out m')
    (ht : ∀ e ∈ es, e = .tick) {label : a.Label → Fin p}
    (hl : Linked M a label stop bad) (priv : Word w → Word w) :
    m' = m ∧ Prefix M ⟨label a.entry,st,rs,priv⟩ es ⟨stop,st,out,priv⟩ := by
  induction h generalizing stop with
  | line he =>
    have hz := ht _ (List.mem_cons_self ..)
    subst hz
    obtain ⟨hm,step⟩ := line_tick he hl priv
    exact ⟨hm,.tick step (.nil _)⟩
  | seq _ _ left right =>
    obtain ⟨hm,pre⟩ := left (fun e he => ht e (List.mem_append_left _ he)) hl.seqLeft
    obtain ⟨hm',suf⟩ := right (fun e he => ht e (List.mem_append_right _ he)) hl.seqRight
    exact ⟨hm'.trans hm,pre.append suf⟩
  | @ifEqYes _ _ _ _ input _ _ _ _ test _ ih =>
    obtain ⟨hm,body⟩ := ih (fun e he => ht e (List.mem_cons_of_mem _ he)) hl.ifEqYes
    refine ⟨hm,.tick ?_ body⟩
    have step := stepEq (st := st) (rs := input) hl priv
    rw [ite_eq_left test] at step
    exact step
  | @ifEqNo _ _ _ _ input _ _ _ _ test _ ih =>
    obtain ⟨hm,body⟩ := ih (fun e he => ht e (List.mem_cons_of_mem _ he)) hl.ifEqNo
    refine ⟨hm,.tick ?_ body⟩
    have step := stepEq (st := st) (rs := input) hl priv
    rw [ite_eq_right test] at step
    exact step
  | @ifLtYes _ _ _ _ input _ _ _ _ test _ ih =>
    obtain ⟨hm,body⟩ := ih (fun e he => ht e (List.mem_cons_of_mem _ he)) hl.ifLtYes
    refine ⟨hm,.tick ?_ body⟩
    have step := stepLt (st := st) (rs := input) hl priv
    rw [ite_eq_left test] at step
    exact step
  | @ifLtNo _ _ _ _ input _ _ _ _ test _ ih =>
    obtain ⟨hm,body⟩ := ih (fun e he => ht e (List.mem_cons_of_mem _ he)) hl.ifLtNo
    refine ⟨hm,.tick ?_ body⟩
    have step := stepLt (st := st) (rs := input) hl priv
    rw [ite_eq_right test] at step
    exact step
  | branchYes _ _ | branchNo _ _ => cases ht _ (List.mem_cons_self ..)
  | whileDone test =>
    refine ⟨rfl,.tick ?_ (.nil _)⟩
    change (M.code (label (.inl ()))).run M.publicData _ = _
    erw [hl.atLabel (.inl ())]
    simp [code,Jump.map,Jump.emit,Instr.resize,Instr.run,test]
  | whileStep test _ _ body rest =>
    obtain ⟨hm,hbody⟩ := body (fun e he => ht e (List.mem_cons_of_mem _ (List.mem_append_left _ he))) hl.loopBody
    obtain ⟨hm',hrest⟩ := rest (fun e he => ht e (List.mem_cons_of_mem _ (List.mem_append_right _ he))) hl
    refine ⟨hm'.trans hm,.tick ?_ (hbody.append hrest)⟩
    change (M.code (label (.inl ()))).run M.publicData _ = _
    erw [hl.atLabel (.inl ())]
    simp [code,Jump.map,Jump.emit,Instr.resize,Instr.run,test]; rfl

/-- Specialization used by the operand and cache arithmetic, which supply
their tick count directly. -/
theorem Exec.toPrefix {ticks : ℕ}
    (h : Exec M.publicData st a rs m (List.replicate ticks .tick) out m')
    {label : a.Label → Fin p} (hl : Linked M a label stop bad) (priv : Word w → Word w) :
    Prefix M ⟨label a.entry,st,rs,priv⟩ (List.replicate ticks .tick) ⟨stop,st,out,priv⟩ :=
  (h.toPrefix_of_ticks (fun _ he => (List.mem_replicate.mp he).2) hl priv).2

end PrimedInputRAM.Flow

end VPVNP
end Computability
end OAI
