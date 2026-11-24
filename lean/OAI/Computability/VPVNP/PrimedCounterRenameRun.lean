import OAI.Computability.VPVNP.PrimedCounterRename
import OAI.Computability.VPVNP.PrimedInputRAMFlowEval

/-!
# Executing embedded parser and assembly programs

Relocating operands preserves the complete event sequence and external memory
of every successful structured execution. This allows the uniform assembly
and traversal codes to share one private register file.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter

open BurstRAM PrimedStackRAM PrimedInputRAM

variable {w r k R K : ℕ}

/-- One relocated opcode can only write an embedded register. -/
private theorem line_outside (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K) (op : Op r k)
    (data : Fin K → Word w) (state : Word w) (rs : Regs w R) (mem : Memory w)
    {e out m'} (he : (renameOp reg pub op).effect data state rs mem = some (e,out,m'))
    (j : Fin R) (hj : j ∉ Set.range reg) : out j = rs j := by
  have hn (i : Fin r) : j ≠ reg i := fun hh => hj ⟨i, hh.symm⟩
  cases op <;> simp only [renameOp, Op.effect] at he
  all_goals first | split at he | skip
  all_goals first | contradiction | (cases Option.some.inj he; simp [Function.update_of_ne (hn _)])

/-- Lift a finite small-register computation to the enclosing register space.
All unrelated enclosing registers retain their prior values. -/
theorem liftExec (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K) (data : Fin K → Word w)
    {state : Word w} {a : Flow r k} {small m es out m'}
    (he : Flow.Exec (data ∘ pub) state a small m es out m')
    (rs : Regs w R) (hr : rs ∘ reg = small) :
    ∃ rs', Flow.Exec data state (renameFlow reg pub a) rs m es rs' m' ∧
      rs' ∘ reg = out ∧ ∀ j, j ∉ Set.range reg → rs' j = rs j := by
  induction he generalizing rs with
  | @line op small m e small' m' h =>
    subst small
    have hx := (effect_rename reg pub op data state rs m).trans h
    obtain ⟨⟨ev, rs', m''⟩, hh, heq⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨rfl, heq, rfl⟩ := Prod.mk.inj heq
    exact ⟨rs', .line hh, rfl, line_outside reg pub op data state rs m hh⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨mid, hm, he, ho⟩ := ih₁ rs hr
    obtain ⟨out, hrun, he', ho'⟩ := ih₂ mid he
    exact ⟨out, .seq hm hrun, he', fun j hj => (ho' j hj).trans (ho j hj)⟩
  | ifEqYes ht _ ih | ifEqNo ht _ ih | ifLtYes ht _ ih | ifLtNo ht _ ih =>
    obtain ⟨out, ho, he, hh⟩ := ih rs hr
    subst_vars
    first | exact ⟨out, .ifEqYes ht ho, rfl, hh⟩ | exact ⟨out, .ifEqNo ht ho, rfl, hh⟩
          | exact ⟨out, .ifLtYes ht ho, rfl, hh⟩ | exact ⟨out, .ifLtNo ht ho, rfl, hh⟩
  | branchYes _ ih =>
    obtain ⟨out, ho, he, hh⟩ := ih rs hr
    exact ⟨out, .branchYes ho, he, hh⟩
  | branchNo _ ih =>
    obtain ⟨out, ho, he, hh⟩ := ih rs hr
    exact ⟨out, .branchNo ho, he, hh⟩
  | whileDone ht =>
    subst_vars
    exact ⟨rs, .whileDone ht, rfl, fun _ _ => rfl⟩
  | whileStep ht _ _ ih₁ ih₂ =>
    obtain ⟨mid, hb, he, ho⟩ := ih₁ rs hr
    obtain ⟨out, hrun, he', ho'⟩ := ih₂ mid he
    rw [← hr] at ht
    exact ⟨out, .whileStep ht hb hrun, he', fun j hj => (ho' j hj).trans (ho j hj)⟩

/-- Conversely, every successful enclosing execution restricts to a genuine
execution of the original program. Both directions include the exact event log. -/
theorem restrictExec (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K) (data : Fin K → Word w)
    {state : Word w} (a : Flow r k) {rs m es out m'}
    (he : Flow.Exec data state (renameFlow reg pub a) rs m es out m') :
    Flow.Exec (data ∘ pub) state a (rs ∘ reg) m es (out ∘ reg) m' ∧
      ∀ j, j ∉ Set.range reg → out j = rs j := by
  generalize hcmd : renameFlow reg pub a = cmd at he
  induction he generalizing a with
  | @line op rs m e out m' h =>
    cases a <;> simp only [renameFlow, reduceCtorEq, Flow.line.injEq] at hcmd
    subst op
    constructor
    · apply Flow.Exec.line
      rw [← effect_rename reg pub _ data state rs m, h]
      rfl
    · exact line_outside reg pub _ data state rs m h
  | seq _ _ ih₁ ih₂ =>
    cases a <;> simp only [renameFlow, reduceCtorEq, Flow.seq.injEq] at hcmd
    obtain ⟨ha, hb⟩ := hcmd
    obtain ⟨h₁, o₁⟩ := ih₁ _ ha
    obtain ⟨h₂, o₂⟩ := ih₂ _ hb
    exact ⟨.seq h₁ h₂, fun j hj => (o₂ j hj).trans (o₁ j hj)⟩
  | ifEqYes ht _ ih | ifEqNo ht _ ih | ifLtYes ht _ ih | ifLtNo ht _ ih =>
    cases a <;> simp only [renameFlow, reduceCtorEq, Flow.ifEq.injEq, Flow.ifLt.injEq] at hcmd
    obtain ⟨rfl, rfl, ha, hb⟩ := hcmd
    first
    | obtain ⟨h, ho⟩ := ih _ ha; exact ⟨.ifEqYes ht h, ho⟩
    | obtain ⟨h, ho⟩ := ih _ hb; exact ⟨.ifEqNo ht h, ho⟩
    | obtain ⟨h, ho⟩ := ih _ ha; exact ⟨.ifLtYes ht h, ho⟩
    | obtain ⟨h, ho⟩ := ih _ hb; exact ⟨.ifLtNo ht h, ho⟩
  | branchYes _ ih | branchNo _ ih =>
    cases a <;> simp only [renameFlow, reduceCtorEq, Flow.branch.injEq] at hcmd
    obtain ⟨ha, hb⟩ := hcmd
    first
    | obtain ⟨h, ho⟩ := ih _ ha; exact ⟨.branchYes h, ho⟩
    | obtain ⟨h, ho⟩ := ih _ hb; exact ⟨.branchNo h, ho⟩
  | whileDone ht =>
    cases a <;> simp only [renameFlow, reduceCtorEq, Flow.whileLt.injEq] at hcmd
    obtain ⟨rfl, rfl, _⟩ := hcmd
    exact ⟨.whileDone ht, fun _ _ => rfl⟩
  | whileStep ht _ _ ih₁ ih₂ =>
    cases a <;> simp only [renameFlow, reduceCtorEq, Flow.whileLt.injEq] at hcmd
    obtain ⟨rfl, rfl, rfl⟩ := hcmd
    obtain ⟨h₁, o₁⟩ := ih₁ _ rfl
    obtain ⟨h₂, o₂⟩ := ih₂ (.whileLt _ _ _) rfl
    exact ⟨.whileStep ht h₁ h₂, fun j hj => (o₂ j hj).trans (o₁ j hj)⟩

end PrimedCounter

end VPVNP
end Computability
end OAI
