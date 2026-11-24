import OAI.Computability.VPVNP.PrimedCounterRenameRun

/-!
# Calling a native flow with a register as its persistent argument

The enclosing call keeps its own persistent word. Each persistent-word load in
a component becomes a copy from a register outside its ordinary operand bank.
The component therefore observes one fixed input throughout loops and branches.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Rebased

open BurstRAM PrimedStackRAM PrimedInputRAM PrimedCounter

variable {w r k R K : ℕ}

/-- Relabel an instruction's operands, replacing a persistent-state load by a copy from the
designated argument register. -/
def opAt (reg : Fin r → Fin R) (pub : Fin k → Fin K) (arg : Fin R) : Op r k → Op R K
  | .stateWord dst => .copy (reg dst) arg
  | op => renameOp reg pub op

private theorem effect (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K) (arg : Fin R) (op : Op r k)
    (data : Fin K → Word w) (state : Word w) (rs : Regs w R) (mem : Memory w) :
    ((opAt reg pub arg op).effect data state rs mem).map (fun (e,r',m') => (e,r' ∘ reg,m')) =
      op.effect (data ∘ pub) (rs arg) (rs ∘ reg) mem := by
  have upd (dst : Fin r) (v : Word w) :
      Function.update rs (reg dst) v ∘ reg = Function.update (rs ∘ reg) dst v := by
    funext j
    by_cases h : j = dst <;> simp [h,Function.comp_apply]
  cases op <;> simp [opAt,renameOp,Op.effect,upd,Function.comp_apply]

/-- Rebase a whole flow on an argument register while relabeling registers, public operands,
and branch conditions. -/
def code (reg : Fin r → Fin R) (pub : Fin k → Fin K) (arg : Fin R) : Flow r k → Flow R K
  | .line op => .line (opAt reg pub arg op)
  | .seq a b => .seq (code reg pub arg a) (code reg pub arg b)
  | .ifEq x y a b => .ifEq (reg x) (reg y) (code reg pub arg a) (code reg pub arg b)
  | .ifLt x y a b => .ifLt (reg x) (reg y) (code reg pub arg a) (code reg pub arg b)
  | .branch a b => .branch (code reg pub arg a) (code reg pub arg b)
  | .whileLt x y a => .whileLt (reg x) (reg y) (code reg pub arg a)

/-- One relocated opcode can only write an embedded register. -/
private theorem line_outside (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K) (arg : Fin R) (op : Op r k)
    (data : Fin K → Word w) (state : Word w) (rs : Regs w R) (mem : Memory w)
    {e out m'} (he : (opAt reg pub arg op).effect data state rs mem = some (e,out,m'))
    (j : Fin R) (hj : j ∉ Set.range reg) : out j = rs j := by
  have hn (i : Fin r) : j ≠ reg i := fun hh => hj ⟨i, hh.symm⟩
  cases op <;> simp only [opAt, renameOp, Op.effect] at he
  all_goals first | split at he | skip
  all_goals first | contradiction | (cases Option.some.inj he; simp [Function.update_of_ne (hn _)])

/-- Lift a finite small-register computation to the enclosing register space.
All unrelated enclosing registers retain their prior values. -/
theorem liftExec (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K) (arg : Fin R) (outside : arg ∉ Set.range reg) (data : Fin K → Word w)
    {state argument : Word w} {a : Flow r k} {small m es out m'}
    (he : Flow.Exec (data ∘ pub) argument a small m es out m')
    (rs : Regs w R) (hr : rs ∘ reg = small) (harg : rs arg = argument) :
    ∃ rs', Flow.Exec data state (code reg pub arg a) rs m es rs' m' ∧
      rs' ∘ reg = out ∧ ∀ j, j ∉ Set.range reg → rs' j = rs j := by
  induction he generalizing rs with
  | @line op small m e small' m' h =>
    subst small
    have hx := (effect reg pub arg op data state rs m).trans (harg ▸ h)
    obtain ⟨⟨ev, rs', m''⟩, hh, heq⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨rfl, heq, rfl⟩ := Prod.mk.inj heq
    exact ⟨rs', .line hh, rfl, line_outside reg pub arg op data state rs m hh⟩
  | seq _ _ ih₁ ih₂ =>
    obtain ⟨mid, hm, he, ho⟩ := ih₁ rs hr harg
    obtain ⟨out, hrun, he', ho'⟩ := ih₂ mid he ((ho arg outside).trans harg)
    exact ⟨out, .seq hm hrun, he', fun j hj => (ho' j hj).trans (ho j hj)⟩
  | ifEqYes ht _ ih | ifEqNo ht _ ih | ifLtYes ht _ ih | ifLtNo ht _ ih =>
    obtain ⟨out, ho, he, hh⟩ := ih rs hr harg
    subst_vars
    first | exact ⟨out, .ifEqYes ht ho, rfl, hh⟩ | exact ⟨out, .ifEqNo ht ho, rfl, hh⟩
          | exact ⟨out, .ifLtYes ht ho, rfl, hh⟩ | exact ⟨out, .ifLtNo ht ho, rfl, hh⟩
  | branchYes _ ih =>
    obtain ⟨out, ho, he, hh⟩ := ih rs hr harg
    exact ⟨out, .branchYes ho, he, hh⟩
  | branchNo _ ih =>
    obtain ⟨out, ho, he, hh⟩ := ih rs hr harg
    exact ⟨out, .branchNo ho, he, hh⟩
  | whileDone ht =>
    subst_vars
    exact ⟨rs, .whileDone ht, rfl, fun _ _ => rfl⟩
  | whileStep ht _ _ ih₁ ih₂ =>
    obtain ⟨mid, hb, he, ho⟩ := ih₁ rs hr harg
    obtain ⟨out, hrun, he', ho'⟩ := ih₂ mid he ((ho arg outside).trans harg)
    rw [← hr] at ht
    exact ⟨out, .whileStep ht hb hrun, he', fun j hj => (ho' j hj).trans (ho j hj)⟩

/-- Conversely, every successful enclosing execution restricts to a genuine
execution of the original program. Both directions include the exact event log. -/
theorem restrictExec (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K) (arg : Fin R) (outside : arg ∉ Set.range reg) (data : Fin K → Word w)
    {state : Word w} (a : Flow r k) {rs m es out m'}
    (he : Flow.Exec data state (code reg pub arg a) rs m es out m') :
    Flow.Exec (data ∘ pub) (rs arg) a (rs ∘ reg) m es (out ∘ reg) m' ∧
      ∀ j, j ∉ Set.range reg → out j = rs j := by
  generalize hcmd : code reg pub arg a = cmd at he
  induction he generalizing a with
  | @line op rs m e out m' h =>
    cases a <;> simp only [code, reduceCtorEq, Flow.line.injEq] at hcmd
    subst op
    constructor
    · apply Flow.Exec.line
      rw [← effect reg pub arg _ data state rs m, h]
      rfl
    · exact line_outside reg pub arg _ data state rs m h
  | seq _ _ ih₁ ih₂ =>
    cases a <;> simp only [code, reduceCtorEq, Flow.seq.injEq] at hcmd
    obtain ⟨ha, hb⟩ := hcmd
    obtain ⟨h₁, o₁⟩ := ih₁ _ ha
    obtain ⟨h₂, o₂⟩ := ih₂ _ hb
    rw [o₁ arg outside] at h₂
    exact ⟨.seq h₁ h₂, fun j hj => (o₂ j hj).trans (o₁ j hj)⟩
  | ifEqYes ht _ ih | ifEqNo ht _ ih | ifLtYes ht _ ih | ifLtNo ht _ ih =>
    cases a <;> simp only [code, reduceCtorEq, Flow.ifEq.injEq, Flow.ifLt.injEq] at hcmd
    obtain ⟨rfl, rfl, ha, hb⟩ := hcmd
    first
    | obtain ⟨h, ho⟩ := ih _ ha; exact ⟨.ifEqYes ht h, ho⟩
    | obtain ⟨h, ho⟩ := ih _ hb; exact ⟨.ifEqNo ht h, ho⟩
    | obtain ⟨h, ho⟩ := ih _ ha; exact ⟨.ifLtYes ht h, ho⟩
    | obtain ⟨h, ho⟩ := ih _ hb; exact ⟨.ifLtNo ht h, ho⟩
  | branchYes _ ih | branchNo _ ih =>
    cases a <;> simp only [code, reduceCtorEq, Flow.branch.injEq] at hcmd
    obtain ⟨ha, hb⟩ := hcmd
    first
    | obtain ⟨h, ho⟩ := ih _ ha; exact ⟨.branchYes h, ho⟩
    | obtain ⟨h, ho⟩ := ih _ hb; exact ⟨.branchNo h, ho⟩
  | whileDone ht =>
    cases a <;> simp only [code, reduceCtorEq, Flow.whileLt.injEq] at hcmd
    obtain ⟨rfl, rfl, _⟩ := hcmd
    exact ⟨.whileDone ht, fun _ _ => rfl⟩
  | whileStep ht _ _ ih₁ ih₂ =>
    cases a <;> simp only [code, reduceCtorEq, Flow.whileLt.injEq] at hcmd
    obtain ⟨rfl, rfl, rfl⟩ := hcmd
    obtain ⟨h₁, o₁⟩ := ih₁ _ rfl
    obtain ⟨h₂, o₂⟩ := ih₂ (.whileLt _ _ _) rfl
    rw [o₁ arg outside] at h₂
    exact ⟨.whileStep ht h₁ h₂, fun j hj => (o₂ j hj).trans (o₁ j hj)⟩

end CompressorRecords.Rebased

end VPVNP
end Computability
end OAI
