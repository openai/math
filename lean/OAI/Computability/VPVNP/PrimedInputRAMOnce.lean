import OAI.Computability.VPVNP.PrimedInputRAMFlowEval

/-!
# Running acyclic opcode fragments of the input assembler

These fragments have no internal loop. A supplied Boolean controls any
explicit choice, and the returned event sequence records its occurrence.
The implementation below provides executable witnesses for structured
execution and a static instruction bound on every successful path.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Flow

open BurstRAM PrimedStackRAM

variable {w r k : ℕ}

/-- The event trace, final registers and final memory produced by executing an acyclic code
fragment. -/
abbrev Effect (w r : ℕ) := List (Event w) × Regs w r × Memory w

private def leading (e : Event w) (z : Effect w r) : Effect w r := (e :: z.1, z.2)

/-- Execute the branch selected by the register comparison. A loop requires
its own finite derivation and is excluded from this acyclic evaluator. -/
def once (pub : Fin k → Word w) (state : Word w) (bit : Bool) :
    PrimedInputRAM.Flow r k → Regs w r → Memory w → Option (Effect w r)
  | .line op, rs, m => (op.effect pub state rs m).map fun (e,rs',m') ↦ ([e],rs',m')
  | .seq a b, rs, m => do
    let (ea,ra,ma) ← once pub state bit a rs m
    let (eb,rb,mb) ← once pub state bit b ra ma
    return (ea++eb,rb,mb)
  | .ifEq l q yes no, rs, m =>
    if rs l = rs q then (once pub state bit yes rs m).map (leading .tick)
    else (once pub state bit no rs m).map (leading .tick)
  | .ifLt l q yes no, rs, m =>
    if rs l < rs q then (once pub state bit yes rs m).map (leading .tick)
    else (once pub state bit no rs m).map (leading .tick)
  | .branch yes no, rs, m =>
    if bit then (once pub state bit yes rs m).map (leading (.choice bit))
    else (once pub state bit no rs m).map (leading (.choice bit))
  | .whileLt .., _, _ => none

/-- The computed trace is a real finite execution and is bounded by the
static instruction count. -/
theorem once_sound (pub : Fin k → Word w) (state : Word w) (bit : Bool) (a : PrimedInputRAM.Flow r k)
    (rs : Regs w r) (m : Memory w) {es rs' m'}
    (he : once pub state bit a rs m = some (es,rs',m')) :
    Exec pub state a rs m es rs' m' ∧ es.length ≤ a.length := by
  induction a generalizing rs m es rs' m' with
  | line op =>
    obtain ⟨⟨e,ra,ma⟩,h,hc⟩ := Option.map_eq_some_iff.mp he
    cases hc
    exact ⟨.line h, Nat.le_refl 1⟩
  | seq a b iha ihb =>
    simp only [once, bind, Option.bind_eq_some_iff] at he
    obtain ⟨⟨ea,ra,ma⟩,ha,⟨eb,rb,mb⟩,hb,hc⟩ := he
    cases hc
    obtain ⟨hA, cA⟩ := iha _ _ ha
    obtain ⟨hB, cB⟩ := ihb _ _ hb
    exact ⟨.seq hA hB, by simpa [length] using Nat.add_le_add cA cB⟩
  | ifEq l q yes no ihy ihn =>
    by_cases ht : rs l = rs q
    · simp only [once, ht, ite_true, Option.map_eq_some_iff] at he
      obtain ⟨⟨e,ra,ma⟩,h,hc⟩ := he
      cases hc
      obtain ⟨hE,c⟩ := ihy _ _ h
      exact ⟨.ifEqYes ht hE, by simp only [List.length_cons,length]; omega⟩
    · simp only [once, ht, ite_false, Option.map_eq_some_iff] at he
      obtain ⟨⟨e,ra,ma⟩,h,hc⟩ := he
      cases hc
      obtain ⟨hE,c⟩ := ihn _ _ h
      exact ⟨.ifEqNo ht hE, by simp only [List.length_cons,length]; omega⟩
  | ifLt l q yes no ihy ihn =>
    by_cases ht : rs l < rs q
    · simp only [once, ht, ite_true, Option.map_eq_some_iff] at he
      obtain ⟨⟨e,ra,ma⟩,h,hc⟩ := he
      cases hc
      obtain ⟨hE,c⟩ := ihy _ _ h
      exact ⟨.ifLtYes ht hE, by simp only [List.length_cons,length]; omega⟩
    · simp only [once, ht, ite_false, Option.map_eq_some_iff] at he
      obtain ⟨⟨e,ra,ma⟩,h,hc⟩ := he
      cases hc
      obtain ⟨hE,c⟩ := ihn _ _ h
      exact ⟨.ifLtNo ht hE, by simp only [List.length_cons,length]; omega⟩
  | branch yes no ihy ihn =>
    cases bit
    · simp only [once, Bool.false_eq_true, ite_false, Option.map_eq_some_iff] at he
      obtain ⟨⟨e,ra,ma⟩,h,hc⟩ := he
      cases hc
      obtain ⟨hE,c⟩ := ihn _ _ h
      exact ⟨.branchNo hE, by simp only [List.length_cons,length]; omega⟩
    · simp only [once, ite_true, Option.map_eq_some_iff] at he
      obtain ⟨⟨e,ra,ma⟩,h,hc⟩ := he
      cases hc
      obtain ⟨hE,c⟩ := ihy _ _ h
      exact ⟨.branchYes hE, by simp only [List.length_cons,length]; omega⟩
  | whileLt => simp [once] at he

end PrimedInputRAM.Flow

end VPVNP
end Computability
end OAI
