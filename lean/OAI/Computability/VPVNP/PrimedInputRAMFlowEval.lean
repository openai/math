import OAI.Computability.VPVNP.PrimedInputRAMFlowLinks

/-!
# Finite executions of structured burst-RAM code

A derivation records the successful elementary instructions of a block and its final
registers and memory. Every test contributes a tick, every binary choice retains its
bit, and every visit to a loop test is counted, including the final false test.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Flow

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w r k p : ℕ}

/-- Fuel-free successful execution of structured code. A derivation is finite even when
the program contains a loop. The event-list length is its exact number of instructions. -/
inductive Exec (pub : Fin k → Word w) (state : Word w) :
    PrimedInputRAM.Flow r k → Regs w r → Memory w → List (Event w) → Regs w r → Memory w → Prop
  | line {op rs m e rs' m'} (h : op.effect pub state rs m = some (e, rs', m')) :
      Exec pub state (.line op) rs m [e] rs' m'
  | seq {a b rs m es r₁ m₁ fs r₂ m₂}
      (first : Exec pub state a rs m es r₁ m₁) (last : Exec pub state b r₁ m₁ fs r₂ m₂) :
      Exec pub state (.seq a b) rs m (es ++ fs) r₂ m₂
  | ifEqYes {l q a b rs m es rs' m'} (test : rs l = rs q)
      (body : Exec pub state a rs m es rs' m') : Exec pub state (.ifEq l q a b) rs m (.tick :: es) rs' m'
  | ifEqNo {l q a b rs m es rs' m'} (test : rs l ≠ rs q)
      (body : Exec pub state b rs m es rs' m') : Exec pub state (.ifEq l q a b) rs m (.tick :: es) rs' m'
  | ifLtYes {l q a b rs m es rs' m'} (test : rs l < rs q)
      (body : Exec pub state a rs m es rs' m') : Exec pub state (.ifLt l q a b) rs m (.tick :: es) rs' m'
  | ifLtNo {l q a b rs m es rs' m'} (test : ¬ rs l < rs q)
      (body : Exec pub state b rs m es rs' m') : Exec pub state (.ifLt l q a b) rs m (.tick :: es) rs' m'
  | branchYes {a b rs m es rs' m'} (body : Exec pub state a rs m es rs' m') :
      Exec pub state (.branch a b) rs m (.choice true :: es) rs' m'
  | branchNo {a b rs m es rs' m'} (body : Exec pub state b rs m es rs' m') :
      Exec pub state (.branch a b) rs m (.choice false :: es) rs' m'
  | whileDone {l q a rs m} (test : ¬ rs l < rs q) :
      Exec pub state (.whileLt l q a) rs m [.tick] rs m
  | whileStep {l q a rs m es r₁ m₁ fs r₂ m₂} (test : rs l < rs q)
      (body : Exec pub state a rs m es r₁ m₁)
      (rest : Exec pub state (.whileLt l q a) r₁ m₁ fs r₂ m₂) :
      Exec pub state (.whileLt l q a) rs m (.tick :: (es ++ fs)) r₂ m₂

theorem choiceBits_append (es fs : List (Event w)) :
    choiceBits (es ++ fs) = choiceBits es ++ choiceBits fs := by
  induction es with
  | nil => rfl
  | cons e es ih => cases e <;> simp [choiceBits, ih]

/-- A successful straight-line opcode never consumes a binary branch bit. -/
theorem line_choices {op : Op r k} {pub : Fin k → Word w} {state : Word w}
    {rs : Regs w r} {m : Memory w} {e rs' m'} (h : op.effect pub state rs m = some (e, rs', m')) :
    choiceBits [e] = [] := by
  cases op <;> simp only [Op.effect, Option.some.injEq, Prod.mk.injEq] at h
  all_goals first | rw [← h.1]; rfl | split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals rw [← h.1]; rfl

/-- Attach the actual executed instruction events to the report of the continuation. -/
def prependEvents (es : List (Event w)) (t : Report w) : Report w := ⟨es ++ t.events, t.result⟩

private theorem line_execute {M : Machine w p r k} {op : Op r k} {label : (Flow.line op).Label → Fin p}
    {stop bad : Fin p} (hl : Linked M (.line op) label stop bad) (hb : M.code bad = .reject)
    {state : Word w} (priv : Word w → Word w) {rs m e rs' m'}
    (he : op.effect M.publicData state rs m = some (e,rs',m')) (fuel : ℕ) (bits : List Bool) :
    execute M.program ([e].length + fuel) ⟨label (Flow.line op).entry,state,rs,priv⟩ m (choiceBits [e] ++ bits) =
      (execute M.program fuel ⟨stop,state,rs',priv⟩ m' bits).map (prependEvents [e]) := by
  rw [line_choices he, List.nil_append, hl.execute hb state priv _ (Flow.line op).entry rs m bits]
  simp [run, code, Jump.run, he, Nat.one_add]
  rfl

private theorem prepend_comp (e : Event w) (es : List (Event w)) :
    Report.prepend e ∘ prependEvents es = prependEvents (e :: es) := rfl

private theorem prependEvents_comp (es fs : List (Event w)) :
    prependEvents es ∘ prependEvents fs = prependEvents (es ++ fs) := by
  funext t
  simp [prependEvents, List.append_assoc]

/-- A finite structured execution runs on the actual machine using exactly one fuel
unit per event. Its branch bits are the choices in the derivation. It transfers control
to the linked exit with the remaining fuel and bits and the updated registers and memory. -/
theorem Exec.execute {M : Machine w p r k} {a : PrimedInputRAM.Flow r k} {state : Word w}
    {rs m es rs' m'} (h : Exec M.publicData state a rs m es rs' m')
    {label : a.Label → Fin p} {stop bad : Fin p} (hl : Linked M a label stop bad)
    (hb : M.code bad = .reject) (priv : Word w → Word w) (fuel : ℕ) (bits : List Bool) :
    BurstRAM.execute M.program (es.length + fuel) ⟨label a.entry,state,rs,priv⟩ m
      (choiceBits es ++ bits) =
      (BurstRAM.execute M.program fuel ⟨stop,state,rs',priv⟩ m' bits).map (prependEvents es) := by
  induction h generalizing stop fuel bits with
  | line he => exact line_execute hl hb priv he fuel bits
  | @seq _ _ _ _ _ _ _ fs _ _ _ _ iha ihb =>
    have ha := iha hl.seqLeft (fs.length + fuel) (choiceBits fs ++ bits)
    have hlast := ihb hl.seqRight fuel bits
    simp only [entry, List.length_append, Nat.add_assoc, choiceBits_append, List.append_assoc]
    erw [ha, hlast, Option.map_map, prependEvents_comp]
  | ifEqYes ht _ ih | ifEqNo ht _ ih | ifLtYes ht _ ih | ifLtNo ht _ ih =>
    first | have hr := ih hl.ifEqYes fuel bits | have hr := ih hl.ifEqNo fuel bits
          | have hr := ih hl.ifLtYes fuel bits | have hr := ih hl.ifLtNo fuel bits
    dsimp only [Function.comp_def] at hr
    simp only [entry, List.length_cons, Nat.succ_add, choiceBits]
    first | rw [hl.execute_ifEq state priv _ _ _ _] | rw [hl.execute_ifLt state priv _ _ _ _]
    simp only [ht, ↓reduceIte]
    erw [hr, Option.map_map]
    rfl
  | branchYes _ ih | branchNo _ ih =>
    first | have hr := ih hl.branchYes fuel bits | have hr := ih hl.branchNo fuel bits
    dsimp only [Function.comp_def] at hr
    simp only [entry, List.length_cons, Nat.succ_add, choiceBits, List.cons_append]
    rw [hl.execute_branch state priv _ _ _ _ _]
    erw [hr, Option.map_map]
    rfl
  | whileDone ht =>
    simp only [entry, List.length_cons, List.length_nil, Nat.succ_add, Nat.zero_add, choiceBits,
      List.nil_append]
    rw [hl.execute_whileLt state priv _ _ _ _, ite_eq_right ht]
    rfl
  | @whileStep _ _ _ _ _ _ _ _ fs _ _ ht _ _ ihb ihr =>
    have hbdy := ihb hl.loopBody (fs.length + fuel) (choiceBits fs ++ bits)
    have hr := ihr hl fuel bits
    simp only [entry] at hr
    simp only [entry, List.length_cons, Nat.succ_add, List.length_append, Nat.add_assoc,
      choiceBits, choiceBits_append, List.append_assoc]
    erw [hl.execute_whileLt state priv _ _ _ _, ite_eq_left ht, hbdy, hr, Option.map_map,
      prepend_comp, Option.map_map, prependEvents_comp, List.cons_append]

end PrimedInputRAM.Flow

end VPVNP
end Computability
end OAI
