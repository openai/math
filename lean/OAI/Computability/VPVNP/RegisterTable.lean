import OAI.Computability.VPVNP.RAMTapeISADispatch
import OAI.Computability.VPVNP.UniversalCountStackBounds

/-!
# Fixed register instruction tables on binary stacks

A deterministic register program for a coordinate query can run for
exponentially many instructions. Its program counter is finite control.
Ordinary instruction callbacks resume directly at the next program counter,
so the machine needs no stack of fuel credits. Each instruction restores a
bank of width-bounded registers before the next instruction starts.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.RegisterTable

open BurstRAM PrivateRAM UniversalCountStack

variable {w v p r k : ℕ}

/-- The next program counter and register contents for a register-only opcode. -/
def step (i : Instr v p r k) (pub : Fin k → Word w) (persistent : Word w) (reg : Fin r → Word w) :
    Option (Fin p × (Fin r → Word w)) :=
  match i with
  | .constant dst x j => some (j, Function.update reg dst (Fin.ofNat _ x.val))
  | .publicWord dst a j => some (j, Function.update reg dst (pub a))
  | .stateWord dst j => some (j, Function.update reg dst persistent)
  | .copy dst src j => some (j, Function.update reg dst (reg src))
  | .binary op dst x y j => some (j, Function.update reg dst (op.eval (reg x) (reg y)))
  | .jumpEq x y a b => some (if reg x = reg y then a else b, reg)
  | .jumpLt x y a b => some (if reg x < reg y then a else b, reg)
  | _ => none

/-- Runs between instruction-entry boundaries, including the boundary at which a caller takes over. -/
inductive Runs (T : Template p r k) (pub : Fin k → Word w) (persistent : Word w) :
    ℕ → Fin p → (Fin r → Word w) → Fin p → (Fin r → Word w) → Prop
  | nil (j R) : Runs T pub persistent 0 j R j R
  | cons {j R j' R' n out A} (hs : step (T.code j) pub persistent R = some (j', R')) :
      Runs T pub persistent n j' R' out A → Runs T pub persistent (n+1) j R out A

theorem Runs.one {T : Template p r k} {pub : Fin k → Word w} {persistent : Word w}
    {j R j' R'} (hs : step (T.code j) pub persistent R = some (j',R')) :
    Runs T pub persistent 1 j R j' R' := .cons hs (.nil ..)

theorem Runs.trans {T : Template p r k} {pub : Fin k → Word w} {persistent : Word w}
    {a b j R j' R' l A} (h : Runs T pub persistent a j R j' R') (g : Runs T pub persistent b j' R' l A) :
    Runs T pub persistent (a+b) j R l A := by
  induction h with
  | nil => simpa using g
  | cons hs _ ih => simpa only [Nat.succ_add] using Runs.cons hs (ih g)

/-- Fixed physical binary control. Nonlocal callbacks are exit labels for callers. -/
def code (T : Template p r k) : StackCode (ISA.Port r k) (ISA.State T) :=
  fun q => match ISA.resume? T q with
  | some (.next j) => .goto (ISA.entry T j)
  | _ => ISA.code T q

/-- Initial bit stacks for the register table, encoding the public words, persistent word, and
registers with an empty address log. -/
def bank (pub : Fin k → Word w) (persistent : Word w) (reg : Fin r → Word w) : Stacks (ISA.Port r k) :=
  ISA.bank pub persistent reg []

theorem bank_length_le (pub : Fin k → Word w) (persistent : Word w) (reg : Fin r → Word w)
    (a : ISA.Port r k) : (bank pub persistent reg a).length ≤ w := by
  cases a with
  | reg | pub | persistent => simp [bank, ISA.bank]
  | work => simp [bank, ISA.bank]
  | logPort a => cases a <;> simp [bank, ISA.bank, ISA.logStacks, AddressLog.keys, AddressLog.values]

private theorem dispatch_of_step (i : Instr v p r k) (pub : Fin k → Word w)
    (pc : Fin p) (persistent : Word w) (reg : Fin r → Word w) {j reg'}
    (hs : step i pub persistent reg = some (j,reg')) :
    let c : LogConfig w p r := ⟨pc, persistent, reg, []⟩
    ISA.exitFor i ((ISA.jumpTest i c).getD false) = .next j ∧
      ISA.configBank pub (ISA.post i pub c) = bank pub persistent reg' := by
  cases i <;> simp only [step, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hs
  all_goals first | contradiction | obtain ⟨rfl, rfl⟩ := hs
  all_goals simp [ISA.exitFor, ISA.jumpTest, ISA.post, ISA.configBank, bank, TapeWord.Comparison.Op.eval]

/-- One register instruction is simulated by the physical machine within a
quadratic word-length bound. -/
theorem one_run {T : Template p r k} {pub : Fin k → Word w} {persistent : Word w}
    {j R j' R'} (hs : step (T.code j) pub persistent R = some (j',R')) :
    ∃ t ≤ ISA.prepareBound w 0 + 3,
      StackRuns (code T) t (ISA.entry T j) (bank pub persistent R) (ISA.entry T j') (bank pub persistent R') := by
  let c : LogConfig w p r := ⟨j,persistent,R,[]⟩
  obtain ⟨t,ht,hr⟩ := ISA.dispatch_step T pub c
  obtain ⟨hcb,hbank⟩ := dispatch_of_step (T.code j) pub j persistent R hs
  have hl := hr.lift id Function.injective_id id (bank pub persistent R) (target := code T)
    (by intro q hq; simp only [id_eq, code, ISA.resume_none_of_continuing T q hq]; cases ISA.code T q <;> rfl)
  have install (s : Stacks (ISA.Port r k)) : installStacks id (bank pub persistent R) s = s := by
    funext a; exact installStacks_at Function.injective_id ..
  simp only [id_eq, install] at hl
  change StackRuns (code T) t (ISA.entry T j) (bank pub persistent R)
    (ISA.callback T (ISA.exitFor (T.code j) ((ISA.jumpTest (T.code j) c).getD false)))
    (ISA.configBank pub (ISA.post (T.code j) pub c)) at hl
  rw [hcb, hbank] at hl
  have hg := StackStep.goto (s := bank pub persistent R') (q := ISA.callback T (.next j'))
    (show code T _ = .goto (ISA.entry T j') from by simp [code])
  refine ⟨t+1, ?_, hl.trans (.cons hg (.nil ..))⟩
  change t ≤ ISA.prepareBound w 0 + 2 at ht
  omega

/-- End-to-end simulation between arbitrary instruction-entry labels. Each
stack has polynomial height independently of the number of loop iterations. -/
theorem run {T : Template p r k} {pub : Fin k → Word w} {persistent : Word w}
    {n j R j' R'} (h : Runs T pub persistent n j R j' R') :
    ∃ t ≤ n * (ISA.prepareBound w 0 + 3),
      SpaceRun (code T) (w + (ISA.prepareBound w 0 + 3)) t
        (ISA.entry T j) (bank pub persistent R) (ISA.entry T j') (bank pub persistent R') := by
  induction h with
  | nil j R => exact ⟨0, by simp, .nil _ _ fun a => (bank_length_le _ _ _ a).trans (Nat.le_add_right ..)⟩
  | @cons j R j' R' n l A hs _ ih =>
    obtain ⟨t, ht, hr⟩ := one_run hs
    obtain ⟨u, hu, htail⟩ := ih
    have hbounded := spaceRun_of_steps hr fun a => Nat.add_le_add (bank_length_le _ _ _ a) ht
    refine ⟨t+u, ?_, hbounded.trans htail⟩
    rw [Nat.succ_mul]
    omega

end RAMTape.RegisterTable

end VPVNP
end Computability
end OAI
