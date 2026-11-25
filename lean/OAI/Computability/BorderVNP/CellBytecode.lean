import OAI.Computability.BorderVNP.TeamGuard
import OAI.Computability.VPVNP.StructuredStackClock
import Mathlib.Tactic.DeriveFintype

/-! # Elementary private instructions for the cell validator

The instruction stream and all intermediate Boolean values live on stacks. Offsets count
backwards from the most recently produced value. A read scans the stack and restores it.
One guess is one genuine binary branch, even if the bit is never used.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro

open VPVNP.RAMTape

/-- Instructions for Boolean tests and signed weights inside one cell. -/
inductive Op where
  | literal (bit : Bool)
  | guess
  | read (offset : ℕ)
  | nand
  | guard
  | sign
  deriving DecidableEq

/-- Prefix code for a single instruction. A read offset is unary in the private working copy. -/
def Op.bits : Op → List Bool
  | .literal b => [false, b]
  | .guess => [true, false]
  | .read k => [true, true, false] ++ List.replicate k true ++ [false]
  | .nand => [true, true, true, false]
  | .guard => [true, true, true, true, false]
  | .sign => [true, true, true, true, true]

/-- Three independent bit stacks used by the finite instruction interpreter. -/
inductive Port where
  | stream | values | scratch
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Accumulated guard and sign, retained across all instructions. -/
structure Flags where
  /-- All checks up to this point passed. -/
  ok : Bool
  /-- Parity of the selected negative factors. -/
  minus : Bool
  deriving DecidableEq, Fintype

/-- Finite control for prefix decoding, a temporary Boolean, and the two sweeps of a read. -/
inductive Phase where
  | fetch | literal | second | third | fourth | fifth
  | choose | emit (b : Bool) | seek | advance | save (b : Bool)
  | restore (b : Bool) | putBack (value bit : Bool) | pick | replace (b : Bool)
  | nandFirst | nandSecond (b : Bool) | guard | sign | stop | bad
  deriving DecidableEq, Fintype

/-- A complete instruction-boundary control label. -/
abbrev State := Flags × Phase

private def decode (f : Flags) (lo hi : Phase) : Option Bool → State
  | none => (f, .bad)
  | some false => (f, lo)
  | some true => (f, hi)

/-- Fixed signed stack machine. Unused suffixes of a truncated instruction reject. -/
def code : StackCode Port State
  | (f, .fetch) => .pop .stream fun v => v.elim (f,.stop) (fun b => (f, if b then .second else .literal))
  | (f, .literal) => .pop .stream fun v => v.elim (f,.bad) (fun b => (f,.emit b))
  | (f, .second) => .pop .stream (decode f .choose .third)
  | (f, .third) => .pop .stream (decode f .seek .fourth)
  | (f, .fourth) => .pop .stream (decode f .nandFirst .fifth)
  | (f, .fifth) => .pop .stream (decode f .guard .sign)
  | (f, .choose) => .choose (f,.emit false) (f,.emit true)
  | (f, .emit b) => .push .values b (f,.fetch)
  | (f, .seek) => .pop .stream (decode f .pick .advance)
  | (f, .advance) => .pop .values fun v => v.elim (f,.seek) (fun b => (f,.save b))
  | (f, .save b) => .push .scratch b (f,.seek)
  | (f, .pick) => .pop .values fun v => v.elim (f,.restore false) (fun b => (f,.replace b))
  | (f, .replace b) => .push .values b (f,.restore b)
  | (f, .restore b) => .pop .scratch fun v => v.elim (f,.emit b) (fun x => (f,.putBack b x))
  | (f, .putBack b x) => .push .values x (f,.restore b)
  | (f, .nandFirst) => .pop .values fun v => (f, .nandSecond (v.getD false))
  | (f, .nandSecond b) => .pop .values fun v => (f, .emit (!(b && v.getD false)))
  | (f, .guard) => .pop .values fun v => (⟨f.ok && v.getD false, f.minus⟩,.fetch)
  | (f, .sign) => .pop .values fun v => (⟨f.ok, f.minus ^^ v.getD false⟩,.fetch)
  | (f, .stop) => .halt f.ok
  | (_, .bad) => .halt false

/-- Only a successful terminal contributes its accumulated sign. -/
def negative : State → Bool := fun q => q.1.minus

/-- Input stream, persistent Boolean values and scan scratch. -/
def bank (stream values scratch : List Bool) : Stacks Port
  | .stream => stream
  | .values => values
  | .scratch => scratch

@[simp] private theorem setStream (s v a s' : List Bool) :
    Function.update (bank s v a) .stream s' = bank s' v a := by funext i; cases i <;> simp [bank]

@[simp] private theorem setValues (s v a v' : List Bool) :
    Function.update (bank s v a) .values v' = bank s v' a := by funext i; cases i <;> simp [bank]

@[simp] private theorem setScratch (s v a a' : List Bool) :
    Function.update (bank s v a) .scratch a' = bank s v a' := by funext i; cases i <;> simp [bank]

local macro "machine_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [bank, List.head?_cons, List.head?_nil, List.tail_cons, List.tail_nil,
    Option.elim_some, Option.elim_none, Option.getD_some, Option.getD_none, decode,
    Bool.false_eq_true, ite_false, ite_true, setStream, setScratch, setValues, ↓reduceIte])

private theorem seek_run (f : Flags) (s a : List Bool) (k : ℕ) (v : List Bool) :
    ∃ t ≤ 3*k+1, StackRuns code t (f,.seek) (bank (List.replicate k true ++ false :: s) v a)
      (f,.pick) (bank s (v.drop k) ((v.take k).reverse ++ a)) := by
  induction k generalizing v a with
  | zero =>
    refine ⟨1, by omega, ?_⟩
    simp only [List.replicate_zero, List.nil_append, List.drop_zero, List.take_zero, List.reverse_nil]
    machine_step
    exact .nil ..
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    cases v with
    | nil =>
      obtain ⟨t, ht, h⟩ := ih a []
      refine ⟨t+1+1, by omega, ?_⟩
      machine_step
      machine_step
      simpa using h
    | cons x v =>
      obtain ⟨t, ht, h⟩ := ih (x::a) v
      refine ⟨t+1+1+1, by omega, ?_⟩
      machine_step
      machine_step
      machine_step
      simpa using h

private theorem restore_run (f : Flags) (s : List Bool) (b : Bool) (a v : List Bool) :
    StackRuns code (2*a.length+1) (f,.restore b) (bank s v a)
      (f,.emit b) (bank s (a.reverse ++ v) []) := by
  induction a generalizing v with
  | nil =>
    simp only [List.length_nil, mul_zero, zero_add, List.reverse_nil, List.nil_append]
    machine_step
    exact .nil ..
  | cons x a ih =>
    rw [List.length_cons, Nat.mul_succ, show 2*a.length+2+1=(2*a.length+1)+1+1 by omega]
    machine_step
    machine_step
    simpa using ih (x::v)

private theorem pick_run (f : Flags) (s a v : List Bool) :
    ∃ t ≤ 2, StackRuns code t (f,.pick) (bank s v a) (f,.restore (v.head?.getD false)) (bank s v a) := by
  cases v with
  | nil => refine ⟨1, by decide, ?_⟩; machine_step; exact .nil ..
  | cons b v => refine ⟨2, by decide, ?_⟩; machine_step; machine_step; exact .nil ..

/-- A read copies the selected bit and leaves all earlier bits at their original addresses
under the new top. Out-of-range reads copy a zero. -/
theorem read_run (f : Flags) (s v : List Bool) (k : ℕ) :
    ∃ t ≤ 5*k+8, StackRuns code t (f,.fetch) (bank ((Op.read k).bits ++ s) v [])
      (f,.fetch) (bank s (((v.drop k).head?.getD false) :: v) []) := by
  obtain ⟨t, ht, h⟩ := seek_run f s [] k v
  rw [List.append_nil] at h
  obtain ⟨u, hu, hp⟩ := pick_run f s (v.take k).reverse (v.drop k)
  have r := restore_run f s ((v.drop k).head?.getD false) (v.take k).reverse (v.drop k)
  rw [List.length_reverse, List.reverse_reverse, List.take_append_drop] at r
  have emit : StackRuns code 1 (f,.emit ((v.drop k).head?.getD false)) (bank s v [])
      (f,.fetch) (bank s (((v.drop k).head?.getD false) :: v) []) := by machine_step; exact .nil ..
  have all := (((h.trans hp).trans r).trans emit)
  have hk : (v.take k).length ≤ k := by simp
  refine ⟨t+u+(2*(v.take k).length+1)+1+1+1+1, ?_, ?_⟩
  · exact show t+u+(2*(v.take k).length+1)+1+1+1+1 ≤ 5*k+8 by omega
  simp [Op.bits]
  machine_step
  machine_step
  machine_step
  simpa using all


/-- Stack and flag effect of one private instruction with its choice bit supplied. -/
def Op.effect (f : Flags) (v : List Bool) (choice : Bool) : Op → Flags × List Bool
  | .literal b => (f, b :: v)
  | .guess => (f, choice :: v)
  | .read k => (f, (v.drop k).head?.getD false :: v)
  | .nand => (f, (!(v.head?.getD false && v.tail.head?.getD false)) :: v.tail.tail)
  | .guard => (⟨f.ok && v.head?.getD false, f.minus⟩, v.tail)
  | .sign => (⟨f.ok, f.minus ^^ v.head?.getD false⟩, v.tail)

/-- A uniform branch clock for one instruction at any initial stack contents. -/
def Op.ticks : Op → ℕ
  | .literal _ => 3
  | .guess => 4
  | .read k => 5*k+8
  | .nand => 7
  | .guard | .sign => 6

private theorem deterministic_run (o : Op) (ho : o ≠ .guess) (f : Flags) (s v : List Bool) :
    ∃ t ≤ o.ticks, StackRuns code t (f,.fetch) (bank (o.bits ++ s) v [])
      ((o.effect f v false).1,.fetch) (bank s (o.effect f v false).2 []) := by
  cases o with
  | guess => exact (ho rfl).elim
  | read k => exact read_run f s v k
  | literal b =>
    refine ⟨3, le_rfl, ?_⟩
    simp only [Op.bits, List.cons_append, List.nil_append, Op.effect]
    iterate 3 machine_step
    exact .nil ..
  | nand =>
    refine ⟨7, le_rfl, ?_⟩
    simp only [Op.bits, List.cons_append, List.nil_append, Op.effect]
    iterate 7 machine_step
    exact .nil ..
  | guard | sign =>
    refine ⟨6, le_rfl, ?_⟩
    simp only [Op.bits, List.cons_append, List.nil_append, Op.effect]
    iterate 6 machine_step
    exact .nil ..

private theorem guess_decode (f : Flags) (s v : List Bool) :
    StackRuns code 2 (f,.fetch) (bank (Op.guess.bits ++ s) v []) (f,.choose) (bank s v []) := by
  simp only [Op.bits, List.cons_append, List.nil_append]
  iterate 2 machine_step
  exact .nil ..

/-- Contiguous binary encoding of the whole working instruction stream. -/
def stream (program : List Op) : List Bool := program.flatMap Op.bits

/-- Worst-case branch clock, including the end-of-stream test and terminal instruction. -/
def budget (program : List Op) : ℕ := (program.map Op.ticks).sum + 2

/-- Signed private multiplicity, summing both children only at genuine fresh guesses. -/
def value : List Op → Flags → List Bool → ℤ
  | [], f, _ => TeamTape.haltWeight f.ok f.minus
  | .guess :: ops, f, v => value ops f (false :: v) + value ops f (true :: v)
  | o :: ops, f, v => let (f', v') := o.effect f v false; value ops f' v'

private theorem value_deterministic {o : Op} (h : o ≠ .guess) (ops : List Op)
    (f : Flags) (v : List Bool) :
    value (o :: ops) f v = value ops (o.effect f v false).1 (o.effect f v false).2 := by
  cases o <;> first | rfl | exact (h rfl).elim

/-- On every initial value stack every branch of the actual finite machine stops at this
clock and its signed sum is exactly the instruction-stream semantics. -/
theorem execute (ops : List Op) (f : Flags) (v : List Bool) (t : ℕ) (ht : budget ops ≤ t) :
    StopsWithin code t (f,.fetch) (bank (stream ops) v []) ∧
      TeamStack.paths code negative t (f,.fetch) (bank (stream ops) v []) = value ops f v := by
  induction ops generalizing f v t with
  | nil =>
    have h : 2 ≤ t := ht
    obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [Nat.add_comm 2 l]
    simp only [stream, List.flatMap_nil, StopsWithin, code, bank, TeamStack.paths,
      List.head?_nil, Option.elim_none, negative, value, true_and]
  | cons o ops ih =>
    have h : o.ticks + budget ops ≤ t := by simpa [budget, Nat.add_assoc] using ht
    change StopsWithin code t (f,.fetch) (bank (o.bits ++ stream ops) v []) ∧
      TeamStack.paths code negative t (f,.fetch) (bank (o.bits ++ stream ops) v []) = _
    by_cases hg : o = .guess
    · subst o
      change 4 + budget ops ≤ t at h
      obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le (show 4 ≤ t by omega)
      have hb : budget ops ≤ l := by omega
      have hlo := ih f (false::v) l hb
      have hhi := ih f (true::v) l hb
      have hd := guess_decode f (stream ops) v
      rw [show t = (l+1+1)+2 by omega, hd.stopsWithin_iff, TeamGuard.runs_paths hd negative]
      simp only [StopsWithin, code, TeamStack.paths, setValues, bank, value]
      exact ⟨⟨hlo.1, hhi.1⟩, congrArg₂ (·+·) hlo.2 hhi.2⟩
    · obtain ⟨d, hd, run⟩ := deterministic_run o hg f (stream ops) v
      have he : t = t-d+d := by omega
      rw [he, run.stopsWithin_iff, TeamGuard.runs_paths run negative, value_deterministic hg]
      exact ih _ _ _ (by omega)

/-- The physical cost of decoding the bytecode is linear in the length of its private
working stream. The read offset is paid for on each use. -/
theorem budget_le (ops : List Op) : budget ops ≤ 5*(stream ops).length+2 := by
  induction ops with
  | nil => simp [budget, stream]
  | cons o ops ih =>
    have h : o.ticks ≤ 5*o.bits.length := by
      cases o <;> simp [Op.ticks, Op.bits]
      omega
    change (o.ticks + (ops.map Op.ticks).sum) + 2 ≤ 5*(o.bits ++ stream ops).length+2
    rw [List.length_append, Nat.mul_add]
    unfold budget at ih
    omega

end CellMacro

end BorderVNP
end Computability
end OAI
