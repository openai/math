import OAI.Computability.NearSquareRoot.CommonAlphabetRead
import OAI.Computability.NearSquareRoot.CommonAlphabetWrite
import OAI.Computability.NearSquareRoot.CommonAlphabetMotion
import OAI.Computability.NearSquareRoot.CommonAlphabetSpace

/-! # Exact physical trace of a block-serialized multitape machine -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet
open IntegerMultiplication
variable {A Q I : Type} (c : Code A) (m : TM.Rule A Q I)

abbrev PhysicalTapes (I : Type) := I → TM.Tape (Option Bool)

def boundary (x : TM.Config A Q I) (S : PhysicalTapes I) : TM.Config (Option Bool) (PC A Q I c.width) I :=
  ⟨.ready x.pc (fun i => (x.tape i).view 0), S⟩

def initial (x : TM.Config A Q I) (S : PhysicalTapes I) : TM.Config (Option Bool) (PC A Q I c.width) I :=
  ⟨readStart c x.pc, S⟩

def clock (n : ℕ) := 2*c.width + (1+5*c.width)*n

/-- Read every block and rewind, charging the initialization of the symbol cache. -/
theorem initializeCache (x : TM.Config A Q I) (S : PhysicalTapes I)
    (repr : ∀ i, Represents c (S i) (x.tape i)) :
    ∃ S', Trace (TM.advance (rule c m)) (initial c x S) (2*c.width) (boundary c x S') ∧
      ∀ i, Represents c (S' i) (x.tape i) := by
  obtain ⟨R, read, cells, pos, _⟩ := readSweep c m x.pc S x.tape repr
  obtain ⟨S', rewind, endT⟩ := rewind_run c m x.pc _ R
  refine ⟨S', by simpa only [two_mul, initial, boundary] using read.trans rewind, fun i => ⟨?_, fun p d => ?_⟩⟩
  · rw [(endT i).2, pos, add_sub_cancel_right]
  · rw [(endT i).1]
    exact cells i p d

/-- One source transition, including writing its new symbols, aligning the independent
heads, reading the new blocks, and rewinding to the new instruction boundary. -/
theorem simulate_one {x y : TM.Config A Q I} (step : TM.advance m x = some y)
    (S : PhysicalTapes I) (repr : ∀ i, Represents c (S i) (x.tape i)) :
    ∃ S', Trace (TM.advance (rule c m)) (boundary c x S) (1+5*c.width) (boundary c y S') ∧
      ∀ i, Represents c (S' i) (y.tape i) := by
  cases inst : m x.pc (fun i => (x.tape i).view 0) with
  | none => simp [TM.advance, inst] at step
  | some cmd =>
    obtain ⟨q,op⟩ := cmd
    simp only [TM.advance, inst, Option.map_some, Option.some.injEq] at step
    subst y
    let T := fun i => (x.tape i).apply (op i)
    let next : TM.Config A Q I := ⟨q,T⟩
    have dispatch : TM.advance (rule c m) (boundary c x S) =
        some ⟨.work q op .write (first c), S⟩ := by
      simp [TM.advance, boundary, rule, inst, hold, SM.Action.apply_stay]
    obtain ⟨U, writeRun, writeCells, writePos⟩ := writeSweep c m q op x.tape S repr
    obtain ⟨V, alignRun, alignT⟩ := align_run c m q op x.tape U writePos
    have nextRepr (i : I) : Represents c (V i) (next.tape i) := by
      constructor
      · rw [(alignT i).2]
        change _ = ((x.tape i).pos + (op i).2.shift)*c.width
        rw [add_mul]
      · intro p d
        rw [(alignT i).1]
        exact writeCells i p d
    obtain ⟨S', readRun, finish⟩ := initializeCache c m next V nextRepr
    refine ⟨S', ?_, finish⟩
    have all := (((Trace.single dispatch).trans writeRun).trans alignRun).trans readRun
    convert all using 1
    omega

theorem simulate_halt {x : TM.Config A Q I} (halt : TM.advance m x = none) (S : PhysicalTapes I) :
    TM.advance (rule c m) (boundary c x S) = none := by
  have h : m x.pc (fun i => (x.tape i).view 0) = none := by simpa [TM.advance] using halt
  simp [TM.advance, rule, boundary, h]

/-- Concatenate all microsteps from a cached instruction boundary. -/
theorem from_boundary {x y : TM.Config A Q I} {n : ℕ}
    (run : Trace (TM.advance m) x n y) (S : PhysicalTapes I)
    (repr : ∀ i, Represents c (S i) (x.tape i)) :
    ∃ S', Trace (TM.advance (rule c m)) (boundary c x S) ((1+5*c.width)*n) (boundary c y S') ∧
      ∀ i, Represents c (S' i) (y.tape i) := by
  induction run generalizing S with
  | nil => exact ⟨S, by simp only [Nat.mul_zero]; exact .nil _, repr⟩
  | cons step _ ih =>
    obtain ⟨R, one, hr⟩ := simulate_one c m step S repr
    obtain ⟨S', rest, hs⟩ := ih R hr
    exact ⟨S', by simpa only [Nat.mul_add, Nat.mul_one] using one.trans rest, hs⟩

/-- Actual initialization and all source transitions, ending in a configuration which
represents the entire virtual tape contents and every head position. -/
theorem simulate {x y : TM.Config A Q I} {n : ℕ} (run : Trace (TM.advance m) x n y)
    (S : PhysicalTapes I) (repr : ∀ i, Represents c (S i) (x.tape i)) :
    ∃ S', Trace (TM.advance (rule c m)) (initial c x S) (clock c n) (boundary c y S') ∧
      ∀ i, Represents c (S' i) (y.tape i) := by
  obtain ⟨R,setup,hR⟩ := initializeCache c m x S repr
  obtain ⟨S',body,hS⟩ := from_boundary c m run R hR
  exact ⟨S', setup.trans body, hS⟩

/-- Count distinct physical cells of the same run, through all partial sweeps. -/
theorem simulate_space {x y : TM.Config A Q I} {n cells : ℕ} (run : Trace (TM.advance m) x n y)
    (space : VisitsAtMost m x n cells) (S : PhysicalTapes I)
    (repr : ∀ i, Represents c (S i) (x.tape i)) :
    VisitsAtMost (rule c m) (initial c x S) (clock c n) ((2*(1+5*c.width)+1)*cells) := by
  apply visitsAtMost_of_checkpoints c.width (clock c) space (by simp [clock])
    (by intro k _; simp [clock, Nat.mul_succ, Nat.add_assoc])
  intro k hk
  obtain ⟨z, h, _⟩ := trace_split run hk
  obtain ⟨S', sim, align⟩ := simulate c m h S repr
  exact ⟨z, boundary c z S', h, sim, fun i => (align i).1⟩

end CommonAlphabet

end NearSquareRoot
end Computability
end OAI
