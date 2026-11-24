import OAI.Computability.VPVNP.PairShrinkHiddenCode

/-!
# Executing the shrinking hidden-array row control

One count probe initializes the row. The guard uses the remaining number of
entries, and the back edge advances the dense-ID pointer by one word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkHiddenGuess

open BurstRAM PrivateRAM NodeArguments.ChildScan
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.tick ReadPrefix.read ReadPrefix.nil ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

variable {W p r k : ℕ} {M : Machine W p r k} {pc : Control → Fin p} {reg : Fin 22 ↪ Fin r}
variable {width guess done : Fin p}

private theorem control_step (link : ControlLinked M pc reg width guess done)
    (j : Control) {c : Config W p r} (h : c.pc = pc j) :
    M.program.step c = (control pc reg width guess done j).run M.publicData c := by
  simp [Machine.program, h, link j]

/-- The six events before the first loop test. They include one external read of the selected
owner's count and five local steps. -/
def setupEvents (m : Memory W) (g : Args W) : List (Event W) :=
  [.tick, .tick, .tick, .read ((g.countBase + g.owner : ℕ) : Word W) (m (g.countBase + g.owner)),
   .tick, .tick]

/-- Load the count and the start of this owner's row, and establish the two
constant registers used by the guard and back edge. -/
theorem setup_run (link : ControlLinked M pc reg width guess done) (m : Memory W) (g : Args W)
    (c : Config W p r) (hc : c.pc = pc .one) (inputs : Inputs g reg c)
    (fit : g.countBase + g.owner < 2 ^ W) :
    ∃ d, Prefix M m c d [] (setupEvents m g) ∧ d.pc = pc .test ∧
      d.reg (reg 14) = m (g.countBase + g.owner) ∧ d.reg (reg 5) = (g.row : Word W) ∧
      Ready g reg d ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      ∀ i, i ≠ reg 3 → i ≠ reg 5 → i ≠ reg 14 → i ≠ reg 21 → d.reg i = c.reg i := by
  let addr := ((g.countBase + g.owner : ℕ) : Word W)
  have val : addr.val = g.countBase + g.owner := by
    exact Nat.mod_eq_of_lt fit
  let one := c.put (pc .zero) (reg 3) 1
  let zero := one.put (pc .countAddr) (reg 21) 0
  let load := zero.put (pc .readCount) (reg 14) addr
  let offset := load.put (pc .rowOffset) (reg 14) (m addr.val)
  let start := offset.put (pc .rowStart) (reg 5) ((g.owner * g.rowStride : ℕ) : Word W)
  let d := start.put (pc .test) (reg 5) (g.row : Word W)
  have s₀ : M.program.step c = .localStep one := control_step link .one hc
  have s₁ : M.program.step one = .localStep zero := control_step link .zero rfl
  have s₂ : M.program.step zero = .localStep load := by
    rw [control_step link .countAddr rfl]
    change CallAction.localStep (zero.put _ _ (zero.reg (reg 17) + zero.reg (reg 18))) = _
    simp [load, zero, one, Config.put, inputs.counts, inputs.owner, addr]
  have s₃ : M.program.step load = .read addr (fun v => load.put (pc .rowOffset) (reg 14) v) := by
    rw [control_step link .readCount rfl]
    change CallAction.read (load.reg (reg 14)) _ = _
    rw [Config.put_same]
  have s₄ : M.program.step offset = .localStep start := by
    rw [control_step link .rowOffset rfl]
    change CallAction.localStep (offset.put _ _ (offset.reg (reg 18) * offset.reg (reg 20))) = _
    simp [start, offset, load, zero, one, Config.put, inputs.owner, inputs.rowStride]
  have s₅ : M.program.step start = .localStep d := by
    rw [control_step link .rowStart rfl]
    change CallAction.localStep (start.put _ _ (start.reg (reg 19) + start.reg (reg 5))) = _
    simp [d, start, offset, load, zero, one, Config.put, inputs.rows, Args.row]
  have path := ReadPrefix.tick (m := m) s₀ (ReadPrefix.tick s₁ (ReadPrefix.tick s₂
    (ReadPrefix.read addr s₃ (ReadPrefix.tick s₄ (ReadPrefix.tick s₅ (ReadPrefix.nil _))))))
  have keep (i : Fin r) (h₃ : i ≠ reg 3) (h₅ : i ≠ reg 5) (h₁₄ : i ≠ reg 14) (h₂₁ : i ≠ reg 21) :
      d.reg i = c.reg i := by
    simp [d, start, offset, load, zero, one, Config.put, Function.update_of_ne, h₃, h₅, h₁₄, h₂₁]
  have same (j : Fin 22) (h₃ : j ≠ 3) (h₅ : j ≠ 5) (h₁₄ : j ≠ 14) (h₂₁ : j ≠ 21) :
      d.reg (reg j) = c.reg (reg j) :=
    keep _ (reg.injective.ne h₃) (reg.injective.ne h₅) (reg.injective.ne h₁₄) (reg.injective.ne h₂₁)
  have params : Inputs g reg d := by
    constructor <;> rw [same _ (by decide) (by decide) (by decide) (by decide)]
    exacts
      [inputs.term, inputs.termStride, inputs.layout, inputs.selectors, inputs.scratch,
       inputs.stride, inputs.counts, inputs.owner, inputs.rows, inputs.rowStride]
  refine ⟨d, ?_, rfl, ?_, Config.put_same .., ⟨params, ?_, ?_⟩, rfl, rfl, keep⟩
  · intro fuel bs
    simpa only [setupEvents, List.nil_append, val] using ReadPrefix.execute path fuel bs
  · simp [d, start, offset, Config.put, val]
  · simp [d, start, offset, load, zero, one, Config.put]
  · simp [d, start, offset, load, zero, Config.put]

/-- One local branch tests the remaining count, including a zero-length row. -/
theorem test_run (link : ControlLinked M pc reg width guess done) (m : Memory W) (g : Args W)
    (c : Config W p r) (hc : c.pc = pc .test) (ready : Ready g reg c)
    (n : ℕ) (count : c.reg (reg 14) = (n : Word W)) (fit : n < 2 ^ W) :
    ∃ d, Prefix M m c d [] [.tick] ∧ d.pc = (if n = 0 then done else width) ∧
      d.reg = c.reg ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  let d := {c with pc := if n = 0 then done else width}
  have eqzero : (n : Word W) = 0 ↔ n = 0 := by
    constructor
    · intro hz
      have h := congrArg Fin.val hz
      change n % (2 ^ W) = 0 at h
      rwa [Nat.mod_eq_of_lt fit] at h
    · rintro rfl
      rfl
  have step : M.program.step c = .localStep d := by
    rw [control_step link .test hc]
    change CallAction.localStep {c with pc := if c.reg (reg 14) = c.reg (reg 21) then done else width} = _
    simp only [d, count, ready.zero, eqzero]
  exact ⟨d, fun fuel bs => ReadPrefix.execute (ReadPrefix.tick step (ReadPrefix.nil _)) fuel bs,
    rfl, rfl, rfl, rfl⟩

/-- The two local back-edge instructions consume one row entry and advance
the ID pointer, preserving the field buffers and the loop's stable registers. -/
theorem advance_run (link : ControlLinked M pc reg width guess done) (m : Memory W) (g : Args W)
    (c : Config W p r) (hc : c.pc = pc .decrement) (ready : Ready g reg c) (rem ptr : ℕ)
    (count : c.reg (reg 14) = ((rem + 1 : ℕ) : Word W)) (pointer : c.reg (reg 5) = (ptr : Word W)) :
    ∃ d, Prefix M m c d [] [.tick, .tick] ∧ d.pc = pc .test ∧
      d.reg (reg 14) = (rem : Word W) ∧ d.reg (reg 5) = ((ptr + 1 : ℕ) : Word W) ∧
      Frame reg c d ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  let next := c.put (pc .advance) (reg 14) (rem : Word W)
  let d := next.put (pc .test) (reg 5) ((ptr + 1 : ℕ) : Word W)
  have s₀ : M.program.step c = .localStep next := by
    rw [control_step link .decrement hc]
    change CallAction.localStep (c.put _ _ (c.reg (reg 14) - c.reg (reg 3))) = _
    simp [next, count, ready.one]
  have s₁ : M.program.step next = .localStep d := by
    rw [control_step link .advance rfl]
    change CallAction.localStep (next.put _ _ (next.reg (reg 5) + next.reg (reg 3))) = _
    simp [d, next, Config.put, pointer, ready.one]
  exact ⟨d, fun fuel bs => ReadPrefix.execute
    (ReadPrefix.tick s₀ (ReadPrefix.tick s₁ (ReadPrefix.nil _))) fuel bs, rfl,
    by simp [d, next, Config.put], Config.put_same ..,
    (frame_put c _ 14 _ (by decide)).trans (frame_put next _ 5 _ (by decide)), rfl, rfl⟩

end PairSimulation.ShrinkHiddenGuess

end VPVNP
end Computability
end OAI
