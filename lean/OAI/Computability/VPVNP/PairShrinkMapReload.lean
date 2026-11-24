import OAI.Computability.VPVNP.PairVertexLocatedBody
import OAI.Computability.VPVNP.PairVertexSegmentChain

/-!
# Reloading the geometry and histogram heads before the shrinking maps

The DFS end register points to a private word containing the geometry head. The
histogram head is its eleventh field. This fixed prefix reads those two words from
the actual configuration before entering the grid and party map loop.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapReload

open BurstRAM BurstRAM.PrivateRAM NodeArguments.ChildScan VertexImage
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.tick ReadPrefix.nil ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

variable {p r w : ℕ}

/-- Four native instructions follow the private geometry pointer at the stack end and load
geometry word 11, the histogram base, into locator register 10. -/
def instruction (pc : Fin 4 → Fin p) (reg : Fin 14 ↪ Fin r) (stack : Fin r) (done : Fin p) :
    Fin 4 → Instr w p r 11 :=
  ![.loadPrivate (reg 9) stack (pc 1), .constant (reg 10) 11 (pc 2),
    .binary .add (reg 10) (reg 9) (reg 10) (pc 3), .loadPrivate (reg 10) (reg 10) done]

theorem resize_instruction (pc : Fin 4 → Fin p) (reg : Fin 14 ↪ Fin r)
    (stack : Fin r) (done : Fin p) (i : Fin 4) :
    (instruction (w := 5) pc reg stack done i).resize w = instruction pc reg stack done i := by
  fin_cases i <;> rfl

/-- The private reload leaves the packed owner and the cached hidden-field head intact. -/
theorem run {M : Machine w p r 11} {pc : Fin 4 → Fin p} {reg : Fin 14 ↪ Fin r}
    {stack : Fin r} {done : Fin p} (linked : ∀ i, M.code (pc i) = instruction pc reg stack done i)
    (c : Config w p r) (hc : c.pc = pc 0) (m : Memory w) :
    let G := c.privateMem (c.reg stack)
    ∃ out, Prefix M m c out [] (List.replicate 4 .tick) ∧ out.pc = done ∧
      out.reg (reg 9) = G ∧ out.reg (reg 10) = c.privateMem (G + 11) ∧
      (∀ j, j ≠ reg 9 → j ≠ reg 10 → out.reg j = c.reg j) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent := by
  intro G
  let a := c.put (pc 1) (reg 9) G
  let b := a.put (pc 2) (reg 10) 11
  let d := b.put (pc 3) (reg 10) (G + 11)
  let out := d.put done (reg 10) (c.privateMem (G + 11))
  have atRow (i : Fin 4) (q : Config w p r) (hp : q.pc = pc i) :
      M.program.step q = (instruction pc reg stack done i).run M.publicData q := by
    simp only [Machine.program, hp, linked]
  have s₀ : M.program.step c = .localStep a := atRow 0 c hc
  have s₁ : M.program.step a = .localStep b := atRow 1 a rfl
  have s₂ : M.program.step b = .localStep d := by
    rw [atRow 2 b rfl]
    change CallAction.localStep (b.put _ _ (b.reg (reg 9) + b.reg (reg 10))) = _
    simp [a, b, d, Config.put]
  have s₃ : M.program.step d = .localStep out := by
    rw [atRow 3 d rfl]
    change CallAction.localStep (d.put _ _ (d.privateMem (d.reg (reg 10)))) = _
    simp [a, b, d, out, Config.put]
  have pre : ReadPrefix M m c (List.replicate 4 .tick) out :=
    ReadPrefix.tick s₀ (ReadPrefix.tick s₁ (ReadPrefix.tick s₂
      (ReadPrefix.tick s₃ (ReadPrefix.nil _))))
  refine ⟨out, ReadPrefix.execute pre, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · simp [out, d, b, a, Config.put]
  · simp [out]
  · intro j h₉ h₁₀
    simp [out, d, b, a, Config.put, Function.update_of_ne h₉, Function.update_of_ne h₁₀]

/-- Install the four histogram-reload instructions ahead of a located resident map body, using
its locator registers and DFS stack-end register. -/
def setup (B : LocatedBody) : Segment where
  count := 4
  privateRegs := B.code.privateRegs
  entry := 0
  row pc dfs _ regs done := instruction pc (B.locator.trans regs) (dfs 6) done

/-- Geometry preparation and the installed map share their full register bank. -/
def body (B : LocatedBody) : LocatedBody where
  code := Segment.thenWith (setup B) B.code (Function.Embedding.refl _) (Function.Embedding.refl _)
  locator := B.locator

theorem links (B : LocatedBody) (M : Machine w p r 11)
    (pc : Fin (body B).code.count → Fin p) (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
    (regs : Fin B.code.privateRegs ↪ Fin r) (done : Fin p)
    (installed : ∀ i, M.code (pc i) = ((body B).code.row pc dfs saved regs done i).resize w) :
    (∀ i, M.code (Segment.leftPC (setup B) B.code pc i) =
      instruction (Segment.leftPC (setup B) B.code pc) (B.locator.trans regs) (dfs 6)
        (Segment.rightPC (setup B) B.code pc B.code.entry) i) ∧
    (∀ i, M.code (Segment.rightPC (setup B) B.code pc i) =
      (B.code.row (Segment.rightPC (setup B) B.code pc) dfs saved regs done i).resize w) := by
  obtain ⟨l, r⟩ := Segment.split_link (setup B) B.code (Function.Embedding.refl _)
    (Function.Embedding.refl _) pc dfs saved regs done M installed
  exact ⟨fun i => (l i).trans (resize_instruction ..), r⟩

end PairSimulation.ShrinkMapReload

end VPVNP
end Computability
end OAI
