import OAI.Computability.VPVNP.PairVertexLevelBounds
import OAI.Computability.VPVNP.PairSimulationPrivateSlices

/-! # Hosted initialization of the descending traversal-level scan -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexLevel

open BurstRAM BurstRAM.PrivateRAM TraversalControllerInputs
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.tick ReadPrefix.read ReadPrefix.nil ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

variable {w p r : ℕ}

/-- Copy the popped row address, form the terminal header and read the first
level header, pitch, stride and number of levels. Start at the last level. -/
def boot (pc : Fin 24 → Fin p) (reg : Fin 14 ↪ Fin r) (src : Fin r) (next : Fin p) :
    Fin 24 → Instr w p r 11 :=
  ![.copy (reg 0) src (pc 1),
    .constant (reg 8) 1 (pc 2),
    .publicWord (reg 1) 2 (pc 3),
    .publicWord (reg 9) 7 (pc 4),
    .binary .shiftLeft (reg 9) (reg 8) (reg 9) (pc 5),
    .binary .mul (reg 9) (reg 9) (reg 9) (pc 6),
    .binary .add (reg 1) (reg 1) (reg 9) (pc 7),
    .constant (reg 9) 16 (pc 8),
    .binary .sub (reg 1) (reg 1) (reg 9) (pc 9),
    .binary .sub (reg 1) (reg 1) (reg 9) (pc 10),
    .binary .add (reg 9) (reg 1) (reg 9) (pc 11),
    .readExternal (reg 4) (reg 9) (pc 12),
    .constant (reg 9) 17 (pc 13),
    .binary .add (reg 9) (reg 1) (reg 9) (pc 14),
    .readExternal (reg 2) (reg 9) (pc 15),
    .constant (reg 9) 15 (pc 16),
    .binary .add (reg 9) (reg 1) (reg 9) (pc 17),
    .readExternal (reg 6) (reg 9) (pc 18),
    .binary .add (reg 9) (reg 1) (reg 8) (pc 19),
    .readExternal (reg 3) (reg 9) (pc 20),
    .binary .sub (reg 3) (reg 3) (reg 8) (pc 21),
    .binary .mul (reg 9) (reg 3) (reg 2) (pc 22),
    .binary .add (reg 4) (reg 4) (reg 9) (pc 23),
    .constant (reg 10) 14 next]

theorem resize_boot (pc : Fin 24 → Fin p) (reg : Fin 14 ↪ Fin r) (src : Fin r) (next : Fin p)
    (i : Fin 24) : (boot (w := 5) pc reg src next i).resize w = boot pc reg src next i := by
  fin_cases i <;> rfl

/-- The 24 locator-bootstrap events, including reads of the first level, level pitch, row
pitch, and level count in the terminal header. -/
def bootEvents (pub : Fin 11 → Word w) (m : Memory w) : List (Event w) :=
  let read (i : ℕ) := Event.read (terminalHead pub + (i : Word w)) (terminalField pub m i)
  List.replicate 11 .tick ++ [read 16, .tick, .tick, read 17, .tick, .tick, read 15,
    .tick, read 1, .tick, .tick, .tick, .tick]

theorem bootEvents_cost (pub : Fin 11 → Word w) (m : Memory w) :
    (bootEvents pub m).length = 24 ∧ countProbes (bootEvents pub m) = 4 ∧
    choiceBits (bootEvents pub m) = [] := ⟨rfl, rfl, rfl⟩

/-- The four header probes leave the shared memory unchanged. -/
theorem bootEvents_after (pub : Fin 11 → Word w) (m : Memory w) :
    after m (bootEvents pub m) = m := rfl

/-- Register and control state delivered by the locator bootstrap before the descending level
scan. -/
structure BootResult (pub : Fin 11 → Word w) (m : Memory w) (reg : Fin 14 ↪ Fin r)
    (src : Fin r) (next : Fin p) (c out : Config w p r) : Prop where
  pc : out.pc = next
  node : out.reg (reg 0) = c.reg src
  header : out.reg (reg 1) = terminalHead pub
  pitch : out.reg (reg 2) = terminalField pub m 17
  index : out.reg (reg 3) = terminalField pub m 1 - 1
  current : out.reg (reg 4) = terminalField pub m 16 +
    (terminalField pub m 1 - 1) * terminalField pub m 17
  stride : out.reg (reg 6) = terminalField pub m 15
  one : out.reg (reg 8) = 1
  offset14 : out.reg (reg 10) = 14
  outside : ∀ j, (∀ i, j ≠ reg i) → out.reg j = c.reg j
  privateMem : out.privateMem = c.privateMem
  persistent : out.persistent = c.persistent

variable {M : Machine w p r 11} {pc : Fin 24 → Fin p} {reg : Fin 14 ↪ Fin r}
variable {src : Fin r} {next : Fin p}

set_option maxHeartbeats 2000000 in
-- The complete trace normalizes register updates for all 24 linked instructions.
/-- All 24 instructions execute on the actual host, preserving private memory,
persistent state, and all registers outside the work bank. -/
theorem boot_run (linked : ∀ i, M.code (pc i) = boot pc reg src next i)
    (c : Config w p r) (hc : c.pc = pc 0) (m : Memory w) :
    ∃ out, BootResult M.publicData m reg src next c out ∧ ∀ fuel bs,
      execute M.program (fuel + 24) c m bs =
        (execute M.program fuel out m bs).map
          (fun rep => ⟨bootEvents M.publicData m ++ rep.events, rep.result⟩) := by
  let radix := BinaryOp.shiftLeft.eval 1 (M.publicData 7)
  let upper := M.publicData 2 + radix * radix
  let head := terminalHead M.publicData
  let field := terminalField M.publicData m
  let last := field 1 - 1
  let c1 := c.put (pc 1) (reg 0) (c.reg src)
  let c2 := c1.put (pc 2) (reg 8) 1
  let c3 := c2.put (pc 3) (reg 1) (M.publicData 2)
  let c4 := c3.put (pc 4) (reg 9) (M.publicData 7)
  let c5 := c4.put (pc 5) (reg 9) radix
  let c6 := c5.put (pc 6) (reg 9) (radix * radix)
  let c7 := c6.put (pc 7) (reg 1) upper
  let c8 := c7.put (pc 8) (reg 9) 16
  let c9 := c8.put (pc 9) (reg 1) (upper - 16)
  let c10 := c9.put (pc 10) (reg 1) head
  let c11 := c10.put (pc 11) (reg 9) (head + 16)
  let c12 := c11.put (pc 12) (reg 4) (field 16)
  let c13 := c12.put (pc 13) (reg 9) 17
  let c14 := c13.put (pc 14) (reg 9) (head + 17)
  let c15 := c14.put (pc 15) (reg 2) (field 17)
  let c16 := c15.put (pc 16) (reg 9) 15
  let c17 := c16.put (pc 17) (reg 9) (head + 15)
  let c18 := c17.put (pc 18) (reg 6) (field 15)
  let c19 := c18.put (pc 19) (reg 9) (head + 1)
  let c20 := c19.put (pc 20) (reg 3) (field 1)
  let c21 := c20.put (pc 21) (reg 3) last
  let c22 := c21.put (pc 22) (reg 9) (last * field 17)
  let c23 := c22.put (pc 23) (reg 4) (field 16 + last * field 17)
  let c24 := c23.put next (reg 10) 14
  have step (i : Fin 24) (d : Config w p r) (hd : d.pc = pc i) {act}
      (row : (boot pc reg src next i).run M.publicData d = act) : M.program.step d = act := by
    change (M.code d.pc).run M.publicData d = _
    rw [hd, linked]
    exact row
  have path : ReadPrefix M m c (bootEvents M.publicData m) c24 := by
    refine ReadPrefix.tick (d := c1) (step 0 c hc ?_) <|
      ReadPrefix.tick (d := c2) (step 1 c1 rfl ?_) <|
      ReadPrefix.tick (d := c3) (step 2 c2 rfl ?_) <|
      ReadPrefix.tick (d := c4) (step 3 c3 rfl ?_) <|
      ReadPrefix.tick (d := c5) (step 4 c4 rfl ?_) <|
      ReadPrefix.tick (d := c6) (step 5 c5 rfl ?_) <|
      ReadPrefix.tick (d := c7) (step 6 c6 rfl ?_) <|
      ReadPrefix.tick (d := c8) (step 7 c7 rfl ?_) <|
      ReadPrefix.tick (d := c9) (step 8 c8 rfl ?_) <|
      ReadPrefix.tick (d := c10) (step 9 c9 rfl ?_) <|
      ReadPrefix.tick (d := c11) (step 10 c10 rfl ?_) <|
      ReadPrefix.read (g := fun v => c11.put (pc 12) (reg 4) v) (head + 16) (step 11 c11 rfl ?_) <|
      ReadPrefix.tick (d := c13) (step 12 c12 rfl ?_) <|
      ReadPrefix.tick (d := c14) (step 13 c13 rfl ?_) <|
      ReadPrefix.read (g := fun v => c14.put (pc 15) (reg 2) v) (head + 17) (step 14 c14 rfl ?_) <|
      ReadPrefix.tick (d := c16) (step 15 c15 rfl ?_) <|
      ReadPrefix.tick (d := c17) (step 16 c16 rfl ?_) <|
      ReadPrefix.read (g := fun v => c17.put (pc 18) (reg 6) v) (head + 15) (step 17 c17 rfl ?_) <|
      ReadPrefix.tick (d := c19) (step 18 c18 rfl ?_) <|
      ReadPrefix.read (g := fun v => c19.put (pc 20) (reg 3) v) (head + 1) (step 19 c19 rfl ?_) <|
      ReadPrefix.tick (d := c21) (step 20 c20 rfl ?_) <|
      ReadPrefix.tick (d := c22) (step 21 c21 rfl ?_) <|
      ReadPrefix.tick (d := c23) (step 22 c22 rfl ?_) <|
      ReadPrefix.tick (d := c24) (step 23 c23 rfl ?_) <|
      ReadPrefix.nil _
    all_goals first | rfl | simp (config := { zetaDelta := true, decide := true })
      [boot, Instr.run, Config.put, reg.injective.eq_iff, BinaryOp.eval, terminalHead,
       sub_sub, show (16 : Word w) + 16 = 32 by ring]
  refine ⟨c24, ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩, ReadPrefix.execute path⟩
  all_goals first | intro j hj | skip
  all_goals simp (config := { zetaDelta := true, decide := true })
    [Config.put, reg.injective.eq_iff, Function.update_of_ne, *]

end PairSimulation.VertexLevel

end VPVNP
end Computability
end OAI
