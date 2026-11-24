import OAI.Computability.VPVNP.PairTraversalControllerFormula

/-!
# Native dispatcher for traversal table construction

Each reset entry loads the square base, radix exponent and persistent ordinal,
then computes the fixed operand formulas. Four comparisons dispatch to a role
write, a leaf header, a fiber translation, a phase reset or final acceptance.
All three workers return to the common successor-ordinal instruction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalController.Native

open BurstRAM BurstRAM.PrivateRAM CompressorRecords PrimedStackRAM PrimedInputRAM
open scoped Fin.CommRing

private abbrev nSetup := (RegisterSetup.lines formulas).length
private abbrev nRole := roleAlloc.role.length
private abbrev nLeaf := leafAlloc.leaf.length
private abbrev nFiber := fiberAlloc.fiber.length

/-- Total program-counter count for the traversal controller's prelude, setup, guard, three
worker blocks, and four exits. -/
abbrev P := 3 + (nSetup + (4 + (nRole + (nLeaf + (nFiber + 4)))))
private abbrev Address := Fin 3 ⊕ Fin nSetup ⊕ Fin 4 ⊕ Fin nRole ⊕ Fin nLeaf ⊕ Fin nFiber ⊕ Fin 4

private def join {X : Type} {a b : ℕ} (e : X ≃ Fin b) : Fin a ⊕ X ≃ Fin (a + b) :=
  ((Equiv.refl _).sumCongr e).trans finSumFinEquiv

private def book : Address ≃ Fin P := join (join (join (join (join (join (Equiv.refl _))))))

/-- Place the traversal controller's three prelude instructions at their physical addresses. -/
def preludePC (i : Fin 3) : Fin P := book (.inl i)
/-- Program counters of the guard that chooses the current traversal worker or an exit. -/
def guardPC (i : Fin 4) : Fin P := book (.inr (.inr (.inl i)))

/-- Place a register-setup instruction by its ordinal, falling through to the first guard when
setup is complete. -/
def setupPC (n : ℕ) : Fin P :=
  if h : n < nSetup then book (.inr (.inl ⟨n, h⟩)) else guardPC 0

/-- Physical instruction address in the role-tag writer's linked worker block. -/
def rolePC (i : roleAlloc.role.Label) : Fin P :=
  book (.inr (.inr (.inr (.inl (roleAlloc.role.labels i)))))

/-- Physical instruction address in the leaf-row writer's linked worker block. -/
def leafPC (i : leafAlloc.leaf.Label) : Fin P :=
  book (.inr (.inr (.inr (.inr (.inl (leafAlloc.leaf.labels i))))))

/-- Physical instruction address in the worker that writes a site's selected placement fiber. -/
def fiberPC (i : fiberAlloc.fiber.Label) : Fin P :=
  book (.inr (.inr (.inr (.inr (.inr (.inl (fiberAlloc.fiber.labels i)))))))

private def exitPC (i : Fin 4) : Fin P := book (.inr (.inr (.inr (.inr (.inr (.inr i))))))

/-- Exit returning the controller state for the next active site. -/
def nextPC := exitPC 0
/-- Exit that resets the site ordinal and advances to the next phase-level. -/
def resetPC := exitPC 1
/-- Accepting exit of the completed traversal controller. -/
def acceptPC := exitPC 2
/-- Rejection exit reserved in the traversal controller's instruction table. -/
def rejectPC := exitPC 3

private def preludeCode {w : ℕ} : Fin 3 → Instr w P R 11
  | 0 => .publicWord (extra 7) 2 (preludePC 1)
  | 1 => .publicWord (extra 8) 7 (preludePC 2)
  | 2 => .stateWord (extra 9) (setupPC 0)

private def guardCode {w : ℕ} : Fin 4 → Instr w P R 11
  | 0 => .jumpLt (value 1) (value 3) (guardPC 1) acceptPC
  | 1 => .jumpLt (value 0) (value 4) (guardPC 2) resetPC
  | 2 => .jumpLt (value 1) (value 2) (rolePC roleAlloc.role.entry) (guardPC 3)
  | 3 => .jumpEq (value 5) (value 6) (leafPC leafAlloc.leaf.entry) (fiberPC fiberAlloc.fiber.entry)

private def exitCode {w : ℕ} : Fin 4 → Instr w P R 11
  | 0 => .returnState (value 7)
  | 1 => .returnState (value 8)
  | 2 => .accept
  | 3 => .reject

private def blockText (f : Flow R 11) (pc : f.Label → Fin P) (i : Fin f.length) : Instr 2 P R 11 :=
  (((f.code (f.labels.symm i)).map (fun l => (l.map pc).getD nextPC)).emit rejectPC)

private def text : Address → Instr 2 P R 11
  | .inl i => preludeCode i
  | .inr (.inl i) => RegisterSetup.instruction vm inputs
      (RegisterSetup.lines formulas)[i.val] (setupPC (i.val + 1))
  | .inr (.inr (.inl i)) => guardCode i
  | .inr (.inr (.inr (.inl i))) => blockText roleAlloc.role rolePC i
  | .inr (.inr (.inr (.inr (.inl i)))) => blockText leafAlloc.leaf leafPC i
  | .inr (.inr (.inr (.inr (.inr (.inl i))))) => blockText fiberAlloc.fiber fiberPC i
  | .inr (.inr (.inr (.inr (.inr (.inr i))))) => exitCode i

/-- One finite template for all inputs, word widths, layer counts and term choices. -/
def table : Template P R 11 where
  literalWidth := 2
  entry := preludePC 0
  code i := text (book.symm i)

variable {w : ℕ} (pub : Fin 11 → Word w)

/-- Instantiate the fixed traversal controller template at the supplied word width and eleven
public operands. -/
def machine := table.instantiate w pub

private theorem atAddress (a : Address) : (machine pub).code (book a) = (text a).resize w := by
  simp only [machine, Template.instantiate, table, Equiv.symm_apply_apply]

theorem setup_end : setupPC (RegisterSetup.lines formulas).length = guardPC 0 := by
  simp only [setupPC, nSetup, lt_self_iff_false, ↓reduceDIte]

theorem linked_setup :
    RegisterSetup.Linked vm inputs (machine pub) setupPC (RegisterSetup.lines formulas) := by
  intro i
  rw [setupPC, dite_eq_left i.isLt, atAddress]
  exact RegisterSetup.resize_instruction vm inputs _ _

theorem linked_role : Flow.Linked (machine pub) roleAlloc.role rolePC nextPC rejectPC := by
  constructor
  intro i
  simp only [rolePC, atAddress, text, blockText, Equiv.symm_apply_apply]

theorem linked_leaf : Flow.Linked (machine pub) leafAlloc.leaf leafPC nextPC rejectPC := by
  constructor
  intro i
  simp only [leafPC, atAddress, text, blockText, Equiv.symm_apply_apply]

theorem linked_fiber : Flow.Linked (machine pub) fiberAlloc.fiber fiberPC nextPC rejectPC := by
  constructor
  intro i
  simp only [fiberPC, atAddress, text, blockText, Equiv.symm_apply_apply]

theorem code_next : (machine pub).code nextPC = .returnState (value 7) := atAddress pub _
theorem code_reset : (machine pub).code resetPC = .returnState (value 8) := atAddress pub _
theorem code_accept : (machine pub).code acceptPC = .accept := atAddress pub _
theorem code_reject : (machine pub).code rejectPC = .reject := atAddress pub _

private theorem code_pre (i : Fin 3) : (machine pub).code (preludePC i) = preludeCode i := by
  rw [preludePC, atAddress]
  fin_cases i <;> rfl

private theorem code_guard (i : Fin 4) : (machine pub).code (guardPC i) = guardCode i := by
  rw [guardPC, atAddress]
  fin_cases i <;> rfl

/-- Configuration received by the formula evaluator immediately after reset. -/
def loaded (s : Word w) : Config w P R :=
  ⟨setupPC 0, s, Function.update (Function.update (Function.update (fun _ => 0)
    (extra 7) (pub 2)) (extra 8) (pub 7)) (extra 9) s, fun _ => 0⟩

theorem loaded_inputs (s : Word w) (j : Fin 5) :
    (loaded pub s).reg (inputs j.castSucc) = recipePub pub j := by
  fin_cases j <;> simp (config := { decide := true }) [loaded, inputs, extra, recipePub]

theorem loaded_state (s : Word w) : (loaded pub s).reg (inputs (Fin.last 5)) = s := by
  simp (config := { decide := true }) [loaded, inputs]

/-- The prelude takes exactly three ticks and reaches the first setup instruction
with its public and persistent inputs in registers. -/
theorem enter (s : Word w) (m : Memory w) (bits : List Bool) (fuel : ℕ) :
    let M := machine pub
    execute M.program (fuel + 3) (M.program.start s) m bits =
      (execute M.program fuel (loaded pub s) m bits).map
        (Flow.prependEvents [.tick, .tick, .tick]) := by
  change execute (machine pub).program (fuel + 3)
    ⟨preludePC 0, s, fun _ => 0, fun _ => 0⟩ m bits = _
  simp only [execute, Machine.program, code_pre, preludeCode, Instr.run, Config.put, Option.map_map]
  rfl

/-- Destination selected by the native tests after the formula evaluator. -/
inductive Route where
  | accept | reset | role | leaf | fiber
  deriving DecidableEq

/-- Choose acceptance, phase reset, or the role, leaf, or fiber worker from the decoded
phase-level and site bounds. -/
def route (rs : Regs w R) : Route :=
  if rs (value 1) < rs (value 3) then
    if rs (value 0) < rs (value 4) then
      if rs (value 1) < rs (value 2) then .role
      else if rs (value 5) = rs (value 6) then .leaf else .fiber
    else .reset
  else .accept

/-- Program counter entered after the guard has determined the traversal route. -/
def Route.pc : Route → Fin P
  | .accept => acceptPC
  | .reset => resetPC
  | .role => rolePC roleAlloc.role.entry
  | .leaf => leafPC leafAlloc.leaf.entry
  | .fiber => fiberPC fiberAlloc.fiber.entry

/-- Number of guard ticks before reaching the selected worker or exit, ranging from one at
acceptance to four at a descriptor worker. -/
def Route.ticks : Route → ℕ
  | .accept => 1
  | .reset => 2
  | .role => 3
  | .leaf | .fiber => 4

/-- Every guard contributes one tick and leaves the operand bank and both
memories available to the selected worker or exit instruction. -/
theorem dispatch (state : Word w) (rs : Regs w R) (priv : Word w → Word w) (m : Memory w)
    (bits : List Bool) (fuel : ℕ) :
    let M := machine pub
    let dest := route rs
    execute M.program (fuel + dest.ticks) ⟨guardPC 0, state, rs, priv⟩ m bits =
      (execute M.program fuel ⟨dest.pc, state, rs, priv⟩ m bits).map
        (Flow.prependEvents (List.replicate dest.ticks .tick)) := by
  dsimp only
  unfold route
  split <;> rename_i h₀
  · split <;> rename_i h₁
    · split <;> rename_i h₂
      · simp only [Route.ticks, Route.pc, execute, Machine.program, code_guard, guardCode,
          Instr.run, h₀, h₁, h₂, ↓reduceIte, Option.map_map]
        rfl
      · split <;> rename_i h₃ <;>
          simp only [Route.ticks, Route.pc, execute, Machine.program, code_guard, guardCode,
            Instr.run, h₀, h₁, h₂, h₃, ↓reduceIte, Option.map_map] <;> rfl
    · simp only [Route.ticks, Route.pc, execute, Machine.program, code_guard, guardCode,
        Instr.run, h₀, h₁, ↓reduceIte, Option.map_map]
      rfl
  · simp only [Route.ticks, Route.pc, execute, Machine.program, code_guard, guardCode,
      Instr.run, h₀, ↓reduceIte]
    rfl

end PairSimulation.TraversalController.Native

end VPVNP
end Computability
end OAI
