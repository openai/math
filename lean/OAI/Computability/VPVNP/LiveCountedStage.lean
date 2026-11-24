import OAI.Computability.VPVNP.LiveStageOperands
import OAI.Computability.VPVNP.RAMRecords
import Mathlib.Tactic.FinCases

/-!
# A native counted stage with a public or memory-resident bound

The guard reads the last public word as either the capacity or its external address.
Below that capacity the original table runs. At or above it the stage accepts,
so the enclosing stage linker can hand control to the next table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveCountedStage

open BurstRAM BurstRAM.PrivateRAM

variable {p r k w : ℕ}

private def regs (r : ℕ) : Fin r ↪ Fin (r+2) := ⟨Fin.castAdd 2, Fin.castAdd_injective r 2⟩

private def cursorReg (r : ℕ) : Fin (r+2) := (0 : Fin 2).natAdd r
private def boundReg (r : ℕ) : Fin (r+2) := (1 : Fin 2).natAdd r

private def pre (p : ℕ) (i : Fin 5) := i.castAdd p
private def body (i : Fin p) := i.natAdd 5

/-- Shift only the jump destinations of a native instruction. -/
private def shift : Instr w p r k → Instr w (5+p) r k
  | .constant a v j => .constant a v (body j)
  | .publicWord a x j => .publicWord a x (body j)
  | .stateWord a j => .stateWord a (body j)
  | .copy a b j => .copy a b (body j)
  | .binary op a b c j => .binary op a b c (body j)
  | .loadPrivate a b j => .loadPrivate a b (body j)
  | .storePrivate a b j => .storePrivate a b (body j)
  | .jumpEq a b yes no => .jumpEq a b (body yes) (body no)
  | .jumpLt a b yes no => .jumpLt a b (body yes) (body no)
  | .choose yes no => .choose (body yes) (body no)
  | .readExternal a b j => .readExternal a b (body j)
  | .writeExternal a b j => .writeExternal a b (body j)
  | .returnState a => .returnState a
  | .accept => .accept
  | .reject => .reject

private def wide (T : Template p r k) := LiveStageLink.widen T (regs r) Fin.castSucc

private def guardCode (indirect : Bool) (entry : Fin p) : Fin 5 → Instr w (5+p) (r+2) (k+1)
  | 0 => .stateWord (cursorReg r) (pre p 1)
  | 1 => .publicWord (boundReg r) (Fin.last k) (pre p 2)
  | 2 => if indirect then .readExternal (boundReg r) (boundReg r) (pre p 3)
    else .copy (boundReg r) (boundReg r) (pre p 3)
  | 3 => .jumpLt (cursorReg r) (boundReg r) (body entry) (pre p 4)
  | 4 => .accept

/-- Guard the original table using a direct word or an external memory cell. -/
def counted (T : Template p r k) (indirect : Bool) : Template (5+p) (r+2) (k+1) where
  literalWidth := T.literalWidth
  entry := pre p 0
  code := Fin.addCases (guardCode indirect T.entry) (fun j => shift ((wide T).code j))

/-- Append the stage's bound or bound address as the final public operand of its worker. -/
def publicData (pub : Fin k → Word w) (bound : Word w) : Fin (k+1) → Word w := Fin.snoc pub bound

variable (T : Template p r k) (indirect : Bool) (pub : Fin k → Word w) (bound : Word w)

/-- Instantiate the counted wrapper and underlying worker with their public operands and the
selected bound mode. -/
abbrev machine := (counted T indirect).instantiate w (publicData pub bound)

private theorem code_pre (j : Fin 5) : (machine T indirect pub bound).code (pre p j) = guardCode indirect T.entry j := by
  simp only [machine, counted, pre, Template.instantiate, Fin.addCases_left]
  fin_cases j <;> cases indirect <;> rfl

private theorem code_body (j : Fin p) : (machine T indirect pub bound).code (body j) =
    shift (((wide T).instantiate w (publicData pub bound)).code j) := by
  simp only [machine, counted, body, Template.instantiate, Fin.addCases_right]
  cases (wide T).code j <;> rfl

private def embed (c : Config w p r) : Config w (5+p) r := ⟨body c.pc, c.persistent, c.reg, c.privateMem⟩

private def embedAction : CallAction w (Config w p r) → CallAction w (Config w (5+p) r)
  | .localStep c => .localStep (embed c)
  | .branch q => .branch (embed ∘ q)
  | .read a q => .read a (embed ∘ q)
  | .write a v c => .write a v (embed c)
  | .finish s => .finish s
  | .reject => .reject

private theorem step_body (c : Config w p (r+2)) :
    (machine T indirect pub bound).program.step (embed c) =
      embedAction (((wide T).instantiate w (publicData pub bound)).program.step c) := by
  change ((machine T indirect pub bound).code (body c.pc)).run (publicData pub bound) (embed c) = _
  rw [code_body]
  change (shift _).run _ _ = embedAction ((((wide T).instantiate w (publicData pub bound)).code c.pc).run _ c)
  cases ((wide T).instantiate w (publicData pub bound)).code c.pc <;>
    simp only [shift, Instr.run, embedAction, embed, Config.put, Config.store, Function.comp_def]
  all_goals first | rfl | (simp only [apply_ite body] <;> rfl)

private theorem execute_body (fuel : ℕ) (c : Config w p (r+2)) (m : Memory w) (bits : List Bool) :
    execute (machine T indirect pub bound).program fuel (embed c) m bits =
      execute ((wide T).instantiate w (publicData pub bound)).program fuel c m bits := by
  induction fuel generalizing c m bits with
  | zero => rfl
  | succ f ih =>
    rw [execute, step_body, execute]
    cases ((wide T).instantiate w (publicData pub bound)).program.step c <;>
      simp only [embedAction, Function.comp_apply]
    all_goals first | rfl | (rw [ih]) | (cases bits <;> simp [ih])

private def bootRegs (st bound : Word w) : Fin (r+2) → Word w :=
  Function.update (Function.update (fun _ => 0) (cursorReg r) st) (boundReg r) bound

private def bootConfig (pc : Fin (5+p)) (st bound : Word w) : Config w (5+p) (r+2) :=
  ⟨pc, st, bootRegs st bound, fun _ => 0⟩

private theorem cursor_ne_bound : cursorReg r ≠ boundReg r := by
  intro he
  have := congrArg Fin.val he
  simp [cursorReg, boundReg] at this

/-- Effective stop cursor, as it is read at the start of the current call. -/
def limit (indirect : Bool) (operand : Word w) (m : Memory w) : Word w :=
  if indirect then m operand.val else operand

/-- The guard log records an actual external read precisely for an indirect limit. -/
def guardEvents (indirect : Bool) (operand : Word w) (m : Memory w) : List (Event w) :=
  [.tick, .tick, if indirect then .read operand (m operand.val) else .tick, .tick]

/-- Prepend the direct or indirect bound check's events to a worker report while retaining its
return state. -/
def prefixReport (indirect : Bool) (operand : Word w) (m : Memory w) (rep : Report w) : Report w :=
  ⟨guardEvents indirect operand m ++ rep.events, rep.result⟩

@[simp] theorem guardEvents_length (indirect : Bool) (operand : Word w) (m : Memory w) :
    (guardEvents indirect operand m).length = 4 := rfl

@[simp] theorem prefixReport_after (indirect : Bool) (operand : Word w) (m : Memory w)
    (rep : Report w) : after m (prefixReport indirect operand m rep).events = after m rep.events := by
  cases indirect <;> rfl

@[simp] theorem prefixReport_choices (indirect : Bool) (operand : Word w) (m : Memory w)
    (rep : Report w) : choiceBits (prefixReport indirect operand m rep).events = choiceBits rep.events := by
  cases indirect <;> rfl

@[simp] theorem prefixReport_result (indirect : Bool) (operand : Word w) (m : Memory w)
    (rep : Report w) : (prefixReport indirect operand m rep).result = rep.result := rfl

@[simp] theorem prefixReport_probes (indirect : Bool) (operand : Word w) (m : Memory w)
    (rep : Report w) : (prefixReport indirect operand m rep).probes =
      (if indirect then 1 else 0) + rep.probes := by
  cases indirect <;> simp [prefixReport, guardEvents, Report.probes, countProbes]

private theorem boot_run (fuel : ℕ) (st : Word w) (m : Memory w) (bits : List Bool) :
    let P := (machine T indirect pub bound).program
    let b := limit indirect bound m
    execute P (fuel+4) (P.start st) m bits =
      (execute P fuel (bootConfig (if st < b then body T.entry else pre p 4) st b) m bits).map
        (prefixReport indirect bound m) := by
  dsimp only
  have hpub : (machine T indirect pub bound).publicData (Fin.last k) = bound := by
    simp [machine, Template.instantiate, publicData]
  change execute _ (fuel+4) (Config.mk (pre p 0) st (fun _ => 0) (fun _ => 0)) _ _ = _
  cases indirect <;>
    simp only [execute, Machine.program, code_pre, guardCode, Instr.run, Config.put, hpub,
      Bool.false_eq_true, ite_false, ite_true, Function.update_of_ne cursor_ne_bound,
      Function.update_self, Function.update_idem, Option.map_map, limit]
  all_goals rfl

/-- Four guard instructions precede the original call, with exact remaining fuel,
branch stream, memory effects, and returned word. -/
theorem execute_active (fuel : ℕ) (st : Word w) (m : Memory w)
    (hlt : st < limit indirect bound m) (bits : List Bool) :
    let P := (machine T indirect pub bound).program
    let S := (T.instantiate w pub).program
    execute P (fuel+4) (P.start st) m bits = (execute S fuel (S.start st) m bits).map
      (prefixReport indirect bound m) := by
  dsimp only
  rw [boot_run, ite_eq_left hlt]
  let c : Config w p (r+2) := ⟨T.entry, st, bootRegs st (limit indirect bound m), fun _ => 0⟩
  change (execute _ fuel (embed c) m bits).map _ = _
  rw [execute_body, wide, LiveStageLink.execute_widen]
  have hpub : publicData pub bound ∘ Fin.castSucc = pub := by funext j; simp [publicData]
  rw [hpub]
  have hcfg : LiveStageLink.restrictConfig (regs r) c = (T.instantiate w pub).program.start st := by
    change Config.mk _ _ _ _ = Config.mk _ _ _ _
    congr 1
    funext j
    have h₀ : (regs r) j ≠ cursorReg r := by
      intro he; have hv := congrArg Fin.val he; simp [regs, cursorReg] at hv; omega
    have h₁ : (regs r) j ≠ boundReg r := by
      intro he; have hv := congrArg Fin.val he; simp [regs, boundReg] at hv; omega
    simp [c, bootRegs, Function.comp_apply, h₀, h₁]
  rw [hcfg]

/-- At and beyond the limit, including an initial limit of zero, the wrapper
accepts the empty choice stream and rejects every nonempty stream. -/
theorem execute_closed (fuel : ℕ) (st : Word w) (m : Memory w)
    (hle : limit indirect bound m ≤ st) (bits : List Bool) :
    let P := (machine T indirect pub bound).program
    execute P (fuel+5) (P.start st) m bits =
      if bits = [] then some ⟨guardEvents indirect bound m, none⟩ else none := by
  dsimp only
  rw [show fuel+5 = (fuel+1)+4 by omega, boot_run, ite_eq_right (not_lt.mpr hle)]
  cases bits <;> simp [execute, Machine.program, bootConfig, code_pre, guardCode, Instr.run, prefixReport]

end LiveCountedStage

end VPVNP
end Computability
end OAI
