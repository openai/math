import OAI.Computability.VPVNP.LiveStageOperands
import Mathlib.Tactic.FinCases

/-!
# A public cursor bound for a native stage

Three local instructions compare the persistent cursor with a public capacity.
Below that capacity the original table runs. At or above it the stage accepts,
so the enclosing stage linker can hand control to the next table.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderBounded

open BurstRAM BurstRAM.PrivateRAM

variable {p r k w : ℕ}

private def regs (r : ℕ) : Fin r ↪ Fin (r+2) := ⟨Fin.castAdd 2, Fin.castAdd_injective r 2⟩

private def cursorReg (r : ℕ) : Fin (r+2) := (0 : Fin 2).natAdd r
private def boundReg (r : ℕ) : Fin (r+2) := (1 : Fin 2).natAdd r

private def pre (p : ℕ) (i : Fin 4) := i.castAdd p
private def body (i : Fin p) := i.natAdd 4

/-- Shift only the jump destinations of a native instruction. -/
private def shift : Instr w p r k → Instr w (4+p) r k
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

private def guardCode (entry : Fin p) : Fin 4 → Instr w (4+p) (r+2) (k+1)
  | 0 => .stateWord (cursorReg r) (pre p 1)
  | 1 => .publicWord (boundReg r) (Fin.last k) (pre p 2)
  | 2 => .jumpLt (cursorReg r) (boundReg r) (body entry) (pre p 3)
  | 3 => .accept

/-- Wrap a worker in a public cursor-bound check that accepts when its capacity is reached. -/
def bounded (T : Template p r k) : Template (4+p) (r+2) (k+1) where
  literalWidth := T.literalWidth
  entry := pre p 0
  code := Fin.addCases (guardCode T.entry) (fun j => shift ((wide T).code j))

/-- Append the stage's capacity word to the worker's original public operand bank. -/
def publicData (pub : Fin k → Word w) (bound : Word w) : Fin (k+1) → Word w := Fin.snoc pub bound

variable (T : Template p r k) (pub : Fin k → Word w) (bound : Word w)

/-- Instantiate the cursor-bounded worker on its original operands and supplied capacity. -/
abbrev machine := (bounded T).instantiate w (publicData pub bound)

private theorem code_pre (j : Fin 4) : (machine T pub bound).code (pre p j) = guardCode T.entry j := by
  simp only [machine, bounded, pre, Template.instantiate, Fin.addCases_left]
  fin_cases j <;> rfl

private theorem code_body (j : Fin p) : (machine T pub bound).code (body j) =
    shift (((wide T).instantiate w (publicData pub bound)).code j) := by
  simp only [machine, bounded, body, Template.instantiate, Fin.addCases_right]
  cases (wide T).code j <;> rfl

private def embed (c : Config w p r) : Config w (4+p) r := ⟨body c.pc, c.persistent, c.reg, c.privateMem⟩

private def embedAction : CallAction w (Config w p r) → CallAction w (Config w (4+p) r)
  | .localStep c => .localStep (embed c)
  | .branch q => .branch (embed ∘ q)
  | .read a q => .read a (embed ∘ q)
  | .write a v c => .write a v (embed c)
  | .finish s => .finish s
  | .reject => .reject

private theorem step_body (c : Config w p (r+2)) :
    (machine T pub bound).program.step (embed c) =
      embedAction (((wide T).instantiate w (publicData pub bound)).program.step c) := by
  change ((machine T pub bound).code (body c.pc)).run (publicData pub bound) (embed c) = _
  rw [code_body]
  change (shift _).run _ _ = embedAction ((((wide T).instantiate w (publicData pub bound)).code c.pc).run _ c)
  cases ((wide T).instantiate w (publicData pub bound)).code c.pc <;>
    simp only [shift, Instr.run, embedAction, embed, Config.put, Config.store, Function.comp_def]
  all_goals first | rfl | (simp only [apply_ite body] <;> rfl)

private theorem execute_body (fuel : ℕ) (c : Config w p (r+2)) (m : Memory w) (bits : List Bool) :
    execute (machine T pub bound).program fuel (embed c) m bits =
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

private def bootConfig (pc : Fin (4+p)) (st bound : Word w) : Config w (4+p) (r+2) :=
  ⟨pc, st, bootRegs st bound, fun _ => 0⟩

private theorem cursor_ne_bound : cursorReg r ≠ boundReg r := by
  intro he
  have := congrArg Fin.val he
  simp [cursorReg, boundReg] at this

private theorem boot_run (fuel : ℕ) (st : Word w) (m : Memory w) (bits : List Bool) :
    let P := (machine T pub bound).program
    execute P (fuel+3) (P.start st) m bits =
      (execute P fuel (bootConfig (if st < bound then body T.entry else pre p 3) st bound) m bits).map
        (fun rep => ⟨.tick :: .tick :: .tick :: rep.events, rep.result⟩) := by
  dsimp only
  have hpub : (machine T pub bound).publicData (Fin.last k) = bound := by simp [machine, Template.instantiate, publicData]
  change execute _ (fuel+3) (Config.mk (pre p 0) st (fun _ => 0) (fun _ => 0)) _ _ = _
  simp only [execute, Machine.program, code_pre, guardCode, Instr.run, Config.put, hpub,
    Function.update_of_ne cursor_ne_bound, Function.update_self, Option.map_map]
  rfl

/-- The only overhead on an active call is three ticks. The original choices,
probes, result, and remaining fuel have their exact native semantics. -/
theorem execute_active (fuel : ℕ) (st : Word w) (hlt : st < bound) (m : Memory w) (bits : List Bool) :
    let P := (machine T pub bound).program
    let S := (T.instantiate w pub).program
    execute P (fuel+3) (P.start st) m bits = (execute S fuel (S.start st) m bits).map
      (fun rep => ⟨.tick :: .tick :: .tick :: rep.events, rep.result⟩) := by
  dsimp only
  rw [boot_run, ite_eq_left hlt]
  let c : Config w p (r+2) := ⟨T.entry, st, bootRegs st bound, fun _ => 0⟩
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

/-- At the capacity the unique successful input is the empty choice string. -/
theorem execute_closed (fuel : ℕ) (st : Word w) (hle : bound ≤ st) (m : Memory w) (bits : List Bool) :
    let P := (machine T pub bound).program
    execute P (fuel+4) (P.start st) m bits =
      if bits = [] then some ⟨[.tick,.tick,.tick], none⟩ else none := by
  dsimp only
  rw [show fuel+4 = (fuel+1)+3 by omega, boot_run, ite_eq_right (not_lt.mpr hle)]
  cases bits <;> simp [execute, Machine.program, bootConfig, code_pre, guardCode, Instr.run]

end LiveHeaderBounded

end VPVNP
end Computability
end OAI
