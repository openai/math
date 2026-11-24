import OAI.Computability.VPVNP.LiveStageLink
import OAI.Computability.VPVNP.RAMChain

/-!
# Relocating the operands of a native component template

The live stage linker uses one shared register and public-word format. This
embedding allows arbitrary finite component tables, including their private
loads, stores and jumps, to participate in that format. No extra instruction,
probe or choice is introduced by operand relocation.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveStageLink

open BurstRAM BurstRAM.PrivateRAM

variable {r k r' k' p w : ℕ}

/-- Relabel each native operand while keeping jump targets and literal words fixed. -/
def relocate (ρ : Fin r → Fin r') (π : Fin k → Fin k') : Instr w p r k → Instr w p r' k'
  | .constant a v j => .constant (ρ a) v j
  | .publicWord a i j => .publicWord (ρ a) (π i) j
  | .stateWord a j => .stateWord (ρ a) j
  | .copy a b j => .copy (ρ a) (ρ b) j
  | .binary op a b c j => .binary op (ρ a) (ρ b) (ρ c) j
  | .loadPrivate a b j => .loadPrivate (ρ a) (ρ b) j
  | .storePrivate a b j => .storePrivate (ρ a) (ρ b) j
  | .jumpEq a b y n => .jumpEq (ρ a) (ρ b) y n
  | .jumpLt a b y n => .jumpLt (ρ a) (ρ b) y n
  | .choose y n => .choose y n
  | .readExternal a b j => .readExternal (ρ a) (ρ b) j
  | .writeExternal a b j => .writeExternal (ρ a) (ρ b) j
  | .returnState a => .returnState (ρ a)
  | .accept => .accept
  | .reject => .reject

/-- Relocate a template's registers and public operand references, preserving its entry and
instruction positions. -/
def widen (T : Template p r k) (ρ : Fin r ↪ Fin r') (π : Fin k → Fin k') : Template p r' k' where
  literalWidth := T.literalWidth
  entry := T.entry
  code j := relocate ρ π (T.code j)

/-- Project a relocated configuration onto its component registers while retaining the program
counter, persistent word, and private memory. -/
def restrictConfig (ρ : Fin r ↪ Fin r') (c : Config w p r') : Config w p r :=
  ⟨c.pc, c.persistent, c.reg ∘ ρ, c.privateMem⟩

private theorem restrict_put (ρ : Fin r ↪ Fin r') (c : Config w p r') (j : Fin p) (i : Fin r) (v : Word w) :
    restrictConfig ρ (c.put j (ρ i) v) = (restrictConfig ρ c).put j i v := by
  unfold Config.put restrictConfig
  congr 1
  funext a
  by_cases h : a = i <;> simp [Function.comp_apply, h]

private theorem relocate_resize {v : ℕ} (ρ : Fin r → Fin r') (π : Fin k → Fin k') (i : Instr v p r k) :
    (relocate ρ π i).resize w = relocate ρ π (i.resize w) := by cases i <;> rfl

private def projectAction (ρ : Fin r ↪ Fin r') :
    CallAction w (Config w p r') → CallAction w (Config w p r)
  | .localStep c => .localStep (restrictConfig ρ c)
  | .branch q => .branch (restrictConfig ρ ∘ q)
  | .read a q => .read a (restrictConfig ρ ∘ q)
  | .write a v c => .write a v (restrictConfig ρ c)
  | .finish s => .finish s
  | .reject => .reject

private theorem project_step (T : Template p r k) (ρ : Fin r ↪ Fin r') (π : Fin k → Fin k')
    (pub : Fin k' → Word w) (c : Config w p r') :
    projectAction ρ (((widen T ρ π).instantiate w pub).program.step c) =
      (T.instantiate w (pub ∘ π)).program.step (restrictConfig ρ c) := by
  simp only [Machine.program, Template.instantiate, widen, relocate_resize]
  change projectAction ρ ((relocate ρ π ((T.code c.pc).resize w)).run pub c) =
    ((T.code c.pc).resize w).run (pub ∘ π) (restrictConfig ρ c)
  generalize (T.code c.pc).resize w = op
  cases op <;> simp only [relocate, Instr.run, projectAction, Function.comp_def, restrict_put]
  all_goals rfl

/-- The enclosing register file executes the component on its own embedded
operands, with identical event logs, returned words, and rejection behavior. -/
theorem execute_widen (T : Template p r k) (ρ : Fin r ↪ Fin r') (π : Fin k → Fin k')
    (pub : Fin k' → Word w) (fuel : ℕ) (c : Config w p r') (m : Memory w) (bits : List Bool) :
    execute ((widen T ρ π).instantiate w pub).program fuel c m bits =
      execute (T.instantiate w (pub ∘ π)).program fuel (restrictConfig ρ c) m bits := by
  induction fuel generalizing c m bits with
  | zero => rfl
  | succ f ih =>
    rw [execute, execute, ← project_step]
    cases hs : ((widen T ρ π).instantiate w pub).program.step c <;> simp only [projectAction, Function.comp_apply]
    all_goals first | rfl | (rw [ih]) | (cases bits <;> simp [ih])

/-- At each fresh call boundary operand relocation has zero overhead. -/
theorem execute_widen_start (T : Template p r k) (ρ : Fin r ↪ Fin r') (π : Fin k → Fin k')
    (pub : Fin k' → Word w) (fuel : ℕ) (st : Word w) (m : Memory w) (bits : List Bool) :
    let large := ((widen T ρ π).instantiate w pub).program
    let small := (T.instantiate w (pub ∘ π)).program
    execute large fuel (large.start st) m bits = execute small fuel (small.start st) m bits :=
  execute_widen T ρ π pub fuel _ m bits

end LiveStageLink

end VPVNP
end Computability
end OAI
