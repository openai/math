import OAI.Computability.VPVNP.RAMTapeISAPorts
import OAI.Computability.VPVNP.RAMTapeWordOperands

/-!
# Architectural operand staging and scratch cleanup

Copies may read architectural, public, or temporary stacks. Two reserved
work stacks hold the reversed source and output during a copy. A same-register
copy is a separate no-op in the instruction dispatcher. Other instructions
stage their inputs before writing a destination that aliases an input.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ISA

open TapeWord BurstRAM

variable {r k w : ℕ}

/-- The port avoids work stacks 14 and 15, both reserved by operand copying. -/
def copySafe (i : Port r k) := i ≠ .work 14 ∧ i ≠ .work 15

/-- Route a copying scan to the source, destination, and the two reserved work stacks. -/
def copyPorts (src dst : Port r k) : ScanPort → Port r k
  | .left => src
  | .right => .work 14
  | .tmp => .work 15
  | .out => dst

theorem copyPorts_injective {src dst : Port r k} (hd : src ≠ dst) (hs : copySafe src)
    (ht : copySafe dst) : Function.Injective (copyPorts src dst) := by
  obtain ⟨hs₁, hs₂⟩ := hs
  obtain ⟨ht₁, ht₂⟩ := ht
  have hw : (Port.work 14 : Port r k) ≠ .work 15 := fun he => (by decide : (14 : Fin 16) ≠ 15) (Port.work.inj he)
  intro i j he
  cases i <;> cases j <;> simp_all [copyPorts]

private theorem install_copy {src dst : Port r k} (hd : src ≠ dst) (hs : copySafe src) (ht : copySafe dst)
    (s : Stacks (Port r k)) (h14 : s (.work 14) = []) (h15 : s (.work 15) = []) (out : List Bool) :
    installStacks (copyPorts src dst) s (scanStacks (s src) [] [] out) = Function.update s dst out := by
  have hp := copyPorts_injective hd hs ht
  funext j
  by_cases h : ∃ i, copyPorts src dst i = j
  · obtain ⟨i, rfl⟩ := h
    rw [installStacks_at hp]
    cases i <;> simp [copyPorts, scanStacks, Function.update, hd, Ne.symm ht.1, Ne.symm ht.2, h14, h15]
  · have hj : j ≠ dst := fun he => h ⟨.out, he.symm⟩
    rw [installStacks_outside _ _ (not_exists.mp h), Function.update_of_ne hj]

private def operandReturn {A : Type} : Operand.State A → Bool
  | .done _ => true
  | _ => false

private theorem operandReturn_halts {A : Type} (step : A → Bool → Bool × A) :
    ∀ q, operandReturn q = true → ((Operand.code step) q).returns = true := by
  intro q h
  cases q <;> simp_all [operandReturn, Operand.code]

/-- Copy a word from the source port to the destination with the finite operand scan. -/
def loadOperand (src dst : Port r k) : FiniteRoutine (Port r k) :=
  FiniteRoutine.ofStackCode (Operand.code Operand.copyBit) (copyPorts src dst) (.clear ()) operandReturn

theorem loadOperand_runs {src dst : Port r k} (hd : src ≠ dst) (hs : copySafe src) (ht : copySafe dst)
    (s : Stacks (Port r k)) (h14 : s (.work 14) = []) (h15 : s (.work 15) = []) :
    (loadOperand src dst).Runs ((s dst).length + 7 * (s src).length + 3) s (Function.update s dst (s src)) := by
  have h := FiniteRoutine.runs_ofStackCode (copyPorts_injective hd hs ht) (normal := operandReturn)
    rfl rfl (operandReturn_halts _) s (Operand.copy_run (s src) (s dst))
  rwa [install_copy hd hs ht s h14 h15, Function.update_eq_self, install_copy hd hs ht s h14 h15] at h

/-- Clear a stack by popping until the first empty test. -/
def clearPort (i : Port r k) : FiniteRoutine (Port r k) := FiniteRoutine.ofRoutine {
  entry := ()
  code := fun _ => .pop i fun b => b.map fun _ => () }

theorem clearPort_runs (i : Port r k) (s : Stacks (Port r k)) :
    (clearPort i).Runs ((s i).length + 1) s (Function.update s i []) := by
  suffices h : ∀ xs (t : Stacks (Port r k)), t i = xs →
      (clearPort i).Runs (xs.length + 1) t (Function.update t i []) by exact h _ s rfl
  intro xs
  induction xs with
  | nil =>
    intro t he
    have hs := StackStep.pop (s := t) (code := (clearPort i).body.standalone)
      (q := some (clearPort i).body.entry)
      (show (clearPort i).body.standalone (some (clearPort i).body.entry) =
          .pop i (fun b => b.map fun _ => ()) from rfl)
    rw [he] at hs
    exact .cons hs (.nil ..)
  | cons b xs ih =>
    intro t he
    have hs := StackStep.pop (s := t) (code := (clearPort i).body.standalone)
      (q := some (clearPort i).body.entry)
      (show (clearPort i).body.standalone (some (clearPort i).body.entry) =
          .pop i (fun b => b.map fun _ => ()) from rfl)
    rw [he] at hs
    have hr := ih (Function.update t i xs) (Function.update_self ..)
    rw [Function.update_idem] at hr
    exact .cons hs hr

/-- Load a fixed natural literal into the destination register using the persistent word to
determine the bit width. -/
def loadLiteral (n : ℕ) (dst : Fin r) : FiniteRoutine (Port r k) :=
  FiniteRoutine.ofStackCode (Operand.code (Operand.literalBit n)) (copyPorts .persistent (.reg dst))
    (.clear (Fin.last n)) operandReturn

theorem loadLiteral_run (n : ℕ) (dst : Fin r) (pub : Fin k → Word w) (persist : Word w)
    (reg : Fin r → Word w) (log : PrivateRAM.WriteLog w) :
    (loadLiteral n dst).Runs (8*w+3) (bank pub persist reg log)
      (bank pub persist (Function.update reg dst (Fin.ofNat (2^w) n)) log) := by
  let s := bank pub persist reg log
  obtain ⟨exit, h⟩ := Operand.literal_run n persist (s (.reg dst))
  have hd : (Port.persistent : Port r k) ≠ .reg dst := by simp
  have hs : copySafe (Port.persistent : Port r k) := by simp [copySafe]
  have ht : copySafe (Port.reg dst : Port r k) := by simp [copySafe]
  have hr := FiniteRoutine.runs_ofStackCode (copyPorts_injective hd hs ht) (normal := operandReturn)
    rfl (exit := .done exit) rfl (operandReturn_halts _) s h
  change (loadLiteral n dst).Runs ((s (.reg dst)).length + 7*w+3)
    (installStacks (copyPorts .persistent (.reg dst)) s (scanStacks (s .persistent) [] [] (s (.reg dst))))
    (installStacks (copyPorts .persistent (.reg dst)) s (scanStacks (s .persistent) [] [] (wordBits (Fin.ofNat _ n)))) at hr
  rw [install_copy hd hs ht s rfl rfl, Function.update_eq_self, install_copy hd hs ht s rfl rfl] at hr
  dsimp only [s] at hr
  rw [bank_updateReg] at hr
  convert hr using 1
  change 8*w+3 = (wordBits (reg dst)).length + 7*w+3
  rw [length_wordBits]
  omega

/-- A fresh call may initially have empty registers. The width template in
the persistent port determines the literal independently of the old register. -/
theorem loadLiteral_at (n : ℕ) (dst : Fin r) (s : Stacks (Port r k)) (persist : Word w)
    (hp : s .persistent = wordBits persist) (h14 : s (.work 14) = []) (h15 : s (.work 15) = []) :
    (loadLiteral n dst).Runs ((s (.reg dst)).length + 7*w+3) s
      (Function.update s (.reg dst) (wordBits (Fin.ofNat (2^w) n))) := by
  obtain ⟨exit, h⟩ := Operand.literal_run n persist (s (.reg dst))
  have hd : (Port.persistent : Port r k) ≠ .reg dst := by simp
  have hs : copySafe (Port.persistent : Port r k) := by simp [copySafe]
  have ht : copySafe (Port.reg dst : Port r k) := by simp [copySafe]
  have hr := FiniteRoutine.runs_ofStackCode (copyPorts_injective hd hs ht) (normal := operandReturn)
    rfl (exit := .done exit) rfl (operandReturn_halts _) s h
  rw [← hp] at hr
  rw [install_copy hd hs ht s h14 h15, Function.update_eq_self, install_copy hd hs ht s h14 h15] at hr
  exact hr

end RAMTape.ISA

end VPVNP
end Computability
end OAI
