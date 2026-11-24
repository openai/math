import OAI.Computability.VPVNP.RAMTapeISASemantics
import OAI.Computability.VPVNP.RAMTapeISAComparison
import OAI.Computability.VPVNP.RAMTapePrivateISALoad
import OAI.Computability.VPVNP.RAMTapePrivateISAStore
import OAI.Computability.VPVNP.RAMTapeWordISAStage

/-!
# Compiling the deterministic work of every RAM instruction

Each fixed instruction selects one finite stack routine. Register operands are
copied before overwriting a destination. Conditional branches leave one test
bit. Operations handled by the outer call controller return immediately.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ISA

open BurstRAM PrivateRAM TapeWord

variable {v w p r k : ℕ}

/-- Compile the deterministic portion of an instruction, staging operands and leaving a
comparison bit for a conditional jump. -/
def prepare : Instr v p r k → FiniteRoutine (Port r k)
  | .constant dst val _ => loadLiteral val.val dst
  | .publicWord dst j _ => loadOperand (.pub j) (.reg dst)
  | .stateWord dst _ => loadOperand .persistent (.reg dst)
  | .copy dst src _ => if src = dst then FiniteRoutine.ret else loadOperand (.reg src) (.reg dst)
  | .binary op dst x y _ => binary op dst x y
  | .loadPrivate dst addr _ => loadPrivate dst addr
  | .storePrivate addr src _ => storePrivate addr src
  | .jumpEq x y _ _ => compareRegs .eq x y
  | .jumpLt x y _ _ => compareRegs .lt x y
  | _ => FiniteRoutine.ret

/-- Bank after the instruction’s local effects, with its jump-test bit placed on work stack
zero when applicable. -/
def preparedBank (i : Instr v p r k) (pub : Fin k → Word w) (c : LogConfig w p r) : Stacks (Port r k) :=
  let s := configBank pub (post i pub c)
  match jumpTest i c with
  | none => s
  | some b => Function.update s (.work 0) [b]

private theorem loadReg_at (pub : Fin k → Word w) (c : LogConfig w p r) (src : Port r k) (dst : Fin r)
    (v : Word w) (hd : src ≠ .reg dst) (hs : copySafe src) (he : configBank pub c src = wordBits v) :
    (loadOperand src (.reg dst)).Runs (8*w + 3) (configBank pub c)
      (bank pub c.persistent (Function.update c.reg dst v) c.writes) := by
  have h := loadOperand_runs hd hs (by simp [copySafe]) (configBank pub c) rfl rfl
  rw [he] at h
  change (loadOperand src (.reg dst)).Runs ((wordBits (c.reg dst)).length + 7*(wordBits v).length+3)
    (configBank pub c) (Function.update (bank pub c.persistent c.reg c.writes) (.reg dst) (wordBits v)) at h
  rw [bank_updateReg, length_wordBits, length_wordBits] at h
  convert h using 1
  omega

/-- The dispatch bound is independent of register values, addresses, and
private branch choices. Each private load may inspect every prior write. -/
def prepareBound (width writes : ℕ) := 100 * (width + 1)^2 * (writes + 1)

private theorem basic_bound (w n : ℕ) : 100 * (w + 1)^2 ≤ prepareBound w n :=
  Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

private theorem linear_bound (w n : ℕ) : 26*w+11 ≤ prepareBound w n :=
  (by nlinarith [Nat.zero_le (w^2)] : 26*w+11 ≤ 100*(w+1)^2).trans (basic_bound ..)

private theorem private_bound (a : Word w) (log : WriteLog w) :
    17*w+8+AddressLog.loadCost a log ≤ prepareBound w log.length := by
  apply (loadPrivate_cost_le a log).trans
  unfold prepareBound
  ring_nf
  omega

theorem prepare_runs (i : Instr v p r k) (pub : Fin k → Word w) (c : LogConfig w p r) :
    ∃ t ≤ prepareBound w c.writes.length, (prepare i).Runs t (configBank pub c) (preparedBank i pub c) := by
  have hlin := linear_bound w c.writes.length
  cases i with
  | constant dst val pc => exact ⟨_, by omega, loadLiteral_run ..⟩
  | publicWord dst j pc => exact ⟨_, by omega, loadReg_at pub c (.pub j) dst (pub j)
      (by simp) (by simp [copySafe]) rfl⟩
  | stateWord dst pc => exact ⟨_, by omega, loadReg_at pub c .persistent dst c.persistent
      (by simp) (by simp [copySafe]) rfl⟩
  | copy dst src pc =>
    by_cases h : src = dst
    · subst src
      refine ⟨1, by omega, ?_⟩
      simpa [prepare, preparedBank, jumpTest, post, configBank, FiniteRoutine.ret, FiniteRoutine.ofRoutine] using
        Routine.runs_ret (configBank pub c)
    · refine ⟨8*w+3, by omega, ?_⟩
      simpa only [prepare, h, ↓reduceIte, preparedBank, jumpTest, post, configBank] using
        loadReg_at pub c (.reg src) dst (c.reg src) (by simpa using h) (by simp [copySafe]) rfl
  | binary op dst x y pc =>
    obtain ⟨t, ht, hr⟩ := binary_runs op dst x y pub c.persistent c.reg c.writes
    exact ⟨t, ht.trans (basic_bound ..), hr⟩
  | loadPrivate dst addr pc => exact ⟨_, private_bound .., loadPrivate_run ..⟩
  | storePrivate addr src pc => exact ⟨_, hlin, storePrivate_run ..⟩
  | jumpEq x y yes no => exact ⟨_, by omega, compareRegs_run .eq x y pub c.persistent c.reg c.writes⟩
  | jumpLt x y yes no => exact ⟨_, by omega, compareRegs_run .lt x y pub c.persistent c.reg c.writes⟩
  | choose | readExternal | writeExternal | returnState | accept | reject =>
    exact ⟨1, by omega, Routine.runs_ret _⟩

end RAMTape.ISA

end VPVNP
end Computability
end OAI
